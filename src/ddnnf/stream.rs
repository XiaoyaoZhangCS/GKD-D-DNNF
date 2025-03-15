use std::cmp::Reverse;
use std::collections::{BTreeSet, BinaryHeap, HashSet};
use std::io::BufRead;
use std::iter::FromIterator;
use std::path::Path;
use std::process::exit;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, TryRecvError};
use std::sync::Arc;
use std::{io, thread};

use itertools::{Either, Itertools};
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::character::complete::{char, digit1};
use nom::combinator::{map_res, opt, recognize};
use nom::sequence::{pair, tuple};
use nom::IResult;
use workctl::WorkQueue;

use crate::parser::persisting::{write_cnf_to_file, write_ddnnf_to_file};
use crate::{parser::util::*, Ddnnf};

impl Ddnnf {
    /// Initiate the Stream mode. This enables a commincation channel between stdin and stdout.
    /// Queries from stdin will be computed using max_worker many threads und results will be written
    /// to stdout. 'exit' as Input and breaking the stdin pipe exits Stream mode.
    pub fn init_stream(&self) {
        let mut queue: WorkQueue<(u32, String)> = WorkQueue::new();
        let stop = Arc::new(AtomicBool::new(false));
        // Create a MPSC (Multiple Producer, Single Consumer) channel. Every worker
        // is a producer, the main thread is a consumer; the producers put their
        // work into the channel when it's done.
        let (results_tx, results_rx) = mpsc::channel();
        let mut threads = Vec::new();

        for _ in 0..self.max_worker {
            // copy all the data each worker needs
            let mut t_queue = queue.clone();
            let t_stop = stop.clone();
            let t_results_tx = results_tx.clone();
            let mut ddnnf: Ddnnf = self.clone();

            // spawn a worker thread with its shared and exclusive data
            let handle = thread::spawn(move || {
                loop {
                    if t_stop.load(Ordering::SeqCst) {
                        break;
                    }
                    if let Some((id, buffer)) = t_queue.pull_work() {
                        let response = ddnnf.handle_stream_msg(&buffer);
                        match t_results_tx.send((id, response)) {
                            Ok(_) => (),
                            Err(err) => {
                                eprintln!(
                                    "Error while worker thread tried to sent \
                                a result to the master: {err}"
                                );
                                break;
                            }
                        }
                    } else {
                        // If there isn't any more work left, we can stop the busy waiting
                        // and sleep til unparked again by the main thread.
                        std::thread::park();
                    }
                }
            });

            // Add the handle for the newly spawned thread to the list of handles
            threads.push(handle);
        }

        // Main thread reads all the tasks from stdin and puts them in the queue
        let stdin_channel = spawn_stdin_channel();
        let mut remaining_answers = 0;
        let mut id = 0_u32;
        let mut output_id = 0_u32;
        let mut results: BinaryHeap<Reverse<(u32, String)>> = BinaryHeap::new();

        // Check whether next result/s to print is/are already in the result heap.
        // If thats the case, we print it/them. Anotherwise, we do nothing.
        let mut print_result = |results: &mut BinaryHeap<Reverse<(u32, String)>>| {
            while let Some(Reverse((id, res))) = results.peek() {
                if *id == output_id {
                    println!("{res}");
                    results.pop();
                    output_id += 1;
                } else {
                    break;
                }
            }
        };

        // loop til there are no more tasks to do
        loop {
            print_result(&mut results);

            // Check if we got any result
            match results_rx.try_recv() {
                Ok(val) => {
                    results.push(Reverse(val));
                    remaining_answers -= 1;
                }
                Err(err) => {
                    if err == TryRecvError::Disconnected {
                        eprintln!(
                            "A worker thread disconnected \
                        while working on a stream task. Aborting..."
                        );
                        exit(1);
                    }
                }
            }

            // Check if there is anything we can distribute to the workers
            match stdin_channel.try_recv() {
                Ok(buffer) => {
                    if buffer.as_str() == "exit" {
                        break;
                    }
                    queue.push_work((id, buffer.clone()));
                    id += 1;
                    remaining_answers += 1;
                }
                Err(err) => {
                    if err == TryRecvError::Disconnected {
                        break;
                    }
                }
            }

            // Wake up all worker if there is work left todo
            if remaining_answers > 0 {
                threads.iter().for_each(|worker| worker.thread().unpark());
            }
        }

        // After all tasks are distributed, we wait for the remaining results and print them.
        while remaining_answers != 0 {
            match results_rx.recv() {
                Ok(val) => {
                    results.push(Reverse(val));
                    remaining_answers -= 1;
                }
                Err(err) => {
                    eprintln!(
                        "A worker thread send an error ({err}) \
                    while working on a stream task. Aborting..."
                    );
                    exit(1);
                }
            }
            print_result(&mut results);
        }

        // Stop busy worker loops
        stop.store(true, Ordering::SeqCst);

        // join threads
        for handle in threads {
            handle.thread().unpark(); // unpark once more to terminate threads
            handle.join().unwrap();
        }
    }

    /// error codes:
    /// E1 Operation is not yet supported
    /// E2 Operation does not exist. Neither now nor in the future
    /// E3 Parse error
    /// E4 Syntax error
    /// E5 Operation was not able to be done, because of wrong input
    /// E6 File or path error
    pub fn handle_stream_msg(&mut self, msg: &str) -> String {
        let mut args: Vec<&str> = msg.split_whitespace().collect();
        if args.is_empty() {
            return String::from("E4 error: got an empty msg");
        }
        if let Some(duplicate) = contains_input_duplicate_commands_or_params(msg) {
            return format!("E4 error: \"{duplicate}\" occurs at least twice in the stream msg");
        }

        let mut param_index = 1;

        let mut params = Vec::new();
        let mut values = Vec::new();
        let mut seed = 42;
        let mut limit = None;
        let mut add_clauses: Vec<BTreeSet<i32>> = Vec::new();
        let mut rmv_clauses: Vec<BTreeSet<i32>> = Vec::new();
        let mut total_features = self.number_of_variables;
        let mut path = Path::new("");

        // We check for an adjustement of total-features beforehand.
        // This adjustment is only valid together with the clause-update command.
        if let Some(index) = args.iter().position(|&s| s == "total-features" || s == "t") {
            if args[0] != "clause-update" {
                return format!(
                    "E4 error: {:?} can only be used in combination with \"clause-update\"",
                    args[index]
                );
            }
            let mut succesful_update = false;
            // The boundary must be positive while still being in the limits of an i32
            if let Ok((numbers, len)) = get_numbers(&args[index + 1..], i32::MAX as u32) {
                if len == 1 && numbers[0] > 0 {
                    if self
                        .cached_state
                        .as_mut()
                        .unwrap()
                        .contains_conflicting_clauses(numbers[0] as u32)
                    {
                        return String::from("E5 error: at least one clause is in conflict with the feature reduction; remove conflicting clauses");
                    }

                    total_features = numbers[0] as u32;
                    succesful_update = true;
                    // Remove the "total-features" param and its subsequent value
                    args.remove(index);
                    args.remove(index);
                }
            }
            if !succesful_update {
                return format!(
                    "E4 error: {:?} must be set to a single positive number",
                    args[index]
                );
            }
        }

        // go through all possible extra values that can be provided til
        // either there are no more or we can't parse anymore
        while param_index < args.len() {
            param_index += 1;
            match args[param_index - 1] {
                "a" | "assumptions" => {
                    params = match get_numbers(&args[param_index..], total_features) {
                        Ok((numbers, len)) => {
                            param_index += len;
                            numbers
                        }
                        Err(e) => return e,
                    };
                }
                "v" | "variables" => {
                    values = match get_numbers(&args[param_index..], total_features) {
                        Ok((numbers, len)) => {
                            param_index += len;
                            numbers
                        }
                        Err(e) => return e,
                    };
                }
                "seed" | "s" | "limit" | "l" | "path" | "p" => {
                    if param_index < args.len() {
                        match args[param_index - 1] {
                            "seed" | "s" => {
                                seed = match args[param_index].parse::<u64>() {
                                    Ok(x) => x,
                                    Err(e) => return format!("E3 error: {}", e),
                                };
                                param_index += 1;
                            }
                            "limit" | "l" => {
                                limit = match args[param_index].parse::<usize>() {
                                    Ok(x) => Some(x),
                                    Err(e) => return format!("E3 error: {}", e),
                                };
                                param_index += 1;
                            }
                            _ => {
                                // has to be path because of the outer patter match
                                // we use a wildcard to satisfy the rust compiler
                                path = Path::new(args[param_index]);
                                param_index += 1;
                            }
                        }
                    } else {
                        return format!(
                            "E4 error: param \"{}\" was used, but no value supplied",
                            args[param_index - 1]
                        );
                    }
                }
                "add" | "rmv" => {
                    let mut res = Vec::new();
                    let is_add = args[param_index - 1] == "add";

                    match split_clauses(&args[param_index..]) {
                        Ok(split) => {
                            for s in split {
                                res.push(get_numbers(&s, total_features));
                                match get_numbers(&s, total_features) {
                                    Ok((numbers, len)) => {
                                        param_index += len;
                                        // Additional offset if the last clause end with '0'
                                        if param_index < args.len() && "0" == args[param_index] {
                                            param_index += 1;
                                        }

                                        // Mapping of clauses to set of additions / removals
                                        if is_add {
                                            add_clauses.push(numbers.into_iter().collect());
                                        } else {
                                            rmv_clauses.push(numbers.into_iter().collect());
                                        }
                                    }
                                    Err(err) => return err,
                                };
                            }
                        }
                        Err(err) => return err,
                    }
                }
                other => {
                    return format!(
                        "E4 error: the option \"{}\" is not valid in this context",
                        other
                    )
                }
            }
        }

        match args[0] {
            "core" => op_with_assumptions_and_vars(
                |d, assumptions, vars| {
                    if vars {
                        let could_be_core = assumptions.pop().unwrap();
                        let without_cf = Ddnnf::execute_query(d, assumptions);
                        assumptions.push(could_be_core);
                        let with_cf = Ddnnf::execute_query(d, assumptions);

                        if with_cf == without_cf {
                            Some(could_be_core.to_string())
                        } else {
                            None
                        }
                    } else if assumptions.is_empty() {
                        let mut core = Vec::from_iter(&d.core);
                        core.sort_by_key(|a| a.abs());
                        Some(format_vec(core.iter()))
                    } else {
                        let mut core = Vec::new();
                        let reference = Ddnnf::execute_query(d, assumptions);
                        for i in 1_i32..=d.number_of_variables as i32 {
                            assumptions.push(i);
                            let inter = Ddnnf::execute_query(d, assumptions);
                            if reference == inter {
                                core.push(i);
                            }
                            if inter == 0 {
                                core.push(-i);
                            }
                            assumptions.pop();
                        }
                        Some(format_vec(core.iter()))
                    }
                },
                self,
                &mut params,
                &values,
            ),
            "count" => op_with_assumptions_and_vars(
                |d, x, _| Some(Ddnnf::execute_query(d, x)),
                self,
                &mut params,
                &values,
            ),
            "sat" => op_with_assumptions_and_vars(
                |d, x, _| Some(Ddnnf::sat(d, x)),
                self,
                &mut params,
                &values,
            ),
            "enum" => {
                let limit_interpretation = match limit {
                    Some(limit) => limit,
                    None => {
                        if self.rc() > 1_000 {
                            1_000
                        } else {
                            self.rc().to_usize_wrapping()
                        }
                    }
                };
                let configs = self.enumerate(&mut params, limit_interpretation);
                match configs {
                    Some(s) => format_vec_vec(s.iter()),
                    None => String::from("E5 error: with the assumptions, the ddnnf is not satisfiable. Hence, there exist no valid sample configurations"),
                }
            }
            "random" => {
                let limit_interpretation = limit.unwrap_or(1);
                let samples = self.uniform_random_sampling(&params, limit_interpretation, seed);
                match samples {
                    Some(s) => format_vec_vec(s.iter()),
                    None => String::from("E5 error: with the assumptions, the ddnnf is not satisfiable. Hence, there exist no valid sample configurations"),
                }
            }
            "atomic" | "atomic-cross" => {
                if values.iter().any(|&f| f.is_negative()) {
                    return String::from("E5 error: candidates must be positive");
                }
                let candidates = if !values.is_empty() {
                    Some(values.iter().map(|&f| f as u32).collect_vec())
                } else {
                    None
                };
                let cross = args[0] == "atomic-cross";
                format_vec_vec(self.get_atomic_sets(candidates, &params, cross).iter())
            }
            "t-wise" => {
                let limit_interpretation = limit.unwrap_or(1);
                self.sample_t_wise(limit_interpretation).to_string()
            }
            "clause-update" => {
                if self.can_save_state() {
                    if self.update_cached_state(
                        Either::Left((add_clauses, rmv_clauses)),
                        Some(total_features),
                    ) {
                        String::from("")
                    } else {
                        String::from("E5 error: could not update cached state")
                    }
                } else {
                    String::from("E5 error: clauses corresponding to the d-DNNF aren't available; the input file must be a CNF")
                }
            }
            "undo-update" => {
                if self.undo_on_cached_state() {
                    String::from("")
                } else {
                    String::from(
                        "E5 error: could not perform undo; there does not exist any cached state1",
                    )
                }
            }
            "exit" => String::from("exit"),
            "save-cnf" | "save-ddnnf" => {
                if path.to_str().unwrap() == "" {
                    return String::from("E6 error: no file path was supplied");
                }
                if !path.is_absolute() {
                    return String::from("E6 error: file path is not absolute, but has to be");
                }

                if args[0] == "save-ddnnf" {
                    match write_ddnnf_to_file(self, path.to_str().unwrap()) {
                        Ok(_) => String::from(""),
                        Err(e) => format!(
                            "E6 error: {} while trying to write ddnnf to {}",
                            e,
                            path.to_str().unwrap()
                        ),
                    }
                } else {
                    if self.cached_state.is_none() {
                        return String::from(
                            "E5 error: cannot save as CNF because clauses are not available",
                        );
                    }
                    match write_cnf_to_file(
                        &self.cached_state.as_mut().unwrap().clauses,
                        total_features,
                        path.to_str().unwrap(),
                    ) {
                        Ok(_) => String::from(""),
                        Err(e) => format!(
                            "E6 error: {} while trying to write cnf to {}",
                            e,
                            path.to_str().unwrap()
                        ),
                    }
                }
            }
            other => format!("E2 error: the operation \"{}\" is not supported", other),
        }
    }
}

fn op_with_assumptions_and_vars<T: ToString>(
    operation: fn(&mut Ddnnf, &mut Vec<i32>, bool) -> Option<T>,
    ddnnf: &mut Ddnnf,
    assumptions: &mut Vec<i32>,
    vars: &[i32],
) -> String {
    if vars.is_empty() {
        if let Some(v) = operation(ddnnf, assumptions, false) {
            return v.to_string();
        }
    }

    let mut response = Vec::new();
    for var in vars {
        assumptions.push(*var);
        if let Some(v) = operation(ddnnf, assumptions, true) {
            response.push(v.to_string())
        }
        assumptions.pop();
    }

    response.join(";")
}

// Checks for duplicates such as in "count a 1 2 3 a 1" which would be invalid due to a occuring twice
fn contains_input_duplicate_commands_or_params(s: &str) -> Option<&str> {
    let mut seen_text_substrings: HashSet<&str> = HashSet::new();

    for word in s.split_whitespace() {
        // Check if the word is a text substring (and also not a minus sign)
        if !word.chars().all(|c| c.is_ascii_digit() || c == '-') {
            // Check if the text substring has already been seen
            if !seen_text_substrings.insert(word) {
                // If the text substring has been seen before, the string is invalid
                return Some(word);
            }
        }
    }
    None
}

// Takes a vector of strings and splits them further in sub-vectors when encountering a '0'.
// Example:
//  ["1", "2", "3", "0", "-4", "5", "0", "6"] becomes [["1", "2", "3"], ["-4", "5"], ["6"]]
fn split_clauses<'a>(input_strings: &'a [&'a str]) -> Result<Vec<Vec<&'a str>>, String> {
    let mut result = Vec::new();
    let mut subvec = Vec::new();

    for &sub_str in input_strings {
        // If the next element isn't a number, we stop splitting
        if sub_str.parse::<f64>().is_err() {
            break;
        }

        if sub_str == "0" {
            if subvec.is_empty() {
                return Err(String::from("E4 error: detected an unallowed empty clause"));
            }
            result.push(subvec.clone());
            subvec.clear();
        } else {
            subvec.push(sub_str);
        }
    }

    // Last clause is allowed to not end with a '0'
    if !subvec.is_empty() {
        result.push(subvec);
    }
    if result.is_empty() {
        return Err(String::from("E4 error: key word is missing arguments"));
    }

    Ok(result)
}

// Parses numbers and ranges of the form START..[STOP] into a vector of i32
fn get_numbers(params: &[&str], boundary: u32) -> Result<(Vec<i32>, usize), String> {
    let mut numbers = Vec::new();
    let mut parsed_str_count = 0;

    for &param in params.iter() {
        if param.chars().any(|c| c.is_alphabetic()) {
            return Ok((numbers, parsed_str_count));
        }

        fn signed_number(input: &str) -> IResult<&str, &str> {
            recognize(pair(opt(char('-')), digit1))(input)
        }

        // try parsing by starting with the most specific combination and goind
        // to the least specific one
        let range: IResult<&str, Vec<i32>> = alt((
            // limited range
            map_res(
                tuple((signed_number, tag(".."), signed_number)),
                |s: (&str, &str, &str)| {
                    match (s.0.parse::<i32>(), s.2.parse::<i32>()) {
                        // start and stop are inclusive (removing the '=' would make stop exclusive)
                        (Ok(start), Ok(stop)) => Ok((start..=stop).collect()),
                        (Ok(_), Err(e)) | (Err(e), _) => Err(e),
                    }
                },
            ),
            // unlimited range
            map_res(pair(signed_number, tag("..")), |s: (&str, &str)| {
                match s.0.parse::<i32>() {
                    Ok(start) => Ok((start..=boundary as i32).collect()),
                    Err(e) => Err(e),
                }
            }),
            // single number
            map_res(signed_number, |s: &str| match s.parse::<i32>() {
                Ok(v) => Ok(vec![v]),
                Err(e) => Err(e),
            }),
        ))(param);

        match range {
            // '0' isn't valid in this context and gets removed
            Ok(num) => num.1.into_iter().for_each(|f| {
                if f != 0 {
                    numbers.push(f)
                }
            }),
            Err(e) => return Err(format!("E3 {}", e)),
        }
        parsed_str_count += 1;
    }

    if numbers.is_empty() {
        return Err(String::from(
            "E4 error: option used but there was no value supplied",
        ));
    }

    match check_boundary(&numbers, boundary) {
        Ok(_) => Ok((numbers, parsed_str_count)),
        Err(e) => Err(e),
    }
}

// Verifies that all numbers connected to features are within the range boundary set by the total number of features for that model
fn check_boundary(numbers: &[i32], boundary: u32) -> Result<(), String> {
    if numbers.iter().any(|v| v.abs() > boundary as i32) {
        return Err(format!(
            "E3 error: not all parameters are within the boundary of {} to {}",
            -(boundary as i32),
            boundary as i32
        ));
    }
    Ok(())
}

// spawns a new thread that listens on stdin and delivers its request to the stream message handling
fn spawn_stdin_channel() -> Receiver<String> {
    let (tx, rx) = mpsc::channel::<String>();
    thread::spawn(move || {
        let stdin = io::stdin();
        let lines = stdin.lock().lines();
        for line in lines {
            tx.send(line.unwrap()).unwrap()
        }
    });
    rx
}