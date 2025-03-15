use std::{
    error::Error,
    fs::File,
    io::{BufWriter, Write},
    sync::mpsc,
    thread, time::Duration,
};
use std::time::Instant;
use workctl::WorkQueue;

use crate::{parser, Ddnnf};
use std::cmp::max;

impl Ddnnf {
    #[inline]
    /// Computes the given operation for all queries in path_in.
    /// The results are saved in the path_out. The .csv ending always gets added to the user input.
    /// Here, the number of threads influence the speed by using a shared work queue.
    pub fn operate_on_queries<T: std::fmt::Debug + Ord + Send + 'static>(
        &mut self,
        operation: fn(&mut Ddnnf, &[i32]) -> T,
        path_in: &str,
        path_out: &str,
    ) -> Result<(), Box<dyn Error>> {
        println!("max_worker = {}",self.max_worker);
        if self.max_worker == 1 {
            self.queries_single_thread(operation, path_in, path_out)
        } else {
            self.queries_multi_thread(operation, path_in, path_out)
        }
    }

    /// Computes the operation for all queries in path_in
    /// in a multi threaded environment
    /// Here we have to take into account:
    ///     1) using channels for communication
    ///     2) cloning the ddnnf
    ///     3) sorting our results
    fn queries_single_thread<T: std::fmt::Debug>(
        &mut self,
        operation: fn(&mut Ddnnf, &[i32]) -> T,
        path_in: &str,
        path_out: &str,
    ) -> Result<(), Box<dyn Error>> {
        // start the file writer with the file_path
        let f = File::create(path_out).expect("Unable to create file");
        let mut wtr = BufWriter::new(f);

        let work_queue: Vec<(usize, Vec<i32>)> = parser::parse_queries_file(path_in);
        let mut max_duration = Duration::new(0,0);
        let mut avg_duration = Duration::new(0,0);
        let mut num = 0;
        for (_, work) in &work_queue {
            num += 1;
            let start = Instant::now();
            let cardinality = operation(self, work);
            let duration = start.elapsed();

            let mut features_str = work
                .iter()
                .fold(String::new(), |acc, &num| acc + &num.to_string() + " ");
            features_str.pop();

            let data = &format!("partial_config: {}, solution_num: {:?}\n", features_str, cardinality);
            wtr.write_all(data.as_bytes())?;
            
            max_duration = max(duration,max_duration);
            avg_duration += duration;

            let data = &format!("time: {:?}\n\n",duration);
            wtr.write_all(data.as_bytes())?;

        }

        let data = &format!("max_time: {:?}\navg_time: {:?}",max_duration,avg_duration/num);
        wtr.write_all(data.as_bytes())?;

        Ok(())
    }

    /// Computes the cardinality of partial configurations for all queries in path_in
    /// in a multi threaded environment
    fn queries_multi_thread<T: std::fmt::Debug + Ord + Send + 'static>(
        &mut self,
        operation: fn(&mut Ddnnf, &[i32]) -> T,
        path_in: &str,
        path_out: &str,
    ) -> Result<(), Box<dyn Error>> {
        let work: Vec<(usize, Vec<i32>)> = parser::parse_queries_file(path_in);
        let mut queue = WorkQueue::with_capacity(work.len());

        for e in work.clone() {
            queue.push_work(e);
        }

        let (results_tx, results_rx) = mpsc::channel();

        let mut threads = Vec::new();

        for _ in 0..self.max_worker {
            let mut t_queue = queue.clone();
            let t_results_tx = results_tx.clone();
            let mut ddnnf: Ddnnf = self.clone();

            // thread::spawn takes a closure (an anonymous function that "closes"
            // over its environment). The move keyword means it takes ownership of
            // those variables, meaning they can't be used again in the main thread.
            let handle = thread::spawn(move || {
                // Loop while there's expected to be work, looking for work.
                // If work is available, do that work.
                while let Some((index, work)) = t_queue.pull_work() {
                    // Send the work and the result of that work.
                    //
                    // Sending could fail. If so, there's no use in
                    // doing any more work, so abort.
                    let work_c = work.clone();
                    match t_results_tx.send((index, work_c, operation(&mut ddnnf, &work))) {
                        Ok(_) => (),
                        Err(_) => {
                            break;
                        }
                    }
                }

                // Signal to the operating system that now is a good time
                // to give another thread a chance to run.
                std::thread::yield_now();
            });

            // Add the handle for the newly spawned thread to the list of handles
            threads.push(handle);
        }

        // start the file writer with the file_path
        let f = File::create(path_out).expect("Unable to create file");
        let mut wtr = BufWriter::new(f);
        let mut results = Vec::new();

        // Get completed work from the channel while there's work to be done.
        for _ in 0..work.len() {
            match results_rx.recv() {
                // If the control thread successfully receives, a job was completed.
                Ok(result) => {
                    results.push(result);
                }
                // If the control thread is the one left standing, that's pretty
                // problematic.
                Err(_) => {
                    panic!("All workers died unexpectedly.");
                }
            }
        }

        results.sort_unstable();

        for (_, query, result) in results {
            let mut features_str = query
                .iter()
                .fold(String::new(), |acc, &num| acc + &num.to_string() + " ");
            features_str.pop();
            let data = &format!("{},{:?}\n", features_str, result);
            wtr.write_all(data.as_bytes())?;
        }

        // Just make sure that all the other threads are done.
        for handle in threads {
            handle.join().unwrap();
        }

        // Flush everything into the file that is still in a buffer
        // Now we finished writing the csv file
        wtr.flush()?;

        // If everything worked as expected, then we can return Ok(()) and we are happy :D
        Ok(())
    }
}