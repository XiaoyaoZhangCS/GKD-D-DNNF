pub mod c2d_lexer;

use c2d_lexer::{lex_line_c2d, C2DToken, TId};

pub mod d4_lexer;
use d4_lexer::{lex_line_d4, D4Token};

pub mod from_cnf;
use from_cnf::{check_for_cnf_header, CNFToken};
use nom::{And, ToUsize};
use rand_distr::num_traits::ToPrimitive;

pub mod persisting;
pub mod util;


use core::panic;
use std::{
    cell::RefCell, cmp::max, collections::{BTreeSet, HashMap, HashSet, VecDeque}, ffi::OsStr, fs::{self, File}, hash::Hash, io::{BufRead, BufReader, Write}, path::Path, process, rc::Rc, time::Duration
};

use rug::{Complete, Integer};

use crate::ddnnf::{self, anomalies::t_wise_sampling::sat_wrapper, node::{self, Node, NodeType}, Ddnnf};

use petgraph::{
    graph::{Edge, EdgeIndex, NodeIndex},
    stable_graph::{Neighbors, StableGraph},
    visit::{DfsPostOrder, EdgeRef, IntoNeighborsDirected},
    Direction::{Incoming, Outgoing},
};

use bit_set::BitSet;

use rayon::{iter::empty, prelude::*};
use std::sync::Mutex;
/// Parses a ddnnf, referenced by the file path. The file gets parsed and we create
/// the corresponding data structure.
///
/// # Examples
///
/// ```
/// extern crate ddnnf_lib;
/// use ddnnf_lib::parser;
/// use ddnnf_lib::Ddnnf;
///
/// let file_path = "./tests/data/small_ex_c2d.nnf";
///
/// let ddnnfx: Ddnnf = parser::build_ddnnf(file_path, None);
/// ```
///
/// # Panics
///
/// The function panics for an invalid file path.
#[inline]
pub fn build_ddnnf(mut path: &str, mut total_features: Option<u32>) -> Ddnnf {
    let mut clauses = BTreeSet::new();
    if let Some(extension) = Path::new(path).extension().and_then(OsStr::to_str) {
        if extension == "dimacs" || extension == "cnf" {
            #[cfg(feature = "d4")]
            {
                let file = open_file_savely(path);
                let lines = BufReader::new(file).lines();
                for line in lines {
                    let line = line.expect("Unable to read line");
                    match check_for_cnf_header(line.as_str()).unwrap().1 {
                        CNFToken::Header {
                            total_features: total_features_header,
                            total_clauses: _,
                        } => {
                            let ddnnf_file = ".intermediate.nnf";
                            d4_oxide::compile_ddnnf(path.to_string(), ddnnf_file.to_string());
                            path = ddnnf_file;
                            total_features = Some(total_features_header as u32);
                        }
                        CNFToken::Clause { features } => {
                            clauses.insert(features);
                        }
                        CNFToken::Comment => (),
                    }
                }
            }

            #[cfg(not(feature = "d4"))]
            {
                panic!("CNF to d-DNNF compilation is only possible when including d4.");
            }
        }
    }

    let file = open_file_savely(path);
    let lines = BufReader::new(file)
        .lines()
        .map(|line| line.expect("Unable to read line"))
        .collect::<Vec<String>>();

    if path == ".intermediate.nnf" {
        fs::remove_file(path).unwrap();
    }

    if clauses.is_empty() {
        distribute_building(lines, total_features, None)
    } else {
        distribute_building(lines, total_features, Some(clauses))
    }
}





pub static mut GLOBAL_M: u32 = 10;
pub static mut GLOBAL_N: u32 = 10;
pub static mut GLOBAL_T: u32 = 10;


#[inline]
pub fn my_build_ddnnf(mut path: &str, mut total_features: Option<u32>, m: u32,n: u32,t:u32) -> Ddnnf {
    unsafe {
        GLOBAL_M = m;
        GLOBAL_N = n;
        GLOBAL_T = t;
    }
    

    let mut clauses = BTreeSet::new();
    if let Some(extension) = Path::new(path).extension().and_then(OsStr::to_str) {
        if extension == "dimacs" || extension == "cnf" {
            #[cfg(feature = "d4")]
            {
                let file = open_file_savely(path);
                let lines = BufReader::new(file).lines();
                for line in lines {
                    let line = line.expect("Unable to read line");
                    match check_for_cnf_header(line.as_str()).unwrap().1 {
                        CNFToken::Header {
                            total_features: total_features_header,
                            total_clauses: _,
                        } => {
                            let ddnnf_file = ".intermediate.nnf";
                            d4_oxide::compile_ddnnf(path.to_string(), ddnnf_file.to_string());
                            path = ddnnf_file;
                            total_features = Some(total_features_header as u32);
                        }
                        CNFToken::Clause { features } => {
                            clauses.insert(features);
                        }
                        CNFToken::Comment => (),
                    }
                }
            }

            #[cfg(not(feature = "d4"))]
            {
                panic!("CNF to d-DNNF compilation is only possible when including d4.");
            }
        }
    }

    let file = open_file_savely(path);
    let lines = BufReader::new(file)
        .lines()
        .map(|line| line.expect("Unable to read line"))
        .collect::<Vec<String>>();

    if path == ".intermediate.nnf" {
        fs::remove_file(path).unwrap();
    }

    if clauses.is_empty() {
        distribute_building(lines, total_features, None)
    } else {
        distribute_building(lines, total_features, Some(clauses))
    }
}











/// Chooses, depending on the first read line, which building implmentation to choose.
/// Either the first line is a header and therefore the c2d format or total_features
/// is supplied and its the d4 format.
#[inline]
pub fn distribute_building(
    lines: Vec<String>,
    total_features: Option<u32>,
    clauses: Option<BTreeSet<BTreeSet<i32>>>,
) -> Ddnnf {
    use C2DToken::*;

    match lex_line_c2d(lines[0].trim()) {
        Ok((
            _,
            Header {
                nodes: _,
                edges: _,
                variables,
            },
        )) => build_c2d_ddnnf(lines, variables as u32, clauses),
        Ok(_) | Err(_) => {
            // tried to parse the c2d standard, but failes
            match total_features {
                Some(o) => {
                    // we try to parse the d4 standard
                    build_d4_ddnnf(lines, Some(o), clauses)
                }
                None => {
                    // unknown standard or combination -> we assume d4 and choose total_features
                    // Bold, Yellow, Foreground Color (see https://gist.github.com/fnky/458719343aabd01cfb17a3a4f7296797)
                    println!("\x1b[1;38;5;226mWARNING: The first line of the file isn't a header and the option 'total_features' is not set. \
                        Hence, we can't determine the number of variables and as a result, we might not be able to construct a valid ddnnf. \
                        Nonetheless, we build a ddnnf with our limited information, but we discourage using ddnnife in this manner.\n\x1b[0m"
                    );
                    build_d4_ddnnf(lines, None, clauses)
                }
            }
        }
    }
}






use std::time::Instant;
/// Parses a ddnnf, referenced by the file path.
/// This function uses C2DTokens which specify a d-DNNF in c2d format.
/// The file gets parsed and we create the corresponding data structure.
#[inline]
fn build_c2d_ddnnf(
    lines: Vec<String>,
    variables: u32,
    clauses: Option<BTreeSet<BTreeSet<i32>>>,
) -> Ddnnf {
    
    use C2DToken::*;

    let mut parsed_nodes: Vec<Node> = Vec::with_capacity(lines.len());

    let mut literals: HashMap<i32, usize> = HashMap::new();
    let mut true_nodes = Vec::new();

    // opens the file with a BufReader and
    // works off each line of the file data seperatly
    // skip the first line, because we already looked at the header
    for line in lines.into_iter().skip(1) {
        let next: Node = match lex_line_c2d(line.as_ref()).unwrap().1 {
            And { children } => {
                Node::new_and(calc_and_count(&mut parsed_nodes, &children), children)
            }
            Or { decision, children } => Node::new_or(
                decision,
                calc_or_count(&mut parsed_nodes, &children),
                children,
            ),
            Literal { feature } => Node::new_literal(feature),
            True => Node::new_bool(true),
            False => Node::new_bool(false),
            _ => panic!("Tried to parse the header of the .nnf at the wrong time"),
        };

        // fill the parent node pointer, save literals
        match &next.ntype {
            NodeType::And { children } | NodeType::Or { children } => {
                let next_indize: usize = parsed_nodes.len();
                for &i in children {
                    parsed_nodes[i].parents.push(next_indize);
                }
            }
            // fill the FxHashMap with the literals
            NodeType::Literal { literal } => {
                literals.insert(*literal, parsed_nodes.len());
            }
            NodeType::True => {
                true_nodes.push(parsed_nodes.len());
            }
            _ => (),
        }

        parsed_nodes.push(next);
    }

    Ddnnf::new(parsed_nodes, literals, true_nodes, variables, clauses)
}


/// Parses a ddnnf, referenced by the file path.
/// This function uses D4Tokens which specify a d-DNNF in d4 format.
/// The file gets parsed and we create the corresponding data structure.
#[inline]
fn build_d4_ddnnf(
    lines: Vec<String>,
    total_features_opt: Option<u32>,
    clauses: Option<BTreeSet<BTreeSet<i32>>>,
) -> Ddnnf {
    // let start = Instant::now();
    let mut ddnnf_graph = StableGraph::<TId, ()>::new();

    let mut total_features = total_features_opt.unwrap_or(0);
    let literal_occurences: Rc<RefCell<Vec<bool>>> =
        Rc::new(RefCell::new(vec![
            false;
            max(100_000, total_features as usize)
        ]));

    let mut indices: Vec<NodeIndex> = Vec::new();

    // With the help of the literals node state, we can add the required nodes
    // for the balancing of the or nodes to archieve smoothness
    let nx_literals: Rc<RefCell<HashMap<NodeIndex, i32>>> = Rc::new(RefCell::new(HashMap::new()));
    let literals_nx: Rc<RefCell<HashMap<i32, NodeIndex>>> = Rc::new(RefCell::new(HashMap::new()));

    let get_literal_indices =
        |ddnnf_graph: &mut StableGraph<TId, ()>, literals: Vec<i32>| -> Vec<NodeIndex> {
            let mut nx_lit = nx_literals.borrow_mut();
            let mut lit_nx = literals_nx.borrow_mut();

            let mut literal_nodes = Vec::new();

            for literal in literals {
                if literal.is_positive() {
                    literal_nodes.push(match lit_nx.get(&literal) {
                        Some(x) => *x,
                        None => {
                            let nx = ddnnf_graph.add_node(TId::PositiveLiteral);
                            nx_lit.insert(nx, literal);
                            lit_nx.insert(literal, nx);
                            nx
                        }
                    })
                } else {
                    literal_nodes.push(match lit_nx.get(&literal) {
                        Some(x) => *x,
                        None => {
                            let nx = ddnnf_graph.add_node(TId::NegativeLiteral);
                            nx_lit.insert(nx, literal);
                            lit_nx.insert(literal, nx);
                            nx
                        }
                    })
                }
            }
            literal_nodes
        };

    // while parsing:
    // remove the weighted edges and substitute it with the corresponding
    // structure that uses AND-Nodes and Literal-Nodes. Example:
    //
    //                   n1                       n1
    //                 /   \                   /    \
    //              Ln|    |Lm     into     AND    AND
    //                \   /                /   \  /   \
    //                 n2                 Ln    n2    Lm
    //
    //
    let resolve_weighted_edge = |ddnnf_graph: &mut StableGraph<TId, ()>,
                                 from: NodeIndex,
                                 to: NodeIndex,
                                //  edge: EdgeIndex,
                                 weights: Vec<i32>| 
    {
        if ddnnf_graph[to] == TId::False {
            return;
        }
        if weights.len() == 0 {
            if ddnnf_graph[to] == TId::True {
                if ddnnf_graph[from] == TId::Or {
                    ddnnf_graph.add_edge(from, to, ());
                }
            }else {
                ddnnf_graph.add_edge(from, to, ());
            }
            return;
        }
        let and_node = ddnnf_graph.add_node(TId::And);
        let literal_nodes = get_literal_indices(ddnnf_graph, weights);
        // ddnnf_graph.remove_edge(edge);
        ddnnf_graph.add_edge(from, and_node, ());
        for node in literal_nodes {
            ddnnf_graph.add_edge(and_node, node, ());
        }
        if ddnnf_graph[to] != TId::True{
            ddnnf_graph.add_edge(and_node, to, ());
        }
        
    };

    // let duration = start.elapsed();
    // println!("耗时: {:?}", duration);


    let start = Instant::now();
    // 预处理false节点
    let mut pre_graph = StableGraph::<TId, ()>::new();
    let mut pre_map: Vec<NodeIndex> = Vec::new();
    let mut pre_unmap= Vec::<usize>::new();
    let mut vis: Vec<bool> = Vec::new();
    let mut q: VecDeque<NodeIndex> = VecDeque::new();
    vis.resize(lines.len(),false);
    pre_unmap.resize(lines.len(),0);
    
    let mut line_list:Vec<D4Token> = Vec::new();
    for line_idx in 0..lines.len() {
        let line = lines[line_idx].clone();
        let next: D4Token = lex_line_d4(line.as_ref()).unwrap().1;
        line_list.push(next.clone());
        use D4Token::*;
        match next {
            Edge { from, to, features } => {
                pre_graph.add_edge(pre_map[from as usize -1], pre_map[to as usize -1], ());
            }
            And => {
                let idx = pre_graph.add_node(TId::And);
                pre_map.push(idx);
                pre_unmap[idx.index()] = pre_map.len();
            },
            Or => {
                let idx = pre_graph.add_node(TId::Or);
                pre_map.push(idx);
                pre_unmap[idx.index()] = pre_map.len();
            }
            True => {
                let idx = pre_graph.add_node(TId::True);
                pre_map.push(idx);
                pre_unmap[idx.index()] = pre_map.len();
            }
            False => {
                let idx = pre_graph.add_node(TId::False);
                pre_map.push(idx);
                q.push_back(idx);
                vis[idx.index()] = true;
                pre_unmap[idx.index()] = pre_map.len();
            }
            // _ => {}
        }
    }

    let mut flag: Vec<bool> = Vec::with_capacity(pre_map.len() + 1);
    flag.resize(pre_map.len() + 1,true);

    // let mut pre_false_count = 0;
    // bfs,以所有false节点为起点
    while !q.is_empty() {
        let node = q.front().unwrap().clone();
        q.pop_front();
        for neighbor in pre_graph.neighbors_directed(node, Incoming) {
            if pre_graph[neighbor] == TId::And && !vis[neighbor.index()] {
                vis[neighbor.index()]=true;
                q.push_back(neighbor);
                flag[pre_unmap[neighbor.index()]] = false;
                // pre_false_count += 1;
            }
        }
    }
    // println!("pre_false_count = {}",pre_false_count);
    let duration = start.elapsed();
    println!("pre_false耗时: {:?}", duration);

    let start = Instant::now();
    for next in line_list {
        use D4Token::*;
        match next {
            Edge { from, to, features } => {
                for f in &features {
                    literal_occurences.borrow_mut()[f.unsigned_abs() as usize] = true;
                    total_features = max(total_features, f.unsigned_abs());
                }
                let from_n = indices[from as usize - 1];
                let to_n = indices[to as usize - 1];
                if !flag[from as usize] || !flag[to as usize] {
                    continue;
                }
                // ???????
                // let edge = ddnnf_graph.add_edge(from_n, to_n, ());
                // resolve_weighted_edge(&mut ddnnf_graph, from_n, to_n, edge, features);
                resolve_weighted_edge(&mut ddnnf_graph, from_n, to_n, features);
            }
            And => {
                if !flag[indices.len() + 1] {
                    continue;
                }
                indices.push(ddnnf_graph.add_node(TId::And));
            }
            Or => {
                indices.push(ddnnf_graph.add_node(TId::Or));
            }
            True => {
                indices.push(ddnnf_graph.add_node(TId::True));
                // true_count += 1;
            }
            False => {
                indices.push(ddnnf_graph.add_node(TId::False));
                // false_count += 1;
            }
            // _ => {}
        }
        // time_2 += last_time.elapsed();
    }
    println!("pre-delete-true-and-false-time:{:?}",start.elapsed());


    // 这个就是我之前说的保证每个or-正-负这样的结构不会被多次创建。
    let or_triangles: Rc<RefCell<Vec<Option<NodeIndex>>>> =
        Rc::new(RefCell::new(vec![None; (total_features + 1) as usize]));

    let add_literal_node =
        |ddnnf_graph: &mut StableGraph<TId, ()>, f_u32: u32, attach: NodeIndex| {
            let f = f_u32 as i32;
            let mut ort = or_triangles.borrow_mut();

            if ort[f_u32 as usize].is_some() {
                ddnnf_graph.add_edge(attach, ort[f_u32 as usize].unwrap(), ());
            } else {
                let or = ddnnf_graph.add_node(TId::Or);
                ort[f_u32 as usize] = Some(or);

                let pos_lit = get_literal_indices(ddnnf_graph, vec![f])[0];
                let neg_lit = get_literal_indices(ddnnf_graph, vec![-f])[0];

                ddnnf_graph.add_edge(attach, or, ());
                ddnnf_graph.add_edge(or, pos_lit, ());
                ddnnf_graph.add_edge(or, neg_lit, ());
            }
        };

    let balance_or_children =
        |ddnnf_graph: &mut StableGraph<TId, ()>,
         from: NodeIndex,
         children: Vec<(NodeIndex, HashSet<u32>)>| {
            for child in children {
                let and_node = ddnnf_graph.add_node(TId::And);

                // place the newly created and node between the or node and its child
                ddnnf_graph.remove_edge(ddnnf_graph.find_edge(from, child.0).unwrap());
                ddnnf_graph.add_edge(from, and_node, ());
                ddnnf_graph.add_edge(and_node, child.0, ());

                for literal in child.1 {
                    add_literal_node(ddnnf_graph, literal, and_node);
                }
            }
        };
    

    // add a new root which hold the unmentioned variables within the total_features range
    let root = ddnnf_graph.add_node(TId::And);
    ddnnf_graph.add_edge(root, NodeIndex::new(0), ());

    // add literals that are not mentioned in the ddnnf to the new root node
    for i in 1..=total_features {
        if !literal_occurences.borrow()[i as usize] {
            add_literal_node(&mut ddnnf_graph, i, root);
        }
    }
    

    // 但是会出现链的情况：
    let mut edges_to_add: Vec<(NodeIndex, NodeIndex)> = Vec::new();
    let mut nodes_to_remove: Vec<NodeIndex> = Vec::new();
    let mut dfs = DfsPostOrder::new(&ddnnf_graph, root);
    let mut dfs_list: Vec<NodeIndex> = Vec::new();
    let mut set: Vec<bool> = Vec::new();
    set.resize(ddnnf_graph.node_count(), false);
    set[root.index()] = true;
    while let Some(idx) = dfs.next(&ddnnf_graph) {
        dfs_list.push(idx);
        if set[idx.index()] {
            continue;
        }
        let mut count = 0;
        let mut index=  NodeIndex::new(1);
        // 如果这个点只有一个儿子
        for edge in ddnnf_graph.edges_directed(idx,Outgoing) {
            count += 1;
            index = edge.target();
        }
        let raw = idx;
        let mut idx = idx;
        
        if count == 1 && idx != root {
            let son = index;
            let mut last = son;
            // 从idx开始，如果idx只有一个儿子并且只有一个父亲，就将idx设置为父亲，并标记为要删除的点，否则添加边
            while true {
                // println!("{:?}",idx);
                let mut son_count = 0;
                let mut parent_count = 0;
                let mut p = NodeIndex::new(1);
                for _ in ddnnf_graph.edges_directed(idx, Outgoing) {
                    son_count += 1;
                }
                for edge in ddnnf_graph.edges_directed(idx, Incoming) {
                    parent_count += 1;
                    p = edge.source();
                }
                // println!("{},{}",son_count,parent_count);
                if son_count == 1 && parent_count == 1 {
                    nodes_to_remove.push(idx);
                    set[idx.index()] = true;
                    last = idx;
                    idx = p;
                }else {
                    if parent_count == 0 {
                        // 如果是根
                        edges_to_add.push((idx,son));
                    }else{
                        // 如果不止一个儿子：
                        if son_count != 1{
                            edges_to_add.push((idx,son));
                        }else{
                            // 如果只有一个儿子：
                            nodes_to_remove.push(idx);
                            set[idx.index()] = true;
                            for edge in ddnnf_graph.edges_directed(idx, Incoming) {
                                edges_to_add.push((edge.source(),son));
                            }
                        }
                    }
                    break;
                }
            }
        }
    }
    set[root.index()] = false;

    for (parent,son) in edges_to_add {
        ddnnf_graph.add_edge(parent, son, ());
    }    

    // my_smoothness_bitset:
    // let mut dfs = DfsPostOrder::new(&ddnnf_graph, root);
    // 获取所有的或节点列表
    let mut or_node_list: Vec<NodeIndex> = Vec::new();
    for nx in &dfs_list{
        if nx.index() < set.capacity() && set[nx.index()] {
            continue;
        }
        if ddnnf_graph[*nx] == TId::Or {
            or_node_list.push(*nx);
        }
    }
    // 为每个node创建一个大小为total_features的bitset
    // 这里需要计算最终dag的节点数量，应该是原来的节点数量 + 或节点的数量 + 变量数
    
    let ttf = total_features.to_i32().unwrap();
    let ttf = ttf.to_usize().unwrap();
    let len = ddnnf_graph.node_count() + or_node_list.len() + ttf + 1;
    let mut bitset_list: Vec<BitSet> = Vec::new();
    for _ in 0..len {
        bitset_list.push(BitSet::new());
    }
    pre_bitset_multi_thread(&ddnnf_graph, &mut bitset_list, &nx_literals.borrow(), &set,root);


    // let mut last = duration;
    // let mut dfs = DfsPostOrder::new(&ddnnf_graph, root);
    for nx in &dfs_list{
        if  nx.index() < set.capacity() && set[nx.index()] {
            continue;
        }
        // edges between going from an and node to another node do not
        // have any weights attached to them. Therefore, we can skip them
        if ddnnf_graph[*nx] == TId::Or {
            // dif存了每个儿子需要被添加的变量集合。
            let diffrences = get_literal_diff_bitset(&ddnnf_graph, &mut bitset_list, *nx,&set);

            balance_or_children(&mut ddnnf_graph, *nx, diffrences);
        }
    }
    // println!("time_find = {:?}",time_find);
    // println!("time_add_node = {:?}",time_add_node);
    // let duration = start.elapsed();
    // println!("smoothness耗时: {:?}", duration);

    let mut edgeflag:Vec<bool> = vec![false;ddnnf_graph.edge_count() * 2];
    merge_edge(&mut ddnnf_graph, &set, &mut edgeflag, 2);
    
    // perform a depth first search to get the nodes ordered such
    // that child nodes are listed before their                                                                                                                                                             parents
    // transform that interim representation into a node vector
    dfs = DfsPostOrder::new(&ddnnf_graph, root);
    let mut nd_to_usize: HashMap<NodeIndex, usize> = HashMap::new();

    let mut parsed_nodes: Vec<Node> = Vec::with_capacity(ddnnf_graph.node_count());
    let mut literals: HashMap<i32, usize> = HashMap::new();
    let mut true_nodes = Vec::new();
    let nx_lit = nx_literals.borrow();
    while let Some(nx) = dfs.next(&ddnnf_graph) {
        if (nx.index() < set.capacity() && set[nx.index()]) {
            continue;
        }
        nd_to_usize.insert(nx, parsed_nodes.len());

        let mut neighs: Vec<usize> = Vec::new();
        for edge in ddnnf_graph.edges_directed(nx,Outgoing) {
            let idx = edge.id().index();
            if idx< edgeflag.capacity() && edgeflag[idx] == true{
                continue;
            }
            let n = edge.target();
            if (n.index() < set.capacity() && set[n.index()]) {
                continue;
            }
            neighs.push(*nd_to_usize.get(&n).unwrap());
        }
        // for n in ddnnf_graph.neighbors(nx) {
        //     if (n.index() < set.capacity() && set[n.index()]) {
        //         continue;
        //     }
        //     neighs.push(*nd_to_usize.get(&n).unwrap());
        // }
        
        let next: Node = match ddnnf_graph[nx] {
            // extract the parsed Token
            TId::PositiveLiteral | TId::NegativeLiteral => {
                Node::new_literal(nx_lit.get(&nx).unwrap().to_owned())
            }
            TId::And => Node::new_and(calc_and_count(&mut parsed_nodes, &neighs), neighs),

            TId::Or => Node::new_or(0, calc_or_count(&mut parsed_nodes, &neighs), neighs),
            TId::True => Node::new_bool(true),
            TId::False => Node::new_bool(false),
            TId::Header => panic!("The d4 standard does not include a header!"),
        };

        match &next.ntype {
            NodeType::And { children } | NodeType::Or { children } => {
                let next_indize: usize = parsed_nodes.len();
                for &i in children {
                    parsed_nodes[i].parents.push(next_indize);
                }
            }
            // fill the FxHashMap with the literals
            NodeType::Literal { literal } => {
                literals.insert(*literal, parsed_nodes.len());
            }
            NodeType::True => {
                true_nodes.push(parsed_nodes.len());
            }
            _ => (),
        }

        parsed_nodes.push(next);
    }
    // let duration = start.elapsed();
    // println!("rebuild成ddnnf dag需要的时间是:{:?}",duration);
    Ddnnf::new(parsed_nodes, literals, true_nodes, total_features, clauses)
}


fn merge_edge(
    ddnnf_graph: &mut StableGraph<TId, ()>,
    set: &Vec<bool>,
    edgeflag: &mut Vec<bool>,
    turn: i32,
) {
    let mut m: u32;
    let mut n: u32;
    let mut t: u32;

    unsafe {
        m = GLOBAL_M;
        n = GLOBAL_N;
        t = GLOBAL_T;
    }

    for k in 1..t+1 {
        let k = k as usize;
        // check有多少个我说的交错结构:
        // 每个点创建一个HashSet,存他的儿子
        let mut max_son_num = 0;
        let mut max_node_index = 0;
        let mut vlist:Vec<(usize,NodeIndex)> = Vec::new();

        let merge_num = m as usize/k;
        let group_num = n as usize/k;
        
        if group_num <= 2 && merge_num <= 2{
            continue;
        }

        for node in ddnnf_graph.node_indices() {
            if  node.index() < set.capacity() && set[node.index()] {
                continue;
            }
            let mut son_num = 0;
            // use c2d_lexer::TokenIdentifier::*;
            for edge in ddnnf_graph.edges_directed(node, Outgoing){
                let id = edge.id().index();
                if edgeflag[id] {
                    continue;
                }
                son_num += 1;
            }
            max_son_num = max(max_son_num,son_num);
            max_node_index = max(max_node_index,node.index());
            if son_num <= merge_num {
                continue;
            }
            vlist.push((son_num,node));
        }
        // println!("non-literal-node-num = {}",vlist.len());
        // println!("max_son_num = {}",max_son_num);

        let mut needless_edge_num = 0;
        // 把Hashset_list按照set的len从大到小排序,然后相邻的项结合.
        vlist.sort();
        
        let mut flag:Vec<usize> = vec![0; max_node_index + 1];

        
        if vlist.len() > group_num {
            // group_num个一组：
            for i in (group_num - 1..vlist.len()-1).rev().step_by(group_num) {
                let mut node_list : Vec<NodeIndex> = Vec::new();
                for j in 0..group_num {
                    node_list.push(vlist[i-j].1);
                    for edge in ddnnf_graph.edges_directed(node_list[j], Outgoing){
                        let id = edge.id().index();
                        if edgeflag[id] {
                            continue;
                        }
                        flag[edge.target().index()] += 1;
                    }
                }
                let mut num = 0;
                // 计算有多少个儿子是这一组中所有的node都共享的：
                for neighbor in ddnnf_graph.neighbors_directed(node_list[0], Outgoing){
                    if flag[neighbor.index()] == group_num {
                        num += 1;
                    }
                }
                // 多与merge_num个就合并：
                if num >= merge_num{
                    needless_edge_num += (group_num- 1)*num;
        
                    // 添加一个新的node,把原来的edge都删掉,把重复的儿子都连到这个点上,然后把这个点连上node1和node2
                    // 这里删除边不能直接删除,得用一个edgeflag给他标记掉,然后后面遍历的时候跳过.
                    // 新建节点:
                    let new_node = ddnnf_graph.add_node(TId::And);
                    let mut nodelist:Vec<NodeIndex> = Vec::new();
                    for edge in ddnnf_graph.edges_directed(node_list[0], Outgoing){
                        let id = edge.id().index();
                        if edgeflag[id] {
                            continue;
                        }
                        let to = edge.target();
                        if flag[to.index()] == group_num {
                            nodelist.push(to);
                        }
                    }
                    for j in 0..group_num {
                        for edge in ddnnf_graph.edges_directed(node_list[j], Outgoing){
                            let id = edge.id().index();
                            let to = edge.target();
                            if flag[to.index()] == group_num {
                                edgeflag[id] = true;
                            }
                        }
                    }
                    for j in 0..group_num {
                        for neighbor in ddnnf_graph.neighbors_directed(node_list[j], Outgoing){
                            flag[neighbor.index()] = 0;
                        }
                    }
        
                    for node in nodelist {
                        ddnnf_graph.add_edge(new_node, node, ());
                    }
                    for j in 0..group_num {
                        ddnnf_graph.add_edge(node_list[j], new_node, ());
                    }
        
                }else{
        
                    for j in 0..group_num {
                        for neighbor in ddnnf_graph.neighbors_directed(node_list[j], Outgoing){
                            flag[neighbor.index()] = 0;
                        }
                    }
                }
                
            }
        }
    }
    // println!("edge_count = {}",ddnnf_graph.edge_count());
    // println!("消减重边耗时:{:?}",time.elapsed());
    
}



fn get_literal_diff_bitset(
    di_graph: &StableGraph<TId, ()>,
    bitset_list: &mut Vec<BitSet>,
    or_node: NodeIndex,
    set: &Vec<bool>,
) -> Vec<(NodeIndex, HashSet<u32>)> {
    // 预处理做法：
    let mut inter_res = Vec::new();
    let neighbors = di_graph.neighbors_directed(or_node, Outgoing);
    for neighbor in neighbors {
        if (neighbor.index() < set.capacity() && set[neighbor.index()]) {
            continue;
        }
        inter_res.push((
            neighbor,
            bitset_list[neighbor.index()].clone()
        ));
    }
    // 修改后做法：
    let or_res = bitset_list[or_node.index()].clone();
    let mut res: Vec<(NodeIndex, HashSet<u32>)> = Vec::new();
    
    for i in 0..inter_res.len() {
        let mut val: HashSet<u32> = HashSet::new();
        for x in or_res.symmetric_difference(&inter_res[i].1) {
            val.insert(x.to_u32().unwrap());
        }
        // or_res.symmetric_difference_with(&inter_res[i].1);
        if !val.is_empty() {
            res.push((inter_res[i].0, val));
        }
    }
    res

}


fn pre_bitset_multi_thread(
    di_graph: &StableGraph<TId, ()>,
    bitset_list: &mut Vec<BitSet>,
    nx_literals: &HashMap<NodeIndex, i32>,
    set: &Vec<bool>,
    root: NodeIndex,
    // thread_num: u32,
){
    // println!("---------pre-bitset-multi-thread---------");
    // let start = Instant::now();

    let mut vis: Vec<bool> = Vec::new();
    // dep可以改称Vec,剩下3log的时间
    // let mut dep: HashMap<NodeIndex,u32> = HashMap::new();
    let mut dep: Vec<u32> = Vec::new();
    let mut len = 0;
    for node in di_graph.node_indices() {
        len = max(len,node.index());
    }
    len += 1;
    dep.resize(len,0);
    vis.resize(len,false);

    let mut q: VecDeque<NodeIndex> = VecDeque::new();
    for node in di_graph.node_indices() {
        if node.index() < set.capacity() && set[node.index()] {
            continue;
        }
        use c2d_lexer::TokenIdentifier::*;
        match di_graph[node]{
            Or => {
                q.push_back(node);
                vis[node.index()] = true;
            }
            _ => (),
        }
    }
    while !q.is_empty() {
        let node = q.front().unwrap().clone();
        q.pop_front();
        for son in di_graph.neighbors_directed(node, Outgoing){
            if vis[son.index()] || (son.index() < set.capacity() && set[son.index()]) {
                continue;
            }
            q.push_back(son);
            vis[son.index()]= true;
        }
    }
    
    let mut dfs = DfsPostOrder::new(&di_graph, root);
    let mut max_dep:  u32 = 0;
    while let Some(node) = dfs.next(&di_graph) {
        if !vis[node.index()] ||(node.index() < set.capacity() && set[node.index()]){
            continue;
        }
        use c2d_lexer::TokenIdentifier::*;
        match di_graph[node]{
            PositiveLiteral | NegativeLiteral => {
                dep[node.index()] = 1;
            }
            _ => (),
        }
        let neighbors = di_graph.neighbors_directed(node, Outgoing);
        for neighbor in neighbors {
            dep[node.index()] = max(dep[neighbor.index()]+1,dep[node.index()]);
            // dep.insert(node,max(dep[&neighbor].clone() + 1,dep[&node].clone()));
        }
        max_dep = max(max_dep,dep[node.index()]);
    }
    max_dep += 1;
    
    // let duration = start.elapsed();
    // println!("count-max-dep-time:{:?}",duration);

    // println!("max_dep = {}",max_dep);

    let mut dep_node_list: Vec<Vec<NodeIndex>> = Vec::with_capacity(max_dep as usize);
    for d in 0..max_dep{
        dep_node_list.push(Vec::new());
    }
    for node in di_graph.node_indices() {
        if dep[node.index()] == 0 {
            continue;
        }
        let idx = dep[node.index()];
        dep_node_list[idx as usize].push(node);
    }

    let start = Instant::now();    

    for d in 1..max_dep {
        // 均分max_thread_num份，分别计算。
        let res_list:Vec<BitSet> = dep_node_list[d as usize].par_iter().map(|node|{
            let neighbors = di_graph.neighbors_directed(*node, Outgoing);
            use c2d_lexer::TokenIdentifier::*;
            let mut res = BitSet::new();
            match di_graph[*node]{
                PositiveLiteral | NegativeLiteral => {
                    let idx = nx_literals.get(&node).unwrap().unsigned_abs().to_i32().unwrap().to_usize().unwrap();
                    res.insert(idx);
                }
                _ => (),
            }
            for neighbor in neighbors {
                // if vis[neighbor.index()] {
                    res.union_with(&bitset_list[neighbor.index()]);
                // }
            }
            res
        }).collect();
        for idx in 0..dep_node_list[d as usize].len() {
            let node = dep_node_list[d as usize][idx];
            bitset_list[node.index()] = res_list[idx].clone();
        }
    }

    let Duration = start.elapsed();
    println!("并行计算bitset_list花费的时间:{:?}",Duration);
    // println!();
    return;
}














fn pre_hashset_multi_thread(
    di_graph: &StableGraph<TId, ()>,
    hashset_list: &mut Vec<HashSet<usize>>,
    nx_literals: &HashMap<NodeIndex, i32>,
    // set: &HashSet<NodeIndex>,
    root: NodeIndex,
    // thread_num: u32,
){
    // println!("---------pre-bitset-multi-thread---------");
    // let start = Instant::now();

    let mut vis: Vec<bool> = Vec::new();
    // dep可以改称Vec,剩下3log的时间
    // let mut dep: HashMap<NodeIndex,u32> = HashMap::new();
    let mut dep: Vec<u32> = Vec::new();
    let mut len = 0;
    for node in di_graph.node_indices() {
        len = max(len,node.index());
    }
    len += 1;
    dep.resize(len,0);
    vis.resize(len,false);

    let mut q: VecDeque<NodeIndex> = VecDeque::new();
    for node in di_graph.node_indices() {
        // if set.contains(&node){
        //     continue;
        // }
        use c2d_lexer::TokenIdentifier::*;
        match di_graph[node]{
            Or => {
                q.push_back(node);
                vis[node.index()] = true;
            }
            _ => (),
        }
    }
    while !q.is_empty() {
        let node = q.front().unwrap().clone();
        q.pop_front();
        for son in di_graph.neighbors_directed(node, Outgoing){
            if vis[son.index()] {
                continue;
            }
            q.push_back(son);
            vis[son.index()]= true;
        }
    }
    
    let mut dfs = DfsPostOrder::new(&di_graph, root);
    let mut max_dep:  u32 = 0;
    while let Some(node) = dfs.next(&di_graph) {
        if !vis[node.index()]{
            continue;
        }
        use c2d_lexer::TokenIdentifier::*;
        match di_graph[node]{
            PositiveLiteral | NegativeLiteral => {
                dep[node.index()] = 1;
            }
            _ => (),
        }
        let neighbors = di_graph.neighbors_directed(node, Outgoing);
        for neighbor in neighbors {
            dep[node.index()] = max(dep[neighbor.index()]+1,dep[node.index()]);
            // dep.insert(node,max(dep[&neighbor].clone() + 1,dep[&node].clone()));
        }
        max_dep = max(max_dep,dep[node.index()]);
    }
    max_dep += 1;
    
    // let duration = start.elapsed();
    // println!("count-max-dep-time:{:?}",duration);

    // println!("max_dep = {}",max_dep);

    let mut dep_node_list: Vec<Vec<NodeIndex>> = Vec::with_capacity(max_dep as usize);
    for d in 0..max_dep{
        dep_node_list.push(Vec::new());
    }
    for node in di_graph.node_indices() {
        if dep[node.index()] == 0 {
            continue;
        }
        let idx = dep[node.index()];
        dep_node_list[idx as usize].push(node);
    }

    let start = Instant::now();    

    for d in 1..max_dep {
        // 均分max_thread_num份，分别计算。
        let res_list:Vec<HashSet<usize>> = dep_node_list[d as usize].par_iter().map(|node|{
            let neighbors = di_graph.neighbors_directed(*node, Outgoing);
            use c2d_lexer::TokenIdentifier::*;
            let mut res: HashSet<usize> = HashSet::new();
            match di_graph[*node]{
                PositiveLiteral | NegativeLiteral => {
                    let idx = nx_literals.get(&node).unwrap().unsigned_abs().to_i32().unwrap().to_usize().unwrap();
                    res.insert(idx);
                }
                _ => (),
            }
            for neighbor in neighbors {
                if vis[neighbor.index()] {
                    res.extend(&hashset_list[neighbor.index()]);
                }
            }
            res
        }).collect();
        for idx in 0..dep_node_list[d as usize].len() {
            let node = dep_node_list[d as usize][idx];
            hashset_list[node.index()] = res_list[idx].clone();
        }
    }

    let Duration = start.elapsed();
    println!("并行计算hashset_list花费的时间:{:?}",Duration);
    // println!();
    return;
}














fn get_literals(
    di_graph: &StableGraph<TId, ()>,
    safe: &mut HashMap<NodeIndex, HashSet<u32>>,
    nx_literals: &HashMap<NodeIndex, i32>,
    or_child: NodeIndex,
    set: &HashSet<NodeIndex>,
) -> HashSet<u32> {
    let lookup = safe.get(&or_child);
    if let Some(x) = lookup {
        return x.clone();
    }

    let mut res = HashSet::new();
    use c2d_lexer::TokenIdentifier::*;
    match di_graph[or_child] {
        And | Or => {
            for neighbor in di_graph.neighbors_directed(or_child, Outgoing) {
                if set.contains(&neighbor){
                    continue;
                }
                res.extend(get_literals(di_graph, safe, nx_literals, neighbor, set));
            }
            // di_graph
            //     .neighbors_directed(or_child, Outgoing)
            //     .for_each(|n| res.extend(get_literals(di_graph, safe, nx_literals, n, set)));
            safe.insert(or_child, res.clone());
        }
        PositiveLiteral | NegativeLiteral => {
            res.insert(nx_literals.get(&or_child).unwrap().unsigned_abs());
            safe.insert(or_child, res.clone());
        }
        _ => (),
    }
    res
}

                                                                                                                                                            



fn get_literals_bitset(
    di_graph: &StableGraph<TId, ()>,
    bitset_list: &mut Vec<BitSet>,
    nx_literals: &HashMap<NodeIndex, i32>,
    or_child: NodeIndex,
    set: &HashSet<NodeIndex>,
) -> BitSet {
    if bitset_list[or_child.index()].is_empty() == false {
        return bitset_list[or_child.index()].clone();
    }

    let mut res = BitSet::new();
    use c2d_lexer::TokenIdentifier::*;
    match di_graph[or_child] {
        And | Or => {
            for neighbor in di_graph.neighbors_directed(or_child, Outgoing) {
                if set.contains(&neighbor){
                    continue;
                }
                let degbug = get_literals_bitset(di_graph, bitset_list, nx_literals, neighbor, set);
                // println!("{:?}",degbug);
                res.union_with(&degbug);
                // for x in degbug.symmetric_difference(&res.clone()) {
                //     res.insert(x);
                // }
            }
            // println!("{:?}",res);
            // println!();
            bitset_list[or_child.index()] = res.clone();
        }
        PositiveLiteral | NegativeLiteral => {
            let idx = nx_literals.get(&or_child).unwrap().unsigned_abs().to_i32().unwrap().to_usize().unwrap();
            res.insert(idx);
            bitset_list[or_child.index()] = res.clone();
            // println!("{:?}",res);
        }
        _ => (),
    }
    // println!("{:?}",res);
    res
}





// multiplies the count of all child Nodes of an And Node
#[inline]
fn calc_and_count(nodes: &mut [Node], indices: &[usize]) -> Integer {
    Integer::product(indices.iter().map(|&index| &nodes[index].count)).complete()
}

// adds up the count of all child Nodes of an And Node
#[inline]
fn calc_or_count(nodes: &mut [Node], indices: &[usize]) -> Integer {
    Integer::sum(indices.iter().map(|&index| &nodes[index].count)).complete()
}

/// Is used to parse the queries in the config files
/// The format is:
/// -> A feature is either positiv or negative i32 value with a leading "-"
/// -> Multiple features in the same line form a query
/// -> Queries are seperated by a new line ("\n")
///
/// # Example
/// ```
/// use ddnnf_lib::parser::parse_queries_file;
///
/// let config_path = "./tests/data/auto1.config";
/// let queries: Vec<(usize, Vec<i32>)> = parse_queries_file(config_path);
///
/// assert_eq!((0, vec![1044, 885]), queries[0]);
/// assert_eq!((1, vec![1284, -537]), queries[1]);
/// assert_eq!((2, vec![-1767, 675]), queries[2]);
/// ```
/// # Panic
///
/// Panics for a path to a non existing file
pub fn parse_queries_file(path: &str) -> Vec<(usize, Vec<i32>)> {
    let file = open_file_savely(path);

    let lines = BufReader::new(file)
        .lines()
        .map(|line| line.expect("Unable to read line"));
    let mut parsed_queries: Vec<(usize, Vec<i32>)> = Vec::new();

    for (line_number, line) in lines.enumerate() {
        // takes a line of the file and parses the i32 values
        let res: Vec<i32> = line
            .split_whitespace()
            .map(|elem| elem.parse::<i32>()
                .unwrap_or_else(|_| panic!("Unable to parse {:?} into an i32 value while trying to parse the querie file at {:?}.\nCheck the help page with \"-h\" or \"--help\" for further information.\n", elem, path)))
            .collect();
        parsed_queries.push((line_number, res));
    }
    parsed_queries
}

/// Tries to open a file.
/// If an error occurs the program prints the error and exists.
pub fn open_file_savely(path: &str) -> File {
    // opens the file with a BufReader and
    // works off each line of the file data seperatly
    match File::open(path) {
        Ok(x) => x,
        Err(err) => {
            // Bold, Red, Foreground Color (see https://gist.github.com/fnky/458719343aabd01cfb17a3a4f7296797)
            eprintln!("\x1b[1;38;5;196mERROR: The following error code occured while trying to open the file \"{}\":\n{}\nAborting...", path, err);
            process::exit(1);
        }
    }
}
