pub mod anomalies;
pub mod clause_cache;
pub mod counting;
pub mod heuristics;
pub mod multiple_queries;
pub mod node;
pub mod stream;
use std::{collections::{BTreeSet, HashMap, HashSet, VecDeque}, hash::Hash, io::BufRead, time::Duration};
use std::collections::BinaryHeap;
use bitvec::{index, ptr::swap, vec};
use counting::features;
use itertools::{Either, Interleave};
use rand_distr::num_traits::ToPrimitive;
use rug::{Assign, Complete,Integer};
use std::time::Instant;

use self::{clause_cache::ClauseCache, node::Node};
use node::NodeType::*;

use std::path::Path;
use std::fs::File;
use std::io::{self};

#[derive(Clone, Debug)]
/// A Ddnnf holds all the nodes as a vector, also includes meta data and further information that is used for optimations
pub struct Ddnnf {
    /// The actual nodes of the d-DNNF in postorder
    pub nodes: Vec<Node>,
    /// The saved state to enable undoing and adapting the d-DNNF. Avoid exposing this field outside of this source file!
    cached_state: Option<ClauseCache>,
    /// Literals for upwards propagation
    pub literals: HashMap<i32, usize>, // <var_number of the Literal, and the corresponding indize>
    true_nodes: Vec<usize>, // Indices of true nodes. In some cases those nodes needed to have special treatment
    /// The core/dead features of the model corresponding with this ddnnf
    pub core: HashSet<i32>,
    /// An interim save for the marking algorithm
    pub md: Vec<usize>,
    pub number_of_variables: u32,
    /// The number of threads
    pub max_worker: u16,
    // /// 本次partial_config计算涉及到的边数和点数
    // pub node_count: i128,
    // pub edge_count: i128,
    
    pub literals_list: HashMap<usize, i32>,
    pub core_list: HashSet<i32>,

    pub weight_list: Vec<i32>,

    pub limit_solution_num: i32,

    pub v_m: u32,
    pub v_n: u32,
    pub v_t: u32,
}

impl Default for Ddnnf {
    fn default() -> Self {
        Ddnnf {
            nodes: Vec::new(),
            cached_state: None,
            literals: HashMap::new(),
            true_nodes: Vec::new(),
            core: HashSet::new(),
            md: Vec::new(),
            number_of_variables: 0,
            max_worker: 1,
            // node_count: 0,
            // edge_count: 0,
            literals_list: HashMap::new(),
            core_list: HashSet::new(),
            weight_list: Vec::new(),
            limit_solution_num: 0,
            v_m: 0,
            v_n: 0,
            v_t: 0,
        }
    }
}

impl Ddnnf {
    /// Creates a new ddnnf including dead and core features
    pub fn new(
        nodes: Vec<Node>,
        literals: HashMap<i32, usize>,
        true_nodes: Vec<usize>,
        number_of_variables: u32,
        clauses: Option<BTreeSet<BTreeSet<i32>>>,
    ) -> Ddnnf {
        let mut ddnnf = Ddnnf {
            nodes,
            cached_state: None,
            literals,
            true_nodes,
            core: HashSet::new(),
            md: Vec::new(),
            number_of_variables,
            max_worker: 1,
            // node_count: 0,
            // edge_count: 0,
            literals_list: HashMap::new(),
            core_list: HashSet::new(),
            weight_list: Vec::new(),
            limit_solution_num: 0,
            v_m: 0,
            v_n: 0,
            v_t: 0,
        };
        ddnnf.get_core();
        if let Some(c) = clauses {
            ddnnf.update_cached_state(Either::Right(c), Some(number_of_variables));
        }
        ddnnf
    }

    /// Checks if the creation of a cached state is valid.
    /// That is only the case if the input format was CNF.
    pub fn can_save_state(&self) -> bool {
        self.cached_state.is_some()
    }

    /// Either initialises the ClauseCache by saving the clauses and its corresponding clauses
    /// or updates the state accordingly.
    pub fn update_cached_state(
        &mut self,
        clause_info: Either<(Vec<BTreeSet<i32>>, Vec<BTreeSet<i32>>), BTreeSet<BTreeSet<i32>>>, // Left(edit operation) or Right(clauses)
        total_features: Option<u32>,
    ) -> bool {
        match self.cached_state.as_mut() {
            Some(state) => match clause_info.left() {
                Some((add, rmv)) => {
                    if total_features.is_none()
                        || !state.apply_edits_and_replace(add, rmv, total_features.unwrap())
                    {
                        return false;
                    }
                    // The old d-DNNF got replaced by the new one.
                    // Consequently, the current higher level d-DNNF becomes the older one.
                    // We swap their field data to keep the order without needing to deal with recursivly building up
                    // obselete d-DNNFs that trash the RAM.
                    self.swap();
                }
                None => return false,
            },
            None => match clause_info.right() {
                Some(clauses) => {
                    let mut state = ClauseCache::default();
                    state.initialize(clauses, total_features.unwrap());
                    self.cached_state = Some(state);
                }
                None => return false,
            },
        }
        true
    }

    fn swap(&mut self) {
        if let Some(cached_state) = self.cached_state.as_mut() {
            if let Some(save_state) = cached_state.old_state.as_mut() {
                std::mem::swap(&mut self.nodes, &mut save_state.nodes);
                std::mem::swap(&mut self.literals, &mut save_state.literals);
                std::mem::swap(&mut self.true_nodes, &mut save_state.true_nodes);
                std::mem::swap(&mut self.core, &mut save_state.core);
                std::mem::swap(&mut self.md, &mut save_state.md);
                std::mem::swap(
                    &mut self.number_of_variables,
                    &mut save_state.number_of_variables,
                );
                std::mem::swap(&mut self.max_worker, &mut save_state.max_worker);
            }
        }
    }

    // Performes an undo operation resulting in swaping the current d-DNNF with its older version.
    // Hence, the perviously older version becomes the current one and the current one becomes the older version.
    // A second undo operation in a row is equivalent to a redo. Can fail if there is no old d-DNNF available.
    pub fn undo_on_cached_state(&mut self) -> bool {
        match self.cached_state.as_mut() {
            Some(state) => {
                state.setup_for_undo();
                self.swap();
                //std::mem::swap(self, &mut state.to_owned().get_old_state().unwrap());
                true
            }
            None => false,
        }
    }

    // Returns the current count of the root node in the ddnnf.
    // That value is the same during all computations
    pub fn rc(&self) -> Integer {
        self.nodes[self.nodes.len() - 1].count.clone()
    }

    // Returns the current temp count of the root node in the ddnnf.
    // That value is changed during computations
    fn rt(&self) -> Integer {
        self.nodes[self.nodes.len() - 1].temp.clone()
    }

    /// Determines the positions of the inverted featueres
    pub fn map_features_opposing_indexes(&self, features: &[i32]) -> Vec<usize> {
        let mut indexes = Vec::with_capacity(features.len());
        for number in features {
            if let Some(i) = self.literals.get(&-number).cloned() {
                indexes.push(i);
            }
        }
        indexes
    }

    pub fn debug(&mut self){
        return;
        println!("node:");
        for idx in 0..self.nodes.len(){
            print!("{}: ",idx);
            print!("{:?} ",self.nodes[idx].ntype);
            for index in 0..self.nodes[idx].parents.len(){
                print!(" {}",self.nodes[idx].parents[index]);
            }
            println!();
        }
        println!("literals: ");
        for (key,value) in self.literals.clone() {
            println!("{} {}",key,value);
        }
        
    }


    pub fn new_my_partial_config_counter(&mut self, features: &[i32]) -> Integer{
        // 先mark一下所有涉及到的点
        // 从下到上,标记出所有为0的点:如果一个点为0,则他的所有乘法父亲都被标记为0
        // 再从上到下,标记出所有为0的点:如果一个点的所有父亲都被标记成0,那他就是0(这个0的意思是不需要被计算)
        // 最后只对被mark了,但是没有被标记为0的点进行计算,但是计算规则要小小修改一下,这里只会出现几种情况:
        // 1-要被计算的节点是乘法节点,那么他的所有被mark的儿子一定都没有被标记为0
        // 2-要被计算的节点是加法节点,那么需要判断一下每个儿子是否是is_zero
        // 所以都不用改
        let start = Instant::now();
        if self.query_is_not_sat(features) {
            // println!("!!!");
            return Integer::ZERO;
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        if indexes.is_empty() {
            return self.rc();
        }
        // 里面用的dfs,改成bfs会快吗?
        // 内部sorted了
        self.mark_assumptions(&indexes);

        // 从下到上,标记出所有为0的点:如果一个点为0,则他的所有乘法父亲都被标记为0
        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And {..} => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or {children} => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        }else{
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }
        
        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And {..} => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or {children} => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        }else{
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return Integer::ZERO;
        }
        // 再从上到下,标记出所有为0的点:如果一个点的所有父亲都被标记成0,那他就是0(这个0的意思是不需要被计算)
        let mut vis: Vec<bool> = Vec::new();
        vis.resize(self.nodes.len(),false);
        vis[self.nodes.len() - 1] = true;
        for idx in (0..self.md.len()).rev() {
            let index = self.md[idx];
            if !vis[index] || self.nodes[index].is_zero {
                continue;
            }
            match &self.nodes[index].ntype {
                And {children} => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }   
                }
                Or {children} => {
                    for child in children {
                        if !self.nodes[*child].is_zero {
                            vis[*child] = true;
                        }
                    }  
                }
                _=>{}
            }
        }
        // 最后只对vis的点进行计算
        for idx in 0..self.md.len() {
            if !vis[self.md[idx]] {
                continue;
            }
            let i = self.md[idx];
            match &self.nodes[i].ntype {
                And { children } => {
                    let marked_children = children
                        .iter()
                        .filter(|&&child| self.nodes[child].marker)
                        .collect::<Vec<&usize>>();
                    self.nodes[i].temp = if marked_children.len() <= children.len() / 2 {
                        marked_children
                            .iter()
                            .fold(self.nodes[i].count.clone(), |mut acc, &&index| {
                                let node = &self.nodes[index];
                                if node.count != 0 {
                                    acc /= &node.count;
                                }
                                acc *= &node.temp;
                                acc
                            })
                    } else {
                        Integer::product(children.iter().map(|&index| {
                            let node = &self.nodes[index];
                            if node.marker {
                                &node.temp
                            } else {
                                &node.count
                            }
                        }))
                        .complete()
                    }
                }
                Or { children } => {
                    self.nodes[i].temp = Integer::sum(children.iter().map(|&index| {
                        let node = &self.nodes[index];
                        if node.marker {
                            &node.temp
                        } else {
                            &node.count
                        }
                    }))
                    .complete()
                }
                False => self.nodes[i].temp.assign(0),
                _ => self.nodes[i].temp.assign(1), // True and Literal
            }
        }
        
        // reset everything
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();

        return self.rt();
    }








    pub fn my_zero_checker(&mut self, features: &[i32]) -> bool {
        if self.query_is_not_sat(features) {
            // println!("!!!");
            return false;
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        if indexes.is_empty() {
            return false;
        }
        // 里面用的dfs,改成bfs会快吗?
        // 内部sorted了
        self.mark_assumptions(&indexes);
        

        // 从下到上,标记出所有为0的点:如果一个点为0,则他的所有乘法父亲都被标记为0
        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And {..} => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or {children} => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        }else{
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }
        
        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And {..} => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or {children} => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        }else{
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return false;
        }
        else{
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return true;
        }
    }











    pub fn my_weighted_dp(&mut self, features: &[i32]) -> (Vec<(Integer, Vec<i32>)>) {
        if self.query_is_not_sat(features) {
            return Vec::new();
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        // 里面用的dfs,改成bfs会快吗?
        // 内部sorted了
        self.mark_assumptions(&indexes);

        // 从下到上,标记出所有为0的点:如果一个点为0,则他的所有乘法父亲都被标记为0
        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match &self.nodes[parent].ntype {
                    And { .. } => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    Or { children } => {
                        if children.len() == 1 {
                            self.nodes[parent].is_zero = true;
                        }
                        if !self.nodes[parent].or_flag {
                            self.nodes[parent].or_flag = true;
                        } else {
                            self.nodes[parent].is_zero = true;
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
                self.nodes[index].or_flag = false;
            }
            self.md.clear();
            return Vec::new();
        }

        // 对每一个节点创建两个东西：
        // dp[i] 表示当前节点所代表的解集中weight最大的
        // Vec<i32> 表示当前节点所代表的解集中weight最大的那个解是什么
        let len = self.nodes.len();
        let mut dp: Vec<Vec<(Integer,Vec<i32>)>> = Vec::new();
        for i in 0..len {
            dp.push(Vec::new());
        }
        let mut heap: BinaryHeap<(Integer,usize,usize)> = BinaryHeap::new();
        for idx in 0..self.nodes.len() {
            if self.nodes[idx].is_zero == true {
                continue;
            }
            let mut res: Vec<(Integer,Vec<i32>)> = Vec::new();
            heap.clear();

            match &self.nodes[idx].ntype {
                And { children } => {
                    // 每个儿子单独计算：
                    for son in children.iter() {
                        if res.is_empty(){
                            res = dp[*son].clone();
                            continue;
                        }
                        let mut fp = 0;
                        let mut sp = 0;
                        let mut w = Integer::ZERO;
                        heap.push((res[fp].0.clone() + dp[*son][sp].0.clone(),fp,sp));
                        let mut n_res: Vec<(Integer,Vec<i32>)> = Vec::new();
                        // k轮，每轮找出第k大的
                        for k in 0..self.limit_solution_num as usize{
                            if heap.is_empty(){
                                break;
                            }
                            (w,fp,sp) = heap.pop().unwrap();

                            // 用fp和sp组合成新的res[k]
                            let mut n_v: Vec<i32> = res[fp].1.clone();
                            n_v.extend(&dp[*son][sp].1);
                            n_res.push((w,n_v));

                            // 把可能成为第k+1大的候补塞进去
                            if fp + 1 < res.len() {
                                heap.push((res[fp+1].0.clone() + dp[*son][sp].0.clone(),fp+1,sp));
                            }
                            if sp + 1 < dp[*son].len() {
                                heap.push((res[fp].0.clone() + dp[*son][sp+1].0.clone(),fp,sp+1));
                            }
                        }
                        res = n_res;
                    }
                    
                }
                // Or的情况是两边的解集合没有交集，所以直接取max
                Or { children } => {
                    // 所有儿子塞到堆里
                    for son in children.iter() {
                        for j in 0..dp[*son].len() {
                            let (w,_vec) = &dp[*son][j];
                            heap.push((w.clone(),*son,j));
                        }
                    }
                    // 取前k大的
                    while let Some((_,son,j)) = heap.pop() {
                        if res.len() >= self.limit_solution_num as usize {
                            break;
                        }
                        let (w,v) = &dp[son][j];
                        res.push((w.clone(),v.clone()));
                    }
                }
                Literal { literal } => {
                    // solution.push(*literal);
                    let mut v = Vec::new();
                    v.push(*literal);
                    if *literal > 0 {
                        let mut max_weight = Integer::ZERO;
                        max_weight += self.weight_list[*literal as usize].clone();
                        res.push((max_weight,v));
                    }else{
                        res.push((Integer::ZERO,v));
                    }
                }
                _ => {}
            }
            dp[idx] = res;
        }
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
            self.nodes[index].or_flag = false;
        }
        self.md.clear();
        // println!("max_weight:{:?}",dp[len-1].clone());
        return dp[len - 1].clone();
    }


    pub fn my_execute_query(&mut self, features: &[i32]) -> Integer {
        let res = match features.len() {
            0 => self.rc(),
            _ => self.new_my_partial_config_counter(features)
        };
        
        return res;
    }

    pub fn my_project_query(&mut self, features: &[i32]) -> (Vec<Vec<i32>>,Duration) {
        if features.len() > 7 {
            return self.new_my_project_query(features);
        }
        let start = Instant::now();
        let mut res:Vec<Vec<i32>> = Vec::new();
        let len = features.len();
        for i in 0..(1<<len) {
            let mut feature_list:Vec<i32> = Vec::new();
            for j in 0..len {
                if ((1<<j)&i)!=0 {
                    feature_list.push(features[j]);
                }else{
                    feature_list.push(features[j] * -1);
                }
            }
            // println!("{:?}",feature_list);
            if self.my_zero_checker(&feature_list) {
                // println!("{:?}",self.my_partial_config_counter(&feature_list.clone()));
                res.push(feature_list);
                
            }
        }
        println!("solution_num:{}",res.len());
        return (res,start.elapsed());
    }



    pub fn new_my_project_query(&mut self, features: &[i32]) -> (Vec<Vec<i32>>,Duration) {

        let mut solution_map:Vec<HashSet<Vec<i32>>> = Vec::new();
        solution_map.resize(self.nodes.len(), HashSet::new());

        let start = Instant::now();
        let mut res:Vec<Vec<i32>> = Vec::new();
        let mut features_list:Vec<i32> = Vec::new();
        for f in features {
            features_list.push(f.clone());
            features_list.push(f.clone() * -1);
        }
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features_list);
        self.mark_assumptions(&indexes);
        for &index in &indexes {
            let mut vec:Vec<i32> = Vec::new();
            let mut solution:HashSet<Vec<i32>> = HashSet::new();
            match &self.nodes[index].ntype {
                Literal { literal } => {
                    vec.push(*literal);
                    solution.insert(vec);
                    solution_map[index]=solution;
                }
                _ => {}
            }
        }
        
        for idx in 0..self.md.len() {
            
            let idx = self.md[idx];
            
            let i = idx;
            let mut vec:Vec<i32> = Vec::new();
            let mut solution:HashSet<Vec<i32>> = HashSet::new();

            match &self.nodes[i].ntype {
                And { children } => {
                    for son in children.iter() {
                        for son_vec_list in solution_map.get(*son) {
                            let old_solution = solution.clone();
                            if !son_vec_list.is_empty() {
                                solution.clear();
                            }
                            
                            for son_vec in son_vec_list{
                                for temp_vec in old_solution.clone() {
                                    let mut temp = temp_vec.clone();
                                    for item in son_vec {
                                        temp.push(*item);
                                    }
                                    temp.sort_unstable();
                                    solution.insert(temp);
                                }
                                if old_solution.is_empty() {
                                    solution.insert(son_vec.clone());
                                }
                             }
                        }
                    }
                    solution_map[i]=solution;
                }
                // Or的情况是两边的解集合没有交集，所以直接合并
                Or { children } => {
                    for son in children.iter() {
                        for son_vec_list in solution_map.get(*son) {
                            for son_vec in son_vec_list {
                                solution.insert(son_vec.clone());
                            }
                        }
                    }
                    solution_map[i]=solution;
                }
                Literal { literal } => {
                    vec.push(*literal);
                    solution.insert(vec);
                    solution_map[i]=solution;
                }
                _ => {}
            }
        }

        for &index in &self.md {
            self.nodes[index].marker = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
        }
        self.md.clear();

        for list in &solution_map[self.nodes.len() -1 ] {
            res.push(list.clone());
        }
        println!("solution_num:{}",res.len());
        return (res,start.elapsed());
    }



    pub fn init_weight(&mut self, weight_file_path: String) {
        let path = Path::new(&weight_file_path);
        let file = File::open(path).unwrap();
        let reader = io::BufReader::new(file);

        println!("num_of_feature:{}",self.number_of_variables);
        for i in 0..self.number_of_variables + 1 {
            self.weight_list.push(0);
        }

        for line in reader.lines(){
            let line = line.unwrap();
            let parts: Vec<&str> = line.split_whitespace().collect();
            let feature: i32 = parts[0].parse().expect("Not a number");
            let weight: i32 = parts[1].parse().expect("Not a number");
            self.weight_list[feature as usize] += weight;
        }

    }

    

    pub fn my_weighted_query(&mut self, features: &[i32]) -> (Vec<(Integer, Vec<i32>)>,Duration) {
        self.limit_solution_num = 5;
        let start = Instant::now();
        let mut res: Vec<(Integer, Vec<i32>)> = Vec::new();
        res = self.my_weighted_dp(features);

        if res.is_empty(){
            res = self.my_weighted_dp(&Vec::new());
            for idx in 0..res.len() {
                res[idx].1.sort_by_key(|&x| x.abs());
                res[idx].1.push(0);
            }
        }else{
            for idx in 0..res.len() {
                res[idx].1.sort_by_key(|&x| x.abs());
                res[idx].1.push(1);
            }
        }
        
        return (res, start.elapsed());
    }












    pub fn my_partial_config_counter(&mut self, features: &[i32]) -> Integer{
        // self.debug();
        // 先mark一下所有涉及到的点
        // 从下到上,标记出所有为0的点:如果一个点为0,则他的所有乘法父亲都被标记为0
        // 再从上到下,标记出所有为0的点:如果一个点的所有父亲都被标记成0,那他就是0(这个0的意思是不需要被计算)
        // 最后只对被mark了,但是没有被标记为0的点进行计算,但是计算规则要小小修改一下,这里只会出现几种情况:
        // 1-要被计算的节点是乘法节点,那么他的所有被mark的儿子一定都没有被标记为0
        // 2-要被计算的节点是加法节点,那么需要判断一下每个儿子是否是is_zero
        // 所以都不用改
        // for i in features.iter() {
        //     print!("{} ",i);
        // }
        // println!();
        // for i in self.core.iter() {
        //     println!("{}",i);
        // }
        if self.query_is_not_sat(features) {
            // println!("!!!");
            return Integer::ZERO;
        }
        let features: Vec<i32> = self.reduce_query(features);
        let indexes: Vec<usize> = self.map_features_opposing_indexes(&features);
        if indexes.is_empty() {
            return self.rc();
        }
        // 里面用的dfs,改成bfs会快吗?
        // 内部sorted了
        self.mark_assumptions(&indexes);
        // for idx in 0..self.md.len() {
        //     print!("{} ",self.md[idx]);
        // }
        // println!();
        

        // 从下到上,标记出所有为0的点:如果一个点为0,则他的所有乘法父亲都被标记为0
        for &index in &indexes {
            self.nodes[index].is_zero = true;
            self.nodes[index].temp = Integer::ZERO;
            // println!("{}",index);
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match self.nodes[parent].ntype {
                    And {..} => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    _ => {}
                }
            }
        }
        
        for idx in 0..self.md.len() {
            let index = self.md[idx];
            if self.nodes[index].is_zero == false {
                continue;
            }
            for idx in 0..self.nodes[index].parents.len() {
                let parent = self.nodes[index].parents[idx];
                match self.nodes[parent].ntype {
                    And {..} => {
                        self.nodes[parent].is_zero = true;
                        self.nodes[parent].temp = Integer::ZERO;
                    }
                    _ => {}
                }
            }
        }

        // 再从上到下,标记出所有为0的点:如果一个点的所有父亲都被标记成0,那他就是0(这个0的意思是不需要被计算)
        if self.md.len() > 1 {
            for idx in (0..self.md.len() -1).rev() {
                let index = self.md[idx];
                if self.nodes[index].is_zero == true {
                    continue;
                }
                let mut flag = true;
                for id in 0..self.nodes[index].parents.len() {
                    let parent = self.nodes[index].parents[id];
                    flag &= self.nodes[parent].is_zero;
                }
                if flag == true {
                    self.nodes[index].is_zero = flag;
                    self.nodes[index].temp = Integer::ZERO;
                }
            }
        }
        if self.nodes.last().unwrap().is_zero {
            for &index in &self.md {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
            }
            for index in indexes {
                self.nodes[index].marker = false;
                self.nodes[index].is_zero = false;
            }
            self.md.clear();
            return Integer::ZERO;
        }
        // println!("self.md.len = {}",self.md.len());
        
        
        // print!("core_list:");
        // let mut core_list = self.core.clone();
        // // check一下所有的literal_node，看哪些节点被标记了。
        // for i in 0..self.nodes.len() {
        //     match &self.nodes[i].ntype {
        //         Literal {literal} => {
        //             if self.nodes[i].is_zero {
        //                 core_list.insert((*literal)*(-1));
        //             }
        //         }
        //         _ => {}
        //     }
        // }
        // self.core_list = core_list;
        // for core in core_list {
        //     print!(" {}",core);
        // }
        // println!();
        
        // self.node_count = 0;
        // self.edge_count = 0;
        // 最后只对被mark了,但是没有被标记为0的点进行计算
        for idx in 0..self.md.len() {
            if self.nodes[self.md[idx]].is_zero == true {
                continue;
            }
            // self.node_count += 1;
            let i = self.md[idx];
            match &self.nodes[i].ntype {
                And { children } => {
                    let marked_children = children
                        .iter()
                        .filter(|&&child| self.nodes[child].marker)
                        .collect::<Vec<&usize>>();
                    self.nodes[i].temp = if marked_children.len() <= children.len() / 2 {
                        marked_children
                            .iter()
                            .fold(self.nodes[i].count.clone(), |mut acc, &&index| {
                                let node = &self.nodes[index];
                                if node.count != 0 {
                                    acc /= &node.count;
                                }
                                acc *= &node.temp;
                                // self.edge_count += 1;
                                acc
                            })
                    } else {
                        Integer::product(children.iter().map(|&index| {
                            let node = &self.nodes[index];
                            // self.edge_count += 1;
                            if node.marker {
                                &node.temp
                            } else {
                                &node.count
                            }
                        }))
                        .complete()
                    }
                }
                Or { children } => {
                    self.nodes[i].temp = Integer::sum(children.iter().map(|&index| {
                        let node = &self.nodes[index];
                        // self.edge_count += 1;
                        if node.marker {
                            &node.temp
                        } else {
                            &node.count
                        }
                    }))
                    .complete()
                }
                False => self.nodes[i].temp.assign(0),
                _ => self.nodes[i].temp.assign(1), // True and Literal
            }
        }
        
        // reset everything
        for &index in &self.md {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
        }
        for index in indexes {
            self.nodes[index].marker = false;
            self.nodes[index].is_zero = false;
        }
        self.md.clear();
        // println!("The node_count is:{}",self.node_count);
        // println!("The edge_count is:{}",self.edge_count);
        // println!();
        // println!("solution_num: {}",self.rt());
        return self.rt();
    }

    pub fn execute_query(&mut self, features: &[i32]) -> Integer {
        let res = match features.len() {
            0 => self.rc(),
            1 => self.card_of_feature_with_marker(features[0]),
            2..=20 => {
                self.operate_on_partial_config_marker(features,Ddnnf::calc_count_marked_node)
            }
            _ => self.operate_on_partial_config_default(features, Ddnnf::calc_count),
        };
        return res;
    }

}
