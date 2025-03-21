use rand_distr::num_traits::ToPrimitive;
use rug::Float;
use std::error::Error;

use super::super::Ddnnf;

impl Ddnnf {
    #[inline]
    /// Computes the cardinality of features for all features in a model.
    /// The results are saved in the file_path. The .csv ending always gets added to the user input.
    /// The function exclusively uses the marking based function.
    /// Here the number of threads influence the speed by using a shared work queue.
    /// # Example
    /// ```
    /// extern crate ddnnf_lib;
    /// use ddnnf_lib::Ddnnf;
    /// use ddnnf_lib::parser::*;
    /// use rug::Integer;
    /// use std::fs;
    ///
    /// // create a ddnnf
    /// // and run the queries
    /// let mut ddnnf: Ddnnf = build_ddnnf("./tests/data/small_ex_c2d.nnf", None);
    /// ddnnf.card_of_each_feature("./tests/data/smt_out.csv")
    ///      .unwrap_or_default();
    /// let _rm = fs::remove_file("./tests/data/smt_out.csv");
    ///
    /// ```
    pub fn card_of_each_feature(&mut self, file_path: &str) -> Result<(), Box<dyn Error>> {
        self.annotate_partial_derivatives();

        // start the csv writer with the file_path
        let mut wtr = csv::Writer::from_path(file_path)?;

        for work in 1_i32..self.number_of_variables as i32 + 1 {
            let cardinality = self.card_of_feature_with_partial_derivatives(work);
            wtr.write_record(vec![
                work.to_string(),
                cardinality.to_string(),
                format!("{:.20}", Float::with_val(200, cardinality) / self.rc()),
            ])?;
        }

        // self.literals_list.clear();
        // for id in 1..self.number_of_variables+1{
        //     let mut idx = id.to_i32().unwrap();
            
        //     let temp = self.literals.get(&idx).clone();
        //     if temp != None {
        //         let index = *temp.unwrap();
        //         self.literals_list.insert(index, idx);
        //     }
        //     idx *= -1;
        //     let temp = self.literals.get(&idx).clone();
        //     if temp != None {
        //         let index = *temp.unwrap();
        //         self.literals_list.insert(index, idx);
        //     }
        // }

        // // for idx in 0..self.literals_list.len(){
        // //     print!("{}",self.literals_list[idx]);
        // // }
        // // println!();
        
        // for id in 1..self.number_of_variables+1{
        //     let mut idx = id.to_i32().unwrap();
        //     let mut index: usize = 0;
        //     let temp = self.literals.get(&idx).clone();
        //     if temp != None {
        //         index = *temp.unwrap();
        //         // print!("{}: ",idx);
        //         self.zero_mark(index);
        //         // println!();
        //     }
            

        //     idx *= -1;
        //     let temp = self.literals.get(&idx).cloned();
        //     if temp != None {
        //         index = temp.unwrap();
        //         // print!("{}: ",idx);
        //         self.zero_mark(index);
        //         // println!();
        //     }
            
        // }

        Ok(())
    }
    
}

#[cfg(test)]
mod test {
    use file_diff::diff_files;
    use serial_test::serial;
    use std::fs::{self, File};

    use crate::parser::build_ddnnf;

    use super::*;

    #[test]
    fn card_multi_queries() {
        let mut ddnnf: Ddnnf = build_ddnnf("./tests/data/VP9_d4.nnf", Some(42));
        ddnnf.max_worker = 1;
        ddnnf.card_of_each_feature("./tests/data/fcs.csv").unwrap();

        ddnnf.max_worker = 4;
        ddnnf.card_of_each_feature("./tests/data/fcm.csv").unwrap();

        let mut is_single = File::open("./tests/data/fcs.csv").unwrap();
        let mut is_multi = File::open("./tests/data/fcm.csv").unwrap();
        let mut should_be = File::open("./tests/data/VP9_sb_fs.csv").unwrap();

        // diff_files is true if the files are identical
        assert!(
            diff_files(&mut is_single, &mut is_multi),
            "card of features results of single und multi variant have differences"
        );
        is_single = File::open("./tests/data/fcs.csv").unwrap();
        assert!(
            diff_files(&mut is_single, &mut should_be),
            "card of features results differ from the expected results"
        );

        fs::remove_file("./tests/data/fcs.csv").unwrap();
        fs::remove_file("./tests/data/fcm.csv").unwrap();
    }

    #[test]
    #[serial]
    fn test_card_of_features_pd() {
        const PD_FILE: &str = "./tests/data/cof_pd.csv";
        const SHOULD_FILE: &str = "./tests/data/VP9_sb_fs.csv";

        let mut ddnnf: Ddnnf = build_ddnnf("./tests/data/VP9_d4.nnf", Some(42));
        ddnnf.max_worker = 1;
        ddnnf.card_of_each_feature(PD_FILE).unwrap();

        let mut pd: File = File::open(PD_FILE).unwrap();
        let mut should_be = File::open(SHOULD_FILE).unwrap();

        assert!(
            diff_files(&mut pd, &mut should_be),
            "card of features results differ from the expected results"
        );

        fs::remove_file(PD_FILE).unwrap();
    }
}
