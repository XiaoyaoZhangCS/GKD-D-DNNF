use crate::ddnnf::anomalies::t_wise_sampling::data_structure::{Config, Sample};
use crate::ddnnf::anomalies::t_wise_sampling::sat_wrapper::SatWrapper;

/// Covering strategy that uses the sat state caching.
pub(super) fn cover_with_caching(
    sample: &mut Sample,
    interaction: &[i32],
    sat_solver: &SatWrapper,
    node_id: usize,
    number_of_vars: usize,
) {
    debug_assert!(!interaction.iter().any(|x| *x == 0));
    if sample.covers(interaction) {
        return; // already covered
    }
    let mut interaction_sat_state = sat_solver.new_state();
    if !sat_solver.is_sat_in_subgraph_cached(interaction, node_id, &mut interaction_sat_state) {
        return; // interaction invalid
    }

    let mut found = None;
    for (index, config) in sample.partial_configs.iter_mut().enumerate() {
        if config.conflicts_with(interaction) {
            continue;
        }

        config.update_sat_state(sat_solver, node_id);

        // clone sat state so that we don't change the state that is cached in the config
        let mut sat_state = config
            .get_sat_state()
            .cloned()
            .expect("sat state should exist because update_sat_state() was called before");

        if sat_solver.is_sat_in_subgraph_cached(interaction, node_id, &mut sat_state) {
            // we found a config - extend config with interaction and update sat state
            config.extend(interaction.iter().cloned());
            config.set_sat_state(sat_state);
            found = Some(index);
            break;
        }
    }

    if let Some(index) = found {
        // move config to the complete configs if it is complete now
        let config = sample.partial_configs.get(index).expect("");
        if sample.is_config_complete(config) {
            let config = sample.partial_configs.swap_remove(index);
            sample.add_complete(config);
        }
    } else {
        // no config found - create new config
        let mut config = Config::from(interaction, number_of_vars);
        config.set_sat_state(interaction_sat_state);
        sample.add(config);
    }
}
