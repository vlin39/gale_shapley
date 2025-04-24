#lang forge/temporal
// open "gs.frg"
open "gs_temporal.frg"
option test_keep last

---- HELPER FUNCTIONS -----


test expect {
  // so these work
  check_transition: {gs_transition} for exactly 2 Proposer, exactly 2 Receiver is sat
  check_init: {init} for exactly 2 Proposer, exactly 2 Receiver is sat
  // first step works
  check_first_step: {init and gs_transition} for exactly 2 Proposer, exactly 2 Receiver is sat
  two_pairs: {gs_traces} for exactly 2 Proposer, exactly 2 Receiver is sat
  three_pairs: {gs_traces} for exactly 3 Proposer, exactly 3 Receiver is sat
  four_pairs: {gs_traces} for exactly 4 Proposer, exactly 4 Receiver is sat
  // five_pairs: {gs_traces} for exactly 5 Proposer, exactly 5 Receiver is sat
  // six_pairs: {gs_traces} for exactly 6 Proposer, exactly 6 Receiver is sat
  // these take a REALLY LONG TIME to run and somehow end up unsat? 
  // so I tried testing for unsat
  // which worked??? 
}


test expect {
  // test that once you've matched everyone, it's stable
  // is there a case where the algorithm does not produce a stable match?
  // note: matched includes wellformed_matches
  problem_solved: {gs_traces => (eventually always all_matched_and_do_nothing)} for exactly 3 Proposer, exactly 3 Receiver is checked
  // matched isn't under any temporal constraints
  // so it would be false because it would expect matched from the start
  all_matched_test: {gs_traces => {always (all_matched_and_do_nothing iff all_matched)}} for exactly 3 Proposer, exactly 3 Receiver is checked
  stable_matches: {gs_traces implies {
    (always all_matched_and_do_nothing) implies noBetterMatch
  }} for exactly 3 Proposer, exactly 3 Receiver is checked
  stable_matches_another_way: {
  (gs_traces and (always all_matched_and_do_nothing)) implies { noBetterMatch }
  } for exactly 3 Proposer, exactly 3 Receiver is checked
  no_stable_match: {(always all_matched_and_do_nothing) and (no match)} for exactly 3 Proposer, exactly 3 Receiver is unsat
}



test expect {
  // I'm curious about if there are unbalanced numbers
  balanced_nums: {gs_traces and (eventually always (do_nothing and all_matched and noBetterMatch))} for exactly 3 Proposer, exactly 3 Receiver is sat
  more_proposers: {gs_traces and (eventually always (do_nothing and noBetterMatch))} for exactly 3 Proposer, exactly 2 Receiver is unsat
  // our model... our gs_transition is predicated on the idea there is a best match
  more_receivers: {gs_traces and (eventually always (do_nothing and noBetterMatch))} for exactly 2 Proposer, exactly 3 Receiver is sat
}

test expect {
  // TODO: how to visualize the two states? 
  -- so far we've only seen cases where the preferences aren't broken ... 
  -- ...so try to find a case where an engagement gets broken
  engagement_breaks: { 
    // order doesn't matter 
    // normally in index 0 / state 0, and you can only get out by using temporal operators
    gs_traces
    // this evaluates from the first state
    // so we specify that it doesn't have to be from the first state using eventually
    eventually {some disj p1, p2: Proposer | some r: Receiver | {
      // should we also check for the preferences here?
      -- state 1 -- 
      p1.match = r
      p2.match = none
      r.match = p1
      
      -- state 2 -- 
      p1.match' = none
      p2.match' = r
      r.match' = p2
      // all other: Person - (p1 + p2 + r) | {
      // other.match' = other.match
    }}
  } for exactly 3 Proposer, exactly 3 Receiver is sat
}

test expect {
  -- is the case where every proposer gets their first choice and ever receiver their last?
  // this passes a lot
  proposer_bias: {
    gs_traces
    eventually {
    // every proposer has their first choice
    // every receiver gets their last choice
      all p: Proposer, r: Receiver | {
        some p.match
        some r.match
        p.p_preferences[p.match] >= p.p_preferences[r]
        r.r_preferences[r.match] <= r.r_preferences[p]
      }
    }
  } for exactly 3 Proposer, exactly 3 Receiver is sat
  
  -- is the reverse possible?
  receiver_bias: {
    gs_traces
    eventually {
    // every proposer has their first choice
    // every receiver gets their last choice
      all p: Proposer, r: Receiver | {
        some p.match
        some r.match
        p.p_preferences[p.match] <= p.p_preferences[r]
        r.r_preferences[r.match] >= r.r_preferences[p]
      }
    }
  } for exactly 3 Proposer, exactly 3 Receiver is unsat
}

