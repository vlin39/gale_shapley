#lang forge/temporal
open "gs.frg"
open "gs_temporal.frg"
option test_keep last

test expect {
  // so these work
  {gs_transition} for exactly 2 Proposer, exactly 2 Receiver is sat
  {init} for exactly 2 Proposer, exactly 2 Receiver is sat
  // first step works
  {init and gs_transition} for exactly 2 Proposer, exactly 2 Receiver is sat
}

/*
test expect {
  {gs_traces} for exactly 2 Proposer, exactly 2 Receiver is sat
  {gs_traces} for exactly 4 Proposer, exactly 4 Receiver is sat
  {gs_traces} for exactly 5 Proposer, exactly 5 Receiver is sat
  // test that once you've matched everyone, it's stable
  // gs_traces implies { eventually always do_nothing
  // } is checked ? 

  // is there a case where the algorithm does not produce a stable match?
  // note: matched includes wellformed_matches
  problem_solved: {gs_traces => (eventually always do_nothing)} for exactly 4 Proposer, exactly 4 Receiver is checked
  // matched isn't under any temporal constraints
  // so it would be false because it would expect matched from the start
  all_matched: {gs_traces => {always (do_nothing iff matched)}} for exactly 4 Proposer, exactly 4 Receiver is checked
  stable_matches: {
    (always do_nothing) implies noBetterMatch
  } for exactly 4 Proposer, exactly 4 Receiver is checked
  no_stable_match: {(always do_nothing) and (no match)} for exactly 4 Proposer, exactly 4 Receiver is unsat
  // I'm curious about if there are unbalanced numbers
  {gs_traces and (eventually always (do_nothing and matched and noBetterMatch))} for exactly 4 Proposer, exactly 4 Receiver is sat
  {gs_traces and (eventually always (do_nothing and noBetterMatch))} for exactly 4 Proposer, exactly 3 Receiver is unsat //???
  // our model... our gs_transition is predicated on the idea there is a best match
  {gs_traces and (eventually always (do_nothing and noBetterMatch))} for exactly 3 Proposer, exactly 4 Receiver is sat
  // this won't work with how we've written do_nothing --- since that requires everyone to have some match
  // When 4 Proposer, 3 Receiver:
  // some unmatched: Proposer | all p: (Person - unmatched) | { some p.match } 
  // cardinality? 
  // # of matches = # of smallest of proposers and receivers
  // 


  -- so far we've only seen cases where the preferences aren't broken ... 
  -- ...so try to find a case where an engagement gets broken
  engagement_breaks : {
    some disj p1, p2: Proposer | some r: Receiver | {
      // should we also check for the preferences here?

      -- state 1 -- 
      p1.match = r
      p2.match = none
      r.match = p1
      
      -- state 2 -- 
      p1.match = none
      p2.match = r
      r.match = p2
      
      // all other: Person - (p1 + p2 + r) | {
      // other.match' = other.match
    }
  } for exactly 4 Proposer, exactly 4 Receiver is sat
  -- is the case where every proposer gets their first choice and ever receiver their last?
  proposer_biased: {
    // every proposer has their first choice
    all p: Proposer, r: Receiver | {
      p.p_preferences[p.match] >= p.p_preferences[r]
      r.r_preferences[r.match] <= r.r_preferences[p]
    }
  } for exactly 4 Proposer, exactly 4 Receiver is sat
  
  -- is the reverse possible?
  receiver_biased : {
    // every proposer has their first choice
    all p: Proposer, r: Receiver | {
      p.p_preferences[p.match] <= p.p_preferences[r]
      r.r_preferences[r.match] >= r.r_preferences[p]
    }
  } for exactly 4 Proposer, exactly 4 Receiver is unsat
}
*/