#lang forge/temporal
// open "gs.frg"

/* ALGORITHM PSEUDOCODE

  def gale_shapley(men, women):
      engagements = {}
      free_men = list(men.keys())

      while free_men:
          man = free_men.pop(0)
          preferences = men[man]
          -----------------------------------------------
          for woman in preferences:
              fiance = engagements.get(woman)

              if not fiance:
                  engagements[woman] = man
                  break

              elif women[woman].index(man) < women[woman].index(fiance):
                  free_men.append(fiance)
                  engagements[woman] = man
                  break
          -----------------------------------------------
      return engagements

*/

abstract sig Person {
  var match : lone Person
}

sig Proposer extends Person { 
  p_preferences: func Receiver -> Int
}

sig Receiver extends Person { 
  r_preferences: func Proposer -> Int
}


pred wellformed_preferences {
  #{Proposer} = #{Receiver}
  all p: Proposer | {
    all disj r1, r2 : Receiver | p.p_preferences[r1] != p.p_preferences[r2]
  }
  all r: Receiver | {
    all disj p1, p2 : Proposer | r.r_preferences[p1] != r.r_preferences[p2]
  }
}

pred init {
  wellformed_preferences
  no match
}

// one sig GSState {
//   var engagements: pfunc Proposer -> Receiver,
//   var freeProposers: set Proposer
// } 

pred guard_match[p: Proposer, best_match : Receiver] {
  let free_receivers = { 
    r : Receiver | no r.match
  } | 
  let would_prefer = {
    r : Receiver | { 
        some r.match
        r.r_preferences[p] > r.r_preferences[r.match]
      }
  } | 
  best_match = {
    r1 : Receiver | {
      all r2 : Receiver {
        r1 + r2 in (free_receivers + would_prefer)
        p.p_preferences[r1] >= p.p_preferences[r2]
      }
    }
  }
  // no return -- so include it as a parameter
}

pred gs_transition {
  some p : Proposer, best_match : Receiver | {
    no p.match
    guard_match[p, best_match]
    some best_match.match => {
      best_match.match.match' = none
    }
    best_match.match' = p
    p.match' = best_match

    all other: Person - (p + best_match + best_match.match) | {
      other.match' = other.match
    }
  }
}

pred do_nothing {
  all p : Person | {
    some p.match
  }
  match' = match
}

pred gs_traces {
  init
  always (gs_transition or do_nothing)
}

// test expect {
//   // so these work
//   {gs_transition} for exactly 2 Proposer, exactly 2 Receiver is sat
//   {init} for exactly 2 Proposer, exactly 2 Receiver is sat
//   // first step works
//   {init and gs_transition} for exactly 2 Proposer, exactly 2 Receiver is sat
// }

run gs_traces for exactly 3 Proposer, exactly 3 Receiver


// test expect {
//   two_pairs: {gs_traces} for exactly 2 Proposer, exactly 2 Receiver is sat
//   three_pairs: {gs_traces} for exactly 3 Proposer, exactly 3 Receiver is sat
//   four_pairs: {gs_traces} for exactly 4 Proposer, exactly 4 Receiver is sat
//   // five_pairs: {gs_traces} for exactly 5 Proposer, exactly 5 Receiver is sat
//   // ^ this fails??? And when I try to run it, it's unsat?
//   // test that once you've matched everyone, it's stable
//   // gs_traces implies { eventually always do_nothing
//   // } is checked ? 

//   // is there a case where the algorithm does not produce a stable match?
//   // note: matched includes wellformed_matches
//   problem_solved: {gs_traces => (eventually always do_nothing)} for exactly 4 Proposer, exactly 4 Receiver is checked
//   // matched isn't under any temporal constraints
//   // so it would be false because it would expect matched from the start
//   all_matched: {gs_traces => {always (do_nothing iff matched)}} for exactly 4 Proposer, exactly 4 Receiver is checked
//   stable_matches: {
//     (always do_nothing) implies noBetterMatch
//   } for exactly 4 Proposer, exactly 4 Receiver is checked
//   no_stable_match: {(always do_nothing) and (no match)} for exactly 4 Proposer, exactly 4 Receiver is unsat
//   // I'm curious about if there are unbalanced numbers
//   {gs_traces and (eventually always (do_nothing and matched and noBetterMatch))} for exactly 4 Proposer, exactly 4 Receiver is sat
//   {gs_traces and (eventually always (do_nothing and noBetterMatch))} for exactly 4 Proposer, exactly 3 Receiver is unsat //???
//   // our model... our gs_transition is predicated on the idea there is a best match
//   {gs_traces and (eventually always (do_nothing and noBetterMatch))} for exactly 3 Proposer, exactly 4 Receiver is sat
//   // this won't work with how we've written do_nothing --- since that requires everyone to have some match
//   // When 4 Proposer, 3 Receiver:
//   // some unmatched: Proposer | all p: (Person - unmatched) | { some p.match } 
//   // cardinality? 
//   // # of matches = # of smallest of proposers and receivers
//   // 

//   -- so far we've only seen cases where the preferences aren't broken ... 
//   -- ...so try to find a case where an engagement gets broken
//   engagement_breaks : {
//     some disj p1, p2: Proposer | some r: Receiver | {
//       // should we also check for the preferences here?

//       -- state 1 -- 
//       p1.match = r
//       p2.match = none
//       r.match = p1
      
//       -- state 2 -- 
//       p1.match = none
//       p2.match = r
//       r.match = p2
      
//       // all other: Person - (p1 + p2 + r) | {
//       // other.match' = other.match
//     }
//   } for exactly 4 Proposer, exactly 4 Receiver is sat

//   -- is the case where every proposer gets their first choice and ever receiver their last?
//   proposer_biased : {
//     // every proposer has their first choice
//     all p: Proposer, r: Receiver | {
//       p.p_preferences[p.match] >= p.p_preferences[r]
//       r.r_preferences[r.match] <= r.r_preferences[p]
//     }
//   } for exactly 4 Proposer, exactly 4 Receiver is sat
  
//   -- is the reverse possible?
//   receiver_biased : {
//     // every proposer has their first choice
//     all p: Proposer, r: Receiver | {
//       p.p_preferences[p.match] <= p.p_preferences[r]
//       r.r_preferences[r.match] >= r.r_preferences[p]
//     }
//   } for exactly 4 Proposer, exactly 4 Receiver is unsat

// } 
