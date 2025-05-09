#lang forge/temporal

// abstract sig Person {
//   match : lone Person
//   // lone vs one
//   // one automatically generates while matched
// }
// sig Proposer extends Person { 
//   p_preferences: func Receiver -> Int //,
//   // temporal 
//   // next_perference: Receiver
//   // var status: Free
// }

// sig Receiver extends Person { 
//   r_preferences: func Proposer -> Int
// }


// - check for validity
// - get a free Proposer/the next(?) free Proposer
// - get the Proposer's most preferred Receiver
// - if that Receiver doesn't have a match, set that match to this Proposer
// - if that Receiver has a match but prefers this Proposer to the current match, change their match to this current match and remove the former match
// - go back to step 2 (get a free Proposer)
// - stop when there are no more unmatched Proposers

// abstract sig Status {
//     var free_proposers: set Proposer
// }
// one sig Single extends Status {}
// one sig Matched extends Status {}

// helper for temporal--- get the next unmatched person

// one sig Free {}


// sig R_Preferences {
//   next_person: lone Proposer
//   // list: func Proposer -> Proposer
// }

// arbitrary person

// def gale_shapley(men, women):
//     engagements = {}
//     free_men = list(men.keys())

//     while free_men:
//         man = free_men.pop(0)
//         preferences = men[man]
//         -----------------------------------------------
//         for woman in preferences:
//             fiance = engagements.get(woman)

//             if not fiance:
//                 engagements[woman] = man
//                 break

//             elif women[woman].index(man) < women[woman].index(fiance):
//                 free_men.append(fiance)
//                 engagements[woman] = man
//                 break
//         -----------------------------------------------

//     return engagements




---------------------------------------------------------------------

-- Initial State:
// - Equal number of prospers and receivers 
// - a Proposer can only have #(Receiver) preferences
// - a Receiver can only have #(Proposer) preferences
// - Preferences must be distinct (one int per person)
// - No one is matched
// - Everyone has a list of Preferences, with everyone in the other party ranked

pred wellformed_preferences {
  #{Proposer} = #{Receiver}
  all p: Proposer | {
    all disj r1, r2 : Receiver | p.p_preferences[r1] != p.p_preferences[r2]
  }
  all r: Receiver | {
    all disj p1, p2 : Proposer | r.r_preferences[p1] != r.r_preferences[p2]
  }
}

pred wellformed_matches {
  // a proposer can't match to another proposer
  all p1, p2: Proposer | {
    not p1.match = p2
  }
  // a receiver can't match to another receiver
  all r1, r2: Receiver | {
    not r1.match = r2
  }
  // this should also rule out the case that someone matches themselves
  
  // two people cannot match to the same person
  all disj p1, p2: Person |{
    p1.match != p2.match
  }

  // a match needs to be reciprocated
  all p1, p2: Person | {
    (p1.match = p2) => (p2.match = p1)
      // in Forge, assignment and comparison might as well be the same thing
  }
  // risk of unsat with 
  // all disj p1, p2: Person | {
  //     p1.match = p2
  //     p2.match = p1
  // }
}

-- Final State:
// - Everyone is matched in stable matches 
// - there exists no Proposer and Receiver such that they would rather have each other than their current partners

pred matched {
  all p: Person | {
    p.match != none
    // this works with lone and makes it behave like one
  }
  wellformed_matches
}

pred noBetterMatch {
  no p: Proposer, r: Receiver | {
    // such that they are not currently matched
    p.match != r
    r.match != p
    // and would prefer each other
    p.p_preferences[r] > p.p_preferences[p.match]
    r.r_preferences[p] > r.r_preferences[r.match]
  }
}

pred gale_shapley {
  wellformed_preferences
  wellformed_matches
  matched
  noBetterMatch
}

// run {
//   gale_shapley
// } for exactly 2 Proposer, exactly 2 Receiver

---------------------------------------------------------------------

-- PART 1: MODEL STABLE MATCHING WITHOUT AN ALGORITHM
// - just solve for or recognize stable matchings 
//     - set up datatypes
//     - write a predicate for "this matching is stable, generate stable matching via `run`
// - + is it a matching, is it total, is it stable, etc.

---------------------------------------------------------------------

-- PART 2: MODEL G-S USING TRACES (TEMPORAL?)
//  - If you use temporal, watch out for deadlocks (add a defensive no-op transition that frames everything)

abstract sig Person {
  var match : lone Person
}

sig Proposer extends Person { 
  p_preferences: func Receiver -> Int
}

sig Receiver extends Person { 
  r_preferences: func Proposer -> Int
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
  // let free_receivers = all r : Receiver | {
  //   no r.match
  // }
  let free_receivers = { 
    r : Receiver | no r.match
  } | 
  let would_prefer = {
    r : Receiver | { 
        some r.match
        r.r_preferences[p] > r.r_preferences[r.match]
      }
  } | 
  // the semantics when Forge switches between integer and relational 
  // is that the empty set is 0 
  // but if r_preferences[p] is negative and r_preferences[r.match] is 0 ... that could cause issues
  // let best_match = one r1 : Receiver | {
  //   r1 in (free_receivers + would_prefer)
  //   all r2 : Receiver {
  //     r1 >= r2
  //   }
  // }
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
  // how to keep track of the matches???
  // nobody else changes
  // will probably involve an all
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

// run gs_traces for exactly 4 Proposer, exactly 4 Receiver

// test expect {
//   // so these work
//   {gs_transition} for exactly 2 Proposer, exactly 2 Receiver is sat
//   {init} for exactly 2 Proposer, exactly 2 Receiver is sat
//   // first step works
//   {init and gs_transition} for exactly 2 Proposer, exactly 2 Receiver is sat
  
// test example 
// Proposers get their best choice, Receivers get their worst

// is there a case where the algorithm does not produce a stable match?
// test expect {

// }

// }

// pred assign_matches[p: Proposer, r: Receiver]{
//     // there are four cases going into a match:
//     // p is unmatched and r is unmatched
//     // p is matched and r is unmatched
//     // p is unmatched and r is matched
//     // p is matched and r is matched
//     // I think I need to account for all of these? 
    
//     no r.match => {
//         r.match' = p
//         p.match' = r
//     }
//     (r.r_preferences[p] < r.r_preferences[r.match]) => {
//         (r.match).match' = none
//         (p.match).match' = none
//         r.match' = p
//         p.match' = r
//     }

// }

---------------------------------------------------------------------

-- PART 3: CHECK FOR BIAS
//  - now combine them: use the defn of stable matching from
//    part 1 to check the results of G-S from part 2.
//    "can we find a G-S trace that produces something other than
//     a stable matching?"
//  - (this is the experimental part): can we encode some notion of bias-detection?
//    we know we always get a stable matching (yay) but can we encode what goes wrong


// Is it possible that there exists a scenario in which 
// each Proposer gets their first choice and each Receiver gets their last choice?

// Is it possible for the reverse scenario to occur? 

---------------------------------------------------------------------

-- Tests

// SAT -- examples?

// implies? 


// example, for expressing that specific instances should satisfy (or not satisfy) a predicate;
// assert, for expressing that a predicate should be...
//     sufficient to satisfy another (is sufficient for);
//     necessary for another to be satisfied (is necessary for);
//     is consistent with another, i.e., that the combination of the two predicates can be satisfied by at least one instance (is consistent with);
//     is satisfiable or unsatisfiable (is sat and is unsat).


// assert fullFirstRow is sufficient for winning for 1 Board
// assert someMoveTaken is necessary for winning for 1 Board
// nonvacuous_fullFirstRow: assert fullFirstRow is consistent with wellformed
// nonvacuous_someMoveTaken: assert someMoveTaken is consistent with wellformed


pred is_stable{
  eventually always do_nothing
}

assert {gs_traces} implies {eventually always do_nothing} 

test expect {
  // test that once you've matched everyone, it's stable
  // gs_traces implies { eventually always do_nothing
  // } is checked
  

  -- so far we've only seen cases where the preferences aren't broken ... 
  -- ...so try to find a case where an engagement gets broken

  -- is the case where every proposer gets their first choice and ever receiver their last?
  -- is the reverse possible?

  -- think about visualization? 

  -- visualize which rank preference each person gets?
  -- so at each state, show if they're matched with their highest/second-highest/lowest preference

  -- javascript?
  -- Siddhartha's been working with something (CND) -- 3D printing pun
  -- but that doesn't let you visualize additional data
  -- another ISP student has been working on a "what you see is what you get" visualizer
  -- which can visualize predicates, but also isn't optimal for views
  -- we might need to add some state to make this happen... (if we want to count distance)

  -- good example for thinking about how we're going to give students assistance in adding extra information 
  -- that isn't part of the instance
}

// UNSAT 

pred missing_match {
  // NOTE: can be unsat when there are uneven numbers of Proposers and Reciever
  some p: Person | {
    no p.match
  }
}

pred no_matches {
  all p: Person |{
    no p.match
  }
}

pred self_match {
  some p: Person | {
    p.match = p
  }
}

pred p_matched_p {
  some disj p1, p2: Proposer | {
    p1.match = p2
  }
}

pred r_matched_r{
  some disj r1, r2: Receiver | {
    r1.match = r2
  }
}

pred better_match {
  some disj p: Proposer, r: Receiver | {
    p.match != r
    r.match != p
    p.p_preferences[r] > p.p_preferences[p.match]
    r.r_preferences[p] > r.r_preferences[r.match]
  }
}

pred nonunique {
  some disj p1, p2: Person | {
    p1.match = p2.match
  }
}



// try tests with uneven numbers?




---------------------------------------------------------------------