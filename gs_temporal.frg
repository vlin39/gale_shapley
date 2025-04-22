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
  // #{Proposer} = #{Receiver}
  all p: Proposer | {
    all disj r1, r2 : Receiver | p.p_preferences[r1] != p.p_preferences[r2]
  }
  all r: Receiver | {
    all disj p1, p2 : Proposer | r.r_preferences[p1] != r.r_preferences[p2]
  }
}

pred wellformed_matches {
  // a proposer can't match to another proposer
  all p1, p2: Proposer | { not p1.match = p2 }
  // a receiver can't match to another receiver
  // this should also rule out the case that someone matches themselves
  all r1, r2: Receiver | { not r1.match = r2 }
  // two people cannot match to the same person
  all disj p1, p2: Person | { p1.match != p2.match }
  // a match needs to be reciprocated
  all p1, p2: Person | {(p1.match = p2) => (p2.match = p1)}
}

pred init {
  wellformed_preferences
  no match
}

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
    some (best_match.match) => {
      (best_match.match).match' = none
    }
    best_match.match' = p
    p.match' = best_match

    all other: Person - (p + best_match + best_match.match) | {
      other.match' = other.match
    }
  }
}

pred all_matched_and_do_nothing {
  all p : Person | {
    some p.match
  }
  match' = match
}

pred all_p_matched_and_do_nothing {
  all p : Proposer, r : Receiver | {
    some p.match
    p.match' = p.match
    {some r.match} => {r.match' = r.match}
    // the above lines work
    // this works for matching numbers even if I comment out the no r.match line
    // so that's not working somehow in 
    {r.match = none} => {r.match' = none}
  }
  // all p : Proposer | {
  //   some p.match
  // }
  // match' = match
}

pred all_p_matched_and_do_nothing2 {
  all p : Proposer | {
    some p.match
    p.match' = p.match
  }
}

pred all_p_matched_and_do_nothing3 {
  all p : Proposer | {
    some p.match
  }
  match' = match
}

pred literally_do_nothing {
  match' = match
}

pred all_available_matched {
  (#{Proposer} >= #{Receiver}) => { #{match} = #{Proposer} }
  (#{Proposer} <= #{Receiver}) => { #{match} = #{Receiver} }
}

pred gs_traces1 {
  init
  always (gs_transition or all_matched_and_do_nothing)
}

pred swap {
  some disj p1, p2: Proposer | some r: Receiver | {
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
  }
}

pred gs_traces2 {
  init
  always wellformed_matches
  always (gs_transition or all_matched_and_do_nothing)
}

pred gs_traces3 { //unsat 
  init
  eventually all_available_matched 
  always (gs_transition or do_nothing)
}

pred gs_traces4 {
  init 
  always (gs_transition or all_p_matched_and_do_nothing)
}

pred gs_traces5 {
  init 
  always (gs_transition or all_p_matched_and_do_nothing2)
}

pred gs_traces6 {
  init 
  always (gs_transition or all_p_matched_and_do_nothing3)
}

pred do_nothing{
  all_p_matched_and_do_nothing3
}
pred gs_traces {
  init 
  always (gs_transition or do_nothing)
}

// run gs_traces for exactly 3 Proposer, exactly 3 Receiver


// these run
// run gs_traces4 for exactly 1 Proposer, exactly 1 Receiver
// run gs_traces4 for exactly 2 Proposer, exactly 2 Receiver
// run gs_traces4 for exactly 3 Proposer, exactly 3 Receiver

// run gs_traces5 for exactly 3 Proposer, exactly 5 Receiver


pred all_matched {
  all p: Person | {
    p.match != none
  }
  wellformed_matches
}

pred noBetterMatch {
  no p: Proposer, r: Receiver | {
    // such that they are not currently matched
    p.match != r
    r.match != p
    // and would prefer each other
    (p.p_preferences[r] > p.p_preferences[p.match]) and (r.r_preferences[p] > r.r_preferences[r.match])
  }
}

pred betterMatch {
  some p: Proposer, r: Receiver | {
    // such that they are not currently matched
    p.match != r
    r.match != p
    // and would prefer each other
    (p.p_preferences[r] > p.p_preferences[p.match]) and (r.r_preferences[p] > r.r_preferences[r.match])
  }
}

// so this works
// test expect {
//   stable_matches: {(gs_traces and (always all_matched_and_do_nothing)) implies { noBetterMatch }} for exactly 3 Proposer, exactly 3 Receiver is checked
//   stable_matches_solved: {(gs_traces and (always all_matched_and_do_nothing)) implies { all_available_matched }} for exactly 3 Proposer, exactly 3 Receiver is checked
//   testing_pred1: {(gs_traces and (always all_matched_and_do_nothing)) implies { do_nothing }} for exactly 3 Proposer, exactly 3 Receiver is checked
//   testing_pred2: {(gs_traces and (always all_matched_and_do_nothing)) implies { all_p_matched_and_do_nothing }} for exactly 3 Proposer, exactly 3 Receiver is checked
//   testing_pred3: {gs_traces implies {
//     (always all_matched_and_do_nothing) implies (all_available_matched)
//   }} for exactly 3 Proposer, exactly 3 Receiver is checked
// }