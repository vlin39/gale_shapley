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

pred do_nothing {
  all p : Person | {
    some p.match
  }
  match' = match
}

pred gs_traces {
  init
  always (gs_transition or all_matched_and_do_nothing)
}

// run gs_traces for exactly 3 Proposer, exactly 3 Receiver