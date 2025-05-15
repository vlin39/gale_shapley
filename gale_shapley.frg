#lang forge/temporal

------- ALGORITHM PSEUDOCODE ----------------------------
/*
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

-------- SIGNATURES --------------------------
abstract sig Person {
  var match : lone Person
}
sig Proposer extends Person { 
  p_preferences: func Receiver -> Int
}
sig Receiver extends Person { 
  r_preferences: func Proposer -> Int
}

--------- INITIAL STATE ------------------------
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

------------ TRANSITIONS --------------------------------

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
    r1 : (free_receivers + would_prefer) | {
      all r2 : (free_receivers + would_prefer) | {
        p.p_preferences[r1] >= p.p_preferences[r2]
      }
    }
  }
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
  all p : Proposer | {
    some p.match
  }
  match' = match
}

pred do_nothing{
  all_p_matched_and_do_nothing3
}

---------- TRACES ------------------------------------

pred gs_traces {
  init 
  always (gs_transition or do_nothing)
}

----------- RUN --------------------------------------
option max_tracelength 8
option min_tracelength 2

two_matches: run gs_traces for exactly 2 Proposer, exactly 2 Receiver
three_matches: run gs_traces for exactly 3 Proposer, exactly 3 Receiver
four_matches: run gs_traces for exactly 4 Proposer, exactly 4 Receiver
five_matches: run gs_traces for exactly 5 Proposer, exactly 5 Receiver


--------- EVALUATOR HELPERS ---------------------------

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

pred sadReceivers {
  all p: Proposer, r: Receiver | {
    some r.match 
    r.r_preferences[r.match] <= r.r_preferences[p]
  }
}

pred sadProposers {
  all p: Proposer, r: Receiver | {
    some p.match 
    p.p_preferences[p.match] <= p.p_preferences[r]
  }
}

pred happyReceivers {
  all p: Proposer, r: Receiver | {
    some r.match 
    r.r_preferences[r.match] >= r.r_preferences[p]
  }
}

pred happyProposers {
  all p: Proposer, r: Receiver | {
    some p.match 
    p.p_preferences[p.match] >= p.p_preferences[r]
  }
}