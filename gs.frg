#lang forge/froglet

----- SIGNATURES -----
abstract sig Person {
  match : lone Person
  // lone vs one - one automatically generates while matched
}
sig Proposer extends Person { 
  p_preferences: func Receiver -> Int
}

sig Receiver extends Person { 
  r_preferences: func Proposer -> Int
}

----- PREDICATES -----

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
}

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

