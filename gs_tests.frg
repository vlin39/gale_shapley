#lang forge/froglet
open "gs.frg"
option test_keep last

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

test expect{
  // someone doesn't have a match
  missing_match: {gale_shapley and missing_match} for exactly 5 Proposer, exactly 5 Receiver is unsat
  // no one has a match
  no_matches: {gale_shapley and no_matches} for exactly 5 Proposer, exactly 5 Receiver is unsat
  // someone matched themself
  self_match: {gale_shapley and self_match}for exactly 5 Proposer, exactly 5 Receiver is unsat
  // a proposer matched to another proposer
  r_matched_r: {gale_shapley and r_matched_r} for exactly 5 Proposer, exactly 5 Receiver is unsat
  // a receiver matched to another receiver
  r_matched_r: {gale_shapley and r_matched_r} for exactly 5 Proposer, exactly 5 Receiver is unsat
  // two people prefer each other to their current partners
  better_match: {gale_shapley and better_match} for exactly 5 Proposer, exactly 5 Receiver is unsat
  // two people matched to one person
  nonunique: {gale_shapley and nonunique} for exactly 5 Proposer, exactly 5 Receiver is unsat
}