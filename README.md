# gale_shapley
## The Problem of Stable Matching

The **stable matching problem** involves finding a way to pair individuals from two equally sized sets based on ranked preferences, such that no two individuals would rather be with each other than with their assigned partners. Each individual ranks every member of the opposite group in order of preference.

A matching is **stable** if:
- Every individual is matched.
- There are no two people (a proposer and a receiver) who would both prefer to be with each other than with their current matches. Such a pair is called a **blocking pair**.

The problem applies to many real-world domains:
- College admissions
- Medical residency placements
- Job recruiting
- School choice mechanisms

## The Gale–Shapley Algorithm

The **Gale–Shapley algorithm**, introduced in 1962 by David Gale and Lloyd Shapley, provides a guaranteed solution to the stable matching problem. It ensures that a stable matching always exists and can be efficiently found through a process of proposals and tentative acceptances.

### How It Works

The algorithm follows an iterative process:
- Each **proposer** starts by proposing to their most-preferred **receiver** who has not yet rejected them.
- Each receiver tentatively holds onto the most preferred proposal they’ve received so far and rejects the others.
- Rejected proposers continue down their preference list in subsequent rounds.
- The process continues until all proposers are matched and no proposals remain unprocessed.

### Properties

- The resulting matching is **proposer-optimal**: no proposer could get a better match in any stable pairing.
- It is **receiver-pessimal**: each receiver gets their worst valid match among all possible stable matchings.

### History and Criticism

The algorithm was originally framed in terms of heterosexual marriage, with men proposing to women. This framing embeds a **gendered power imbalance**:
- Proposers always benefit, while receivers have limited agency.
- In real-world systems, this bias can affect outcomes depending on which side is allowed to propose.

Algorithm Psuedocode: 
```
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
```

Today, the terminology is instead generalized to "proposers" and "receivers".

For further reading:  
https://en.wikipedia.org/wiki/Gale%E2%80%93Shapley_algorithm

This is implemented using Forge: https://csci1710.github.io/forge-documentation/home.html

See the To run section for more information. 


## Froglet version

Code: gs.frg

Tests: gs_tests.frg

This models a group of stable matches. 

### Signatures
```
abstract sig Person {
  match : lone Person
}
sig Proposer extends Person { 
  p_preferences: func Receiver -> Int
}

sig Receiver extends Person { 
  r_preferences: func Proposer -> Int
}
```
- Proposer / Receiver are sets representing participants that extend Person.
- Person.match: A relation representing an individual's match. Using `lone` enables the match to be none, while `one` would cause it to generate already matched.
- Proposer.p_preferences is meant to store the proposers’ ordered preferences regarding receivers as a function that maps each Receiver to an Int. 
- Receiver.r_preferences is the same, but for Receivers. 

### Predicates 
We'll use these to constrain the ...

`wellformed_preferences` constrains the domain of the preferences. It assumes an equal number of Proposers and Receivers, and constrains it so that no two Receivers can have the same preference by a Proposer. 

`wellformed_matches` constrains the matches. a proposer can't match to another proposer, a receiver can't match to another receiver (which should also rule out the case that someone matches themselves), two people cannot match to the same person, and a match needs to be reciprocated. 

`matched` ensures that everyone is matched.

`noBetterMatch` ensures that the matching is stable--there are no two people (a proposer and a receiver) who would both prefer to be with each other than with their current matches.

### Tests

## Temporal version

Code: gs_temporal.frg

Tests: gs_temporal_tests.frg

### Sigs

```
abstract sig Person {
  var match : lone Person
}

sig Proposer extends Person { 
  p_preferences: func Receiver -> Int
}

sig Receiver extends Person { 
  r_preferences: func Proposer -> Int
}
```

### Initial State

wellformed_preferences
no match

### Transition Predicates
```
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
  // no return -- so include it as a parameter
}
```

```
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
```

```
all_p_matched_and_do_nothing {
  all p : Proposer | {
    some p.match
  }
  match' = match
}
```

### Design Decisions
do nothing is kinda like the end state, in this case we focus on only checking if all the proposers are matched. This fits with the pseudocode. 

### Traces

## To run
- https://csci1710.github.io/forge-documentation/getting-started/installation.html
- Go to file in VSCode--green arrow, upper-right

```
option max_tracelength 8
option min_tracelength 6
```

`option test_keep last`

Visualizations
Theme: theme.json

Helper functions: 
- Evaluator (lower-right), `eventually all_matched`, `eventually noBetterMatch`, etc. 


## Visualizations
Theme: theme.json

gs_vis.js

CND YAML 
```
constraints:
  - orientation:
      selector: (Receiver -> Proposer) & match
      directions:
        - directlyLeft
  - orientation:
      selector: (Proposer -> Receiver) & match
      directions:
        - directlyRight
directives:
  - flag: hideDisconnectedBuiltIns
  - attribute:
      field: r_preferences
  - attribute:
      field: p_preferences
```

