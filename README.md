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

Today, the terminology is instead generalized to "proposers" and "receivers".

For further reading:  
https://en.wikipedia.org/wiki/Gale%E2%80%93Shapley_algorithm

This is run in Forge...
https://csci1710.github.io/forge-documentation/home.html

See the To run section for more information. 

## Algorithm Psuedocode
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

## Froglet version

Code: gs.frg

Tests: gs_tests.frg

This is stable matching

### Sigs

### Predicates 
We'll use these to constrain the ...

## Temporal version

Code: gs_temporal.frg

Tests: gs_temporal_tests.frg

### Sigs

### Initial State

### Transition Predicates

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

