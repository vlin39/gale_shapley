# gale_shapley

The problem of stable matching.

One algorithm to address the 

The Gale-Shapley algorithm is ...
- stable matching
- mysogynistic history
- biased

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

