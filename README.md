# gale_shapley

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

### ???

## Temporal version

Code: gs_temporal.frg

Tests: gs_temporal_tests.frg

### Sigs

### Init

### Transition

## To run
- https://csci1710.github.io/forge-documentation/getting-started/installation.html
- Go to file in VSCode--green arrow, upper-right

Visualizations
Theme: theme.json

Helper functions: 
- Evaluator (lower-right), `eventually all_matched`, `eventually noBetterMatch`, etc. 


## Visualizations
Theme: theme.json

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