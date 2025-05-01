# gale_shapley

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