# gale_shapley
## The Problem of Stable Matching

The **stable matching problem** involves finding a way to pair individuals from two different sets A and B, which are usually of equal size, based on ranked preferences such that no two individuals would rather be with each other than with their assigned partners. Each individual ranks every member of the opposite group in order of preference.

A matching is **stable** if:
1. Every individual is matched.
2. There are no two people who would both prefer to be with each other than with their current matches. Such a pair is called a **blocking pair**.

The problem applies to many real-world domains, such as:
- College admissions
- Medical residency placements
- Job recruiting
- School choice mechanisms

## The Gale–Shapley Algorithm

The **Gale–Shapley algorithm**, introduced in 1962 by David Gale and Lloyd Shapley, provides a guaranteed solution to the stable matching problem. It ensures that a stable matching always exists and can be efficiently found through a process of proposals and acceptances.

### How It Works

The algorithm follows an iterative process:
- Each unmatched **proposer** starts by proposing to their most-preferred **receiver** who has not yet rejected them.
- Each receiver holds onto the most preferred proposal _that they’ve received so far_ and rejects the others.
- Rejected proposers continue down their preference list in subsequent rounds.
- The process continues until all proposers are matched and no proposals remain unprocessed.

### Properties

- The resulting matching is **proposer-optimal**: no proposer could get a better match in any stable pairing.
- It is **receiver-pessimal**: it is possible for each receiver gets their worst valid match among all possible stable matchings.

### History and Criticism

The algorithm was originally framed in terms of heterosexual marriage, with men proposing to women. This framing embeds a **gendered power imbalance**:
- Proposers always benefit, while receivers have limited agency. This is in spite of a common assumption that receivers would hold the power, since they have the capacity to reject proposals. 
- In real-world systems, this bias can affect outcomes depending on who is allowed to propose.

#### Algorithm Psuedocode: 
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

See the **To run** section for more information. 

# Code

There are two types of models coded: 
- The Froglet version is a more broad/basic version of stable matching that generates a group of stable matches.
- The Temporal version uses a temporal transition system to model the Gale-Shapley Algorithm. 

## Froglet: Stable Matching

Code: `stable_matching.frg`

Tests: `stable_matching_tests.frg`

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

- `Proposer` / `Receiver` are sets representing participants that each extend Person.
- `Person.match`: A relation representing an individual's match. Using `lone` enables the match to be none, while `one` would cause it to generate already matched.
- `Proposer.p_preferences` is meant to store the proposers’ ordered preferences regarding receivers as a function that maps each Receiver to an Int. 
- `Receiver.r_preferences` is the same for Receivers. 

### Predicates 

- `wellformed_preferences` constrains the domain of the preferences. It assumes an equal number of Proposers and Receivers, and constrains it so that no two Receivers can have the same level of preference by a Proposer. 

- `wellformed_matches` constrains the matches:
  - A proposer can't match to another proposer, and a receiver can't match to another receiver (which should also rule out the case that someone matches themselves)
  - Two people cannot match to the same person
  - A match needs to be reciprocated. 

- `matched` ensures that everyone is matched.

- `noBetterMatch` ensures that the matching is stable--there are no two people (a Proposer and a Receiver) who would both prefer to be with each other than with their current matches.

## Temporal: Gale Shapley

Code: `gale_shapley.frg`

Tests: `gale_shapley_tests.frg`

Many things remain similar to the previous **Froglet: Stable Matching** model, but there are some changes. 

### Signatures

```
abstract sig Person {
  var match : lone Person
}
```

The `Proposer` and `Receiver` sigs remain unchanged, but since we will be modeling a series of states and building the matches, `match` is a `var`.

### Initial State

We constrain the initial state to be a set of Proposers and Receivers such that the preferences are well-formed and there are no matches yet. 
- `wellformed_preferences` - no longer assumes that the two groups must be equal, otherwise unchanged. 
- `no match` 

### Transition Predicates

- `guard_match` is a helper for the transition that provides the most-preferred available Receiver for the given Proposer
- `gs_transition` goes through unmatched Proposers and assigns their best_match. All existing matches do not change.
- `all_p_matched_and_do_nothing` - when all proposers have a match, the matches remain unchanged between states.

### Design Decisions

- `do_nothing` is similar to our end state--in this case, we focus on only checking if all the proposers are matched. This fits with the pseudocode, and still allows for all Proposers to receive their best match when there are more Receivers than Proposers.
- `guard_match` finds the most preferred Receiver for that Proposer out of all the candidates (with the candidates being the set of all the unmatched Receivers joined with the set of all Receivers that would prefer the given Proposer to their current match)
- `gs_transition` goes through all Proposers without a match and finds a Receiver as their `best_match`. The Proposer and Receiver are matched, and in the case the Reciever had a previous match p : Proposer, that match is now removed.

## To run the code... 

(For more detailed instructions, go to: https://csci1710.github.io/forge-documentation/running-models/sterling-visualizer.html) 

1. Make sure Forge is installed according to the directions here (https://csci1710.github.io/forge-documentation/getting-started/installation.html). The preferred IDE is VSCode.
2. Open a file in VSCode and go to the green arrow in the upper-right-hand corner. Click to run -- a window should appear in your browser of choice shortly. 
3. In the upper-right-hand corner of the browser window, select a command from "Select an Available Command" and click the "Run" button. Wait until an output appears on the screen. (If you cannot see this, click on "Graph" in the upper border/heading, to the right, and then click on "Explore" in the right-most border/column, to the bottom.)
5. In the right-most border/column, click the first option "Time". This should be towards the top of the page. Use the arrow keys to go through the states. 

### Visualizations

Options for visualization involve using a custom theme, using JavaScript, and using CnD. For more information on using any of these, go to the documention. 

**Custom Theme:** https://csci1710.github.io/forge-documentation/running-models/sterling-visualizer.html

1. Upon seeing an output in the browser window, go to the second option in the right-most border/column and click on "Theme". 
2. In the heading of the right-hand column, go to the middle button and click on "Browse...".
3. Provide the `theme.json` file in the project folder and click "Open".
4. In the window, click and drag past the `Int`s to view the `Receiver` and `Proposer` boxes. (Click on the right side of the screen, then hold and drag left.)
5. Go to "Time" in the right-most border/column and use the arrow keys to go through the states.

**JavaScript:** https://csci1710.github.io/forge-documentation/sterling/custom-basics.html

1. In the upper border/heading, go to the right and click "</> Script>".
2. Click the "<svg> button (in the blue buttons at the top of the center column)
3. Copy in the code from gs_vis.js.
4. To return to the default page, click on "Graph". This should be located in the upper border/heading, to the right.

**CND:** https://csci1710.github.io/forge-documentation/sterling/cnd.html

```yaml
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

You can also view everything as a **table**:
1. In the upper border/heading, go to the right and click "Table".
2. To return to the default page, click on "Graph". This should be located in the upper border/heading, to the right.

### Helper functions: 

When using `run`, you can use predicates to evaluate the states provided. Instructions and examples are provided below. 

1. Click on "Evaluator". This should be towards to bottom of the right-most border/column.
2. You should see something like `> Enter an expression` in the right hand column. Here, you can run various predicates from the code. By default, a predicate will evaluate the first state.
3. You will see #t if the predicate evaluates as True and #f if the predicate evaluates as false.

```
EXAMPLES:
> wellformed_preferences
  #t
> no match
  #t
> all_matched
  #f
> eventually all_matched
  #t
> eventually {all p: Person | { p.match != none }}
  #t
> eventually noBetterMatch
  #t
```

### In the code

Forge defaults to a trace length of 4 states. To run for more states (for example, to run the Gale Shapley model for 5+ Proposers and 5+ Receivers), use something similar to the following code. Make sure to set the `max_tracelength` before the `min_tracelength` -- it causes errors when the `min_trancelength` > `max_tracelength`.

```
option max_tracelength 8
option min_tracelength 6
```

When running tests, in order to show which tests broke only after running all the tests, use `option test_keep last`. 



