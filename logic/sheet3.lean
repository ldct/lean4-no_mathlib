/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import Std.Tactic.Basic

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → False`
are *the same thing* and can be used interchangeably. You can change
from one to the other for free.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `change` (optional)
* `by_contra`
* `by_cases`

### The `change` tactic

Seems to not exist in lean4. Just manually translate ¬P in your head.

### The `by_contra` tactic

If your goal is `⊢ P` and you want to prove it by contradiction,
`by_contra h,` will change the goal to `False` and add a hypothesis
`h : ¬ P`.

### The `by_cases` tactic

If `P : Prop` is a True-False statement then `by_cases hP : P,`
turns your goal into two goals, one with hypothesis `hP : P`
and the other with hypothesis `hP : ¬ P`.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variable (P Q R : Prop)

example : ¬ P → (P → False) :=
by
  intro hnP;
  intro hP;
  apply hnP;
  exact hP;

example : ¬ True → False :=
by
  intro hnT;
  apply hnT;
  trivial;

example : False → ¬ True :=
by
  intro hF;
  intro _;
  exact hF;

example : ¬ False → True :=
by
  intro _;
  by_contra h;
  apply h;
  trivial;

example : True → ¬ False :=
by
  intro _;
  intro hF;
  exact hF;

example : False → ¬ P :=
by
  intro hF;
  intro _;
  exact hF;

example : P → ¬ P → False :=
by
  intro hP;
  intro hnP;
  apply hnP;
  exact hP;

example : P → ¬ (¬ P) :=
by
  intro hP;
  intro hnnP;
  apply hnnP;
  exact hP;

example : (P → Q) → (¬ Q → ¬ P) :=
by
  intro hPQ;
  intro hnQ;
  intro hP;
  apply hnQ;
  apply hPQ;
  exact hP;

example : ¬ ¬ False → False :=
by
  intro hnF;
  apply hnF;
  intro hF;
  exact hF;

example : ¬ ¬ P → P :=
by
  intro hnnP;
  by_contra h;
  apply h;
  apply False.elim; -- used to be called exfalso / ex_falso?
  apply hnnP;
  exact h;

example : (¬ Q → ¬ P) → (P → Q) :=
by
  intro hQP;
  intro hP;
  by_contra h;
  apply hQP; -- `apply (R -> S -> goal)` splits into two subgoals for R and S
  exact h;
  exact hP;
