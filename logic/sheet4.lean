/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

### The `cases` tactic

If `h : P ∧ Q` is a hypothesis, then `cases h with hP hQ,`
decomposes it into two hypotheses `hP : P` and `hQ : Q`.

### The `split` tactic

If `⊢ P ∧ Q` is in the goal, The `split` tactic will turn it into
two goals, `⊢ P` and `⊢ Q`. NB tactics operate on the first goal only.

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variable (P Q R : Prop)

example : P ∧ Q → P :=
by
  intro hPQ;
  cases hPQ with
  | intro hp _ => {
    exact hp;
  }

example : P ∧ Q → Q :=
by
  intro hPQ;
  cases hPQ with
  | intro _ hq => {
    exact hq;
  }

example : (P → Q → R) → (P ∧ Q → R) :=
by
  intro hPQR;
  intro hPQ;
  apply hPQR;
  cases hPQ with
  | intro hp hq => exact hp;
  cases hPQ with
  | intro hp hq => exact hq;

example : P → Q → P ∧ Q :=
by
  intro hP;
  intro hQ;
  apply And.intro
  exact hP;
  exact hQ;

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
by
  intro hPQ;
  apply And.intro;
  cases hPQ with
  | intro hp hq => exact hq;
  cases hPQ with
  | intro hp hq => exact hp;


example : P → P ∧ True :=
by
  intro hP;
  apply And.intro;
  exact hP;
  trivial;

example : False → P ∧ False :=
by
  intro hF;
  apply False.elim;
  exact hF;

example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
by
  intro hPQ;
  intro hQR;
  apply And.intro;
  cases hPQ with
  | intro hp hq => exact hp;
  cases hQR with
  | intro hq hr => exact hr;


example : ((P ∧ Q) → R) → (P → Q → R) :=
by
  intro h1;
  intro hP;
  intro hQ;
  apply h1;
  apply And.intro;
  exact hP;
  exact hQ;
