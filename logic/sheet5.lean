/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

### The `refl` tactic

If your goal is `P ↔ P` then `refl,` will solve it.

### The `rw` tactic

If `h : P ↔ Q` is a hypothesis, you can decompose it
using `cases h with hPQ hQP,`. However, if you keep
it around then you can do `rw h,` which changes all `P`s in the goal to `Q`s.
Variant: `rw h at h2,` will change all `P`s to `Q`s in hypothesis `h2`.

-/

variable (P Q R S : Prop)

-- refl doesn't work in this config?
example : P ↔ P :=
by
  apply Iff.intro; repeat intro hP; exact hP;

example : (P ↔ Q) → (Q ↔ P) :=
by
  intro hPQ;
  rw [hPQ];
  apply Iff.intro; repeat intro hP; exact hP;

example : (P ↔ Q) ↔ (Q ↔ P) :=
by
  apply Iff.intro;
  intro hPQ;
  rw [hPQ]; apply Iff.intro; repeat intro hP; exact hP;
  intro hQP;
  rw [hQP]; apply Iff.intro; repeat intro hP; exact hP;

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
by
  intro hPQ;
  intro hQR;
  apply Iff.intro;
  rw [hPQ]; rw [hQR]; intro h; exact h;
  intro hR;
  rw [hPQ]; rw [hQR]; exact hR;

example : P ∧ Q ↔ Q ∧ P :=
by
  apply Iff.intro;
  intro hPQ;
  apply And.intro;
  cases hPQ with
  | intro hp hq => exact hq;
  -- repeat
  cases hPQ with
  | intro hp hq => exact hp;
  intro hPQ;
  apply And.intro;
  cases hPQ with
  | intro hp hq => exact hq;
  cases hPQ with
  | intro hp hq => exact hp;

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
by
  apply Iff.intro;
  intro h;
  apply And.intro;
  cases h with
  | intro h1 h2 => cases h1 with | intro h3 h4 => exact h3;
  apply And.intro;
  cases h with
  | intro h1 h2 => cases h1 with | intro h3 h4 => exact h4;
  cases h with
  | intro h1 h2 => exact h2;
  -- repeat
  intro h;
  apply And.intro;
  apply And.intro;
  cases h with
  | intro h1 h2 => exact h1;
  cases h with
  | intro h1 h2 => cases h2 with | intro h3 h4 => exact h3;
  cases h with
  | intro h1 h2 => cases h2 with | intro h3 h4 => exact h4;

example : P ↔ (P ∧ True) :=
by
  apply Iff.intro;
  intro hP;
  apply And.intro;
  exact hP;
  trivial;
  intro h;
  cases h with | intro hP _ => exact hP;

example : False ↔ (P ∧ False) :=
by
  apply Iff.intro;
  intro hF;
  apply False.elim;
  exact hF;
  intro h;
  cases h with | intro _ hF => exact hF;

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by sorry;

example : ¬ (P ↔ ¬ P) := by sorry;
