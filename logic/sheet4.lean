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
begin
  sorry
end

example : P → P ∧ true :=
begin
  sorry
end

example : false → P ∧ false :=
begin
  sorry
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  sorry,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  sorry,
end
