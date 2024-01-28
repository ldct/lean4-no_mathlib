variable (P Q R : Prop)

-- Examples of the `intro`, `exact`, `apply` tactics

example (hP : P) (hQ : Q) (hR : R) : P :=
by
  exact hP

example (hQ : Q) : P → Q :=
by
  intro _
  exact hQ

example (h : P → Q) (hP : P) : Q :=
by
  apply h
  exact hP

-- Homework; everything can be solved with `intro`, `exact`, `apply`

example : P → P :=
by
  intro hP
  exact hP

example : P → Q → P :=
by
  intro hP
  intro _
  exact hP

example : P → (P → Q) → Q :=
by
  intro hPQ
  intro hPQhPQ
  apply hPQhPQ
  exact hPQ

example : (P → Q) → (Q → R) → (P → R) :=
by
  intro hPQ
  intro hQR
  intro hP
  apply hQR
  apply hPQ
  exact hP

-- If `h : P → Q → R` with goal `⊢ R` and you `apply h`, you'll get
-- two goals! Note that tactics operate on only the first goal.
example : (P → Q → R) → (P → Q) → (P → R) :=
by
  intro hPQR
  intro hPQ
  intro hP
  apply hPQR
  exact hP
  apply hPQ
  exact hP


variable (S T : Prop)

example : (P → R) → (S → Q) → (R → T) → (Q → R) → S → T :=
by
  intro _
  intro hSQ
  intro hRT
  intro hQR
  intro hS
  apply hRT
  apply hQR
  apply hSQ
  exact hS


example : (P → Q) → ((P → Q) → P) → Q :=
by
  intro hPQ
  intro hPQP
  apply hPQ
  apply hPQP
  exact hPQ


example : ((P → Q) → R) → ((Q → R) → P) → ((R → P) → Q) → P :=
by
  intro hPQR
  intro hQRP
  intro _
  apply hQRP
  intro Q
  apply hPQR
  intro _
  exact Q


example : ((Q → P) → P) → (Q → R) → (R → P) → P :=
by
  intro hQPP
  intro hQR
  intro RP
  apply hQPP
  intro hQ
  apply RP
  apply hQR
  exact hQ


example : (((P → Q) → Q) → Q) → (P → Q) :=
by
  intro hPQQQ
  intro hP
  apply hPQQQ
  intro hPQ
  apply hPQ
  exact hP

example :
  (((P → Q → Q) → ((P → Q) → Q)) → R) →
  ((((P → P) → Q) → (P → P → Q)) → R) →
  (((P → P → Q) → ((P → P) → Q)) → R) → R :=
by
  intro _
  intro h2
  intro _
  apply h2
  intro h4
  intro hP
  intro _
  apply h4
  intro _
  exact hP
