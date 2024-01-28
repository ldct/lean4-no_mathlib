variable (P Q R : Prop)

example : True :=
by
  trivial

example : True → True :=
by
  intro _; trivial

example : False → True :=
by
  intro _; trivial

example : False → False :=
by
  intro h; exact h;

example : (True → False) → False :=
by
  intro h; apply h; trivial;

example : False → P :=
by
  intro hF; apply False.elim; exact hF;

example : True → False → True → False → True → False :=
by
  intro _; intro hF; apply False.elim; exact hF;

example : P → ((P → False) → False) :=
by
  intro hP; intro hPF; apply hPF; exact hP;

example : (P → False) → P → Q :=
by
  intro hPF; intro hP; apply False.elim; apply hPF; exact hP

example : (True → False) → P :=
by
  intro hTF; apply False.elim; apply hTF; trivial
