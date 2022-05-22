import tactic

namespace vilnius


/- ### implication -/

example (P Q : Prop) : P → Q → P :=
begin
  intro hP,
  intro h,
  exact hP,
end

/- ### not -/

example (P Q : Prop) : (P → ¬ Q) → (Q → ¬ P) :=
begin
  intros h1 h2 h3,
  apply h1,
  exact h3,
  exact h2,
end


/- ### and -/

example (P Q : Prop) : P ∧ Q → Q :=
begin
  intro h,
  cases h,
  exact h_right,
end

example (P Q : Prop) : P → Q → P ∧ Q :=
begin
  intros h1 h2,
  split,
  exact h1,
  exact h2,
end


example (P Q : Prop) : P ∧ Q → Q ∧ P :=
begin
  intro h,
  split,
  cases h,
  exact h_right,
  cases h,
  exact h_left,
end


example (P : Prop) : P ∧ ¬ P → false :=
begin
  intro h,
  cases h,
  apply h_right,
  exact h_left,
end


/- ## Or -/


example (P Q : Prop) : ¬ P ∨ Q → P → Q :=
begin
  intros h1 h2,
  cases h1,
  by_contradiction,
  apply h1,
  exact h2,
  exact h1,
end


example (P Q R : Prop) : P ∨ (Q ∧ R) → ¬ P → ¬ Q → false :=
begin
  intros h1 h2 h3,
  cases h1,
  apply h2,
  exact h1,
  cases h1,
  apply h3,
  exact h1_left,
end


end vilnius

