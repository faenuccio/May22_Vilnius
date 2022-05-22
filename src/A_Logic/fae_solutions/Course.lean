import tactic

namespace vilnius

/- ### Introduction
The orange stuff on the right are **assumptions** or **hypothesis**; the stuff at the end before
the blue `⊢` sign is the **goal**. A **tactic** is some move that makes the goal change, hopefully
towards an easier one.


 ## intro(s), exact, apply
The main tools here are the tactics
* `intro`, that introduces a *generic* object (and `intros` introducting several ones at once)
* `exact`, telling Lean that the goal is already a hypothesis;
* `apply`, which transforms a goal P into a goal Q when applying a hypothesis `H : Q → P`.
-/

-- **The implication → :**


theorem self_implication (P : Prop) : P → P :=
begin
  intro h,
  exact h,
end

theorem forall_imp (P Q R : Prop) : (P → Q → R) → (P → Q) → (P → R) :=
begin
  intro h1,
  intro h2,
  intro hP,
  apply h1,-- ***why two things? explain...***--
  exact hP,
  apply h2,
  exact hP,
end

theorem modus_ponens (P Q : Prop) : P → (P → Q) → Q :=
begin
  intro hP,
  intro h1,
  apply h1,
  exact hP,
end

/- **not ¬**
`not P`, with notation `¬ P`, is *defined* to mean `P → false`, so the fact that P implies false.
You can easily check with a truth table that P → false and ¬ P are equivalent. -/


theorem modus_tollens (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) :=
begin
  intros h1 hnQ hP,-- ***remember: `¬ P` is equivalent to `P → false`***
  apply hnQ,
  apply h1,
  exact hP,
end


/- ## by_contradiction
For the following, we need to argue _by contradiction_, which can be done by the tactic 
* `by_contradiction`: it introduces the _negation_ of the goal and transforms the goal into `false`.
-/
theorem double_negation_elimination (P : Prop) : ¬ (¬ P) → P :=
begin
  intro hnnP,
  by_contradiction,
  apply hnnP,
  exact h,
end

/- **∧**
Given two propositions P and Q, P ∧ Q is the proposition that is true precisely if both P and Q are
true. Hence, in order to prove something like this, you can use 

## split
* the tactic `split` splits the goal into two sub-goals.
-/

theorem trivial (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
  exact hP,
  exact hQ,
end



/-- ## cases 
 If you want to _use_ an assumption of the form P ∧ Q, you can use 
* the tactic `cases`: it destructures the **assumption** into two sub-assumptions, one being P and
  the other being Q: it is the first tactic seen so far that does not act on the goal but on something
  in orange -/

theorem and.elim_left (P Q : Prop) : P ∧ Q → P :=
begin
  intro h,
  cases h,
  exact h_left,
end


/- **∨**
Similarly, given propositions P and Q, the proposition P ∨ Q is true whenever at least one of P or 
Q is true. Here, the tactic `cases` produces two sub-goals, one assuming that P is true, the other
assuming that Q is true

**Hint** When P and ¬ P are both hypothesis, something is weird: the proposition to prove is
false, so we can try to argue `by_contradiction`.-/

theorem or_not_left (P Q : Prop) : P ∨ Q → ¬ P → Q :=
begin
  intros h1 h2,
  cases h1,
  { by_contradiction,
    apply h2,
    exact h1 },
  { exact h1 },
end

end vilnius

