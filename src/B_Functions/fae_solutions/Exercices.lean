import data.real.basic
import tactic

open function real

namespace vilnius


example (X Y Z : Type) (f : X → Y) (g : Y → Z) 
  (hf : surjective f) (hg : surjective g) : surjective (g ∘ f) :=
begin
  intro b,
  obtain ⟨c, hc⟩ := hg b,
  obtain ⟨a, ha⟩ := hf c,
  use a,
  rw ← hc,
  rw ← ha,
end

/- ### The λ notation:
In Lean (or in Type Theory, rather) the way to define a function is to use λ expressions: here, you should think that `λ = ∀`: so, the function
`λ x, 3*x ^ 2 + 1`
is nothing else that the function
`f(x)=3*x ^ 2 + 1` or `f : x ↦ 3*x ^ 2 + 1`.

As for usual functions, the name of the variable does not matter, so
`λ x, 3*x ^ 2 + 1` is the same as `λ w, 3*w ^ 2 + 1` 

The tactic to get rid of a `λ` term is
* `simp only` (possibly: at h)
because it "evaluates a λ-term", transforming, for instance
`(λ x, 2 * x + 1) 3` into `2 * 3 + 1`.
-/


definition A : ℕ → ℕ := λ n, n + 1 

example : injective A :=
begin
  intros a b h,
  rw A at h,
  simp only at h,
  rw ← nat.succ_eq_add_one at h,
  rw ← nat.succ_eq_add_one at h,
  rw nat.succ.inj_eq at h,
  exact h,
end

example : ¬ surjective A := --λ h, nat.add_one_ne_zero (h 0).some (h 0).some_spec
begin
  intro h,
  have := (h 0).some,
  obtain ⟨a, ha⟩ := h 0,
  exact nat.add_one_ne_zero a ha,
end

-- Recall the-
definition is_linear (f : ℝ → ℝ) : Prop := ∀ c x y, f (c * x + y) = c * f (x) + f(y) 
--as well as
theorem linear_at_0 (f : ℝ → ℝ) (H : is_linear f) : f 0 = 0 := sorry

-- And now a new
definition is_linear' (f : ℝ → ℝ) : Prop :=
(∀ x y, f ( x + y) = f (x) + f (y)) ∧ (∀ c x, f (c * x) = c * f (x))

example (f : ℝ → ℝ) : is_linear f ↔ is_linear' f :=
begin
  split,
  { intro hf,
    split,
    intros x y,
    have h_1 := hf 1 x y,
    rw one_mul at h_1,
    rw one_mul at h_1,
    exact h_1,
    intros a x,
    have h_2 := hf a x 0,
    rw add_zero at h_2,--oh, here we need that f (0) = 0 if f is linear'!f_
    have f_zero : f ( 0 ) = 0,
    { specialize hf 1 0 0,
      rw one_mul at hf,
      rw one_mul at hf,
      rw add_zero at hf,
      apply self_eq_add_left.mp hf },
    rw f_zero at h_2,
    rw add_zero at h_2,
    exact h_2,
  },
  { intro hf,
    intros a x y,
    have h_1 := hf.1 (a * x) y,
    rw h_1,
    have h_2 := hf.2 a x,
    rw h_2, },
end

--Recall the
definition is_affine (f : ℝ → ℝ) : Prop := ∃ a, ∀ x y, f (y) - f(x) = a * (y - x)

-- together with the
theorem linear_add_cnst_of_affine (f : ℝ → ℝ) : is_affine f → (∃ a : ℝ, ∃ g : ℝ → ℝ,
  (f = g + (λ x, a)) ∧ is_linear g) := sorry
-- as well as
theorem affine_of_linear_add_cnst (f : ℝ → ℝ) : (∃ b : ℝ, ∃ g : ℝ → ℝ,
  (f = g + (λ x, b)) ∧ is_linear g) → is_affine f := sorry

-- that we proved in the lesson.


example (f : ℝ → ℝ) : is_affine f ↔ ∃ a : ℝ, ∃ g : ℝ → ℝ, (f = g + (λ x, a)) ∧ is_linear g := -- iff.intro (linear_add_cnst_of_affine _) (affine_of_linear_add_cnst _)
begin
  have h1 := linear_add_cnst_of_affine f,
  have h2 := affine_of_linear_add_cnst f,
  split,
  intro H,
  apply h1 H,
  intro H,
  apply h2 H,
end

end vilnius
