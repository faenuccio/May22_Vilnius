import data.real.basic
import tactic
open function real

namespace vilnius


/-- Composite of two injective functions is injective -/
theorem injective_comp (X Y Z : Type) (f : X → Y) (g : Y → Z) 
  (hf : injective f) (hg : injective g) : injective (g ∘ f) :=
begin
  intros x y H,
  apply hf,
  apply hg,
  exact H,
end

/- ## The λ notation:
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

theorem injective_id (X : Type) : injective (λ x : X, x) :=
begin
  intros x y h,
  simp only at h,
  exact h,
end


definition is_linear (f : ℝ → ℝ) : Prop := ∀ c x y, f (c * x + y) = c * f (x) + f(y) 

theorem linear_at_0 (f : ℝ → ℝ) (H : is_linear f) : f 0 = 0 :=
begin
  have hf := H 1 0 0,
  rewrite one_mul at hf,
  rewrite one_mul at hf,
  rewrite add_zero at hf,
  apply self_eq_add_left.mp hf,
end

theorem linear_explicit (f : ℝ → ℝ) (H : is_linear f) : ∃ a, f = λ x, a * x :=
begin
  use f 1,
  ext, --***ATTENZIONE***
  rw ← mul_one x,
  have := H x 1 0,
  rw linear_at_0 f H at this,
  rw add_zero at this,
  rw add_zero at this,
  rw this,
  rw mul_comm,
  rw mul_one,  
end

definition is_affine (f : ℝ → ℝ) : Prop := ∃ a, ∀ x y, f (y) - f(x) = a * (y - x)

theorem linear_add_cnst_of_affine (f : ℝ → ℝ) : is_affine f → (∃ a : ℝ, ∃ g : ℝ → ℝ, (f = g + (λ x, a)) ∧ is_linear g) :=
begin
  intro hf,
  obtain ⟨a, h_aff⟩ := hf,
  use f 0,
  let g := f - (λ n, f 0),
  use g,
  split,
  simp only [sub_add_cancel], --***ATTENZIONE***
  intros c x y,
  simp [g],
  -- simp only [pi.sub_apply], --***ATTENZIONE***
  have h1 := h_aff 0 (c*x + y),
  rw h_aff,
  have h2 := h_aff 0 y,
  have h3 := h_aff 0 x,
  rw h2,
  rw h3,
  ring, --***ATTENZIONE***
end

theorem affine_of_linear_add_cnst (f : ℝ → ℝ) : (∃ b : ℝ, ∃ g : ℝ → ℝ,
  (f = g + (λ x, b)) ∧ is_linear g) → is_affine f :=
begin
  intro H,
  obtain ⟨b, g, hf1, hg1⟩ := H, --***ATTENZIONE ALLA SINTASSI TRIPLA***
  simp [is_affine],
  obtain ⟨a, hg2⟩ := linear_explicit g hg1,
  use a,
  intros x y,
  rw hf1,
  simp only [add_sub_add_right_eq_sub, pi.add_apply], --***SERVE DAVVERO SIMP***
  rw hg2,
  simp only,
  rw mul_sub,
end

end vilnius
