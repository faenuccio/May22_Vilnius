import analysis.normed_space.hahn_banach
import data.real.basic
import analysis.normed_space.extend
import tactic
import topology.basic

open function metric filter is_R_or_C
open_locale classical topological_space big_operators nnreal
namespace vilnius

variables {𝕜 : Type} [is_R_or_C 𝕜]
variables {V : Type*} [normed_group V] [normed_space 𝕜 V] 

-- ## Example 1

/- 
The Hahn-Banach theorem about extending linear functionals to a field `𝕜 = ℝ` or `𝕜 = ℂ`: -/

theorem Hahn_Banach [complete_space V] (p : subspace 𝕜 V)
(f : p →L[𝕜] 𝕜) : ∃ g : V →L[𝕜] 𝕜, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  letI : module ℝ V := restrict_scalars.module ℝ 𝕜 V,
  letI : is_scalar_tower ℝ 𝕜 V := restrict_scalars.is_scalar_tower _ _ _,
  letI : normed_space ℝ V := normed_space.restrict_scalars _ 𝕜 _,
  -- Let `fr: p →L[ℝ] ℝ` be the real part of `f`.
  let fr := re_clm.comp (f.restrict_scalars ℝ),
  have fr_apply : ∀ x, fr x = re (f x), by { assume x, refl },
  -- Use the real version to get a norm-preserving extension of `fr`, which
  -- we'll call `g : V →L[ℝ] ℝ`.
  rcases real.exists_extension_norm_eq (p.restrict_scalars ℝ) fr with ⟨g, ⟨hextends, hnormeq⟩⟩,
  -- **Now `g` can be extended to the `V →L[𝕜] 𝕜` we need.**
  refine ⟨g.extend_to_𝕜, _⟩,
  -- It is an extension of `f`.
  have h : ∀ x : p, g.extend_to_𝕜 x = f x,
  { assume x,
    rw [continuous_linear_map.extend_to_𝕜_apply, ←submodule.coe_smul, hextends, hextends],
    have : (fr x : 𝕜) - I * ↑(fr (I • x)) = (re (f x) : 𝕜) - (I : 𝕜) * (re (f ((I : 𝕜) • x))),
      by refl,
    rw this,
    apply ext,
    { simp only [add_zero, algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add,
        zero_sub, I_im', zero_mul, of_real_re, eq_self_iff_true, sub_zero, of_real_neg, mul_re,
          mul_zero, sub_neg_eq_add, continuous_linear_map.map_smul, mul_neg, sub_neg_eq_add,
          map_add, of_real_re, I_mul_re, of_real_im, neg_zero', add_zero] },
    { simp only [algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add, zero_sub, I_im',
        zero_mul, of_real_re, mul_im, zero_add, of_real_neg, mul_re,
        sub_neg_eq_add, continuous_linear_map.map_smul, mul_neg, sub_neg_eq_add, map_add, 
        of_real_im, mul_im, mul_zero, of_real_re, I_im', zero_add] } },
  -- And we derive the equality of the norms by bounding on both sides.
  refine ⟨h, le_antisymm _ _⟩,
  { calc ∥g.extend_to_𝕜∥
        ≤ ∥g∥ : g.extend_to_𝕜.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = ∥fr∥ : hnormeq
    ... ≤ ∥re_clm∥ * ∥f∥ : continuous_linear_map.op_norm_comp_le _ _
    ... = ∥f∥ : by rw [re_clm_norm, one_mul] },
  -- We're **almost** there...
  { exact f.op_norm_le_bound g.extend_to_𝕜.op_norm_nonneg (λ x, h x ▸ g.extend_to_𝕜.le_op_norm x) },
end

-- #lint

/-- ## Example 2

We are going to show the trivial result asserting that the sum of two odd numbers is even: first, the definitions:-/

definition even (n : ℕ) := ∃ (k : ℕ), n = 2 * k
definition odd (n : ℕ) := ∃ (k : ℕ), n = 2 * k + 1

/--Then, some results that are already in the library:
* theorem `add_add_add_comm` (a b c d : G) : (a + b) + (c + d) = (a + c) + (b + d)
* theorem `one_add_one_eq_two` : 1 + 1 = 2
* theorem `mul_add` (a b c : G) : a * (b + c) = a * b + a * c
* theorem `mul_add_one` (a b : G) : a * (b + 1) = a * b + a

-/

example (n m : ℕ) (hyp_n : odd n) (hyp_m : odd m) : even (n + m) :=
begin
  sorry,
end










-- **Example 3** --

/-- To play with some topology, observe that the library contains the following
* `definition` continuous_def {f : α → β} : continuous f ↔
  (∀s, is_open s → is_open (f ⁻¹' s))

from which we deduce (= the system automatically constructs) the 
***Modus Ponens*** variant
* `lemma` continuous_def.mp {f : α → β} : continuous f →
  (∀s, is_open s → is_open (f ⁻¹' s))
-/

variables {X Y Z : Type}

example [topological_space X] [topological_space Y] [topological_space Z]
(f : X → Y) (g : Y → Z) (hyp_f : continuous f) (hyp_g : continuous g) :
continuous (g ∘ f : X → Z) :=
begin
  sorry,
end









end vilnius