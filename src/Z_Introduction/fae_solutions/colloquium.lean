import analysis.normed_space.hahn_banach
import data.real.basic
import analysis.normed_space.extend
import tactic
import topology.basic

open function metric filter is_R_or_C
open_locale classical topological_space big_operators nnreal
namespace vilnius

variables {π : Type} [is_R_or_C π]
variables {V : Type*} [normed_group V] [normed_space π V] 

-- ## Example 1

/- 
The Hahn-Banach theorem about extending linear functionals to a field `π = β` or `π = β`: -/

theorem Hahn_Banach [complete_space V] (p : subspace π V)
(f : p βL[π] π) : β g : V βL[π] π, (β x : p, g x = f x) β§ β₯gβ₯ = β₯fβ₯ :=
begin
  letI : module β V := restrict_scalars.module β π V,
  letI : is_scalar_tower β π V := restrict_scalars.is_scalar_tower _ _ _,
  letI : normed_space β V := normed_space.restrict_scalars _ π _,
  -- Let `fr: p βL[β] β` be the real part of `f`.
  let fr := re_clm.comp (f.restrict_scalars β),
  have fr_apply : β x, fr x = re (f x), by { assume x, refl },
  -- Use the real version to get a norm-preserving extension of `fr`, which
  -- we'll call `g : V βL[β] β`.
  rcases real.exists_extension_norm_eq (p.restrict_scalars β) fr with β¨g, β¨hextends, hnormeqβ©β©,
  -- **Now `g` can be extended to the `V βL[π] π` we need.**
  refine β¨g.extend_to_π, _β©,
  -- It is an extension of `f`.
  have h : β x : p, g.extend_to_π x = f x,
  { assume x,
    rw [continuous_linear_map.extend_to_π_apply, βsubmodule.coe_smul, hextends, hextends],
    have : (fr x : π) - I * β(fr (I β’ x)) = (re (f x) : π) - (I : π) * (re (f ((I : π) β’ x))),
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
  refine β¨h, le_antisymm _ _β©,
  { calc β₯g.extend_to_πβ₯
        β€ β₯gβ₯ : g.extend_to_π.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = β₯frβ₯ : hnormeq
    ... β€ β₯re_clmβ₯ * β₯fβ₯ : continuous_linear_map.op_norm_comp_le _ _
    ... = β₯fβ₯ : by rw [re_clm_norm, one_mul] },
  -- We're **almost** there...
  { exact f.op_norm_le_bound g.extend_to_π.op_norm_nonneg (Ξ» x, h x βΈ g.extend_to_π.le_op_norm x) },
end

-- #lint

/-- ## Example 2

We are going to show the trivial result asserting that the sum of two odd numbers is even: first, the definitions:-/

definition even (n : β) := β (k : β), n = 2 * k
definition odd (n : β) := β (k : β), n = 2 * k + 1

/--Then, some results that are already in the library:
* theorem `add_add_add_comm` (a b c d : G) : (a + b) + (c + d) = (a + c) + (b + d)
* theorem `one_add_one_eq_two` : 1 + 1 = 2
* theorem `mul_add` (a b c : G) : a * (b + c) = a * b + a * c
* theorem `mul_add_one` (a b : G) : a * (b + 1) = a * b + a

-/

example (n m : β) (hyp_n : odd n) (hyp_m : odd m) : even (n + m) :=
begin
  obtain β¨k, relation_k_nβ© := hyp_n,
  obtain β¨β, relation_β_mβ© := hyp_m,
  rw relation_k_n,
  rw relation_β_m,
  rw add_add_add_comm,
  rw one_add_one_eq_two,
  rw β mul_add,
  rw β mul_add_one,
  use (k + β + 1),
end










-- **Example 3** --

/-- To play with some topology, observe that the library contains the following
* `definition` continuous_def {f : Ξ± β Ξ²} : continuous f β
  (βs, is_open s β is_open (f β»ΒΉ' s))

from which we deduce (= the system automatically constructs) the 
***Modus Ponens*** variant
* `lemma` continuous_def.mp {f : Ξ± β Ξ²} : continuous f β
  (βs, is_open s β is_open (f β»ΒΉ' s))
-/

variables {X Y Z : Type}

example [topological_space X] [topological_space Y] [topological_space Z]
(f : X β Y) (g : Y β Z) (hyp_f : continuous f) (hyp_g : continuous g) :
continuous (g β f : X β Z) :=
begin
  -- continuity,
  -- exact continuous.comp hyp_g hyp_f,
  rewrite continuous_def,
  intros W hW,
  let V := gβ»ΒΉ' W,
  have hV : is_open V,
  exact continuous_def.mp hyp_g W hW,
  let U := fβ»ΒΉ' V,
  have hU : is_open U,
  exact continuous_def.mp hyp_f V hV,
  exact hU,
end









end vilnius