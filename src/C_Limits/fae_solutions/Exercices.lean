import data.real.basic
import tactic
-- import C_Limits.fae_solutions.Course
-- open vilnius

namespace vilnius

local notation `|` x `|` := abs x


-- Recall the
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε


example {a : ℕ → ℝ} {l : ℝ} (c : ℝ) (ha : is_limit a l) :
  is_limit (λ i, a i + c) (l + c) :=
begin
  intros ε hε,
  obtain ⟨N, hN⟩ := ha ε hε,
  use N,
  intros k hk,
  simp only,
  rw add_sub_add_comm,
  rw sub_self,
  rw add_zero,
  exact hN k hk,
end


example (a : ℕ → ℝ) (l : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i - l) 0 :=
begin
  split,
  all_goals { intros ha ε hε,
    obtain ⟨N, hN⟩ := ha ε hε,
    use N,
    intros n hn,
    simp only [sub_zero] at *,
    exact hN n hn},
end


/- Helpful things:
`abs_pos : 0 < |a| ↔ a ≠ 0`
`div_pos : 0 < a → 0 < b → 0 < a / b`
`abs_mul x y : |x * y| = |x| * |y|`
`lt_div_iff' : 0 < c → (a < b / c ↔ c * a < b)`
I typically find these things myself with a combination of
the "guess the name of the lemma" game (and ctrl-space).


Recall also that we have proved the-/

theorem is_limit_add {a b : ℕ → ℝ} {l m : ℝ}
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) := sorry

--as well as the 

theorem is_limit_mul_const_left {a : ℕ → ℝ} {l c : ℝ} (h : is_limit a l) :
  is_limit (λ n, c * (a n)) (c * l) := sorry

-- And now, over to you!

-- This should just be a couple of lines now.
example (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c d : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, c * (a n) + d * (b n) ) (c * α + d * β) :=
begin
  -- intros ε hε,**BAD IDEA**
  apply is_limit_add,
  apply is_limit_mul_const_left ha,
  apply is_limit_mul_const_left hb,
end

example (a : ℕ → ℝ) (b : ℕ → ℝ)
  (l : ℝ) (m : ℝ) (hl : is_limit a l) (hm : is_limit b m) 
  (hle : ∀ n, a n ≤ b n) : l ≤ m :=
begin
  set ε := l - m with def_ε,
  by_cases hε : ε ≤ 0,
  { exact le_of_sub_nonpos hε },
  { cases hl (ε / 2) (half_pos (not_le.mp hε)) with N hN,
    cases hm (ε / 2) (half_pos (not_le.mp hε)) with M hM,
    specialize hN (max N M) (le_max_left N M),
    specialize hM (max N M) (le_max_right N M),
    rw abs_sub_lt_iff at hN hM,
    replace hM := hM.1,
    replace hN := hN.2,
    rw def_ε at hM hN,
    rw [sub_lt_iff_lt_add] at hM,
    rw sub_lt at hN,
    rw sub_div at hM hN,
    have h_calc: l - (l / 2 - m /2 ) = l / 2 - m / 2 + m,
    rw ← sub_add,
    rw sub_half,
    rw sub_add,
    rw half_sub,
    rw sub_eq_add_neg,
    rw neg_neg,    
    by_contra,
    rw h_calc at hN,
    have := hM.trans hN,
    rw ← not_le at this,
    apply this,
    exact hle (max N M) },
end

end vilnius