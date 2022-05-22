import data.real.basic
import tactic

namespace vilnius

local notation `|` x `|` := abs x


/-- `l` is the limit of the sequence `a` of reals -/
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε


/-- The limit of a constant sequence is the constant. -/
theorem is_limit_const (c : ℝ) : is_limit (λ n, c) c :=
begin
  intros ε hε,
  use 0,
  intros n hn,
  simp only,
  simp,
  -- rw sub_self,
  -- rw abs_zero,
  exact hε,  
end

-- We will chose ε later...
theorem is_limit_add {a b : ℕ → ℝ} {l m : ℝ}
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
begin
  intros ε hε,
  obtain ⟨N, hN⟩ := h1 (ε / 2) (half_pos hε),
  obtain ⟨M, hM⟩ := h2 (ε / 2) (half_pos hε),
  use max N M,
  intros n hn,
  specialize hN n ((le_max_left N M).trans hn),
  specialize hM n ((le_max_right N M).trans hn),
  simp,
  -- rw pi.add_apply,-- **ATTENZIONE**
  rw add_sub_add_comm,
  calc |a n - l + (b n - m)| ≤ |a n - l | + |b n - m| : abs_add _ _
                         ... < (ε / 2) + (ε / 2) : add_lt_add hN hM
                        ... = ε : add_halves ε,
end


-- Helpful things:
-- `abs_pos : 0 < |a| ↔ a ≠ 0`
-- `div_pos : 0 < a → 0 < b → 0 < a / b`
-- `abs_mul x y : |x * y| = |x| * |y|`
-- `lt_div_iff' : 0 < c → (a < b / c ↔ c * a < b)`
-- I typically find these things myself with a combination of
-- the "guess the name of the lemma" game (and ctrl-space).

-- A hint for starting:
-- It might be worth dealing with `c = 0` as a special case. You
-- can start with 
-- `by_cases hc : c = 0`

theorem is_limit_mul_const_left {a : ℕ → ℝ} {l c : ℝ} (h : is_limit a l) :
  is_limit (λ n, c * (a n)) (c * l) :=
begin
  by_cases hc : c = 0,
  { rw hc,
    rw [zero_mul],
    simp only [zero_mul],
    apply is_limit_const },
  { intros ε hε,
    obtain ⟨N, hN⟩ := h (ε / | c |) (div_pos hε (abs_pos.mpr hc)),
    use N,
    simp only,
    intros n hn,
    rw ← mul_sub,
    rw abs_mul,
    exact (lt_div_iff' (abs_pos.mpr hc)).mp (hN n hn) },
end


theorem sandwich (a b c : ℕ → ℝ)
  (l : ℝ) (ha : is_limit a l) (hc : is_limit c l) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l :=
begin
  intros ε hε,
  obtain ⟨N, hN⟩ := ha ε hε,
  obtain ⟨M, hM⟩ := hc ε hε,
  use max N M,
  intros n hn,
  specialize hN n ((le_max_left _ _).trans hn),
  specialize hM n ((le_max_right _ _).trans hn),
  rw abs_sub_lt_iff at hN hM ⊢,
  exact and.intro (lt_of_le_of_lt (sub_le_sub_right (hbc n) l) hM.1)
    (lt_of_le_of_lt (sub_le_sub_left (hab n) l) hN.2),
end


end vilnius