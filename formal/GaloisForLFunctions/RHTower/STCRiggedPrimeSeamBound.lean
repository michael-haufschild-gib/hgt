import GaloisForLFunctions.RHTower.DiagonalEllTwoOperator

/-!
# Bounded prime-seam extractor in rigged squarefree coordinates

The unnormalised critical squarefree source lives in the coefficient completion
with weight `n^(-a)` for every `a > 0`.  In its isometric `ℓ²` coordinates,
the canonical reflected-prime-seam extractor has multiplier
`-log(p) * p^a * (p^(-beta) - p^(beta-1))` on prime coordinates.

This leaf proves, without a spectral or RH premise, that the multiplier defines
a bounded operator whenever `a < min beta (1-beta)`.  It is the bounded side
of the sharp rigged-transport classification in the accompanying paper card;
the source limit, exact landing, and failure at the threshold remain to formalise.
-/

open Complex Filter Topology
namespace RHTower
noncomputable section

private theorem stc_log_power_bound {x delta : ℝ} (hx : 1 ≤ x) (hd : 0 < delta) :
    Real.log x * x ^ (-delta) ≤ 1 / delta := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog := Real.log_le_rpow_div hx0.le hd
  have hpow : 0 < x ^ delta := Real.rpow_pos_of_pos hx0 _
  have hmul := mul_le_mul_of_nonneg_right hlog (le_of_lt (Real.rpow_pos_of_pos hx0 (-delta)))
  rw [div_mul_eq_mul_div, ← Real.rpow_add hx0] at hmul
  have hsum : delta + -delta = 0 := by ring
  rw [hsum, Real.rpow_zero, one_div] at hmul
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmul

private theorem stc_reflection_power_bound {x beta : ℝ}
    (hx : 1 ≤ x) :
    |x ^ (-beta) - x ^ (beta - 1)| ≤
      2 * x ^ (-min beta (1 - beta)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hpow1 : 0 ≤ x ^ (-beta) := le_of_lt (Real.rpow_pos_of_pos hx0 _)
  have hpow2 : 0 ≤ x ^ (beta - 1) := le_of_lt (Real.rpow_pos_of_pos hx0 _)
  have hmin1 : -beta ≤ -min beta (1 - beta) := neg_le_neg (min_le_left _ _)
  have hmin2 : beta - 1 ≤ -min beta (1 - beta) := by
    have h := min_le_right beta (1 - beta)
    linarith
  have h1 : x ^ (-beta) ≤ x ^ (-min beta (1 - beta)) :=
    Real.rpow_le_rpow_of_exponent_le hx hmin1
  have h2 : x ^ (beta - 1) ≤ x ^ (-min beta (1 - beta)) :=
    Real.rpow_le_rpow_of_exponent_le hx hmin2
  calc
    |x ^ (-beta) - x ^ (beta - 1)| ≤ |x ^ (-beta)| + |x ^ (beta - 1)| := abs_sub _ _ |>.trans (by rfl)
    _ = x ^ (-beta) + x ^ (beta - 1) := by rw [abs_of_nonneg hpow1, abs_of_nonneg hpow2]
    _ ≤ 2 * x ^ (-min beta (1 - beta)) := by linarith

private theorem stc_rigged_multiplier_bound {x a beta : ℝ}
    (hx : 1 ≤ x) (_hb0 : 0 < beta) (_hb1 : beta < 1)
    (ha : a < min beta (1 - beta)) :
    Real.log x * x ^ a * |x ^ (-beta) - x ^ (beta - 1)| ≤
      2 / (min beta (1 - beta) - a) := by
  let k := min beta (1 - beta)
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpow0 : 0 ≤ x ^ a := le_of_lt (Real.rpow_pos_of_pos hx0 _)
  have hbound := stc_reflection_power_bound (beta := beta) hx
  have hstep : Real.log x * x ^ a * |x ^ (-beta) - x ^ (beta - 1)| ≤
      Real.log x * x ^ a * (2 * x ^ (-k)) := by
    exact mul_le_mul_of_nonneg_left hbound (mul_nonneg hlog0 hpow0)
  have hrew : Real.log x * x ^ a * (2 * x ^ (-k)) =
      2 * (Real.log x * x ^ (-(k-a))) := by
    calc
      Real.log x * x ^ a * (2 * x ^ (-k)) =
          2 * (Real.log x * (x ^ a * x ^ (-k))) := by ring
      _ = 2 * (Real.log x * x ^ (a + -k)) := by rw [Real.rpow_add hx0]
      _ = 2 * (Real.log x * x ^ (-(k-a))) := by
        have he : a + -k = -(k-a) := by ring
        rw [he]
  rw [hrew] at hstep
  have hd : 0 < k - a := sub_pos.mpr ha
  have hmain := stc_log_power_bound hx hd
  calc
    _ ≤ 2 * (Real.log x * x ^ (-(k-a))) := hstep
    _ ≤ 2 * (1 / (k-a)) := mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 2 / (min beta (1-beta) - a) := by dsimp [k]; ring

/-- Prime-coordinate critical extractor in the isometric `H₋ₐ ≃ ℓ²` coordinates. -/
def stcRiggedPrimeMultiplier (a beta : ℝ) (n : ℕ) : ℂ :=
  if n.Prime then
    ((-(Real.log n * (n : ℝ) ^ a *
      ((n : ℝ) ^ (-beta) - (n : ℝ) ^ (beta - 1))) : ℝ) : ℂ)
  else 0

theorem norm_stcRiggedPrimeMultiplier_le
    {a beta : ℝ} (hb0 : 0 < beta) (hb1 : beta < 1)
    (ha : a < min beta (1 - beta)) (n : ℕ) :
    ‖stcRiggedPrimeMultiplier a beta n‖ ≤
      2 / (min beta (1 - beta) - a) := by
  by_cases hn : n.Prime
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.one_le
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have hpow : 0 ≤ (n : ℝ) ^ a := by positivity
    have h := stc_rigged_multiplier_bound hn1 hb0 hb1 ha
    unfold stcRiggedPrimeMultiplier
    rw [if_pos hn, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul,
      abs_of_nonneg hlog, abs_of_nonneg hpow]
    exact h
  · have hden : 0 ≤ 2 / (min beta (1 - beta) - a) :=
      div_nonneg (by norm_num) (sub_nonneg.mpr ha.le)
    simpa [stcRiggedPrimeMultiplier, hn] using hden

def stcRiggedPrimeOperator {a beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (ha : a < min beta (1 - beta)) : EllTwo →L[ℂ] EllTwo :=
  diagonalOperator (stcRiggedPrimeMultiplier a beta)
    (norm_stcRiggedPrimeMultiplier_le hb0 hb1 ha)

theorem norm_stcRiggedPrimeOperator_le {a beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (ha : a < min beta (1 - beta)) :
    ‖stcRiggedPrimeOperator hb0 hb1 ha‖ ≤
      2 / (min beta (1 - beta) - a) :=
  norm_diagonalOperator_le _ (norm_stcRiggedPrimeMultiplier_le hb0 hb1 ha)

theorem stcRiggedPrimeOperator_apply_prime {a beta : ℝ}
    (hb0 : 0 < beta) (hb1 : beta < 1)
    (ha : a < min beta (1 - beta)) (f : EllTwo)
    {p : ℕ} (hp : p.Prime) :
    (stcRiggedPrimeOperator hb0 hb1 ha f) p =
      (((-(Real.log p * (p : ℝ) ^ a *
          ((p : ℝ) ^ (-beta) - (p : ℝ) ^ (beta - 1))) : ℝ) : ℂ)) * f p := by
  simp [stcRiggedPrimeOperator, stcRiggedPrimeMultiplier, hp]

end
end RHTower
