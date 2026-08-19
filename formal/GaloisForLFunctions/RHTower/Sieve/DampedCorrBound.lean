import GaloisForLFunctions.RHTower.Sieve.DampedEdgeSubstitution

/-!
# A uniform bound for the Euler correction on a half plane

`Sieve/DampedEulerCorrection.norm_prod_dampedEulerFactor_le` bounds the correction at a point by a
product depending on `Re s`.  Along the horizontal edges of the contour `Re s` varies, so the edge
estimates need a bound uniform on `Re s ≥ c`.  Each factor `(1+x)/(1−x)` is increasing in
`x ∈ [0,1)` and `p^{-Re s} ≤ p^{-c}`, so the value at `c` dominates the whole half plane.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The Euler correction's bound at abscissa `c`. -/
def dampedCorrBound (P : Finset ℕ) (c : ℝ) : ℝ :=
  ∏ p ∈ P, (1 + (p : ℝ) ^ (-c)) / (1 - (p : ℝ) ^ (-c))

/-- The prime power is below one on the half plane. -/
theorem rpow_neg_lt_one {p : ℕ} (hp : 2 ≤ p) {c : ℝ} (hc : 1 / 2 ≤ c) :
    (p : ℝ) ^ (-c) < 1 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)

/-- **The correction is bounded uniformly on the half plane `Re s ≥ c`.** -/
theorem norm_prod_dampedEulerFactor_le_corrBound {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {c : ℝ} (hc : 1 / 2 ≤ c) {s : ℂ} (hcs : c ≤ s.re) :
    ‖∏ p ∈ P, dampedEulerFactor t p s‖ ≤ dampedCorrBound P c := by
  have hs : 1 / 2 ≤ s.re := le_trans hc hcs
  refine le_trans (norm_prod_dampedEulerFactor_le hP ht0 ht1 hs) ?_
  rw [dampedCorrBound]
  refine Finset.prod_le_prod ?_ ?_
  · intro p hp
    have hp2 := hP p hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by linarith) _
    have hlt : (p : ℝ) ^ (-s.re) < 1 := rpow_neg_lt_one hp2 hs
    positivity
  · intro p hp
    have hp2 := hP p hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
    have hmono : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-c) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hltc : (p : ℝ) ^ (-c) < 1 := rpow_neg_lt_one hp2 hc
    have hlts : (p : ℝ) ^ (-s.re) < 1 := rpow_neg_lt_one hp2 hs
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos hp0 _
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hmono, hpos, hltc, hlts]

/-- **The damped series' analytic continuation, bounded by `invZeta` times the correction.** -/
theorem norm_dampedInvZeta_le {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {c : ℝ} (hc : 1 / 2 ≤ c) {s : ℂ} (hcs : c ≤ s.re) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ‖invZeta s‖ ≤ M) :
    ‖dampedInvZeta P t s‖ ≤ M * dampedCorrBound P c := by
  rw [dampedInvZeta, norm_mul]
  refine mul_le_mul hM (norm_prod_dampedEulerFactor_le_corrBound hP ht0 ht1 hc hcs)
    (norm_nonneg _) hM0

end

end RHTower.Sieve
