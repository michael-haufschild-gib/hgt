import GaloisForLFunctions.RHTower.Sieve.DampedTwist

/-!
# The Euler correction is an exponential of the prime sum

`dampedCorrBound P c = ∏_{p ∈ P} (1 + p^{-c})/(1 − p^{-c})` is at most `exp(3 ∑_{p ∈ P} p^{-c})`.
On `c ≥ 1` each `p^{-c} ≤ 1/2`, and there `(1+x)/(1−x) ≤ e^x · e^{2x}`, the second factor because
`(1−x)(1+2x) = 1 + x − 2x² ≥ 1`.

At the Route E parameters `∑_{p ∈ P} p^{-c}` is `O(log log x)`, so the correction is a power of
`log x` — which the contour's saving `exp(−c₀(log N)^{1/10})` absorbs.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- One factor of the correction, against an exponential. -/
theorem corr_factor_le_exp {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 2) :
    (1 + x) / (1 - x) ≤ Real.exp (3 * x) := by
  have hden : (0 : ℝ) < 1 - x := by linarith
  have h1x : 1 + x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  have h2x : (1 : ℝ) / (1 - x) ≤ Real.exp (2 * x) := by
    rw [div_le_iff₀ hden]
    have he : 1 + 2 * x ≤ Real.exp (2 * x) := by
      have := Real.add_one_le_exp (2 * x)
      linarith
    nlinarith [he, hx0, hx]
  calc (1 + x) / (1 - x) = (1 + x) * (1 / (1 - x)) := by ring
    _ ≤ Real.exp x * Real.exp (2 * x) :=
        mul_le_mul h1x h2x (by positivity) (Real.exp_pos x).le
    _ = Real.exp (3 * x) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **The correction is an exponential of the prime sum.** -/
theorem dampedCorrBound_le_exp {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) {c : ℝ} (hc : 1 ≤ c) :
    dampedCorrBound P c ≤ Real.exp (3 * ∑ p ∈ P, (p : ℝ) ^ (-c)) := by
  have hchalf : (1 : ℝ) / 2 ≤ c := by linarith
  rw [dampedCorrBound, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod ?_ ?_
  · intro p hp
    have hp2 := hP p hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-c) := Real.rpow_pos_of_pos (by linarith) _
    have hlt : (p : ℝ) ^ (-c) < 1 := rpow_neg_lt_one hp2 hchalf
    positivity
  · intro p hp
    have hp2 := hP p hp
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hpos : (0 : ℝ) < (p : ℝ) ^ (-c) := Real.rpow_pos_of_pos (by linarith) _
    have hhalf : (p : ℝ) ^ (-c) ≤ 1 / 2 := by
      have h1 : (p : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hpR (by linarith)
      have h2 : (2 : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at h2
      linarith
    exact corr_factor_le_exp hpos hhalf

end

end RHTower.Sieve
