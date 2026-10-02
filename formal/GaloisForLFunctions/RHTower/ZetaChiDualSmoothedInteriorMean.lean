import GaloisForLFunctions.RHTower.ZetaChiDualWeightedInteriorMean
import GaloisForLFunctions.RHTower.SmoothAFEReflectedCofactorTransfer

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The cutoff-weighted atom is exactly the literal reflected primal
coefficient used by the full AFE source. -/
theorem cutoff_mul_dualInteriorAtom_eq_reflectedPrimalPositiveCoefficient
    (d b t : ℝ) (N : ℕ) {n : ℕ} (hn : 0 < n) :
    smoothAFECutoff ((n : ℝ) / N) * zetaChiDualInteriorAtom (rightDisplacedLinePt d b) n t =
      smoothAFEZetaRightReflectedPrimalPositiveCoefficient d (t + b) 1 N n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hshift : rightDisplacedLinePt d (t + b) =
      rightDisplacedLinePt d b + (t : ℂ) * I := by
    unfold rightDisplacedLinePt
    push_cast
    ring
  have hp : (n : ℂ) ^ ((t : ℂ) * I) = bourgainOscillation (t * Real.log n) := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnR.le).symm
    rw [hlog]
    unfold bourgainOscillation
    congr 1
    push_cast
    ring
  rw [reflectedPrimalPositiveCoefficient_eq_power_cutoff _ _ _ _ hn, one_mul, hshift,
    show rightDisplacedLinePt d b + (t : ℂ) * I - 1 =
      (rightDisplacedLinePt d b - 1) + (t : ℂ) * I by ring,
    Complex.cpow_add _ _ hnC, hp]
  unfold zetaChiDualInteriorAtom
  ring

/-- The literal Gaussian-smoothed interior block has a real first-mean lower
bound proportional to its full positive coefficient mass. This is not a target-event bound. -/
theorem eventually_zetaChi_dual_smoothed_interior_mean_ge
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r, ∀ S : Finset ℕ,
      (∀ n ∈ S, (m : ℝ) ^ 10 + (m : ℝ) ^ 6 ≤ 2 * Real.pi * n ∧
        2 * Real.pi * n + (m : ℝ) ^ 6 ≤ 2 * (m : ℝ) ^ 10) →
      Real.pi * (∑ n ∈ S, (smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10)).re) ≤
        (∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10),
          ∑ n ∈ S, smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10) *
            zetaChiDualInteriorAtom s n t).re := by
  obtain ⟨D, hD, hb⟩ := exists_zetaChi_dual_weighted_interior_mean c hr hc0 hc1
  obtain ⟨M, hM⟩ := exists_nat_gt (D / Real.pi)
  filter_upwards [hb, eventually_ge_atTop M, eventually_ge_atTop (1 : ℕ)] with m hm hmM hm1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0 : ℝ) < m := by linarith
  have hMR : (M : ℝ) ≤ m := by exact_mod_cast hmM
  have herr : D / (m : ℝ) ≤ Real.pi := by
    apply (div_le_iff₀ hm0).mpr
    have hdM := (div_lt_iff₀ Real.pi_pos).mp hM
    nlinarith [mul_le_mul_of_nonneg_left hMR Real.pi_pos.le]
  intro s hs S hS
  let w : ℕ → ℝ := fun n => (smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10)).re
  have hnpos (n : ℕ) (hn : n ∈ S) : (0 : ℝ) < n := by
    have hnlo := (hS n hn).1
    have hp : 0 < (m : ℝ) ^ 10 := by positivity
    have hq : 0 ≤ (m : ℝ) ^ 6 := by positivity
    nlinarith [Real.pi_pos]
  have hw : ∀ n ∈ S, 0 ≤ w n := by
    intro n hn
    exact (smoothAFECutoff_re_pos (div_pos (hnpos n hn) (by positivity))).le
  have heq (n : ℕ) (hn : n ∈ S) :
      smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10) = (w n : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using
        smoothAFECutoff_im_eq_zero (div_pos (hnpos n hn) (by positivity))
  have hbound := hm s hs S w hw hS
  have hsum : 0 ≤ ∑ n ∈ S, w n := Finset.sum_nonneg hw
  let Z : ℂ := ∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10),
    ∑ n ∈ S, (w n : ℂ) * zetaChiDualInteriorAtom s n t
  have hreal : 2 * Real.pi * (∑ n ∈ S, w n) - Z.re ≤
      ‖Z - ((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ)‖ := by
    have h := Complex.re_le_norm (((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ) - Z)
    rw [norm_sub_rev] at h
    simpa only [Complex.sub_re, Complex.ofReal_re] using h
  have hge : Real.pi * (∑ n ∈ S, w n) ≤ Z.re := by
    have hh := mul_le_mul_of_nonneg_right herr hsum
    change ‖Z - ((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ)‖ ≤ _ at hbound
    linarith
  have hint : (∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10),
      ∑ n ∈ S, smoothAFECutoff ((n : ℝ) / (m : ℝ) ^ 10) *
        zetaChiDualInteriorAtom s n t) = Z := by
    apply intervalIntegral.integral_congr
    intro t _
    apply Finset.sum_congr rfl
    intro n hn
    rw [heq n hn]
  rw [hint]
  exact hge

end RHTower
