import GaloisForLFunctions.RHTower.ZetaBinomialHalfFractionalPole
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import GaloisForLFunctions.HTGeometry.AnalyticSquareRoot

open ArithmeticFunction Complex Filter Metric Set Topology
open scoped BigOperators ArithmeticFunction.zeta ComplexOrder

noncomputable section

namespace RHTower

private theorem abscissaOfAbsConv_zetaBinomialHalf_le_one :
    LSeries.abscissaOfAbsConv zetaBinomialHalf ≤ (1 : ℝ) := by
  exact LSeries.abscissaOfAbsConv_le_of_le_const
    ⟨1, fun n _ => norm_zetaBinomialHalf_le_one n⟩

private theorem analyticOnNhd_LSeries_zetaBinomialHalf :
    AnalyticOnNhd ℂ (LSeries zetaBinomialHalf) {z : ℂ | 1 < z.re} := by
  refine (LSeries_analyticOnNhd zetaBinomialHalf).mono ?_
  intro z hz
  exact lt_of_le_of_lt abscissaOfAbsConv_zetaBinomialHalf_le_one (by exact_mod_cast hz)

/-- The pole-cleared zeta unit has a normalized analytic square root near `s = 1`. -/
theorem exists_local_normalized_analytic_sqrt_zetaPoleUnit :
    ∃ r : ℝ, 0 < r ∧ ∃ P : ℂ → ℂ,
      AnalyticOnNhd ℂ P (ball (1 : ℂ) r) ∧ P 1 = 1 ∧
      ∀ z ∈ ball (1 : ℂ) r, P z ^ 2 = zetaPoleUnit z := by
  have hunit_ne : zetaPoleUnit (1 : ℂ) ≠ 0 := by rw [zetaPoleUnit_one]; exact one_ne_zero
  have hnear : ∀ᶠ z in nhds (1 : ℂ), zetaPoleUnit z ≠ 0 :=
    (differentiable_zetaPoleUnit 1).continuousAt.eventually_ne hunit_ne
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨P, hPdiff, hPsq⟩ :=
    GaloisForLFunctions.HTGeometry.exists_sqrt_of_ne_zero
      differentiable_zetaPoleUnit.differentiableOn (fun z hz => hball hz)
  have hPan : AnalyticOnNhd ℂ P (ball (1 : ℂ) r) :=
    hPdiff.analyticOnNhd isOpen_ball
  have hPone_sq : P 1 ^ 2 = (1 : ℂ) ^ 2 := by
    simpa [zetaPoleUnit_one] using hPsq 1 (mem_ball_self hr)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hPone_sq with hPone | hPone
  · exact ⟨r, hr, P, hPan, hPone, hPsq⟩
  · refine ⟨r, hr, fun z => -P z, hPan.neg, ?_, ?_⟩
    · change -P 1 = 1
      rw [hPone]
      simp
    · intro z hz
      simpa using hPsq z hz

/-- At every non-pole point of the line `Re s = 1`, the positive Dirichlet square root of zeta
extends holomorphically across the line on a disk and remains a square root of zeta there. -/
theorem exists_local_analytic_zetaBinomialHalf_extension_at_oneLine
    {y : ℝ} (hy : y ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∃ B : ℂ → ℂ,
      AnalyticOnNhd ℂ B (ball ((1 : ℂ) + (y : ℂ) * I) r) ∧
      (∀ z ∈ ball ((1 : ℂ) + (y : ℂ) * I) r, B z ^ 2 = riemannZeta z) ∧
      EqOn B (LSeries zetaBinomialHalf)
        (ball ((1 : ℂ) + (y : ℂ) * I) r ∩ {z : ℂ | 1 < z.re}) := by
  let c : ℂ := (1 : ℂ) + (y : ℂ) * I
  have hc_re : c.re = 1 := by simp [c]
  have hc_im : c.im = y := by simp [c]
  have hc_ne_one : c ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp [hc_im] at this
    exact hy this
  have hzeta_c : riemannZeta c ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hc_re])
  have hnear : ∀ᶠ z in nhds c, riemannZeta z ≠ 0 ∧ z ≠ 1 :=
    ((differentiableAt_riemannZeta hc_ne_one).continuousAt.eventually_ne hzeta_c).and
      (continuousAt_id.eventually_ne hc_ne_one)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  have hzne : ∀ z ∈ ball c r, riemannZeta z ≠ 0 := fun z hz => (hball hz).1
  have hdiff : DifferentiableOn ℂ riemannZeta (ball c r) := fun z hz =>
    (differentiableAt_riemannZeta (hball hz).2).differentiableWithinAt
  obtain ⟨s, hsDiff, hsSq⟩ :=
    GaloisForLFunctions.HTGeometry.exists_sqrt_of_ne_zero hdiff hzne
  have hsAn : AnalyticOnNhd ℂ s (ball c r) := hsDiff.analyticOnNhd isOpen_ball
  let a : ℂ := c + ((r / 2 : ℝ) : ℂ)
  have haBall : a ∈ ball c r := by
    change dist (c + ((r / 2 : ℝ) : ℂ)) c < r
    rw [dist_eq, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hr)]
    linarith
  have haRe : 1 < a.re := by
    simp [a, hc_re]
    linarith
  have haSq : s a ^ 2 = (LSeries zetaBinomialHalf a) ^ 2 := by
    calc
      s a ^ 2 = riemannZeta a := hsSq a haBall
      _ = LSeries zetaBinomialHalf a * LSeries zetaBinomialHalf a :=
        (LSeries_zetaBinomialHalf_sq haRe).symm
      _ = (LSeries zetaBinomialHalf a) ^ 2 := by ring
  have hSconvex : Convex ℝ (ball c r ∩ {z : ℂ | 1 < z.re}) :=
    (convex_ball c r).inter (convex_halfSpace_re_gt 1)
  have hsCont : ContinuousOn s (ball c r ∩ {z : ℂ | 1 < z.re}) :=
    hsAn.continuousOn.mono inter_subset_left
  have hLCont : ContinuousOn (LSeries zetaBinomialHalf)
      (ball c r ∩ {z : ℂ | 1 < z.re}) :=
    analyticOnNhd_LSeries_zetaBinomialHalf.continuousOn.mono inter_subset_right
  have hSqOn : EqOn (s ^ 2) ((LSeries zetaBinomialHalf) ^ 2)
      (ball c r ∩ {z : ℂ | 1 < z.re}) := by
    intro z hz
    change s z ^ 2 = (LSeries zetaBinomialHalf z) ^ 2
    calc
      s z ^ 2 = riemannZeta z := hsSq z hz.1
      _ = LSeries zetaBinomialHalf z * LSeries zetaBinomialHalf z :=
        (LSeries_zetaBinomialHalf_sq hz.2).symm
      _ = (LSeries zetaBinomialHalf z) ^ 2 := by ring
  have hLne : ∀ {z : ℂ}, z ∈ ball c r ∩ {z : ℂ | 1 < z.re} →
      LSeries zetaBinomialHalf z ≠ 0 := by
    intro z hz hzero
    have hsq := LSeries_zetaBinomialHalf_sq hz.2
    rw [hzero, zero_mul] at hsq
    exact (riemannZeta_ne_zero_of_one_le_re hz.2.le) hsq.symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp haSq with ha | ha
  · refine ⟨r, hr, s, hsAn, hsSq, ?_⟩
    exact hSconvex.isPreconnected.eq_of_sq_eq hsCont hLCont hSqOn hLne
      ⟨haBall, haRe⟩ ha
  · refine ⟨r, hr, fun z => -s z, hsAn.neg, ?_, ?_⟩
    · intro z hz
      simpa using hsSq z hz
    · have hnegCont : ContinuousOn (-s) (ball c r ∩ {z : ℂ | 1 < z.re}) :=
        hsCont.neg
      have hnegSqOn : EqOn ((-s) ^ 2) ((LSeries zetaBinomialHalf) ^ 2)
          (ball c r ∩ {z : ℂ | 1 < z.re}) := by
        intro z hz
        change (-s z) ^ 2 = (LSeries zetaBinomialHalf z) ^ 2
        rw [neg_sq]
        exact hSqOn hz
      apply hSconvex.isPreconnected.eq_of_sq_eq hnegCont hLCont hnegSqOn hLne
        ⟨haBall, haRe⟩
      change -s a = LSeries zetaBinomialHalf a
      rw [ha]
      simp

end RHTower
