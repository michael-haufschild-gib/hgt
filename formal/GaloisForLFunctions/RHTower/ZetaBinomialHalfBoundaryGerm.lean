import GaloisForLFunctions.RHTower.ZetaBinomialHalfFractionalPole
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import GaloisForLFunctions.RHTower.AnalyticDividedDifference
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

/-- The normalized pole-unit square root is the pole-cleared positive Dirichlet branch on the
right-half overlap.  The normalization at the pole rules out the negative branch. -/
theorem normalized_analytic_sqrt_zetaPoleUnit_eq_cpow_mul_LSeries
    {r : ℝ} (hr : 0 < r) {P : ℂ → ℂ}
    (hPan : AnalyticOnNhd ℂ P (ball (1 : ℂ) r))
    (hPone : P 1 = 1)
    (hPsq : ∀ z ∈ ball (1 : ℂ) r, P z ^ 2 = zetaPoleUnit z) :
    EqOn P (fun z => (z - 1) ^ (1 / 2 : ℂ) * LSeries zetaBinomialHalf z)
      (ball (1 : ℂ) r ∩ {z : ℂ | 1 < z.re}) := by
  let S : Set ℂ := ball (1 : ℂ) r ∩ {z : ℂ | 1 < z.re}
  let R : ℂ → ℂ := fun z => (z - 1) ^ (1 / 2 : ℂ) * LSeries zetaBinomialHalf z
  have hcpowAn : AnalyticOnNhd ℂ (fun z : ℂ => (z - 1) ^ (1 / 2 : ℂ))
      {z : ℂ | 1 < z.re} := by
    intro z hz
    apply (analyticAt_id.sub analyticAt_const).cpow analyticAt_const
    rw [Complex.mem_slitPlane_iff]
    left
    change 1 < z.re at hz
    change 0 < z.re - 1
    linarith
  have hRan : AnalyticOnNhd ℂ R {z : ℂ | 1 < z.re} :=
    hcpowAn.mul analyticOnNhd_LSeries_zetaBinomialHalf
  have hRcont : ContinuousOn R S := hRan.continuousOn.mono inter_subset_right
  have hPcont : ContinuousOn P S := hPan.continuousOn.mono inter_subset_left
  have hhalfSq : ∀ z : ℂ, 1 < z.re → ((z - 1) ^ (1 / 2 : ℂ)) ^ 2 = z - 1 := by
    intro z hz
    rw [← Complex.cpow_nat_mul]
    convert Complex.cpow_one (z - 1) using 2
    all_goals norm_num
  have hRsq : ∀ z ∈ S, R z ^ 2 = zetaPoleUnit z := by
    intro z hz
    change (((z - 1) ^ (1 / 2 : ℂ)) * LSeries zetaBinomialHalf z) ^ 2 =
      zetaPoleUnit z
    rw [mul_pow, hhalfSq z hz.2]
    have hzre : 1 < z.re := hz.2
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hzre
      norm_num at hzre
    calc
      (z - 1) * LSeries zetaBinomialHalf z ^ 2 =
          (z - 1) * (LSeries zetaBinomialHalf z * LSeries zetaBinomialHalf z) := by ring
      _ = (z - 1) * riemannZeta z := by rw [LSeries_zetaBinomialHalf_sq hz.2]
      _ = zetaPoleUnit z := (zetaPoleUnit_of_ne hz1).symm
  have hSqOn : EqOn (P ^ 2) (R ^ 2) S := by
    intro z hz
    change P z ^ 2 = R z ^ 2
    rw [hPsq z hz.1, hRsq z hz]
  have hRne : ∀ {z : ℂ}, z ∈ S → R z ≠ 0 := by
    intro z hz
    have hzre : 1 < z.re := hz.2
    have hbase : z - 1 ≠ 0 := sub_ne_zero.mpr (by
      intro h
      rw [h] at hzre
      norm_num at hzre)
    have hcpowNe : (z - 1) ^ (1 / 2 : ℂ) ≠ 0 := by
      rw [ne_eq, Complex.cpow_eq_zero_iff]
      simp [hbase]
    have hLne : LSeries zetaBinomialHalf z ≠ 0 := by
      intro hzero
      have hsq := LSeries_zetaBinomialHalf_sq hz.2
      rw [hzero, zero_mul] at hsq
      exact (riemannZeta_ne_zero_of_one_le_re hz.2.le) hsq.symm
    exact mul_ne_zero hcpowNe hLne
  have hSpre : IsPreconnected S :=
    ((convex_ball (1 : ℂ) r).inter (convex_halfSpace_re_gt 1)).isPreconnected
  rcases hSpre.eq_or_eq_neg_of_sq_eq hPcont hRcont hSqOn hRne with hEq | hEq
  · exact hEq
  · exfalso
    have hinner : Tendsto (fun t : ℝ => (((1 + t : ℝ) : ℂ)))
        (nhdsWithin 0 (Ioi 0)) (nhds (1 : ℂ)) := by
      have hrealCont : ContinuousAt (fun t : ℝ => 1 + t) 0 :=
        continuousAt_const.add continuousAt_id
      have hreal : Tendsto (fun t : ℝ => 1 + t) (nhds 0) (nhds 1) := by
        simpa using hrealCont.tendsto
      have hfull := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
      have hfull' : Tendsto (fun t : ℝ => (((1 + t : ℝ) : ℂ)))
          (nhds 0) (nhds (1 : ℂ)) := by
        simpa [Function.comp_def] using hfull
      exact hfull'.mono_left nhdsWithin_le_nhds
    have hPlim : Tendsto (fun t : ℝ => P (((1 + t : ℝ) : ℂ)))
        (nhdsWithin 0 (Ioi 0)) (nhds (1 : ℂ)) := by
      have hPcontAt : ContinuousAt P (1 : ℂ) :=
        (hPan 1 (mem_ball_self hr)).continuousAt
      change Tendsto (P ∘ fun t : ℝ => (((1 + t : ℝ) : ℂ)))
        (nhdsWithin 0 (Ioi 0)) (nhds (1 : ℂ))
      simpa only [hPone] using hPcontAt.tendsto.comp hinner
    have hRreal : (fun t : ℝ => R (((1 + t : ℝ) : ℂ))) =ᶠ[
        nhdsWithin (0 : ℝ) (Ioi 0)]
        (fun t : ℝ => ((Real.sqrt t : ℝ) : ℂ) *
          LSeries zetaBinomialHalf (((1 + t : ℝ) : ℂ))) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 ≤ t := ht.le
      change ((((1 + t : ℝ) : ℂ) - 1) ^ (1 / 2 : ℂ)) *
        LSeries zetaBinomialHalf (((1 + t : ℝ) : ℂ)) = _
      have hsub : (((1 + t : ℝ) : ℂ) - 1) = (t : ℂ) := by push_cast; ring
      rw [hsub]
      have hcpow : (t : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt t : ℝ) : ℂ) := by
        calc
          (t : ℂ) ^ (1 / 2 : ℂ) =
              (t : ℂ) ^ (((1 / 2 : ℝ) : ℝ) : ℂ) := by norm_num
          _ = (((t ^ (1 / 2 : ℝ) : ℝ)) : ℂ) :=
            (Complex.ofReal_cpow ht0 _).symm
          _ = ((Real.sqrt t : ℝ) : ℂ) := by rw [Real.sqrt_eq_rpow]
      rw [hcpow]
    have hRlim : Tendsto (fun t : ℝ => R (((1 + t : ℝ) : ℂ)))
        (nhdsWithin 0 (Ioi 0)) (nhds (1 : ℂ)) :=
      RHTower.tendsto_sqrt_mul_LSeries_zetaBinomialHalf_one_add.congr' hRreal.symm
    have hltR : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t < r :=
      (show ∀ᶠ t : ℝ in nhds (0 : ℝ), t < r from Iio_mem_nhds hr).filter_mono
        nhdsWithin_le_nhds
    have hmem : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        (((1 + t : ℝ) : ℂ)) ∈ S := by
      filter_upwards [self_mem_nhdsWithin, hltR] with t ht htr
      constructor
      · rw [mem_ball, dist_eq]
        have hsub : (((1 + t : ℝ) : ℂ) - 1) = (t : ℂ) := by push_cast; ring
        rw [hsub, norm_real, Real.norm_eq_abs, abs_of_pos ht]
        exact htr
      · simpa using ht
    have hEqLine : (fun t : ℝ => P (((1 + t : ℝ) : ℂ))) =ᶠ[nhdsWithin 0 (Ioi 0)]
        (fun t : ℝ => -R (((1 + t : ℝ) : ℂ))) := by
      filter_upwards [hmem] with t ht
      exact hEq ht
    have hnegLim : Tendsto (fun t : ℝ => -R (((1 + t : ℝ) : ℂ)))
        (nhdsWithin 0 (Ioi 0)) (nhds (-1 : ℂ)) := by
      simpa using hRlim.neg
    have hPnegLim : Tendsto (fun t : ℝ => P (((1 + t : ℝ) : ℂ)))
        (nhdsWithin 0 (Ioi 0)) (nhds (-1 : ℂ)) := hnegLim.congr' hEqLine.symm
    have hone : (1 : ℂ) = -1 := tendsto_nhds_unique hPlim hPnegLim
    norm_num at hone

/-- Near the zeta pole, Kato's boundary remainder is an analytic factor times the explicit
square-root cusp. -/
theorem exists_local_zetaBinomialHalf_kato_remainder_factorization :
    ∃ r : ℝ, 0 < r ∧ ∃ P H : ℂ → ℂ,
      AnalyticOnNhd ℂ P (ball (1 : ℂ) r) ∧
      P 1 = 1 ∧
      (∀ z ∈ ball (1 : ℂ) r, P z ^ 2 = zetaPoleUnit z) ∧
      AnalyticOnNhd ℂ H (ball (1 : ℂ) r) ∧
      EqOn
        (fun z => LSeries zetaBinomialHalf z / z - (z - 1) ^ (-(1 / 2 : ℂ)))
        (fun z => (z - 1) ^ (1 / 2 : ℂ) * H z)
        (ball (1 : ℂ) r ∩ {z : ℂ | 1 < z.re}) := by
  obtain ⟨r, hr, P, hPan, hPone, hPsq⟩ :=
    exists_local_normalized_analytic_sqrt_zetaPoleUnit
  let r₀ : ℝ := min r (1 / 2)
  have hr₀ : 0 < r₀ := lt_min hr (by norm_num)
  have hr₀r : r₀ ≤ r := min_le_left _ _
  have hr₀half : r₀ ≤ 1 / 2 := min_le_right _ _
  let N : ℂ → ℂ := fun z => P z / z - 1
  let H : ℂ → ℂ := dslope N 1
  have hz_ne : ∀ z ∈ ball (1 : ℂ) r₀, z ≠ 0 := by
    intro z hz hzero
    subst z
    rw [mem_ball, dist_zero_left, norm_one] at hz
    linarith
  have hNan : AnalyticOnNhd ℂ N (ball (1 : ℂ) r₀) := by
    intro z hz
    exact ((hPan z (ball_subset_ball hr₀r hz)).div analyticAt_id (hz_ne z hz)).sub
      analyticAt_const
  have hHan : AnalyticOnNhd ℂ H (ball (1 : ℂ) r₀) := by
    intro z hz
    exact analyticAt_dslope_of_analyticAt (hNan 1 (mem_ball_self hr₀)) (hNan z hz)
  have hNone : N 1 = 0 := by simp [N, hPone]
  have hNfactor : ∀ z : ℂ, N z = (z - 1) * H z := by
    intro z
    have hs := sub_smul_dslope N 1 z
    rw [hNone, sub_zero, smul_eq_mul] at hs
    exact hs.symm
  have hPmatch := normalized_analytic_sqrt_zetaPoleUnit_eq_cpow_mul_LSeries
    hr hPan hPone hPsq
  refine ⟨r₀, hr₀, P, H, hPan.mono (ball_subset_ball hr₀r), hPone,
    fun z hz => hPsq z (ball_subset_ball hr₀r hz), hHan, ?_⟩
  intro z hz
  have hzre : 1 < z.re := hz.2
  have hz0 : z ≠ 0 := hz_ne z hz.1
  have hw0 : z - 1 ≠ 0 := sub_ne_zero.mpr (by
    intro h
    rw [h] at hzre
    norm_num at hzre)
  have hq0 : (z - 1) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.cpow_eq_zero_iff]
    simp [hw0]
  have hqSq : ((z - 1) ^ (1 / 2 : ℂ)) ^ 2 = z - 1 := by
    rw [← Complex.cpow_nat_mul]
    convert Complex.cpow_one (z - 1) using 2
    all_goals norm_num
  have hPz : P z = (z - 1) ^ (1 / 2 : ℂ) * LSeries zetaBinomialHalf z :=
    hPmatch ⟨ball_subset_ball hr₀r hz.1, hz.2⟩
  have hfac := hNfactor z
  change P z / z - 1 = (z - 1) * H z at hfac
  have hfac2 :
      (z - 1) ^ (1 / 2 : ℂ) * LSeries zetaBinomialHalf z / z - 1 =
        ((z - 1) ^ (1 / 2 : ℂ)) ^ 2 * H z := by
    calc
      (z - 1) ^ (1 / 2 : ℂ) * LSeries zetaBinomialHalf z / z - 1 =
          P z / z - 1 := by rw [hPz]
      _ = (z - 1) * H z := hfac
      _ = ((z - 1) ^ (1 / 2 : ℂ)) ^ 2 * H z := by rw [hqSq]
  change LSeries zetaBinomialHalf z / z - (z - 1) ^ (-(1 / 2 : ℂ)) =
    (z - 1) ^ (1 / 2 : ℂ) * H z
  rw [Complex.cpow_neg]
  field_simp [hz0, hq0] at hfac2 ⊢
  linear_combination hfac2

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
