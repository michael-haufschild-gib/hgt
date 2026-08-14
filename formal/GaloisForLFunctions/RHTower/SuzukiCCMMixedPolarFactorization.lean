import GaloisForLFunctions.RHTower.SuzukiCCMMixedExplicitSource

/-!
# Mixed complex polar factorization for the Suzuki--CCM source

The two rank-one polar coefficients are identified with the literal positive-lag hyperbolic
carrier of a non-even Hermitian cross-correlation.  This is the off-diagonal complex extension
of the previously diagonal real factorization.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct BigOperators
noncomputable section
namespace RHTower

/-- Sharp support of a mixed strict-interior correlation. -/
theorem ccmComplexSmoothCrossCorrelation_eq_zero_of_two_aperture_le_abs
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) {h : ℝ}
    (hh : 2 * a.1 ≤ |h|) :
    ccmComplexSmoothCrossCorrelation u v h = 0 := by
  rw [ccmComplexSmoothCrossCorrelation_apply]
  apply integral_eq_zero_of_ae
  filter_upwards with x
  by_cases hv : v x = 0
  · simp [hv]
  by_cases hu : u (x - h) = 0
  · simp [hu]
  have hxv := v.support_subset hv
  have hxu := u.support_subset hu
  have hbound : |h| < 2 * a.1 := by
    rw [abs_lt]
    constructor <;> linarith [hxv.1, hxv.2, hxu.1, hxu.2]
  exact False.elim (not_lt_of_ge hh hbound)

/-- Exponentially weighted mixed Hermitian correlation factors into its two complex moments. -/
theorem integral_exp_mul_ccmComplexSmoothCrossCorrelation
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) (s : ℝ) :
    (∫ h : ℝ, (Real.exp (s * h) : ℂ) *
        ccmComplexSmoothCrossCorrelation u v h) =
      star (∫ x : ℝ, (Real.exp ((-s) * x) : ℂ) * u x) *
        ∫ x : ℝ, (Real.exp (s * x) : ℂ) * v x := by
  let f : ℝ → ℂ := fun x => (Real.exp (s * x) : ℂ) * v x
  let g : ℝ → ℂ := fun x => (Real.exp (s * x) : ℂ) * star (u (-x))
  have hfcont : Continuous f := by
    dsimp only [f]
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul v.continuous
  have hgcont : Continuous g := by
    dsimp only [g]
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
        (Complex.continuous_conj.comp (u.continuous.comp continuous_neg))
  have hfsupp : HasCompactSupport f := v.hasCompactSupport.mul_left
  have huref : HasCompactSupport (fun x : ℝ => u (-x)) :=
    u.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)
  have huconj : HasCompactSupport (fun x : ℝ => star (u (-x))) := by
    apply huref.mono
    intro x hx hzero
    apply hx
    change (starRingEnd ℂ) (u (-x)) = 0
    simpa only [map_zero] using congrArg (starRingEnd ℂ) hzero
  have hgsupp : HasCompactSupport g := huconj.mul_left
  have hfint : Integrable f := hfcont.integrable_of_hasCompactSupport hfsupp
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgsupp
  have hconv := MeasureTheory.integral_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hfint hgint
  have hpoint : ∀ h : ℝ,
      convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume h =
        (Real.exp (s * h) : ℂ) *
          ccmComplexSmoothCrossCorrelation u v h := by
    intro h
    rw [convolution_def, ccmComplexSmoothCrossCorrelation_apply]
    change (∫ y : ℝ, f y * g (h - y)) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    unfold f g
    rw [show -(h - y) = y - h by ring,
      show s * h = s * y + s * (h - y) by ring, Real.exp_add]
    push_cast
    ring
  have hg : (∫ x : ℝ, g x) =
      star (∫ x : ℝ, (Real.exp ((-s) * x) : ℂ) * u x) := by
    calc
      (∫ x : ℝ, g x) = ∫ x : ℝ, g (-x) :=
        (MeasureTheory.integral_neg_eq_self (μ := volume) g).symm
      _ = ∫ x : ℝ, star ((Real.exp ((-s) * x) : ℂ) * u x) := by
        apply integral_congr_ae
        filter_upwards with x
        unfold g
        rw [neg_neg]
        rw [show s * -x = (-s) * x by ring]
        change (Real.exp ((-s) * x) : ℂ) * (starRingEnd ℂ) (u x) =
          (starRingEnd ℂ) ((Real.exp ((-s) * x) : ℂ) * u x)
        rw [map_mul, Complex.conj_ofReal]
      _ = star (∫ x : ℝ, (Real.exp ((-s) * x) : ℂ) * u x) := integral_conj
  calc
    (∫ h : ℝ, (Real.exp (s * h) : ℂ) *
        ccmComplexSmoothCrossCorrelation u v h) =
        ∫ h : ℝ, convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume h := by
      apply integral_congr_ae
      filter_upwards with h
      exact (hpoint h).symm
    _ = (∫ x : ℝ, f x) * ∫ x : ℝ, g x := by
      simpa using hconv
    _ = _ := by
      rw [hg]
      dsimp only [f]
      ring

/-- Sum of the two whole-line half-density moments is the finite positive-lag hyperbolic
carrier, without assuming the correlation is even or real. -/
theorem integral_exp_half_pair_ccmComplexSmoothCrossCorrelation_eq_Ioc_cosh
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    (∫ h : ℝ, (Real.exp (h / 2) : ℂ) *
        ccmComplexSmoothCrossCorrelation u v h) +
      (∫ h : ℝ, (Real.exp (-(h / 2)) : ℂ) *
        ccmComplexSmoothCrossCorrelation u v h) =
      ∫ h in Ioc (0 : ℝ) (2 * a.1),
        (ccmComplexSmoothCrossCorrelation u v h +
          ccmComplexSmoothCrossCorrelation u v (-h)) *
            (2 * Real.cosh (h / 2) : ℂ) := by
  let H : ℝ → ℂ := ccmComplexSmoothCrossCorrelation u v
  let F : ℝ → ℂ := fun h =>
    (Real.exp (h / 2) : ℂ) * H h +
      (Real.exp (-(h / 2)) : ℂ) * H h
  have hHcont : Continuous H :=
    (ccmComplexSmoothCrossCorrelation u v).continuous
  have hHcompact : HasCompactSupport H := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Icc (-(2 * a.1)) (2 * a.1)) isCompact_Icc ?_
    intro h hh
    have habs : |h| < 2 * a.1 := by
      by_contra hnot
      exact hh (ccmComplexSmoothCrossCorrelation_eq_zero_of_two_aperture_le_abs
        u v (le_of_not_gt hnot))
    exact ⟨(abs_lt.mp habs).1.le, (abs_lt.mp habs).2.le⟩
  have hFcont : Continuous F := by
    dsimp only [F]
    fun_prop
  have hFcompact : HasCompactSupport F := by
    apply HasCompactSupport.add <;> exact hHcompact.mul_left
  have hFint : Integrable F := hFcont.integrable_of_hasCompactSupport hFcompact
  have hfirst : Integrable (fun h : ℝ =>
      (Real.exp (h / 2) : ℂ) * H h) :=
    (by fun_prop : Continuous (fun h : ℝ =>
      (Real.exp (h / 2) : ℂ) * H h)).integrable_of_hasCompactSupport
        hHcompact.mul_left
  have hsecond : Integrable (fun h : ℝ =>
      (Real.exp (-(h / 2)) : ℂ) * H h) :=
    (by fun_prop : Continuous (fun h : ℝ =>
      (Real.exp (-(h / 2)) : ℂ) * H h)).integrable_of_hasCompactSupport
        hHcompact.mul_left
  have hsum :
      (∫ h : ℝ, F h) =
        (∫ h : ℝ, (Real.exp (h / 2) : ℂ) * H h) +
          ∫ h : ℝ, (Real.exp (-(h / 2)) : ℂ) * H h := by
    exact integral_add hfirst hsecond
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := (0 : ℝ)) hFint.integrableOn hFint.integrableOn
  have hreflect := integral_comp_neg_Ioi (0 : ℝ) F
  simp only [neg_zero] at hreflect
  have hFneg : Integrable (fun h => F (-h)) := hFint.comp_neg
  have hwhole : (∫ h : ℝ, F h) =
      ∫ h in Ioi (0 : ℝ),
        (H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ) := by
    calc
      (∫ h : ℝ, F h) =
          (∫ h in Iic (0 : ℝ), F h) + ∫ h in Ioi (0 : ℝ), F h := hsplit.symm
      _ = (∫ h in Ioi (0 : ℝ), F (-h)) + ∫ h in Ioi (0 : ℝ), F h := by
        rw [hreflect]
      _ = ∫ h in Ioi (0 : ℝ), F (-h) + F h := by
        rw [integral_add hFneg.integrableOn hFint.integrableOn]
      _ = ∫ h in Ioi (0 : ℝ),
          (H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with h
        dsimp only [F]
        rw [Real.cosh_eq]
        push_cast
        ring_nf
  have htruncate :
      (∫ h in Ioi (0 : ℝ),
          (H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ)) =
        ∫ h in Ioc (0 : ℝ) (2 * a.1),
          (H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ) := by
    rw [← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with h
    by_cases hshort : h ∈ Ioc (0 : ℝ) (2 * a.1)
    · rw [indicator_of_mem hshort,
        indicator_of_mem (show h ∈ Ioi (0 : ℝ) from hshort.1)]
    · rw [indicator_of_notMem hshort]
      by_cases hpos : h ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hpos]
        have hlarge : 2 * a.1 ≤ |h| := by
          rw [abs_of_pos hpos]
          simp only [mem_Ioc, not_and_or, not_lt, not_le] at hshort
          rcases hshort with hnonpos | htop
          · exact False.elim ((not_lt_of_ge hnonpos) hpos)
          · exact htop.le
        rw [show H h = 0 by
          exact ccmComplexSmoothCrossCorrelation_eq_zero_of_two_aperture_le_abs u v hlarge]
        have hlargeNeg : 2 * a.1 ≤ |-h| := by simpa using hlarge
        rw [show H (-h) = 0 by
          exact ccmComplexSmoothCrossCorrelation_eq_zero_of_two_aperture_le_abs u v hlargeNeg]
        ring
      · rw [indicator_of_notMem hpos]
  dsimp only [H] at hwhole htruncate ⊢
  rw [← hsum, hwhole, htruncate]

/-- The explicit mixed polar--prime source is exactly CCM's two-sided finite-aperture
polar--prime distribution of the Hermitian correlation. -/
theorem ccmComplexSmoothPolarPrimeSource_eq_restrictedPolarPrimeFull
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    ccmComplexSmoothPolarPrimeSource u v =
      ccmRestrictedPolarPrimeFull a.1
        (ccmComplexSmoothCrossCorrelation u v) := by
  have hpos := integral_exp_mul_ccmComplexSmoothCrossCorrelation u v (1 / 2)
  have hneg := integral_exp_mul_ccmComplexSmoothCrossCorrelation u v (-1 / 2)
  have hpair :=
    integral_exp_half_pair_ccmComplexSmoothCrossCorrelation_eq_Ioc_cosh u v
  unfold ccmComplexSmoothPolarPrimeSource ccmRestrictedPolarPrimeFull
  have hpos' :
      star (∫ x : ℝ, (Real.exp ((-1 / 2 : ℝ) * x) : ℂ) * u x) *
          (∫ x : ℝ, (Real.exp ((1 / 2 : ℝ) * x) : ℂ) * v x) =
        ∫ h : ℝ, (Real.exp (h / 2) : ℂ) *
          ccmComplexSmoothCrossCorrelation u v h := by
    have huNeg :
        (∫ x : ℝ, (Real.exp ((-1 / 2 : ℝ) * x) : ℂ) * u x) =
          ∫ x : ℝ, (Real.exp ((-(1 / 2 : ℝ)) * x) : ℂ) * u x := by
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      ring
    calc
      _ = star (∫ x : ℝ, (Real.exp ((-(1 / 2 : ℝ)) * x) : ℂ) * u x) *
          (∫ x : ℝ, (Real.exp ((1 / 2 : ℝ) * x) : ℂ) * v x) := by rw [huNeg]
      _ = ∫ h : ℝ, (Real.exp ((1 / 2 : ℝ) * h) : ℂ) *
          ccmComplexSmoothCrossCorrelation u v h := hpos.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with h
        congr 2
        ring
  have hneg' :
      star (∫ x : ℝ, (Real.exp ((1 / 2 : ℝ) * x) : ℂ) * u x) *
          (∫ x : ℝ, (Real.exp ((-1 / 2 : ℝ) * x) : ℂ) * v x) =
        ∫ h : ℝ, (Real.exp (-(h / 2)) : ℂ) *
          ccmComplexSmoothCrossCorrelation u v h := by
    have huPos :
        (∫ x : ℝ, (Real.exp ((1 / 2 : ℝ) * x) : ℂ) * u x) =
          ∫ x : ℝ, (Real.exp ((-(-1 / 2 : ℝ)) * x) : ℂ) * u x := by
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      ring
    calc
      _ = star (∫ x : ℝ, (Real.exp ((-(-1 / 2 : ℝ)) * x) : ℂ) * u x) *
          (∫ x : ℝ, (Real.exp ((-1 / 2 : ℝ) * x) : ℂ) * v x) := by rw [huPos]
      _ = ∫ h : ℝ, (Real.exp ((-1 / 2 : ℝ) * h) : ℂ) *
          ccmComplexSmoothCrossCorrelation u v h := hneg.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with h
        congr 2
        ring
  rw [hpos', hneg', hpair]

/-- Closed mixed CCM form in the literal two-sided finite-aperture Weil source coordinate. -/
theorem ccmRestrictedWeilForm_ccmComplexSmooth_eq_polarPrimeFull_sub_archimedean
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilForm a u.toCCMFormVector v.toCCMFormVector =
      ccmRestrictedPolarPrimeFull a.1
          (ccmComplexSmoothCrossCorrelation u v) -
        ccmArchimedeanWeilDistribution
          (ccmComplexSmoothCrossCorrelationTest u v) := by
  rw [ccmRestrictedWeilForm_ccmComplexSmooth_eq_explicitDistribution,
    ccmComplexSmoothPolarPrimeSource_eq_restrictedPolarPrimeFull]

end RHTower
