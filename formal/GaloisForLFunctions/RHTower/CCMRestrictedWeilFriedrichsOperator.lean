import GaloisForLFunctions.HTGeometry.BoundedPerturbedFriedrichsOperator
import GaloisForLFunctions.RHTower.CCMArchimedeanDenseFormCore
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Canonical operator of the exact restricted CCM Weil form

The exact archimedean form domain embeds compactly, injectively, and densely into the physical
aperture.  The polar evaluations and every prime with `n ≤ exp (2a)` form one bounded
self-adjoint remainder.  Applying the bounded-perturbation Friedrichs construction therefore
produces the canonical lower-bounded self-adjoint operator of the restricted Weil form, with an
explicit compact resolvent.

Unlike an abstract packaging of a form assumption, every ingredient below is the literal source
term already constructed from the Riemann--Siegel phase, the two polar evaluation vectors, and the
finite von Mangoldt translation sum.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Nontriviality of every positive physical aperture -/

private def ccmApertureConstantL2 (a : SuzukiPositiveAperture) : SoninL2 :=
  MeasureTheory.indicatorConstLp 2 (measurableSet_centralInterval a.1)
    (by simp [centralInterval]) (1 : ℂ)

private theorem indicatorCutoff_ccmApertureConstantL2
    (a : SuzukiPositiveAperture) :
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
        (ccmApertureConstantL2 a) = ccmApertureConstantL2 a := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) (ccmApertureConstantL2 a),
    (MeasureTheory.indicatorConstLp_coeFn
      (p := (2 : ENNReal)) (μ := (volume : Measure ℝ))
      (hs := measurableSet_centralInterval a.1)
      (hμs := by simp [centralInterval]) (c := (1 : ℂ)))] with x hcut hconst
  change (ccmApertureConstantL2 a : ℝ → ℂ) x =
      (centralInterval a.1).indicator (fun _ => (1 : ℂ)) x at hconst
  rw [hcut]
  by_cases hx : x ∈ centralInterval a.1
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hconst, Set.indicator_of_notMem hx]

private def ccmApertureConstantVector (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a := by
  refine ⟨ccmApertureConstantL2 a, ?_⟩
  rw [suzukiApertureHilbert, physicalForbidden, LinearMap.mem_range]
  exact ⟨ccmApertureConstantL2 a, indicatorCutoff_ccmApertureConstantL2 a⟩

private theorem ccmApertureConstantVector_ne_zero
    (a : SuzukiPositiveAperture) : ccmApertureConstantVector a ≠ 0 := by
  intro hzero
  have hval : ccmApertureConstantL2 a = 0 := congrArg Subtype.val hzero
  have hnormZero : ‖ccmApertureConstantL2 a‖ = 0 := by rw [hval, norm_zero]
  have hvol : (volume : Measure ℝ).real (centralInterval a.1) = 2 * a.1 := by
    rw [measureReal_def, centralInterval, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [a.property])]
    ring
  have hnorm := MeasureTheory.norm_indicatorConstLp
    (μ := (volume : Measure ℝ)) (p := (2 : ENNReal))
    (hs := measurableSet_centralInterval a.1)
    (hμs := by simp [centralInterval]) (c := (1 : ℂ))
    (by norm_num) (by norm_num)
  change ‖ccmApertureConstantL2 a‖ = _ at hnorm
  rw [hvol] at hnorm
  have hpos : 0 < ‖ccmApertureConstantL2 a‖ := by
    rw [hnorm]
    have ha2 : 0 < 2 * a.1 := by nlinarith [a.property]
    simp only [norm_one, one_mul]
    exact Real.rpow_pos_of_pos ha2 _
  linarith

noncomputable instance instNontrivialSuzukiApertureHilbert
    (a : SuzukiPositiveAperture) : Nontrivial (suzukiApertureHilbert a) :=
  nontrivial_of_ne (ccmApertureConstantVector a) 0
    (ccmApertureConstantVector_ne_zero a)

/-- Exact restricted Weil sesquilinear form on the complete archimedean form domain. -/
def ccmRestrictedWeilForm (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) : ℂ :=
  inner ℂ u v +
    inner ℂ
      (ccmRestrictedWeilBoundedRemainder a
        (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a v)

theorem norm_ccmArchimedeanFormToAperture
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ‖ccmArchimedeanFormToAperture a u‖ =
      ‖ccmArchimedeanWeightedToL2 u.1‖ := by
  change ‖ccmArchimedeanFourierToTime u.1‖ =
    ‖ccmArchimedeanWeightedToL2 u.1‖
  change ‖fourierUnitary.symm (ccmArchimedeanWeightedToL2 u.1)‖ =
    ‖ccmArchimedeanWeightedToL2 u.1‖
  exact fourierUnitary.symm.norm_map _

/-- Literal diagonal restricted Weil form from Connes--Consani's source formula. -/
def ccmRestrictedWeilSourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
      ‖(u.1 : ℝ → ℂ) xi‖ ^ 2) +
    ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (1 / 2)) f +
        (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (-1 / 2)) f).re -
    ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      (ArithmeticFunction.vonMangoldt n : ℝ) *
        (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re

/-- The abstract closed form is exactly the literal archimedean--polar--prime source formula. -/
theorem ccmRestrictedWeilForm_self_re_eq_source
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (ccmRestrictedWeilForm a u u).re =
      ccmRestrictedWeilSourceQuadratic a u := by
  let f := ccmArchimedeanFormToAperture a u
  have hfNorm : ‖f‖ = ‖ccmArchimedeanWeightedToL2 u.1‖ :=
    norm_ccmArchimedeanFormToAperture a u
  have hselfU : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u]
    norm_cast
  have hselfF : (inner ℂ f f).re = ‖f‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
    norm_cast
  have hprime :
      (inner ℂ (ccmFinitePrimeOperator a f) f).re =
        ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
          (ArithmeticFunction.vonMangoldt n : ℝ) *
            (1 / Real.sqrt n) *
              (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
                inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re := by
    rw [inner_ccmFinitePrimeOperator]
    simp_rw [Complex.re_sum, inner_ccmPrimeTransportOperator]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  have hpolar :
      (inner ℂ (ccmPolarOperator a f) f).re =
        ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
              inner ℂ (ccmPolarApertureVector a (1 / 2)) f +
            (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
              inner ℂ (ccmPolarApertureVector a (-1 / 2)) f).re := by
    rw [inner_ccmPolarOperator]
  have hbounded :
      (inner ℂ (ccmRestrictedWeilBoundedRemainder a f) f).re =
        (2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 +
          (inner ℂ (ccmPolarOperator a f) f).re -
            (inner ℂ (ccmFinitePrimeOperator a f) f).re := by
    rw [inner_ccmRestrictedWeilBoundedRemainder, Complex.sub_re,
      Complex.add_re, Complex.mul_re, hselfF]
    unfold ccmArchimedeanRemainderScalar
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [ccmRestrictedWeilForm, Complex.add_re, hselfU, hbounded]
  unfold ccmRestrictedWeilSourceQuadratic
  dsimp only
  change
    ‖u‖ ^ 2 +
        ((2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 +
          (inner ℂ (ccmPolarOperator a f) f).re -
            (inner ℂ (ccmFinitePrimeOperator a f) f).re) =
      (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
          ‖(u.1 : ℝ → ℂ) xi‖ ^ 2) +
        ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
              inner ℂ (ccmPolarApertureVector a (1 / 2)) f +
            (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
              inner ℂ (ccmPolarApertureVector a (-1 / 2)) f).re -
        ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
          (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
            (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
              inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re
  rw [hpolar, hprime]
  have harch := ccmArchimedean_form_eq_domainNorm_add_scalar u.1
  have harchf :
      (∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) *
          ‖(u.1 : ℝ → ℂ) xi‖ ^ 2) =
        ‖u‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1) * ‖f‖ ^ 2 := by
    rw [harch]
    change ‖u‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1) *
        ‖ccmArchimedeanWeightedToL2 u.1‖ ^ 2 = _
    rw [← hfNorm]
  rw [harchf]
  ring

/-- Uniform lower bound of the exact restricted Weil form. -/
theorem ccmRestrictedWeilForm_lowerBound
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    -‖ccmRestrictedWeilBoundedRemainder a‖ *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      (ccmRestrictedWeilForm a u u).re := by
  have hBnorm :
      |(inner ℂ
          (ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re| ≤
        ‖ccmRestrictedWeilBoundedRemainder a‖ *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
    calc
      |(inner ℂ
          (ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re| ≤
          ‖ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u)‖ *
            ‖ccmArchimedeanFormToAperture a u‖ :=
        (RCLike.abs_re_le_norm (inner ℂ
            (ccmRestrictedWeilBoundedRemainder a
              (ccmArchimedeanFormToAperture a u))
            (ccmArchimedeanFormToAperture a u))).trans
          (norm_inner_le_norm (𝕜 := ℂ)
            (ccmRestrictedWeilBoundedRemainder a
              (ccmArchimedeanFormToAperture a u))
            (ccmArchimedeanFormToAperture a u))
      _ ≤
          (‖ccmRestrictedWeilBoundedRemainder a‖ *
            ‖ccmArchimedeanFormToAperture a u‖) *
              ‖ccmArchimedeanFormToAperture a u‖ :=
        mul_le_mul_of_nonneg_right
          ((ccmRestrictedWeilBoundedRemainder a).le_opNorm _)
          (norm_nonneg _)
      _ = ‖ccmRestrictedWeilBoundedRemainder a‖ *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by ring
  unfold ccmRestrictedWeilForm
  rw [Complex.add_re]
  have hself : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u]
    norm_cast
  rw [hself]
  have hbelow :
      -(‖ccmRestrictedWeilBoundedRemainder a‖ *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2) ≤
        (inner ℂ
          (ccmRestrictedWeilBoundedRemainder a
            (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re :=
    (neg_le_neg hBnorm).trans (neg_abs_le _)
  nlinarith [sq_nonneg ‖u‖]

/-- Canonical self-adjoint operator representing the exact restricted Weil form. -/
def ccmRestrictedWeilOperator (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →ₗ.[ℂ] suzukiApertureHilbert a :=
  boundedPerturbedFriedrichsOperator
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)

/-- Connes--Consani's restricted Weil operator is self-adjoint, unconditionally. -/
theorem ccmRestrictedWeilOperator_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmRestrictedWeilOperator a) := by
  exact boundedPerturbedFriedrichsOperator_isSelfAdjoint
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)

/-- An explicit point of compact resolvent for the exact restricted Weil operator. -/
theorem ccmRestrictedWeilOperator_hasCompactResolventAt_negShift
    (a : SuzukiPositiveAperture) :
    LinearPMap.HasCompactResolventAt
      (ccmRestrictedWeilOperator a)
      (-(boundedPerturbedFormShift
        (ccmRestrictedWeilBoundedRemainder a) : ℂ)) := by
  exact boundedPerturbedFriedrichsOperator_hasCompactResolventAt_negShift
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)
    (isCompactOperator_ccmArchimedeanFormToAperture a)

/-- Compact positive covariance of the explicitly shifted restricted Weil operator. -/
def ccmRestrictedWeilCovariance (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  boundedPerturbedFormCovariance
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)

theorem ccmRestrictedWeilCovariance_injective (a : SuzukiPositiveAperture) :
    Function.Injective (ccmRestrictedWeilCovariance a) := by
  exact boundedPerturbedFormCovariance_injective
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)

theorem ccmRestrictedWeilCovariance_isPositive (a : SuzukiPositiveAperture) :
    ContinuousLinearMap.IsPositive (ccmRestrictedWeilCovariance a) := by
  exact boundedPerturbedFormCovariance_isPositive
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)

theorem ccmRestrictedWeilCovariance_isCompact (a : SuzukiPositiveAperture) :
    IsCompactOperator (ccmRestrictedWeilCovariance a) := by
  exact boundedPerturbedFormCovariance_isCompact
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (isCompactOperator_ccmArchimedeanFormToAperture a)

theorem norm_ccmRestrictedWeilCovariance_pos (a : SuzukiPositiveAperture) :
    0 < ‖ccmRestrictedWeilCovariance a‖ := by
  have hne : ccmRestrictedWeilCovariance a ≠ 0 := by
    intro hzero
    apply ccmApertureConstantVector_ne_zero a
    apply ccmRestrictedWeilCovariance_injective a
    simp [hzero]
  exact (norm_pos_iff (E := suzukiApertureHilbert a →L[ℂ]
    suzukiApertureHilbert a)).mpr hne

/-- Bottom spectral value of the exact restricted Weil operator, obtained from its covariance. -/
def ccmRestrictedWeilGroundEnergy (a : SuzukiPositiveAperture) : ℝ :=
  ‖ccmRestrictedWeilCovariance a‖⁻¹ -
    boundedPerturbedFormShift (ccmRestrictedWeilBoundedRemainder a)

/-- The bottom value is attained by a genuine nonzero eigenstate. -/
theorem ccmRestrictedWeilOperator_exists_groundEigenstate
    (a : SuzukiPositiveAperture) :
    ∃ x : (ccmRestrictedWeilOperator a).domain,
      (x : suzukiApertureHilbert a) ≠ 0 ∧
        ccmRestrictedWeilOperator a x =
          (ccmRestrictedWeilGroundEnergy a : ℂ) •
            (x : suzukiApertureHilbert a) := by
  let C := ccmRestrictedWeilCovariance a
  let mu : ℝ := ‖C‖
  have hCinj : Function.Injective C := ccmRestrictedWeilCovariance_injective a
  have hmu : 0 < mu := norm_ccmRestrictedWeilCovariance_pos a
  obtain ⟨e, hene, he⟩ :=
    boundedPerturbedFormCovariance_exists_norm_eigenvector
      (ccmArchimedeanFormToAperture a)
      (ccmRestrictedWeilBoundedRemainder a)
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
      (ccmArchimedeanFormToAperture_injective a)
      (denseRange_ccmArchimedeanFormToAperture a)
      (isCompactOperator_ccmArchimedeanFormToAperture a)
  change C e = (mu : ℂ) • e at he
  have hmuC : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu.ne'
  let z : suzukiApertureHilbert a := (mu : ℂ)⁻¹ • e
  have hCz : C z = e := by
    change C ((mu : ℂ)⁻¹ • e) = e
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hmuC, one_smul]
  have hedom : e ∈ (closedDenseInverse C).domain := by
    rw [closedDenseInverse_domain]
    exact ⟨z, hCz⟩
  let x : (ccmRestrictedWeilOperator a).domain :=
    ⟨e, by
      change e ∈ (closedDenseInverse C).domain
      exact hedom⟩
  refine ⟨x, hene, ?_⟩
  have hinvZ := (closedDenseInverse_apply_C C hCinj z).2
  have hinv : closedDenseInverse C
      ⟨e, hedom⟩ = z := by
    let Cz : (closedDenseInverse C).domain :=
      ⟨C z, (closedDenseInverse_apply_C C hCinj z).1⟩
    have heq : (⟨e, hedom⟩ : (closedDenseInverse C).domain) = Cz :=
      Subtype.ext hCz.symm
    rw [heq]
    exact hinvZ
  change boundedPerturbedFriedrichsOperator
      (ccmArchimedeanFormToAperture a)
      (ccmRestrictedWeilBoundedRemainder a)
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a) x = _
  rw [boundedPerturbedFriedrichsOperator_apply]
  change closedDenseInverse C ⟨e, hedom⟩ -
      (boundedPerturbedFormShift
        (ccmRestrictedWeilBoundedRemainder a) : ℂ) • e = _
  rw [hinv]
  change (mu : ℂ)⁻¹ • e -
      (boundedPerturbedFormShift
        (ccmRestrictedWeilBoundedRemainder a) : ℂ) • e = _
  unfold ccmRestrictedWeilGroundEnergy
  change (mu : ℂ)⁻¹ • e -
      (boundedPerturbedFormShift
        (ccmRestrictedWeilBoundedRemainder a) : ℂ) • e =
    ((mu⁻¹ - boundedPerturbedFormShift
      (ccmRestrictedWeilBoundedRemainder a) : ℝ) : ℂ) • e
  push_cast
  module

/-- The covariance-defined ground energy is the true quadratic-form floor on the full domain. -/
theorem ccmRestrictedWeilGroundEnergy_mul_norm_sq_le
    (a : SuzukiPositiveAperture)
    (x : (ccmRestrictedWeilOperator a).domain) :
    ccmRestrictedWeilGroundEnergy a *
          ‖(x : suzukiApertureHilbert a)‖ ^ 2 ≤
      (inner ℂ (ccmRestrictedWeilOperator a x)
        (x : suzukiApertureHilbert a)).re := by
  exact boundedPerturbedFriedrichsOperator_ground_mul_norm_sq_le
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)
    x

/-- The covariance-defined ground energy is below every real eigenvalue. -/
theorem ccmRestrictedWeilGroundEnergy_le_eigenvalue
    (a : SuzukiPositiveAperture) {lam : ℝ}
    (x : (ccmRestrictedWeilOperator a).domain)
    (hxne : (x : suzukiApertureHilbert a) ≠ 0)
    (hx : ccmRestrictedWeilOperator a x =
      (lam : ℂ) • (x : suzukiApertureHilbert a)) :
    ccmRestrictedWeilGroundEnergy a ≤ lam := by
  exact boundedPerturbedFriedrichsOperator_ground_le_eigenvalue
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)
    x hxne hx

/-- The exact ground energy is the Rayleigh floor on every source form-domain vector. -/
theorem ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u := by
  have hfloor := boundedPerturbedForm_ground_mul_norm_sq_le
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)
    u
  change ccmRestrictedWeilGroundEnergy a *
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
    (ccmRestrictedWeilForm a u u).re at hfloor
  rwa [ccmRestrictedWeilForm_self_re_eq_source] at hfloor

/-- Exact first representation theorem for the source restricted Weil form. -/
theorem ccmRestrictedWeilOperator_represents_form
    (a : SuzukiPositiveAperture) (y : suzukiApertureHilbert a)
    (v : CCMArchimedeanFormDomain a) :
    let C := boundedPerturbedFormCovariance
      (ccmArchimedeanFormToAperture a)
      (ccmRestrictedWeilBoundedRemainder a)
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    let x : (ccmRestrictedWeilOperator a).domain :=
      ⟨C y, by
        change C y ∈ (closedDenseInverse C).domain
        exact (closedDenseInverse_apply_C C
          (boundedPerturbedFormCovariance_injective
            (ccmArchimedeanFormToAperture a)
            (ccmRestrictedWeilBoundedRemainder a)
            (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
            (ccmArchimedeanFormToAperture_injective a)
            (denseRange_ccmArchimedeanFormToAperture a)) y).1⟩
    let u := boundedPerturbedFormRieszInv
      (ccmArchimedeanFormToAperture a)
      (ccmRestrictedWeilBoundedRemainder a)
      (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
      ((ccmArchimedeanFormToAperture a).adjoint y)
    (x : suzukiApertureHilbert a) = ccmArchimedeanFormToAperture a u ∧
      inner ℂ (ccmRestrictedWeilOperator a x)
          (ccmArchimedeanFormToAperture a v) =
        ccmRestrictedWeilForm a u v := by
  exact boundedPerturbedFriedrichsOperator_represents_form
    (ccmArchimedeanFormToAperture a)
    (ccmRestrictedWeilBoundedRemainder a)
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a)
    (ccmArchimedeanFormToAperture_injective a)
    (denseRange_ccmArchimedeanFormToAperture a)
    y v

end RHTower
