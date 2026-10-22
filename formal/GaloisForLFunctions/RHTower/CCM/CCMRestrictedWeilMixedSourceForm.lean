import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilFriedrichsOperator

/-!
# Exact complex mixed source form of the restricted CCM Weil operator

This module upgrades the diagonal real source identity to the literal complex sesquilinear
identity.  No polarization assumption or reality restriction is used: the archimedean density,
two polar evaluations, and finite von Mangoldt translations are identified off diagonal for
arbitrary vectors in the complete form domain.
-/

open MeasureTheory Set
open scoped ENNReal InnerProduct BigOperators
noncomputable section
namespace RHTower

/-- Pointwise decomposition of the exact archimedean density. -/
theorem ccmArchimedean_density_eq_formWeight_add_scalar (xi : ℝ) :
    2 * gammaHardyPhaseRate (2 * Real.pi * xi) =
      ccmArchimedeanFormWeight xi +
        (2 * gammaHardyPhaseRate 0 - 1) := by
  have heven :
      gammaHardyPhaseRate (2 * Real.pi * xi) =
        gammaHardyPhaseRate (2 * Real.pi * |xi|) := by
    by_cases hxi : 0 ≤ xi
    · rw [abs_of_nonneg hxi]
    · have hneg : xi < 0 := lt_of_not_ge hxi
      have habs : 2 * Real.pi * |xi| = -(2 * Real.pi * xi) := by
        rw [abs_of_neg hneg]
        ring
      rw [habs]
      exact (gammaHardyPhaseRate_neg (2 * Real.pi * xi)).symm
  rw [heven]
  unfold ccmArchimedeanFormWeight
  ring

/-- Exact mixed decomposition of the archimedean spectral density. -/
theorem ccmArchimedean_form_mixed_eq_domainInner_add_scalar
    (f g : CCMArchimedeanFourierL2) :
    (∫ xi : ℝ,
        ((2 * gammaHardyPhaseRate (2 * Real.pi * xi) : ℝ) : ℂ) *
          star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) =
      inner ℂ f g +
        ((2 * gammaHardyPhaseRate 0 - 1 : ℝ) : ℂ) *
          inner ℂ (ccmArchimedeanWeightedToL2 f)
            (ccmArchimedeanWeightedToL2 g) := by
  let c : ℝ := 2 * gammaHardyPhaseRate 0 - 1
  have hpoint (xi : ℝ) :
      ((2 * gammaHardyPhaseRate (2 * Real.pi * xi) : ℝ) : ℂ) *
          star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi =
        ((ccmArchimedeanFormWeight xi : ℝ) : ℂ) *
            star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi +
          (c : ℂ) * star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi := by
    rw [ccmArchimedean_density_eq_formWeight_add_scalar]
    unfold c
    push_cast
    ring
  have hformInt : Integrable
      (fun xi : ℝ =>
        ((ccmArchimedeanFormWeight xi : ℝ) : ℂ) *
          star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) volume := by
    have h := (integrable_withDensity_iff_integrable_smul
      measurable_ccmArchimedeanFormWeightNNReal).mp
        (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f g)
    refine h.congr ?_
    filter_upwards with xi
    change (((Real.toNNReal (ccmArchimedeanFormWeight xi) : NNReal) : ℝ) : ℂ) *
        inner ℂ ((f : ℝ → ℂ) xi) ((g : ℝ → ℂ) xi) = _
    rw [coe_ccmArchimedeanFormWeightNNReal]
    simp only [RCLike.inner_apply, starRingEnd_apply]
    ring
  have hplainInt : Integrable
      (fun xi : ℝ => star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) volume := by
    have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ)
      (ccmArchimedeanWeightedToL2 f) (ccmArchimedeanWeightedToL2 g)
    refine h.congr ?_
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn f,
      ccmArchimedeanWeightedToL2_coeFn g] with xi hfx hig
    simp only [RCLike.inner_apply, starRingEnd_apply]
    rw [hfx, hig]
    ring
  have hformInner :
      (∫ xi : ℝ,
        ((ccmArchimedeanFormWeight xi : ℝ) : ℂ) *
          star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) = inner ℂ f g := by
    rw [MeasureTheory.L2.inner_def]
    change _ = (∫ x : ℝ, inner ℂ ((f : ℝ → ℂ) x) ((g : ℝ → ℂ) x)
      ∂(volume.withDensity fun xi =>
        (Real.toNNReal (ccmArchimedeanFormWeight xi) : ℝ≥0∞)))
    rw [integral_withDensity_eq_integral_smul
      measurable_ccmArchimedeanFormWeightNNReal]
    apply integral_congr_ae
    filter_upwards with xi
    change _ = (((Real.toNNReal (ccmArchimedeanFormWeight xi) : NNReal) : ℝ) : ℂ) *
        inner ℂ ((f : ℝ → ℂ) xi) ((g : ℝ → ℂ) xi)
    rw [coe_ccmArchimedeanFormWeightNNReal]
    simp only [RCLike.inner_apply, starRingEnd_apply]
    ring
  have hplainInner :
      (∫ xi : ℝ, star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) =
        inner ℂ (ccmArchimedeanWeightedToL2 f)
          (ccmArchimedeanWeightedToL2 g) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn f,
      ccmArchimedeanWeightedToL2_coeFn g] with xi hfx hig
    simp only [RCLike.inner_apply, starRingEnd_apply]
    rw [hfx, hig]
    ring
  have hconstInt : Integrable
      (fun xi : ℝ => (c : ℂ) * star ((f : ℝ → ℂ) xi) *
        (g : ℝ → ℂ) xi) volume := by
    refine (hplainInt.const_mul (c : ℂ)).congr ?_
    filter_upwards with xi
    ring
  have hconstIntegral :
      (∫ xi : ℝ, (c : ℂ) * star ((f : ℝ → ℂ) xi) *
          (g : ℝ → ℂ) xi) =
        (c : ℂ) * ∫ xi : ℝ, star ((f : ℝ → ℂ) xi) *
          (g : ℝ → ℂ) xi := by
    calc
      (∫ xi : ℝ, (c : ℂ) * star ((f : ℝ → ℂ) xi) *
          (g : ℝ → ℂ) xi) =
          ∫ xi : ℝ, (c : ℂ) *
            (star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) := by
        apply integral_congr_ae
        filter_upwards with xi
        ring
      _ = _ := integral_const_mul (μ := volume) (c : ℂ)
        (fun xi : ℝ => star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi)
  rw [show (fun xi : ℝ =>
      ((2 * gammaHardyPhaseRate (2 * Real.pi * xi) : ℝ) : ℂ) *
        star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) =
      (fun xi : ℝ =>
        ((ccmArchimedeanFormWeight xi : ℝ) : ℂ) *
          star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) +
      fun xi : ℝ => (c : ℂ) * star ((f : ℝ → ℂ) xi) *
        (g : ℝ → ℂ) xi by
      funext xi
      exact hpoint xi]
  calc
    integral volume
        ((fun xi : ℝ =>
          ((ccmArchimedeanFormWeight xi : ℝ) : ℂ) *
            star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) +
          fun xi : ℝ => (c : ℂ) * star ((f : ℝ → ℂ) xi) *
            (g : ℝ → ℂ) xi) =
        (∫ xi : ℝ,
          ((ccmArchimedeanFormWeight xi : ℝ) : ℂ) *
            star ((f : ℝ → ℂ) xi) * (g : ℝ → ℂ) xi) +
          ∫ xi : ℝ, (c : ℂ) * star ((f : ℝ → ℂ) xi) *
            (g : ℝ → ℂ) xi := by
      exact integral_add hformInt hconstInt
    _ = inner ℂ f g + (c : ℂ) *
          inner ℂ (ccmArchimedeanWeightedToL2 f)
            (ccmArchimedeanWeightedToL2 g) := by
      rw [hformInner, hconstIntegral, hplainInner]
    _ = _ := by rfl

/-- Exact mixed pairing of the two source polar vectors. -/
theorem inner_ccmPolarOperator_mixed (a : SuzukiPositiveAperture)
    (f g : suzukiApertureHilbert a) :
    inner ℂ (ccmPolarOperator a f) g =
      star (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (1 / 2)) g +
        star (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
          inner ℂ (ccmPolarApertureVector a (-1 / 2)) g := by
  rw [ccmPolarOperator, add_apply,
    InnerProductSpace.rankOne_apply, InnerProductSpace.rankOne_apply,
    inner_add_left, inner_smul_left, inner_smul_left]
  rfl

/-- Exact mixed pairing of the finite von Mangoldt translation operator. -/
theorem inner_ccmFinitePrimeOperator_mixed (a : SuzukiPositiveAperture)
    (f g : suzukiApertureHilbert a) :
    inner ℂ (ccmFinitePrimeOperator a f) g =
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
          inner ℂ (ccmPrimeTransportOperator a n f) g := by
  classical
  unfold ccmFinitePrimeOperator
  simp

/-- Exact mixed pairing of the bounded polar--prime remainder. -/
theorem inner_ccmRestrictedWeilBoundedRemainder_mixed
    (a : SuzukiPositiveAperture) (f g : suzukiApertureHilbert a) :
    inner ℂ (ccmRestrictedWeilBoundedRemainder a f) g =
      ccmArchimedeanRemainderScalar * inner ℂ f g +
        inner ℂ (ccmPolarOperator a f) g -
          inner ℂ (ccmFinitePrimeOperator a f) g := by
  change inner ℂ
      (((ccmArchimedeanRemainderScalar •
          (1 : suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a)) f +
        ccmPolarOperator a f) - ccmFinitePrimeOperator a f) g = _
  rw [inner_sub_left, inner_add_left, smul_apply, one_apply_eq_self,
    inner_smul_left]
  change star ccmArchimedeanRemainderScalar * inner ℂ f g +
      inner ℂ (ccmPolarOperator a f) g -
        inner ℂ (ccmFinitePrimeOperator a f) g = _
  have hc : star ccmArchimedeanRemainderScalar =
      ccmArchimedeanRemainderScalar := by
    simpa only [starRingEnd_apply] using star_ccmArchimedeanRemainderScalar
  rw [hc]

/-- Fourier-to-time form embedding preserves the complete mixed inner product after forgetting
the archimedean weight. -/
theorem inner_ccmArchimedeanFormToAperture
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    inner ℂ (ccmArchimedeanFormToAperture a u)
        (ccmArchimedeanFormToAperture a v) =
      inner ℂ (ccmArchimedeanWeightedToL2 u.1)
        (ccmArchimedeanWeightedToL2 v.1) := by
  change inner ℂ (ccmArchimedeanFourierToTime u.1)
      (ccmArchimedeanFourierToTime v.1) = _
  change inner ℂ (fourierUnitary.symm (ccmArchimedeanWeightedToL2 u.1))
      (fourierUnitary.symm (ccmArchimedeanWeightedToL2 v.1)) = _
  exact fourierUnitary.symm.inner_map_map _ _

/-- Literal complex mixed restricted Weil source form. -/
def ccmRestrictedWeilMixedSourceForm
    (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) : ℂ :=
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanFormToAperture a v
  (∫ xi : ℝ,
      ((2 * gammaHardyPhaseRate (2 * Real.pi * xi) : ℝ) : ℂ) *
        star ((u.1 : ℝ → ℂ) xi) * (v.1 : ℝ → ℂ) xi) +
    (star (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
        inner ℂ (ccmPolarApertureVector a (1 / 2)) g +
      star (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
        inner ℂ (ccmPolarApertureVector a (-1 / 2)) g) -
    ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (((1 / Real.sqrt n : ℝ) : ℂ) *
          (inner ℂ (logTranslationCLM (Real.log n) f.1) g.1 +
            inner ℂ (logTranslationCLM (-Real.log n) f.1) g.1))

/-- The canonical closed CCM form is exactly its literal complex archimedean--polar--prime source
formula for every ordered pair in the complete form domain. -/
theorem ccmRestrictedWeilForm_eq_mixedSource
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a u v =
      ccmRestrictedWeilMixedSourceForm a u v := by
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanFormToAperture a v
  have harch := ccmArchimedean_form_mixed_eq_domainInner_add_scalar u.1 v.1
  have hphysical := inner_ccmArchimedeanFormToAperture a u v
  have harch' :
      (∫ xi : ℝ,
          ((2 * gammaHardyPhaseRate (2 * Real.pi * xi) : ℝ) : ℂ) *
            star ((u.1 : ℝ → ℂ) xi) * (v.1 : ℝ → ℂ) xi) =
        inner ℂ u v +
          ((2 * gammaHardyPhaseRate 0 - 1 : ℝ) : ℂ) * inner ℂ f g := by
    rw [harch]
    change inner ℂ u v +
        ((2 * gammaHardyPhaseRate 0 - 1 : ℝ) : ℂ) *
          inner ℂ (ccmArchimedeanWeightedToL2 u.1)
            (ccmArchimedeanWeightedToL2 v.1) = _
    rw [← hphysical]
  rw [ccmRestrictedWeilForm]
  change inner ℂ u v +
      inner ℂ (ccmRestrictedWeilBoundedRemainder a f) g = _
  rw [inner_ccmRestrictedWeilBoundedRemainder_mixed,
    inner_ccmPolarOperator_mixed, inner_ccmFinitePrimeOperator_mixed]
  simp_rw [inner_ccmPrimeTransportOperator]
  unfold ccmArchimedeanRemainderScalar
  unfold ccmRestrictedWeilMixedSourceForm
  dsimp only
  rw [harch']
  ring

end RHTower
