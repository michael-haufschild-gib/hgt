import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.HTGeometry.DifferentialAutomorphismDefectEscape
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary
import GaloisForLFunctions.HTGeometry.UpperEndRationalCoordinateDifferentialAdjoin
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.XiShiftPrimeHypertranscendence

/-!
# Unconditional upper-end hypertranscendence of xi

The rationally corrected `+2` shift defect of the actual logarithmic derivative of `xi` is the
filtered von Mangoldt carrier.  That carrier is hypertranscendental over the genuine upper-end
copy of `C(z)`.  Complex translation is a differential automorphism over `C`, so its defect forces
the rotated logarithmic derivative itself to be hypertranscendental over `C`.

The coordinate satisfies `z' = 1`, hence adjoining it is a differentially algebraic base change.
The same logarithmic derivative is therefore hypertranscendental over the actual `C(z)`.  Finally,
its exact value relation with the logarithmic derivative of `z ↦ xi(-I*z)` proves
hypertranscendence of the actual rotated xi carrier in the upper-end meromorphic field.
-/

namespace RHTower

open Complex Filter Function Set
open scoped Differential

noncomputable section

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

local instance xiUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiUpperEndComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiUpperEndCharZero : CharZero upperEndMeroField :=
  charZero_of_injective_ringHom upperEndComplexToMero.injective

local instance xiUpperEndDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance xiUpperEndComplexDifferential : Differential ℂ where
  deriv := 0

local instance xiUpperEndComplexDifferentialAlgebra :
    DifferentialAlgebra ℂ upperEndMeroField :=
  ⟨fun c ↦ by
    rw [upperEndMero_deriv_complexConstant c]
    change (0 : upperEndMeroField) = algebraMap ℂ upperEndMeroField 0
    rw [map_zero]⟩

local instance xiUpperEndCoordinateDifferential :
    Differential upperEndRationalCoordinateField :=
  derivationClosedDifferential _ upperEndRationalCoordinateField_derivationClosed

local instance xiUpperEndCoordinateDifferentialAlgebra :
    DifferentialAlgebra upperEndRationalCoordinateField upperEndMeroField where
  deriv_algebraMap c := by
    change (c.1)′ = ((c′ : upperEndRationalCoordinateField) : upperEndMeroField)
    rfl

private theorem rotated_re (z : ℂ) : (-I * z).re = z.im := by
  simp [mul_re]

/-- The actual rotated xi function as an eventual-analytic upper-end germ. -/
noncomputable def xiRotatedUpperEndAnalytic : upperEndAnalyticSubring := by
  refine ⟨((fun z : ℂ ↦ xi (-I * z)) : Germ upperEndFilter ℂ), ?_⟩
  refine ⟨fun z : ℂ ↦ xi (-I * z), 1, ?_, rfl⟩
  intro z _
  exact (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
    (analyticAt_const.mul analyticAt_id)

/-- The actual rotated completed logarithmic derivative as an upper-end analytic germ. -/
noncomputable def xiLogDerivRotatedUpperEndAnalytic : upperEndAnalyticSubring := by
  refine ⟨((fun z : ℂ ↦ logDeriv xi (-I * z)) : Germ upperEndFilter ℂ), ?_⟩
  refine ⟨fun z : ℂ ↦ logDeriv xi (-I * z), 1, ?_, rfl⟩
  intro z hz
  have hs : 1 < (-I * z).re := by simpa [rotated_re] using hz
  have hxi : AnalyticAt ℂ xi (-I * z) :=
    xi_analyticOnNhd_univ _ (Set.mem_univ _)
  have hlog : AnalyticAt ℂ (logDeriv xi) (-I * z) := by
    rw [show logDeriv xi = fun s ↦ deriv xi s / xi s by
      funext s
      rw [logDeriv_apply]]
    exact hxi.deriv.div hxi (xi_ne_zero_of_one_lt_re hs)
  exact hlog.comp (analyticAt_const.mul analyticAt_id)

private noncomputable def xiShiftLinearUpperEndAnalytic (c : ℝ) :
    upperEndAnalyticSubring := by
  refine ⟨((fun z : ℂ ↦ -I * z + (c : ℂ)) : Germ upperEndFilter ℂ), ?_⟩
  exact ⟨_, 0, fun _ _ ↦ analyticAt_const.mul analyticAt_id |>.add analyticAt_const, rfl⟩

private noncomputable def xiShiftReciprocalUpperEndAnalytic (c : ℝ) :
    upperEndAnalyticSubring := by
  refine ⟨((fun z : ℂ ↦ 1 / (-I * z + (c : ℂ))) : Germ upperEndFilter ℂ), ?_⟩
  refine ⟨_, 1, ?_, rfl⟩
  intro z hz
  apply analyticAt_const.div
  · exact analyticAt_const.mul analyticAt_id |>.add analyticAt_const
  · intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith

private theorem xiShiftReciprocal_mul_linear (c : ℝ) :
    xiShiftReciprocalUpperEndAnalytic c * xiShiftLinearUpperEndAnalytic c = 1 := by
  apply Subtype.ext
  change ((fun z : ℂ ↦ 1 / (-I * z + (c : ℂ))) : Germ upperEndFilter ℂ) *
      ((fun z : ℂ ↦ -I * z + (c : ℂ)) : Germ upperEndFilter ℂ) = 1
  rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter,
    (1 / (-I * z + (c : ℂ))) * (-I * z + (c : ℂ)) = 1
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨1, trivial, fun z hz ↦ ?_⟩
  have hne : -I * z + (c : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith
  field_simp

private theorem xiShiftReciprocalUpperEndMero (c : ℝ) :
    algebraMap upperEndAnalyticSubring upperEndMeroField
        (xiShiftReciprocalUpperEndAnalytic c) =
      (-algebraMap ℂ upperEndMeroField I * upperEndCoordinateMero +
        algebraMap ℂ upperEndMeroField c)⁻¹ := by
  have hlinear :
      algebraMap upperEndAnalyticSubring upperEndMeroField
          (xiShiftLinearUpperEndAnalytic c) =
        -algebraMap ℂ upperEndMeroField I * upperEndCoordinateMero +
          algebraMap ℂ upperEndMeroField c := by
    change algebraMap upperEndAnalyticSubring upperEndMeroField
        (xiShiftLinearUpperEndAnalytic c) =
      -upperEndComplexToMero I * upperEndCoordinateMero + upperEndComplexToMero c
    change algebraMap upperEndAnalyticSubring upperEndMeroField
        (xiShiftLinearUpperEndAnalytic c) =
      -algebraMap upperEndAnalyticSubring upperEndMeroField
          (upperEndPolyToAnalytic (Polynomial.C I)) *
        algebraMap upperEndAnalyticSubring upperEndMeroField upperEndCoordinateAnalytic +
      algebraMap upperEndAnalyticSubring upperEndMeroField
          (upperEndPolyToAnalytic (Polynomial.C c))
    rw [← map_neg, ← map_mul, ← map_add]
    congr 1
    apply Subtype.ext
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z ↦ by simp
  have hprod := congrArg
    (algebraMap upperEndAnalyticSubring upperEndMeroField)
    (xiShiftReciprocal_mul_linear c)
  rw [map_mul, map_one, hlinear] at hprod
  exact (mul_eq_one_iff_eq_inv₀ (right_ne_zero_of_mul_eq_one hprod)).mp hprod

private noncomputable def xiShiftTwoRationalCorrectionUpperEndAnalytic :
    upperEndAnalyticSubring :=
  xiShiftReciprocalUpperEndAnalytic 2 +
    xiShiftReciprocalUpperEndAnalytic 1 -
      xiShiftReciprocalUpperEndAnalytic (-1)

private noncomputable def upperEndCoordinateInRationalField :
    upperEndRationalCoordinateField :=
  ⟨upperEndCoordinateMero,
    IntermediateField.subset_adjoin ℂ ({upperEndCoordinateMero} : Set _) rfl⟩

private noncomputable def xiShiftTwoRationalCorrectionBase :
    upperEndRationalCoordinateField :=
  (-algebraMap ℂ upperEndRationalCoordinateField I * upperEndCoordinateInRationalField +
      algebraMap ℂ upperEndRationalCoordinateField 2)⁻¹ +
    (-algebraMap ℂ upperEndRationalCoordinateField I * upperEndCoordinateInRationalField +
      algebraMap ℂ upperEndRationalCoordinateField 1)⁻¹ -
    (-algebraMap ℂ upperEndRationalCoordinateField I * upperEndCoordinateInRationalField +
      algebraMap ℂ upperEndRationalCoordinateField (-1))⁻¹

private theorem xiShiftTwoRationalCorrectionBase_coe :
    (xiShiftTwoRationalCorrectionBase : upperEndMeroField) =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        xiShiftTwoRationalCorrectionUpperEndAnalytic := by
  rw [show xiShiftTwoRationalCorrectionUpperEndAnalytic =
      xiShiftReciprocalUpperEndAnalytic 2 + xiShiftReciprocalUpperEndAnalytic 1 -
        xiShiftReciprocalUpperEndAnalytic (-1) by rfl,
    map_sub, map_add, xiShiftReciprocalUpperEndMero,
    xiShiftReciprocalUpperEndMero, xiShiftReciprocalUpperEndMero]
  change algebraMap upperEndRationalCoordinateField upperEndMeroField
      xiShiftTwoRationalCorrectionBase = _
  rw [show xiShiftTwoRationalCorrectionBase =
      (-algebraMap ℂ upperEndRationalCoordinateField I * upperEndCoordinateInRationalField +
          algebraMap ℂ upperEndRationalCoordinateField 2)⁻¹ +
        (-algebraMap ℂ upperEndRationalCoordinateField I * upperEndCoordinateInRationalField +
          algebraMap ℂ upperEndRationalCoordinateField 1)⁻¹ -
        (-algebraMap ℂ upperEndRationalCoordinateField I * upperEndCoordinateInRationalField +
          algebraMap ℂ upperEndRationalCoordinateField (-1))⁻¹ by rfl]
  simp only [map_sub, map_add, map_inv₀, map_mul, map_neg,
    IsScalarTower.algebraMap_apply]
  rfl

/-- Actual upper-end carrier of `z ↦ logDeriv xi (-I*z)`. -/
noncomputable def xiLogDerivRotatedUpperEndCarrier : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField xiLogDerivRotatedUpperEndAnalytic

private noncomputable def xiShiftTwoRationalCorrectionUpperEndCarrier : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField
    xiShiftTwoRationalCorrectionUpperEndAnalytic

/-- **Actual value-reflection law in the meromorphic field.**  Translation by `2*I` of the
rotated completed logarithmic derivative, minus its original value and rational correction, is
exactly the filtered von Mangoldt carrier. -/
theorem xiLogDerivRotatedUpperEnd_translation_defect :
    upperEndTranslationMeroEquiv (2 * I) xiLogDerivRotatedUpperEndCarrier -
        xiLogDerivRotatedUpperEndCarrier -
        xiShiftTwoRationalCorrectionUpperEndCarrier =
      filteredVonMangoldtUpperEndCarrier := by
  change upperEndTranslationMeroEquiv (2 * I)
        (algebraMap upperEndAnalyticSubring upperEndMeroField
          xiLogDerivRotatedUpperEndAnalytic) -
      algebraMap upperEndAnalyticSubring upperEndMeroField
          xiLogDerivRotatedUpperEndAnalytic -
      algebraMap upperEndAnalyticSubring upperEndMeroField
          xiShiftTwoRationalCorrectionUpperEndAnalytic =
      algebraMap upperEndAnalyticSubring upperEndMeroField
        (finiteAbscissaLSeriesToUpperEndAnalytic filteredVonMangoldtFiniteAbscissaSource)
  rw [upperEndTranslationMeroEquiv_algebraMap, ← map_sub, ← map_sub]
  congr 1
  apply Subtype.ext
  change upperEndTranslateGerm (2 * I)
        ((fun z : ℂ ↦ logDeriv xi (-I * z)) : Germ upperEndFilter ℂ) -
      ((fun z : ℂ ↦ logDeriv xi (-I * z)) : Germ upperEndFilter ℂ) -
      (xiShiftTwoRationalCorrectionUpperEndAnalytic : Germ upperEndFilter ℂ) =
      filteredVonMangoldtUpperEndGerm
  rw [show (xiShiftTwoRationalCorrectionUpperEndAnalytic : Germ upperEndFilter ℂ) =
      ((fun z : ℂ ↦ 1 / (-I * z + 2) + 1 / (-I * z + 1) -
        1 / (-I * z - 1)) : Germ upperEndFilter ℂ) by
    apply Germ.coe_eq.mpr
    change ∀ᶠ z in upperEndFilter,
      1 / (-I * z + 2) + 1 / (-I * z + 1) - 1 / (-I * z + (-1 : ℂ)) =
        1 / (-I * z + 2) + 1 / (-I * z + 1) - 1 / (-I * z - 1)
    exact Filter.Eventually.of_forall fun z ↦ by ring]
  rw [upperEndTranslateGerm_coe]
  rw [filteredVonMangoldtUpperEndGerm_eq_xiLogDerivShiftTwoPrimeDefect]
  apply Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun z ↦ by
    congr 4 <;> simp [I_sq] <;> ring

/-- The actual rotated logarithmic derivative is hypertranscendental over the constants. -/
theorem xiLogDerivRotatedUpperEndCarrier_hypertranscendentalOver_complex :
    HypertranscendentalOver ℂ xiLogDerivRotatedUpperEndCarrier := by
  have hcarrier : HypertranscendentalOver ℂ filteredVonMangoldtUpperEndCarrier := by
    have h := filteredVonMangoldtUpperEndCarrier_hypertranscendentalOver
    rw [← differentialAdjoin_upperEndCoordinateMero_eq] at h
    exact (hypertranscendentalOver_differentialAdjoinSingleton_iff
      differentialAlgebraicOver_upperEndCoordinateMero).mp h
  have hcorrection : DifferentialAlgebraicOver ℂ
      xiShiftTwoRationalCorrectionUpperEndCarrier := by
    change DifferentialAlgebraicOver ℂ
      (algebraMap upperEndAnalyticSubring upperEndMeroField
        xiShiftTwoRationalCorrectionUpperEndAnalytic)
    rw [← xiShiftTwoRationalCorrectionBase_coe]
    exact differentialAlgebraicOver_upperEndRationalCoordinate
      xiShiftTwoRationalCorrectionBase
  have hsum : HypertranscendentalOver ℂ
      (filteredVonMangoldtUpperEndCarrier +
        xiShiftTwoRationalCorrectionUpperEndCarrier) :=
    (hypertranscendentalOver_add_differentialAlgebraic_iff hcorrection).2 hcarrier
  have hdefect :
      upperEndTranslationMeroEquiv (2 * I) xiLogDerivRotatedUpperEndCarrier -
          xiLogDerivRotatedUpperEndCarrier =
        filteredVonMangoldtUpperEndCarrier +
          xiShiftTwoRationalCorrectionUpperEndCarrier := by
    linear_combination xiLogDerivRotatedUpperEnd_translation_defect
  have htranslated : HypertranscendentalOver ℂ
      (upperEndTranslationMeroEquiv (2 * I) xiLogDerivRotatedUpperEndCarrier -
        xiLogDerivRotatedUpperEndCarrier) := by
    rwa [hdefect]
  exact DifferentialAlgEquiv.hypertranscendentalOver_of_sub_self
    (upperEndTranslationMeroDifferentialAlgEquiv (2 * I)) htranslated

/-- **Unconditional completed-logarithmic-derivative capstone.**  The actual upper-end carrier of
`z ↦ xi'(-I*z) / xi(-I*z)` is hypertranscendental over the genuine rational coordinate field. -/
theorem xiLogDerivRotatedUpperEndCarrier_hypertranscendentalOver :
    HypertranscendentalOver upperEndRationalCoordinateField
      xiLogDerivRotatedUpperEndCarrier := by
  rw [← differentialAdjoin_upperEndCoordinateMero_eq]
  exact (hypertranscendentalOver_differentialAdjoinSingleton_iff
    differentialAlgebraicOver_upperEndCoordinateMero).2
      xiLogDerivRotatedUpperEndCarrier_hypertranscendentalOver_complex

private noncomputable def xiRotatedReciprocalUpperEndAnalytic :
    upperEndAnalyticSubring := by
  refine ⟨((fun z : ℂ ↦ 1 / xi (-I * z)) : Germ upperEndFilter ℂ), ?_⟩
  refine ⟨_, 1, ?_, rfl⟩
  intro z hz
  apply analyticAt_const.div
  · exact (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_const.mul analyticAt_id)
  · apply xi_ne_zero_of_one_lt_re
    simpa [rotated_re] using hz

private theorem xiRotatedReciprocal_mul_xiRotated :
    xiRotatedReciprocalUpperEndAnalytic * xiRotatedUpperEndAnalytic = 1 := by
  apply Subtype.ext
  change ((fun z : ℂ ↦ 1 / xi (-I * z)) : Germ upperEndFilter ℂ) *
      ((fun z : ℂ ↦ xi (-I * z)) : Germ upperEndFilter ℂ) = 1
  rw [← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
  change ∀ᶠ z in upperEndFilter, (1 / xi (-I * z)) * xi (-I * z) = 1
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨1, trivial, fun z hz ↦ ?_⟩
  have hne : xi (-I * z) ≠ 0 := xi_ne_zero_of_one_lt_re (by
    simpa [rotated_re] using hz)
  field_simp

/-- Actual upper-end carrier of the rotated completed function `z ↦ xi(-I*z)`. -/
noncomputable def xiRotatedUpperEndCarrier : upperEndMeroField :=
  algebraMap upperEndAnalyticSubring upperEndMeroField xiRotatedUpperEndAnalytic

private theorem xiRotatedReciprocalUpperEndMero :
    algebraMap upperEndAnalyticSubring upperEndMeroField
        xiRotatedReciprocalUpperEndAnalytic =
      xiRotatedUpperEndCarrier⁻¹ := by
  have hprod := congrArg
    (algebraMap upperEndAnalyticSubring upperEndMeroField)
    xiRotatedReciprocal_mul_xiRotated
  rw [map_mul, map_one] at hprod
  change algebraMap upperEndAnalyticSubring upperEndMeroField
      xiRotatedReciprocalUpperEndAnalytic * xiRotatedUpperEndCarrier = 1 at hprod
  exact (mul_eq_one_iff_eq_inv₀ (right_ne_zero_of_mul_eq_one hprod)).mp hprod

private theorem xiRotatedAnalytic_logRelation :
    upperEndAnalyticDeriv xiRotatedUpperEndAnalytic *
        xiRotatedReciprocalUpperEndAnalytic =
      -(upperEndPolyToAnalytic (Polynomial.C I)) *
        xiLogDerivRotatedUpperEndAnalytic := by
  apply Subtype.ext
  change upperEndGermDeriv
        ((fun z : ℂ ↦ xi (-I * z)) : Germ upperEndFilter ℂ) *
      ((fun z : ℂ ↦ 1 / xi (-I * z)) : Germ upperEndFilter ℂ) =
      -((fun z : ℂ ↦ (Polynomial.C I).eval z) : Germ upperEndFilter ℂ) *
        ((fun z : ℂ ↦ logDeriv xi (-I * z)) : Germ upperEndFilter ℂ)
  rw [upperEndGermDeriv_coe]
  apply Germ.coe_eq.mpr
  change ∀ᶠ z in upperEndFilter,
    deriv (fun w : ℂ ↦ xi (-I * w)) z * (1 / xi (-I * z)) =
      -I * logDeriv xi (-I * z)
  rw [upperEndFilter_basis.eventually_iff]
  refine ⟨1, trivial, fun z hz ↦ ?_⟩
  have hne : xi (-I * z) ≠ 0 := xi_ne_zero_of_one_lt_re (by
    simpa [rotated_re] using hz)
  have hchain := iteratedDeriv_comp_mul_left_uncond xi (-I) 1 z
  simp only [iteratedDeriv_one, pow_one] at hchain
  rw [hchain, logDeriv_apply]
  field_simp

/-- Exact logarithmic value relation between the actual rotated xi carrier and its completed
logarithmic-derivative carrier. -/
theorem xiRotatedUpperEndCarrier_logDeriv :
    xiRotatedUpperEndCarrier′ / xiRotatedUpperEndCarrier =
      -algebraMap ℂ upperEndMeroField I * xiLogDerivRotatedUpperEndCarrier := by
  change (algebraMap upperEndAnalyticSubring upperEndMeroField
      xiRotatedUpperEndAnalytic)′ /
      algebraMap upperEndAnalyticSubring upperEndMeroField xiRotatedUpperEndAnalytic = _
  rw [upperEndMeroFieldDifferential_algebraMap, div_eq_mul_inv]
  change algebraMap upperEndAnalyticSubring upperEndMeroField
      (upperEndAnalyticDeriv xiRotatedUpperEndAnalytic) *
      xiRotatedUpperEndCarrier⁻¹ = _
  rw [← xiRotatedReciprocalUpperEndMero, ← map_mul,
    xiRotatedAnalytic_logRelation, map_mul, map_neg]
  rfl

/-- **Unconditional upper-end xi hypertranscendence.**  The actual rotated xi carrier is
hypertranscendental over the genuine upper-end rational coordinate field. -/
theorem xiRotatedUpperEndCarrier_hypertranscendentalOver :
    HypertranscendentalOver upperEndRationalCoordinateField xiRotatedUpperEndCarrier := by
  let d : upperEndRationalCoordinateField :=
    algebraMap ℂ upperEndRationalCoordinateField (-I)
  have hd : DifferentialAlgebraicOver upperEndRationalCoordinateField
      (algebraMap upperEndRationalCoordinateField upperEndMeroField d) :=
    differentialAlgebraicOver_algebraMap d
  have hd0 : algebraMap upperEndRationalCoordinateField upperEndMeroField d ≠ 0 := by
    apply (map_ne_zero (algebraMap upperEndRationalCoordinateField upperEndMeroField)).2
    apply (map_ne_zero (algebraMap ℂ upperEndRationalCoordinateField)).2
    exact neg_ne_zero.mpr I_ne_zero
  have hscaled : HypertranscendentalOver upperEndRationalCoordinateField
      (algebraMap upperEndRationalCoordinateField upperEndMeroField d *
        xiLogDerivRotatedUpperEndCarrier) :=
    (hypertranscendentalOver_mul_differentialAlgebraic_iff hd hd0).2
      xiLogDerivRotatedUpperEndCarrier_hypertranscendentalOver
  have hscale : algebraMap upperEndRationalCoordinateField upperEndMeroField d =
      -algebraMap ℂ upperEndMeroField I := by
    rw [show d = algebraMap ℂ upperEndRationalCoordinateField (-I) by rfl,
      IsScalarTower.algebraMap_apply, map_neg]
  rw [hscale, ← xiRotatedUpperEndCarrier_logDeriv] at hscaled
  exact (hypertranscendentalOver_deriv_div_self_iff xiRotatedUpperEndCarrier).mp hscaled

/-- The concrete intermediate-field statement restricts to the canonically embedded abstract
rational-function coefficient field. -/
theorem xiRotatedUpperEndCarrier_hypertranscendentalOver_ratFunc :
    letI : Algebra (RatFunc ℂ) upperEndRationalCoordinateField :=
      upperEndRatfuncToRationalCoordinateField.toAlgebra
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    HypertranscendentalOver (RatFunc ℂ) xiRotatedUpperEndCarrier := by
  letI : Algebra (RatFunc ℂ) upperEndRationalCoordinateField :=
    upperEndRatfuncToRationalCoordinateField.toAlgebra
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI : IsScalarTower (RatFunc ℂ) upperEndRationalCoordinateField upperEndMeroField :=
    .of_algebraMap_eq fun _ ↦ rfl
  have h := xiRotatedUpperEndCarrier_hypertranscendentalOver
  rw [hypertranscendentalOver_iff_differentialIndependent_singleton] at h ⊢
  exact h.restrictScalars

end

end RHTower
