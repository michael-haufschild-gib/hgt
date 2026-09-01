import GaloisForLFunctions.HTGeometry.ModifiedBesselIOrder
import GaloisForLFunctions.HTGeometry.BesselOrderMeromorphic
import GaloisForLFunctions.HTGeometry.BesselOrderJetModule

/-!
# Actual meromorphic fundamental matrix for the Bessel order equation

The phase-twisted modified Bessel function `exp(π i ν) I_ν(s)` obeys the same order recurrence as
`K_ν(s)`.  These two entire solutions form a genuine fundamental matrix over the meromorphic
function field: its Casoratian is nonzero because its value at order zero has strictly negative real
part.  This supplies the analytic fundamental matrix required by the parameterized
Picard--Vessiot comparison; no formal generic matrix or determinant surrogate is used.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- Meromorphic realization of the phase-twisted modified Bessel `I` solution. -/
def modifiedBesselIOrderPhaseMero (s : ℝ) : meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (modifiedBesselIOrderPhase s)
    (analyticOnNhd_modifiedBesselIOrderPhase s)

/-- Translated meromorphic realization of the phase-twisted modified Bessel `I` solution. -/
def modifiedBesselIOrderPhaseShiftMero (s : ℝ) (q : ℂ) :
    meroField (Set.univ : Set ℂ) :=
  analyticMeroElement (fun z => modifiedBesselIOrderPhase s (z + q))
    (analyticOnNhd_comp_addTranslation (analyticOnNhd_modifiedBesselIOrderPhase s) q)

@[simp] theorem modifiedBesselIOrderPhaseShiftMero_zero (s : ℝ) :
    modifiedBesselIOrderPhaseShiftMero s 0 = modifiedBesselIOrderPhaseMero s := by
  rw [modifiedBesselIOrderPhaseShiftMero, modifiedBesselIOrderPhaseMero]
  congr 1
  funext z
  rw [add_zero]

theorem addTranslationMeroEquiv_modifiedBesselIOrderPhaseMero
    (s : ℝ) (q : ℂ) :
    addTranslationMeroEquiv q (modifiedBesselIOrderPhaseMero s) =
      modifiedBesselIOrderPhaseShiftMero s q := by
  exact addTranslationMeroEquiv_analyticMeroElement q
    (analyticOnNhd_modifiedBesselIOrderPhase s)

theorem addTranslationMeroEquiv_modifiedBesselIOrderPhaseShiftMero
    (s : ℝ) (p q : ℂ) :
    addTranslationMeroEquiv q (modifiedBesselIOrderPhaseShiftMero s p) =
      modifiedBesselIOrderPhaseShiftMero s (p + q) := by
  rw [modifiedBesselIOrderPhaseShiftMero,
    addTranslationMeroEquiv_analyticMeroElement]
  apply analyticMeroElement_congr
  funext z
  congr 1
  ring

theorem addTranslationMeroEquiv_modifiedBesselKOrderShiftMero
    (s : ℝ) (hs : 0 < s) (p q : ℂ) :
    addTranslationMeroEquiv q (modifiedBesselKOrderShiftMero s hs p) =
      modifiedBesselKOrderShiftMero s hs (p + q) := by
  rw [modifiedBesselKOrderShiftMero,
    addTranslationMeroEquiv_analyticMeroElement]
  apply analyticMeroElement_congr
  funext z
  congr 1
  ring

/-- The phase-twisted `I` solution obeys the Bessel order recurrence in the meromorphic field. -/
theorem modifiedBesselIOrderPhaseShiftMero_recurrence
    (s : ℝ) (hs : 0 < s) (q : ℂ) :
    modifiedBesselIOrderPhaseShiftMero s (q + 1) =
      modifiedBesselIOrderPhaseShiftMero s (q - 1) +
        besselOrderLinearCoeffShiftMero s q *
          modifiedBesselIOrderPhaseShiftMero s q := by
  let hplus := analyticOnNhd_comp_addTranslation
    (analyticOnNhd_modifiedBesselIOrderPhase s) (q + 1)
  let hminus := analyticOnNhd_comp_addTranslation
    (analyticOnNhd_modifiedBesselIOrderPhase s) (q - 1)
  let hcoeff : AnalyticOnNhd ℂ (fun z : ℂ => 2 * (z + q) / s)
      (Set.univ : Set ℂ) := by
    have hnum : AnalyticOnNhd ℂ (fun z : ℂ => (2 : ℂ) * (z + q)) Set.univ :=
      analyticOnNhd_const.mul (analyticOnNhd_id.add analyticOnNhd_const)
    have hinv : AnalyticOnNhd ℂ (fun _ : ℂ => (s : ℂ)⁻¹) Set.univ :=
      analyticOnNhd_const
    simpa [div_eq_mul_inv] using hnum.mul hinv
  let hy := analyticOnNhd_comp_addTranslation
    (analyticOnNhd_modifiedBesselIOrderPhase s) q
  let hprod := hcoeff.mul hy
  let hrhs := hminus.add hprod
  have hfun : (fun z => modifiedBesselIOrderPhase s (z + (q + 1))) =
      fun z => modifiedBesselIOrderPhase s (z + (q - 1)) +
        (2 * (z + q) / s) * modifiedBesselIOrderPhase s (z + q) := by
    funext z
    rw [show z + (q + 1) = (z + q) + 1 by ring,
      show z + (q - 1) = (z + q) - 1 by ring]
    exact modifiedBesselIOrderPhase_recurrence hs (z + q)
  change analyticMeroElement
    (fun z => modifiedBesselIOrderPhase s (z + (q + 1))) hplus = _
  calc
    _ = analyticMeroElement
        (fun z => modifiedBesselIOrderPhase s (z + (q - 1)) +
          (2 * (z + q) / s) * modifiedBesselIOrderPhase s (z + q)) hrhs :=
      analyticMeroElement_congr hplus _ hfun
    _ = _ := by
      rw [analyticMeroElement_add hminus hprod, analyticMeroElement_mul hcoeff hy]
      rfl

/-- The two actual meromorphic Bessel solutions and their unit translates. -/
def besselOrderActualFundamentalMatrix (s : ℝ) (hs : 0 < s) :
    Matrix (Fin 2) (Fin 2) (meroField (Set.univ : Set ℂ)) :=
  !![modifiedBesselKOrderMero s hs, modifiedBesselIOrderPhaseMero s;
    modifiedBesselKOrderShiftMero s hs 1, modifiedBesselIOrderPhaseShiftMero s 1]

/-- Meromorphic realization of the rational Bessel companion matrix. -/
def besselOrderCompanionMero (s : ℝ) :
    Matrix (Fin 2) (Fin 2) (meroField (Set.univ : Set ℂ)) :=
  (besselOrderCompanion (2 / (s : ℂ))).map
    (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)))

theorem besselOrderCompanionMero_coeff (s : ℝ) :
    algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
        (orderShiftCoeff (2 / (s : ℂ))) =
      besselOrderLinearCoeffShiftMero s 1 := by
  rw [besselOrderLinearCoeffShiftMero_eq_algebraMap]
  congr 1

theorem addTranslationMeroEquiv_modifiedBesselKOrderShiftMero_one
    (s : ℝ) (hs : 0 < s) :
    addTranslationMeroEquiv 1 (modifiedBesselKOrderShiftMero s hs 1) =
      modifiedBesselKOrderMero s hs +
        besselOrderLinearCoeffShiftMero s 1 *
          modifiedBesselKOrderShiftMero s hs 1 := by
  rw [addTranslationMeroEquiv_modifiedBesselKOrderShiftMero,
    show (1 : ℂ) + 1 = 1 + 1 by rfl,
    modifiedBesselKOrderShiftMero_recurrence s hs 1]
  simp

theorem addTranslationMeroEquiv_modifiedBesselIOrderPhaseShiftMero_one
    (s : ℝ) (hs : 0 < s) :
    addTranslationMeroEquiv 1 (modifiedBesselIOrderPhaseShiftMero s 1) =
      modifiedBesselIOrderPhaseMero s +
        besselOrderLinearCoeffShiftMero s 1 *
          modifiedBesselIOrderPhaseShiftMero s 1 := by
  rw [addTranslationMeroEquiv_modifiedBesselIOrderPhaseShiftMero,
    show (1 : ℂ) + 1 = 1 + 1 by rfl,
    modifiedBesselIOrderPhaseShiftMero_recurrence s hs 1]
  simp

/-- The actual Bessel solution matrix satisfies `σ(Y) = A Y`. -/
theorem besselOrderActualFundamentalMatrix_system
    (s : ℝ) (hs : 0 < s) :
    (besselOrderActualFundamentalMatrix s hs).map (addTranslationMeroEquiv 1) =
      besselOrderCompanionMero s * besselOrderActualFundamentalMatrix s hs := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp [besselOrderActualFundamentalMatrix, besselOrderCompanionMero,
      besselOrderCompanion, Matrix.mul_apply, Fin.sum_univ_two,
      addTranslationMeroEquiv_modifiedBesselKOrderMero]
  · simp [besselOrderActualFundamentalMatrix, besselOrderCompanionMero,
      besselOrderCompanion, Matrix.mul_apply, Fin.sum_univ_two,
      addTranslationMeroEquiv_modifiedBesselIOrderPhaseMero]
  · simp [besselOrderActualFundamentalMatrix, besselOrderCompanionMero,
      besselOrderCompanion, Matrix.mul_apply, Fin.sum_univ_two,
      addTranslationMeroEquiv_modifiedBesselKOrderShiftMero_one,
      besselOrderCompanionMero_coeff]
  · simpa [besselOrderActualFundamentalMatrix, besselOrderCompanionMero,
      besselOrderCompanion, Matrix.mul_apply, Fin.sum_univ_two,
      besselOrderCompanionMero_coeff] using
      addTranslationMeroEquiv_modifiedBesselIOrderPhaseShiftMero_one s hs

/-- Casoratian of the two actual Bessel order solutions. -/
def besselOrderActualCasoratian (s : ℝ) (hs : 0 < s) :
    meroField (Set.univ : Set ℂ) :=
  modifiedBesselKOrderMero s hs * modifiedBesselIOrderPhaseShiftMero s 1 -
    modifiedBesselIOrderPhaseMero s * modifiedBesselKOrderShiftMero s hs 1

theorem besselOrderActualFundamentalMatrix_det
    (s : ℝ) (hs : 0 < s) :
    (besselOrderActualFundamentalMatrix s hs).det =
      besselOrderActualCasoratian s hs := by
  simp [besselOrderActualFundamentalMatrix, besselOrderActualCasoratian,
    Matrix.det_fin_two]

private theorem besselOrderActualCasoratian_value_zero_ne
    (s : ℝ) (hs : 0 < s) :
    modifiedBesselKOrder s 0 * modifiedBesselIOrderPhase s 1 -
      modifiedBesselIOrderPhase s 0 * modifiedBesselKOrder s 1 ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have hK0eq : modifiedBesselKOrder s (0 : ℂ) =
      (realModifiedBesselKOrder s 0 : ℂ) := by
    simpa using modifiedBesselKOrder_ofReal hs 0
  have hK1eq : modifiedBesselKOrder s (1 : ℂ) =
      (realModifiedBesselKOrder s 1 : ℂ) := by
    simpa using modifiedBesselKOrder_ofReal hs 1
  rw [modifiedBesselIOrderPhase_zero, modifiedBesselIOrderPhase_one,
    hK0eq, hK1eq] at hre
  simp [Complex.mul_re] at hre
  have hK0 := realModifiedBesselKOrder_pos hs 0
  have hK1 := realModifiedBesselKOrder_pos hs 1
  have hI0 := modifiedBesselIOrder_zero_re_pos hs
  have hI1 := modifiedBesselIOrder_one_re_pos hs
  nlinarith

/-- The actual Casoratian is a nonzero meromorphic function. -/
theorem besselOrderActualCasoratian_ne_zero
    (s : ℝ) (hs : 0 < s) :
    besselOrderActualCasoratian s hs ≠ 0 := by
  let hK := analyticOnNhd_modifiedBesselKOrder hs
  let hI := analyticOnNhd_modifiedBesselIOrderPhase s
  let hKs := analyticOnNhd_comp_addTranslation hK 1
  let hIs := analyticOnNhd_comp_addTranslation hI 1
  let hleft := hK.mul hIs
  let hright := hI.mul hKs
  let hdet := hleft.sub hright
  rw [besselOrderActualCasoratian, modifiedBesselKOrderMero,
    modifiedBesselIOrderPhaseShiftMero, modifiedBesselIOrderPhaseMero,
    modifiedBesselKOrderShiftMero,
    ← analyticMeroElement_mul, ← analyticMeroElement_mul,
    ← analyticMeroElement_sub]
  intro hzero
  have hpoint := (analyticMeroElement_eq_zero_iff hdet).mp hzero 0 (Set.mem_univ 0)
  exact besselOrderActualCasoratian_value_zero_ne s hs (by simpa using hpoint)

/-- The actual meromorphic Bessel solution matrix is nonsingular. -/
theorem besselOrderActualFundamentalMatrix_det_ne_zero
    (s : ℝ) (hs : 0 < s) :
    (besselOrderActualFundamentalMatrix s hs).det ≠ 0 := by
  rw [besselOrderActualFundamentalMatrix_det]
  exact besselOrderActualCasoratian_ne_zero s hs

end

end GaloisForLFunctions.HTGeometry
