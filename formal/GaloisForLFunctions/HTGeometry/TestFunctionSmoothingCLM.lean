import GaloisForLFunctions.HTGeometry.ComplexFlowSmoothing
import GaloisForLFunctions.HTGeometry.TestFunctionBarrelled

/-!
# The smoothing as a continuous linear map on the test space

For a fixed vector, the map sending a test weight to the smoothed vector is linear and bounded by
the order-zero seminorm, hence continuous.  Pairing with another vector gives the continuous
linear functionals whose finite sums are the truncated traces.

* `cFlowSmoothingCLM` : the smoothing as a continuous linear map on the test space.
* `deningerTraceFunctional` : the matrix-coefficient functional `φ ↦ re ⟪y, K_φ x⟫`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory TopologicalSpace

section SmoothingCLM

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedSpace ℝ H] [CompleteSpace H] [IsScalarTower ℝ ℂ H]

omit [CompleteSpace H] in
/-- The complex smoothing is homogeneous in the weight. -/
theorem cFlowSmoothing_smul_weight (U : UnitaryFlow ℂ H) (c : ℝ) (phi : ℝ → ℂ) (x : H) :
    cFlowSmoothing U (c • phi) x = c • cFlowSmoothing U phi x := by
  rw [cFlowSmoothing, cFlowSmoothing, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (c • phi) t • U.op t x = c • (phi t • U.op t x)
  rw [Pi.smul_apply, smul_assoc]

variable (U : UnitaryFlow ℂ H) (J : Compacts ℝ)

/-- The smoothing at a fixed vector, as a linear map on the test space. -/
noncomputable def cFlowSmoothingLinear (x : H) : DeningerTest J →ₗ[ℝ] H where
  toFun phi := cFlowSmoothing U ((phi : ℝ → ℂ)) x
  map_add' phi psi := by
    show cFlowSmoothing U (((phi + psi : DeningerTest J) : ℝ → ℂ)) x = _
    rw [Submodule.coe_add]
    exact cFlowSmoothing_add_weight U J.isCompact phi.2 psi.2 x
  map_smul' c phi := by
    show cFlowSmoothing U (((c • phi : DeningerTest J) : ℝ → ℂ)) x = _
    rw [Submodule.coe_smul]
    exact cFlowSmoothing_smul_weight U c (phi : ℝ → ℂ) x

omit [CompleteSpace H] in
theorem norm_cFlowSmoothingLinear_le (x : H) (phi : DeningerTest J) :
    ‖cFlowSmoothingLinear U J x phi‖
      ≤ ((MeasureTheory.volume (J : Set ℝ)).toReal * ‖x‖)
        * (deningerTestFamily J 0) phi := by
  have h := norm_cFlowSmoothing_le_seminorm U J.isCompact phi.2 x
  calc ‖cFlowSmoothingLinear U J x phi‖
      ≤ ((MeasureTheory.volume (J : Set ℝ)).toReal
          * deningerTestSupNorm 0 ((phi : ℝ → ℂ))) * ‖x‖ := h
    _ = ((MeasureTheory.volume (J : Set ℝ)).toReal * ‖x‖)
          * (deningerTestFamily J 0) phi := by
        have hfam : (deningerTestFamily J 0) phi = deningerTestSupNorm 0 ((phi : ℝ → ℂ)) := rfl
        rw [hfam]
        ring

/-- **The smoothing as a continuous linear map on the test space.** -/
noncomputable def cFlowSmoothingCLM (x : H) : DeningerTest J →L[ℝ] H where
  toLinearMap := cFlowSmoothingLinear U J x
  cont := by
    refine (withSeminorms_deningerTest J).continuous_normedSpace_rng H
      (cFlowSmoothingLinear U J x) ?_
    refine ⟨{0}, ⟨(MeasureTheory.volume (J : Set ℝ)).toReal * ‖x‖, by positivity⟩, ?_⟩
    intro phi
    rw [Finset.sup_singleton]
    exact norm_cFlowSmoothingLinear_le U J x phi

omit [CompleteSpace H] in
@[simp] theorem cFlowSmoothingCLM_apply (x : H) (phi : DeningerTest J) :
    cFlowSmoothingCLM U J x phi = cFlowSmoothing U ((phi : ℝ → ℂ)) x := rfl

/-- **The matrix-coefficient functional** `φ ↦ re ⟪y, K_φ x⟫`, continuous and linear on the test
space.  Finite sums of these over an orthonormal family are the truncated traces. -/
noncomputable def deningerTraceFunctional (x y : H) : DeningerTest J →L[ℝ] ℝ :=
  (Complex.reCLM.comp ((innerSL ℂ y).restrictScalars ℝ)).comp (cFlowSmoothingCLM U J x)

omit [CompleteSpace H] in
@[simp] theorem deningerTraceFunctional_apply (x y : H) (phi : DeningerTest J) :
    deningerTraceFunctional U J x y phi
      = (inner ℂ y (cFlowSmoothing U ((phi : ℝ → ℂ)) x) : ℂ).re := rfl

end SmoothingCLM

end GaloisForLFunctions.HTGeometry
