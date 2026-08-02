import GaloisForLFunctions.RHTower.BurnolSoninDilationMellin
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier

/-!
# Reflected completed-Mellin evaluation on Burnol's extended Sonine space

Below the critical line the raw right-Mellin integral of a general `L²` Sonine vector need not
converge.  Burnol's meromorphic continuation is therefore represented by the absolutely convergent
right-half-plane evaluation of its cosine transform at `1 - w`.  This file constructs that
continuous functional on the actual extended Sonine space, obtains its canonical Riesz vector, and
proves the exact cosine-reflection and dilation laws.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The cosine involution restricted to the actual extended Sonine Hilbert space. -/
def burnolExtendedSoninCosine (a : ℝ) :
    soninExtendedSpace a ≃ₗᵢ[ℂ] soninExtendedSpace a where
  toFun f := ⟨soninCosineUnitary (f : evenSubspace),
    soninCosineUnitary_mem_soninExtendedSpace f.property⟩
  invFun f := ⟨soninCosineUnitary (f : evenSubspace),
    soninCosineUnitary_mem_soninExtendedSpace f.property⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add soninCosineUnitary _ _
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul soninCosineUnitary c _
  left_inv f := by
    apply Subtype.ext
    exact soninCosineUnitary_involutive (f : evenSubspace)
  right_inv f := by
    apply Subtype.ext
    exact soninCosineUnitary_involutive (f : evenSubspace)
  norm_map' f := soninCosineUnitary.norm_map (f : evenSubspace)

@[simp] theorem coe_burnolExtendedSoninCosine (a : ℝ) (f : soninExtendedSpace a) :
    ((burnolExtendedSoninCosine a f : soninExtendedSpace a) : evenSubspace) =
      soninCosineUnitary (f : evenSubspace) :=
  rfl

theorem burnolExtendedSoninCosine_involutive (a : ℝ) (f : soninExtendedSpace a) :
    burnolExtendedSoninCosine a (burnolExtendedSoninCosine a f) = f := by
  apply Subtype.ext
  exact soninCosineUnitary_involutive (f : evenSubspace)

@[simp] theorem burnolExtendedSoninCosine_symm_eq (a : ℝ) :
    (burnolExtendedSoninCosine a).symm = burnolExtendedSoninCosine a := by
  apply LinearIsometryEquiv.ext
  intro f
  have h := burnolExtendedSoninCosine_involutive a
    ((burnolExtendedSoninCosine a).symm f)
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

/-- Burnol's continued completed-Mellin evaluation below the critical line. -/
def burnolExtendedSoninReflectedEvaluation
    (w : ℂ) (a : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (ha : 0 < a) :
    soninExtendedSpace a →L[ℂ] ℂ :=
  burnolExtendedSoninEvaluation (1 - w) a (by
      rw [Complex.sub_re, Complex.one_re]
      linarith) (by
      rw [Complex.sub_re, Complex.one_re]
      linarith) ha ∘L
    (burnolExtendedSoninCosine a).toLinearIsometry.toContinuousLinearMap

@[simp] theorem burnolExtendedSoninReflectedEvaluation_apply
    (w : ℂ) (a : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (ha : 0 < a)
    (f : soninExtendedSpace a) :
    burnolExtendedSoninReflectedEvaluation w a hlo hhi ha f =
      soninMellinEvaluation (1 - w)
        ((((burnolExtendedSoninCosine a f : soninExtendedSpace a) : evenSubspace) :
          SoninL2) : ℝ → ℂ) :=
  rfl

/-- Canonical Riesz vector for the reflected (left-half-plane) evaluation. -/
def burnolExtendedSoninReflectedEvaluationVector
    (w : ℂ) (a : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (ha : 0 < a) :
    soninExtendedSpace a := by
  letI : Fact (0 < a) := ⟨ha⟩
  exact (InnerProductSpace.toDual ℂ (soninExtendedSpace a)).symm
    (burnolExtendedSoninReflectedEvaluation w a hlo hhi ha)

theorem inner_burnolExtendedSoninReflectedEvaluationVector
    (w : ℂ) (a : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (ha : 0 < a)
    (f : soninExtendedSpace a) :
    ⟪burnolExtendedSoninReflectedEvaluationVector w a hlo hhi ha, f⟫_ℂ =
      burnolExtendedSoninReflectedEvaluation w a hlo hhi ha f := by
  letI : Fact (0 < a) := ⟨ha⟩
  rw [burnolExtendedSoninReflectedEvaluationVector,
    InnerProductSpace.toDual_symm_apply]

/-- Exact Hermitian Riesz-vector reflection law. -/
theorem burnolExtendedSoninReflectedEvaluationVector_eq_cosine
    (w : ℂ) (a : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2) (ha : 0 < a) :
    burnolExtendedSoninReflectedEvaluationVector w a hlo hhi ha =
      burnolExtendedSoninCosine a
        (burnolExtendedSoninEvaluationVector (1 - w) a (by
          rw [Complex.sub_re, Complex.one_re]
          linarith) (by
          rw [Complex.sub_re, Complex.one_re]
          linarith) ha) := by
  letI : Fact (0 < a) := ⟨ha⟩
  apply ext_inner_right ℂ
  intro f
  rw [inner_burnolExtendedSoninReflectedEvaluationVector,
    burnolExtendedSoninReflectedEvaluation_apply]
  symm
  calc
    ⟪burnolExtendedSoninCosine a
          (burnolExtendedSoninEvaluationVector (1 - w) a (by
            rw [Complex.sub_re, Complex.one_re]
            linarith) (by
            rw [Complex.sub_re, Complex.one_re]
            linarith) ha), f⟫_ℂ =
        ⟪burnolExtendedSoninCosine a (burnolExtendedSoninCosine a
            (burnolExtendedSoninEvaluationVector (1 - w) a (by
              rw [Complex.sub_re, Complex.one_re]
              linarith) (by
              rw [Complex.sub_re, Complex.one_re]
              linarith) ha)), burnolExtendedSoninCosine a f⟫_ℂ :=
          ((burnolExtendedSoninCosine a).inner_map_map
            (burnolExtendedSoninCosine a
              (burnolExtendedSoninEvaluationVector (1 - w) a (by
                rw [Complex.sub_re, Complex.one_re]
                linarith) (by
                rw [Complex.sub_re, Complex.one_re]
                linarith) ha)) f).symm
    _ = ⟪burnolExtendedSoninEvaluationVector (1 - w) a (by
            rw [Complex.sub_re, Complex.one_re]
            linarith) (by
            rw [Complex.sub_re, Complex.one_re]
            linarith) ha, burnolExtendedSoninCosine a f⟫_ℂ := by
          rw [burnolExtendedSoninCosine_involutive]
    _ = _ := inner_burnolExtendedSoninEvaluationVector (1 - w) a (by
          rw [Complex.sub_re, Complex.one_re]
          linarith) (by
          rw [Complex.sub_re, Complex.one_re]
          linarith) ha (burnolExtendedSoninCosine a f)

/-- Exact normalized dilation character of the continued left-half-plane evaluation. -/
theorem burnolExtendedSoninReflectedEvaluation_evenDilation
    (w : ℂ) (a r : ℝ) (hlo : 0 < w.re) (hhi : w.re < 1 / 2)
    (ha : 0 < a) (hr : 1 ≤ r) (f : soninExtendedSpace a)
    (ha' : 0 < r⁻¹ * a) :
    burnolExtendedSoninReflectedEvaluation w (r⁻¹ * a) hlo hhi ha'
        ⟨evenDilationCLM r (lt_of_lt_of_le zero_lt_one hr) (f : evenSubspace),
          evenDilation_mem_soninExtendedSpace_inv_mul ha hr f.property⟩ =
      (r : ℂ) ^ (w - 1 / 2) *
        burnolExtendedSoninReflectedEvaluation w a hlo hhi ha f := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  rw [burnolExtendedSoninReflectedEvaluation_apply,
    burnolExtendedSoninReflectedEvaluation_apply]
  simp only [coe_burnolExtendedSoninCosine]
  rw [soninCosineUnitary_evenDilation,
    soninMellinEvaluation_evenDilation]
  rw [ofReal_inv_cpow hr0]
  congr 2
  ring

end RHTower
