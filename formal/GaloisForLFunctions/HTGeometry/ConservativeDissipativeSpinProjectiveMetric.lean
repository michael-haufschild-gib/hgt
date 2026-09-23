import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinFidelity
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpinArcLength

/-!
# Projective information metric of the actual conservative–dissipative spin flow

Application of Schaffer–Exl, arXiv:2609.04530, to the corpus's pure-state projective
Gram and replica tangent theorems. The normalized spinor flow is differentiated
including its changing normalization factor, then horizontalized explicitly. Its
Fubini–Study speed equals half the actual Bloch-sphere speed from the Böttcher/Marty
bridge. Every finite chart Gram and every replica count has an exact formula.
-/

set_option autoImplicit false
open scoped Matrix ComplexConjugate
open Matrix
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Normalization identity in the scalar field of the spinor. -/
theorem spinChartScale_complex_identity (z : ℂ) :
    (spinChartScale z : ℂ) ^ (2 : ℕ) * (1 + conj z * z) = 1 := by
  have hd : 1 + ‖z‖ ^ (2 : ℕ) ≠ 0 := by positivity
  have hs : spinChartScale z ^ (2 : ℕ) * (1 + ‖z‖ ^ (2 : ℕ)) = 1 := by
    rw [spinChartScale_sq, inv_mul_cancel₀ hd]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  exact_mod_cast hs

/-- Coordinate differential before removing its normalization and phase direction. -/
def spinChartRawTangent (z δ : ℂ) : Fin 2 → ℂ :=
  (spinChartScale z : ℂ) • ![δ, 0]

/-- Explicit horizontal tangent in the normalized spin chart. -/
def spinChartHorizontal (z δ : ℂ) : Fin 2 → ℂ :=
  ((spinChartScale z : ℂ) ^ (3 : ℕ)) • ![δ, -conj z * δ]

/-- The corpus's projective quotient removes exactly the radial component. -/
theorem spinChartRawTangent_horizontal (z δ : ℂ) :
    finitePureStateHorizontalTangent (spinChartSpinor z) (spinChartRawTangent z δ) =
      spinChartHorizontal z δ := by
  have hc := spinChartScale_complex_identity z
  ext i
  fin_cases i <;>
    simp [finitePureStateHorizontalTangent, finiteComplexInner, spinChartSpinor,
      spinChartRawTangent, spinChartHorizontal, Fin.sum_univ_two]
  · linear_combination -(spinChartScale z : ℂ) * δ * hc
  · ring

/-- Adding any complex multiple of the state leaves its projective tangent unchanged. -/
theorem spinChartHorizontal_radial_cancel (z δ b : ℂ) :
    finitePureStateHorizontalTangent (spinChartSpinor z)
      (b • spinChartSpinor z + spinChartRawTangent z δ) = spinChartHorizontal z δ := by
  rw [← spinChartRawTangent_horizontal]
  have hc := spinChartScale_complex_identity z
  ext i
  fin_cases i <;>
    simp [finitePureStateHorizontalTangent, finiteComplexInner, spinChartSpinor,
      spinChartRawTangent, Fin.sum_univ_two]
  · linear_combination -(spinChartScale z : ℂ) * b * z * hc
  · linear_combination -(spinChartScale z : ℂ) * b * hc

/-- The exact Hermitian Fubini–Study metric in the chart. -/
theorem spinChartHorizontal_inner (z δ η : ℂ) :
    finiteComplexInner (spinChartHorizontal z δ) (spinChartHorizontal z η) =
      (((1 + ‖z‖ ^ (2 : ℕ))⁻¹) ^ (2 : ℕ) : ℝ) * (conj δ * η) := by
  have hc := spinChartScale_complex_identity z
  have hs : (spinChartScale z : ℂ) ^ (4 : ℕ) = ((((1 + ‖z‖ ^ (2 : ℕ))⁻¹) ^ (2 : ℕ) : ℝ) : ℂ) := by
    have hh := congrArg (fun r : ℝ => (r : ℂ)) (spinChartScale_sq z)
    push_cast at hh ⊢
    calc
      _ = ((spinChartScale z : ℂ) ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      _ = _ := by rw [hh]
  rw [← hs]
  simp [finiteComplexInner, spinChartHorizontal, Fin.sum_univ_two]
  linear_combination (spinChartScale z : ℂ) ^ (4 : ℕ) * conj δ * η * hc

/-- Exact derivative of the normalization factor along the actual spin evolution. -/
theorem hasDerivAt_spinChartScale_flow (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun v => spinChartScale (spinPlaneFlow a z v))
      (a ^ (2 : ℕ) * ‖spinPlaneFlow a z t‖ ^ (2 : ℕ) * spinChartScale (spinPlaneFlow a z t) ^ (3 : ℕ)) t := by
  have hd : 1 + ‖spinPlaneFlow a z t‖ ^ (2 : ℕ) ≠ 0 := by positivity
  have hs : Real.sqrt (1 + ‖spinPlaneFlow a z t‖ ^ (2 : ℕ)) ≠ 0 := by positivity
  have h := ((((hasDerivAt_spinPlaneFlow_norm a z t).pow 2).const_add 1).sqrt hd).inv hs
  change HasDerivAt (fun v => (Real.sqrt (1 + ‖spinPlaneFlow a z v‖ ^ (2 : ℕ)))⁻¹) _ t
  apply h.congr_deriv
  simp only [spinChartScale, Pi.pow_apply]
  field_simp
  ring

/-- Actual normalized-spinor velocity, including the changing normalization factor. -/
def spinSpinorVelocity (a : ℝ) (z : ℂ) : Fin 2 → ℂ :=
  ((a ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ) * spinChartScale z ^ (2 : ℕ) : ℝ) : ℂ) • spinChartSpinor z +
    spinChartRawTangent z (spinPlaneRate a * z)

/-- The projective metric is applied to an actual derivative of the exact spinor flow. -/
theorem hasDerivAt_spinSpinorFlow (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (spinSpinorFlow a z) (spinSpinorVelocity a (spinPlaneFlow a z t)) t := by
  have hc := (hasDerivAt_spinChartScale_flow a z t).ofReal_comp
  have hz := hasDerivAt_spinPlaneFlow a z t
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · change HasDerivAt (fun v => (spinChartScale (spinPlaneFlow a z v) : ℂ) * spinPlaneFlow a z v) _ t
    apply (hc.mul hz).congr_deriv
    simp [spinSpinorVelocity, spinChartSpinor, spinChartRawTangent]
    ring
  · change HasDerivAt (fun v => (spinChartScale (spinPlaneFlow a z v) : ℂ) * 1) _ t
    apply (hc.mul_const 1).congr_deriv
    simp [spinSpinorVelocity, spinChartSpinor, spinChartRawTangent]
    ring

/-- Actual spinor velocity has exactly the expected horizontal chart derivative. -/
theorem spinSpinorVelocity_horizontal (a : ℝ) (z : ℂ) :
    finitePureStateHorizontalTangent (spinChartSpinor z) (spinSpinorVelocity a z) =
      spinChartHorizontal z (spinPlaneRate a * z) :=
  spinChartHorizontal_radial_cancel _ _ _

/-- Exact real projective Gram for any finite family of chart directions. -/
theorem spinChartProjectiveGram {v : ℕ} (z : ℂ) (u : Fin v → ℂ) :
    finitePureStateProjectiveGram (spinChartSpinor z) (fun i => spinChartRawTangent z (u i)) =
      fun i j => (conj (u i) * u j).re / (1 + ‖z‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
  ext i j
  simp only [finitePureStateProjectiveGram, spinChartRawTangent_horizontal,
    spinChartHorizontal_inner, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hd : 1 + ‖z‖ ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp

/-- The entire replicated chart metric follows from the corpus's replica theorem. -/
theorem spinChartReplicaProjectiveGram {v : ℕ} (r : ℕ) (z : ℂ) (u : Fin v → ℂ) :
    finitePureStateReplicaProjectiveGram r (spinChartSpinor z)
      (fun i => spinChartRawTangent z (u i)) =
        fun i j => (r : ℝ) * (conj (u i) * u j).re / (1 + ‖z‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
  rw [finitePureStateReplicaProjectiveGram_eq_smul _ _ _
    (finiteComplexInner_spinChartSpinor_self z), spinChartProjectiveGram]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- Projective squared speed of the actual normalized-spinor derivative. -/
def spinSpinorProjectiveSpeedSq (a : ℝ) (z : ℂ) : ℝ :=
  (finiteComplexInner
    (finitePureStateHorizontalTangent (spinChartSpinor z) (spinSpinorVelocity a z))
    (finitePureStateHorizontalTangent (spinChartSpinor z) (spinSpinorVelocity a z))).re

/-- The exact quantum projective speed is the squared spherical derivative. -/
theorem spinSpinorProjectiveSpeedSq_eq (a : ℝ) (z : ℂ) :
    spinSpinorProjectiveSpeedSq a z = ‖spinPlaneRate a * z‖ ^ (2 : ℕ) / (1 + ‖z‖ ^ (2 : ℕ)) ^ (2 : ℕ) := by
  rw [spinSpinorProjectiveSpeedSq, spinSpinorVelocity_horizontal, spinChartHorizontal_inner,
    ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hd : 1 + ‖z‖ ^ (2 : ℕ) ≠ 0 := by positivity
  field_simp

/-- The actual Bloch-sphere speed is twice the quantum projective speed. -/
theorem spinSpinorProjectiveSpeedSq_bloch (a : ℝ) (z : ℂ) (t : ℝ) :
    spinSpinorProjectiveSpeedSq a (spinPlaneFlow a z t) =
      ‖spinSphereField a (spinSphereFlow a z t)‖ ^ (2 : ℕ) / 4 := by
  rw [spinSpinorProjectiveSpeedSq_eq, spinSphereFlow_speed, div_pow, mul_pow]
  ring

/-- Replicated actual spin velocity has exactly linear information-metric amplification. -/
theorem spinSpinorReplicaProjectiveSpeed (r : ℕ) (a : ℝ) (z : ℂ) (t : ℝ) :
    finitePureStateReplicaProjectiveGram r (spinSpinorFlow a z t)
      (fun _ : Fin 1 => spinSpinorVelocity a (spinPlaneFlow a z t)) 0 0 =
        (r : ℝ) * ‖spinSphereField a (spinSphereFlow a z t)‖ ^ (2 : ℕ) / 4 := by
  unfold spinSpinorFlow
  rw [finitePureStateReplicaProjectiveGram_eq_smul _ _ _
    (finiteComplexInner_spinChartSpinor_self (spinPlaneFlow a z t))]
  change (r : ℝ) * spinSpinorProjectiveSpeedSq a (spinPlaneFlow a z t) = _
  rw [spinSpinorProjectiveSpeedSq_bloch]
  ring

/-- In the real/imaginary coordinate basis, the replicated quantum metric is conformally Euclidean. -/
theorem spinChartReplicaProjectiveGram_coordinate (r : ℕ) (z : ℂ) :
    finitePureStateReplicaProjectiveGram r (spinChartSpinor z)
      (fun i : Fin 2 => spinChartRawTangent z (![1, Complex.I] i)) =
        ((r : ℝ) / (1 + ‖z‖ ^ (2 : ℕ)) ^ (2 : ℕ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [spinChartReplicaProjectiveGram]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
