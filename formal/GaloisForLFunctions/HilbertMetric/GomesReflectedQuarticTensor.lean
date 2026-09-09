import GaloisForLFunctions.HilbertMetric.SecondLevelConcavityFifthRootNoGo
import GaloisForLFunctions.HTGeometry.GomesFinitePolynomialTensorSector
import GaloisForLFunctions.HTGeometry.GomesQuarticChargedConnection

/-!
# Tensor-density structure inside the reflected quartic curvature counterexample

The common-connection viewpoint of arXiv:2404.10461 and integer tensor charges of
arXiv:2509.25276v7 section 5.2 are applied experimentally to the
corpus's independent Hilbert-metric example. Its kernel and reflected product are the
charge-one and charge-two quartic densities. They give finite measures, valid normalized
laws and an exact factorized Schwartz ground state. These properties coexist with the
already proved negative fifth-root curvature; they do not repair that obstruction.
-/

noncomputable section
open Polynomial MeasureTheory GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal SchwartzMap

namespace HilbertMetric

/-- The actual real-line measure carried by the existing quartic counterexample kernel. -/
def gomesQuarticKernelMeasure : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (quarticGaussianKernel x))

/-- The actual measure of the counterexample's reflected tensor product. -/
def gomesQuarticReflectedMeasure : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (quarticGaussianReflectedProfile x))

/-- The old kernel is exactly the positive charge-one polynomial density. -/
theorem gomesQuarticKernel_density (x : ℝ) :
    quarticGaussianKernel x = dilatonWeight (gomesQuarticLogWeight 1) x := by
  simp only [quarticGaussianKernel, dilatonWeight, gomesQuarticLogWeight_eval, neg_mul, one_mul]

/-- The old reflected profile is exactly the charge-two polynomial density. -/
theorem gomesQuarticReflected_density (x : ℝ) :
    quarticGaussianReflectedProfile x = dilatonWeight (gomesQuarticLogWeight 2) x := by
  simp only [quarticGaussianReflectedProfile, dilatonWeight, gomesQuarticLogWeight_eval]

/-- The kernel's literal measure agrees with the general reconstruction construction. -/
theorem gomesQuarticKernelMeasure_eq :
    gomesQuarticKernelMeasure = gomesDilatonMeasure (gomesQuarticLogWeight 1) := by
  unfold gomesQuarticKernelMeasure gomesDilatonMeasure
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x => congrArg ENNReal.ofReal (gomesQuarticKernel_density x)

/-- Reflection adds two copies of the generating polynomial in the actual measure. -/
theorem gomesQuarticReflectedMeasure_eq :
    gomesQuarticReflectedMeasure =
      gomesDilatonMeasure (gomesQuarticLogWeight 1 + gomesQuarticLogWeight 1) := by
  have he : gomesQuarticLogWeight 2 = gomesQuarticLogWeight 1 + gomesQuarticLogWeight 1 := by
    apply Polynomial.funext
    intro x
    simp only [eval_add, gomesQuarticLogWeight_eval]
    ring
  rw [← he]
  unfold gomesQuarticReflectedMeasure gomesDilatonMeasure
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x => congrArg ENNReal.ofReal (gomesQuarticReflected_density x)

/-- The original curvature kernel has finite total mass. -/
theorem gomesQuarticKernelMeasure_finite : IsFiniteMeasure gomesQuarticKernelMeasure := by
  rw [gomesQuarticKernelMeasure_eq]
  have h := (gomesQuarticChargeMeasure_finite_iff 1 1).mpr (by
    simp only [Int.cast_one, one_mul]
    exact zero_lt_one)
  simpa only [gomesQuarticChargeMeasure, gomesQuarticTensorDensity,
    gomesQuarticTensorLogWeight, Int.cast_one, one_mul, gomesDilatonMeasure] using h

/-- The reflected tensor product remains finite by the general polynomial-sector closure theorem. -/
theorem gomesQuarticReflectedMeasure_finite : IsFiniteMeasure gomesQuarticReflectedMeasure := by
  rw [gomesQuarticReflectedMeasure_eq]
  have h : gomesQuarticLogWeight 1 ∈ gomesFinitePolynomialProfiles := by
    change IsFiniteMeasure (gomesDilatonMeasure (gomesQuarticLogWeight 1))
    rw [← gomesQuarticKernelMeasure_eq]
    exact gomesQuarticKernelMeasure_finite
  exact gomesFinitePolynomialProfiles.add_mem h h

/-- The old reflected product is literal density reweighting of the kernel measure. -/
theorem gomesQuarticReflectedMeasure_tensor :
    gomesQuarticKernelMeasure.withDensity
      (fun x => ENNReal.ofReal (quarticGaussianKernel (-x))) = gomesQuarticReflectedMeasure := by
  rw [gomesQuarticKernelMeasure, ← withDensity_mul _
    (by simpa only [quarticGaussianKernel, Function.comp_def, Pi.pow_apply, id_eq] using
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_id.pow 4))).measurable.ennreal_ofReal)
    (by simpa only [quarticGaussianKernel, Function.comp_def, Pi.pow_apply, id_eq] using
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_neg.pow 4))).measurable.ennreal_ofReal)]
  apply withDensity_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    rw [Pi.mul_apply, ← ENNReal.ofReal_mul (quarticGaussianKernel_pos x).le,
      ← quarticGaussianReflectedProfile_eq_kernel_mul]

/-- Reflection doubles the inherited cubic connection drift exactly. -/
theorem gomesQuarticReflected_connection :
    dilatonDriftCLM (gomesQuarticLogWeight 2) =
      (2 : ℂ) • dilatonDriftCLM (gomesQuarticLogWeight 1) := by
  ext ψ x
  simp only [gomesQuarticDrift_apply, smul_apply,
    Complex.ofReal_ofNat, Complex.ofReal_one, smul_eq_mul]
  ring

/-- The counterexample kernel is the squared amplitude of an exact Schwartz ground state. -/
theorem gomesQuarticKernel_ground_density (x : ℝ) :
    ‖gomesQuarticChargeGroundState ⟨(1 : ℝ), by change (0 : ℝ) < 1; exact zero_lt_one⟩ x‖ ^ 2 = quarticGaussianKernel x := by
  rw [gomesQuarticChargeGroundState, quarticDilatonGroundState_norm_sq, Real.exp_log zero_lt_one]
  simp only [quarticGaussianKernel, neg_mul, one_mul]

/-- Its factorized Hamiltonian has precisely the one-dimensional ground-state line. -/
theorem gomesQuarticKernel_ground_line (ψ : 𝓢(ℝ, ℂ)) :
    dilatonHamiltonianCLM (gomesQuarticLogWeight 1) ψ = 0 ↔
      ∃ c : ℂ, ψ = c • gomesQuarticChargeGroundState ⟨(1 : ℝ), by change (0 : ℝ) < 1; exact zero_lt_one⟩ :=
  gomesQuarticChargeGroundState_span ⟨(1 : ℝ), by change (0 : ℝ) < 1; exact zero_lt_one⟩ ψ

/-- Both old profiles give probability measures after literal total-mass normalization. -/
theorem gomesQuarticKernel_and_reflected_probability :
    IsProbabilityMeasure ((gomesQuarticKernelMeasure Set.univ)⁻¹ • gomesQuarticKernelMeasure) ∧
    IsProbabilityMeasure ((gomesQuarticReflectedMeasure Set.univ)⁻¹ • gomesQuarticReflectedMeasure) := by
  rw [gomesQuarticKernelMeasure_eq, gomesQuarticReflectedMeasure_eq]
  exact ⟨(gomesDilatonMassNormalized_probability_iff _).mpr (by
      rw [← gomesQuarticKernelMeasure_eq]
      exact gomesQuarticKernelMeasure_finite),
    (gomesDilatonMassNormalized_probability_iff _).mpr (by
      rw [← gomesQuarticReflectedMeasure_eq]
      exact gomesQuarticReflectedMeasure_finite)⟩

/-- The reflected tensor product changes the actual probability law, even after normalization. -/
theorem gomesQuarticKernel_reflected_probability_distinct :
    (gomesQuarticKernelMeasure Set.univ)⁻¹ • gomesQuarticKernelMeasure ≠
      (gomesQuarticReflectedMeasure Set.univ)⁻¹ • gomesQuarticReflectedMeasure := by
  let P : GomesFinitePolynomialProfile := ⟨gomesQuarticLogWeight 1, by
    change IsFiniteMeasure (gomesDilatonMeasure (gomesQuarticLogWeight 1))
    rw [← gomesQuarticKernelMeasure_eq]
    exact gomesQuarticKernelMeasure_finite⟩
  rw [gomesQuarticKernelMeasure_eq, gomesQuarticReflectedMeasure_eq]
  exact (gomesFinitePolynomialProfile_tensor_changes_law P P).symm

/-- Finite tensor probability laws and an exact ground state coexist with the existing curvature failure. -/
theorem gomesQuarticCurvatureFailure_with_tensor_geometry :
    IsFiniteMeasure gomesQuarticKernelMeasure ∧ IsFiniteMeasure gomesQuarticReflectedMeasure ∧
    (∃ ψ : 𝓢(ℝ, ℂ), ψ ≠ 0 ∧ dilatonHamiltonianCLM (gomesQuarticLogWeight 1) ψ = 0 ∧
      ∀ x : ℝ, ‖ψ x‖ ^ 2 = quarticGaussianKernel x) ∧
    fifthRootDividedDropCurvatureNumerator quarticGaussianReflectedProfile (1 / 2) < 0 := by
  let a : Set.Ioi (0 : ℝ) := ⟨1, by change (0 : ℝ) < 1; exact zero_lt_one⟩
  refine ⟨gomesQuarticKernelMeasure_finite, gomesQuarticReflectedMeasure_finite, ?_,
    quarticGaussianReflectedProfile_fifthRootCurvature_neg⟩
  refine ⟨gomesQuarticChargeGroundState a, gomesQuarticChargeGroundState_ne_zero a, ?_, ?_⟩
  · exact gomesQuarticChargeGroundState_kernel a
  · exact gomesQuarticKernel_ground_density

end HilbertMetric
