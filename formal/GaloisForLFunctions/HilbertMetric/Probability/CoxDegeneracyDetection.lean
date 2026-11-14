import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.CoxResidualClassification
import GaloisForLFunctions.HilbertMetric.GaussianJetPositivity
import GaloisForLFunctions.HilbertMetric.FiniteOrbitFrames
import GaloisForLFunctions.HilbertMetric.PolarSupportNormalization
import GaloisForLFunctions.HTGeometry.SeparatingGramLocus
import GaloisForLFunctions.HTGeometry.FiniteLawRelationWallSynchronization

/-!
# Gamma–Cox detection of geometric degeneracy

Gaussian determinant zeros detect collisions, ordinary Gram zeros detect linear
dependence, frame kernels detect invisible directions, and polar normalization
preserves the detected kernel. Each criterion classifies finite families with
vanishing probability of any error.
-/

open scoped Classical
open Filter Topology MeasureTheory
open GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
open GaloisForLFunctions.HTGeometry
noncomputable section

namespace GaloisForLFunctions.HilbertMetric

/-- Gaussian determinant detection converges to the collision indicator. -/
theorem cox_gaussian_collision {d n : ℕ} (y : Fin n → Fin d → ℝ) :
    Tendsto (fun K => detection K (gaussianCoherentGram y).det) atTop
      (𝓝 (if ¬ Function.Injective y then 1 else 0)) := by
  have h : (gaussianCoherentGram y).det = 0 ↔ ¬ Function.Injective y := by
    simpa only [not_not] using (gaussianCoherentGram_det_ne_zero_iff_injective y).not
  simpa only [h] using tendsto_detection (gaussianCoherentGram y).det

/-- A finite collection of Gaussian configurations is classified simultaneously. -/
theorem cox_gaussian_family {ι : Type*} [Fintype ι] {d n : ℕ}
    (y : ι → Fin n → Fin d → ℝ) :
    Tendsto (fun K => (binaryLaw K (fun i => (gaussianCoherentGram (y i)).det)).real
      {b | b ≠ fun i => decide (¬ Function.Injective (y i))}) atTop (𝓝 0) := by
  have h (i : ι) : (gaussianCoherentGram (y i)).det = 0 ↔ ¬ Function.Injective (y i) := by
    simpa only [not_not] using (gaussianCoherentGram_det_ne_zero_iff_injective (y i)).not
  exact tendsto_classification_error (fun i => (gaussianCoherentGram (y i)).det)
    (fun i => ¬ Function.Injective (y i)) fun i => by
    simp only [h]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Gram determinant detection finds exactly the linearly dependent families. -/
theorem cox_linear_dependence {n : ℕ} (v : Fin n → E) :
    Tendsto (fun K => detection K ‖(gramMatrix v).det‖) atTop
      (𝓝 (if ¬ LinearIndependent ℂ v then 1 else 0)) := by
  have h : (gramMatrix v).det = 0 ↔ ¬ LinearIndependent ℂ v := by
    simpa only [not_not] using (det_gramMatrix_ne_zero_iff v).not
  simpa only [norm_eq_zero, h] using tendsto_detection ‖(gramMatrix v).det‖

/-- Simultaneous classification of linear dependence in a finite family of frames. -/
theorem cox_linear_dependence_family {ι : Type*} [Fintype ι] {n : ℕ}
    (v : ι → Fin n → E) :
    Tendsto (fun K => (binaryLaw K (fun i => ‖(gramMatrix (v i)).det‖)).real
      {b | b ≠ fun i => decide (¬ LinearIndependent ℂ (v i))}) atTop (𝓝 0) := by
  have h (i : ι) : (gramMatrix (v i)).det = 0 ↔ ¬ LinearIndependent ℂ (v i) := by
    simpa only [not_not] using (det_gramMatrix_ne_zero_iff (v i)).not
  exact tendsto_classification_error (fun i => ‖(gramMatrix (v i)).det‖)
    (fun i => ¬ LinearIndependent ℂ (v i)) fun i => by
    simp only [norm_eq_zero, h]

/-- Frame-output detection identifies directions invisible to all frame readings. -/
theorem cox_frame_invisibility [CompleteSpace E] {ι : Type*} [Fintype ι] (v : ι → E) (x : E) :
    Tendsto (fun K => detection K ‖frameOperator v x‖) atTop
      (𝓝 (if ∀ i, inner ℂ (v i) x = 0 then 1 else 0)) := by
  simpa only [norm_eq_zero, _root_.HilbertMetric.finite_frame_eq_zero_iff] using
    tendsto_detection ‖frameOperator v x‖

/-- Every test direction in a finite list is classified for frame invisibility. -/
theorem cox_frame_invisibility_family [CompleteSpace E] {ι τ : Type*} [Fintype ι] [Fintype τ]
    (v : ι → E) (x : τ → E) :
    Tendsto (fun K => (binaryLaw K (fun j => ‖frameOperator v (x j)‖)).real
      {b | b ≠ fun j => decide (∀ i, inner ℂ (v i) (x j) = 0)}) atTop (𝓝 0) := by
  exact tendsto_classification_error (fun j => ‖frameOperator v (x j)‖)
    (fun j => ∀ i, inner ℂ (v i) (x j) = 0) fun j => by
    simp only [norm_eq_zero, _root_.HilbertMetric.finite_frame_eq_zero_iff]

variable [FiniteDimensional ℂ E]

/-- Polar normalization changes finite probabilities but preserves their limiting classification. -/
theorem cox_polar_kernel (T : E →L[ℂ] E) (x : E) :
    Tendsto (fun K => detection K ‖_root_.HilbertMetric.finitePolar T x‖) atTop
      (𝓝 (if T x = 0 then 1 else 0)) := by
  simpa only [norm_eq_zero, _root_.HilbertMetric.finitePolar_eq_zero_iff] using
    tendsto_detection ‖_root_.HilbertMetric.finitePolar T x‖

/-- Polar-normalized tests recover the original operator's kernel on finite lists. -/
theorem cox_polar_kernel_family {ι : Type*} [Fintype ι]
    (T : E →L[ℂ] E) (x : ι → E) :
    Tendsto (fun K => (binaryLaw K (fun i => ‖_root_.HilbertMetric.finitePolar T (x i)‖)).real
      {b | b ≠ fun i => decide (T (x i) = 0)}) atTop (𝓝 0) := by
  exact tendsto_classification_error (fun i => ‖_root_.HilbertMetric.finitePolar T (x i)‖)
    (fun i => T (x i) = 0) fun i => by
    simp only [norm_eq_zero, _root_.HilbertMetric.finitePolar_eq_zero_iff]

/-- Positive Gram shadows detect exactly the operators with nontrivial kernel. -/
theorem cox_operator_singularity {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] (A : E →L[ℂ] W) :
    Tendsto (fun K => detection K ‖(gramOperator A).det‖) atTop
      (𝓝 (if A.ker ≠ ⊥ then 1 else 0)) := by
  simpa only [norm_eq_zero, gramOperator_det_eq_zero_iff] using
    tendsto_detection ‖(gramOperator A).det‖

/-- Finite operator families have consistent simultaneous rank-loss classification. -/
theorem cox_operator_singularity_family {ι W : Type*} [Fintype ι]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (A : ι → E →L[ℂ] W) :
    Tendsto (fun K => (binaryLaw K (fun i => ‖(gramOperator (A i)).det‖)).real
      {b | b ≠ fun i => decide ((A i).ker ≠ ⊥)}) atTop (𝓝 0) := by
  exact tendsto_classification_error (fun i => ‖(gramOperator (A i)).det‖)
    (fun i => (A i).ker ≠ ⊥) fun i => by
    simp only [norm_eq_zero, gramOperator_det_eq_zero_iff]

end GaloisForLFunctions.HilbertMetric

#print axioms GaloisForLFunctions.HilbertMetric.cox_gaussian_collision
#print axioms GaloisForLFunctions.HilbertMetric.cox_gaussian_family
#print axioms GaloisForLFunctions.HilbertMetric.cox_linear_dependence
#print axioms GaloisForLFunctions.HilbertMetric.cox_linear_dependence_family
#print axioms GaloisForLFunctions.HilbertMetric.cox_frame_invisibility
#print axioms GaloisForLFunctions.HilbertMetric.cox_frame_invisibility_family
#print axioms GaloisForLFunctions.HilbertMetric.cox_polar_kernel
#print axioms GaloisForLFunctions.HilbertMetric.cox_polar_kernel_family
#print axioms GaloisForLFunctions.HilbertMetric.cox_operator_singularity
#print axioms GaloisForLFunctions.HilbertMetric.cox_operator_singularity_family
