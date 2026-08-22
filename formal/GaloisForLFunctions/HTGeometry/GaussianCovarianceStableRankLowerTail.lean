import GaloisForLFunctions.HTGeometry.GaussianStableRankLowerTail
import Mathlib.Analysis.InnerProductSpace.SingularValues

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem real_inner_apply_eq_sum_eigenvalues
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n) (v : E) :
    inner ℝ v (T v) =
      ∑ i, hT.eigenvalues hn i *
        ((hT.eigenvectorBasis hn).repr v i) ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).sum_inner_mul_inner v (T v)]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm ((hT.eigenvectorBasis hn) i) v,
    ← (hT.eigenvectorBasis hn).repr_apply_apply,
    ← (hT.eigenvectorBasis hn).repr_apply_apply,
    hT.eigenvectorBasis_apply_self_apply hn]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  ring

theorem stdGaussian_measure_symmetric_quadratic_le
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (hpos : ∀ i, 0 ≤ hT.eigenvalues hn i) {θ : ℝ}
    (hθ : θ ≤ gaussianIntervalActivationMass) :
    (stdGaussian E).real
        {v | inner ℝ v (T v) ≤
          θ * ∑ i, hT.eigenvalues hn i} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i, hT.eigenvalues hn i) ^ 2 /
          ∑ i, (hT.eigenvalues hn i) ^ 2) := by
  let b := hT.eigenvectorBasis hn
  let weight : Fin n → ℝ≥0 := fun i => ⟨hT.eigenvalues hn i, hpos i⟩
  have hsynth : Measurable (fun x : Fin n → ℝ => ∑ i, x i • b i) := by
    fun_prop
  have hevent :
      (fun x : Fin n → ℝ => ∑ i, x i • b i) ⁻¹'
          {v | inner ℝ v (T v) ≤ θ * ∑ i, hT.eigenvalues hn i} =
        {x | ∑ i, (weight i : ℝ) * x i ^ 2 ≤
          θ * ∑ i, (weight i : ℝ)} := by
    ext x
    simp only [mem_preimage, mem_setOf_eq]
    rw [real_inner_apply_eq_sum_eigenvalues hT hn]
    have hcoord : ∀ i,
        (hT.eigenvectorBasis hn).repr (∑ j, x j • b j) i = x i := by
      intro i
      have hsynth_eq : (∑ j, x j • b j) =
          b.repr.symm (WithLp.toLp 2 x) := by
        simpa using b.sum_repr_symm (WithLp.toLp 2 x)
      rw [hsynth_eq]
      change b.repr (b.repr.symm (WithLp.toLp 2 x)) i = x i
      simp
    have hleft :
        (∑ i, hT.eigenvalues hn i *
          ((hT.eigenvectorBasis hn).repr (∑ j, x j • b j) i) ^ 2) =
        ∑ i, (weight i : ℝ) * x i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hcoord i]
      rfl
    have hright : (∑ i, hT.eigenvalues hn i) =
        ∑ i, (weight i : ℝ) := by rfl
    rw [hleft, hright]
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [Measure.real, Measure.map_apply hsynth]
  · rw [hevent]
    have hcoe : ∀ i, (weight i : ℝ) = hT.eigenvalues hn i := fun _ => rfl
    simpa only [Measure.real, hcoe] using
      measure_pi_gaussian_weighted_sq_sum_le weight hθ
  · exact measurableSet_le (by fun_prop) (by fun_prop)

/-- Stable-rank lower tail for the norm of an arbitrary finite-dimensional
linear Gaussian image, expressed through the Gram spectrum. -/
theorem stdGaussian_measure_linearMap_norm_sq_le
    {n : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n)
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (stdGaussian E).real
        {v | ‖A v‖ ^ 2 ≤
          θ * ∑ i,
            A.isSymmetric_adjoint_comp_self.eigenvalues hn i} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i,
              A.isSymmetric_adjoint_comp_self.eigenvalues hn i) ^ 2 /
          ∑ i,
            (A.isSymmetric_adjoint_comp_self.eigenvalues hn i) ^ 2) := by
  have hquad := stdGaussian_measure_symmetric_quadratic_le
    A.isSymmetric_adjoint_comp_self hn
    (fun i => A.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i) hθ
  have hevent :
      {v : E | ‖A v‖ ^ 2 ≤
          θ * ∑ i,
            A.isSymmetric_adjoint_comp_self.eigenvalues hn i} =
        {v : E | inner ℝ v ((A.adjoint ∘ₗ A) v) ≤
          θ * ∑ i,
            A.isSymmetric_adjoint_comp_self.eigenvalues hn i} := by
    ext v
    simp only [mem_setOf_eq]
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
      real_inner_self_eq_norm_sq]
  rw [hevent]
  exact hquad

/-- Singular-value form of the arbitrary linear-image lower tail.  Its
exponent is the stable rank of the Gram covariance: `(sum σ²)² / sum σ⁴`. -/
theorem stdGaussian_measure_linearMap_norm_sq_le_singularValues
    {n : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n)
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (stdGaussian E).real
        {v | ‖A v‖ ^ 2 ≤
          θ * ∑ i : Fin n, A.singularValues i ^ 2} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i : Fin n, A.singularValues i ^ 2) ^ 2 /
          ∑ i : Fin n, A.singularValues i ^ 4) := by
  have h := stdGaussian_measure_linearMap_norm_sq_le A hn hθ
  have hpow : ∀ i : Fin n,
      (A.singularValues i ^ 2) ^ 2 = A.singularValues i ^ 4 := by
    intro i
    ring
  simpa only [← A.sq_singularValues_fin hn, hpow] using h

theorem stdGaussian_measure_linearMap_norm_sq_le_halfActivation
    {n : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n) :
    (stdGaussian E).real
        {v | ‖A v‖ ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i : Fin n, A.singularValues i ^ 2} ≤
      Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) *
          ((∑ i : Fin n, A.singularValues i ^ 2) ^ 2 /
            ∑ i : Fin n, A.singularValues i ^ 4)) := by
  have h := stdGaussian_measure_linearMap_norm_sq_le_singularValues
    A hn (θ := gaussianIntervalActivationMass / 2)
    (by linarith [gaussianIntervalActivationMass_pos])
  apply h.trans_eq
  congr 1
  ring

/-- A finite family of linear observer maps pays only its cardinality, provided
their Gram stable ranks share a common floor. -/
theorem stdGaussian_measure_iUnion_linearMap_norm_sq_le_halfActivation
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : C → E →ₗ[ℝ] F) (hn : Module.finrank ℝ E = n)
    (stableFloor : ℝ)
    (hstable : ∀ c,
      stableFloor ≤
        (∑ i : Fin n, (A c).singularValues i ^ 2) ^ 2 /
          ∑ i : Fin n, (A c).singularValues i ^ 4) :
    (stdGaussian E).real
        (⋃ c, {v | ‖A c v‖ ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i : Fin n, (A c).singularValues i ^ 2}) ≤
      (Fintype.card C : ℝ) *
        Real.exp
          (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
  calc
    (stdGaussian E).real
        (⋃ c, {v | ‖A c v‖ ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i : Fin n, (A c).singularValues i ^ 2}) ≤
      ∑ c, (stdGaussian E).real
        {v | ‖A c v‖ ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i : Fin n, (A c).singularValues i ^ 2} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : C,
        Real.exp
          (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
      apply Finset.sum_le_sum
      intro c _
      refine (stdGaussian_measure_linearMap_norm_sq_le_halfActivation
        (A c) hn).trans ?_
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hstable c)
        (neg_nonpos.mpr (by positivity))
    _ = (Fintype.card C : ℝ) *
        Real.exp
          (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
      simp

end

end GaloisForLFunctions.HTGeometry
