import GaloisForLFunctions.HTGeometry.GaussianCovarianceStableRankLowerTail
import GaloisForLFunctions.HTGeometry.GaussianSignedPermutationInvariance

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Activation interval chosen opposite the affine centre. -/
def gaussianAffineActivation (a x : ℝ) : ℝ :=
  if a ≤ 0 then gaussianIntervalActivation x
  else gaussianIntervalActivation (-x)

theorem gaussianAffineActivation_measurable (a : ℝ) :
    Measurable (gaussianAffineActivation a) := by
  unfold gaussianAffineActivation
  split_ifs
  · exact gaussianIntervalActivation_measurable
  · exact gaussianIntervalActivation_measurable.comp measurable_neg

theorem gaussianAffineActivation_mem_Icc (a x : ℝ) :
    gaussianAffineActivation a x ∈ Icc (0 : ℝ) 1 := by
  unfold gaussianAffineActivation
  split_ifs
  · exact gaussianIntervalActivation_mem_Icc x
  · exact gaussianIntervalActivation_mem_Icc (-x)

theorem integral_gaussianIntervalActivation_neg :
    ∫ x, gaussianIntervalActivation (-x) ∂gaussianReal 0 1 =
      gaussianIntervalActivationMass := by
  calc
    (∫ x, gaussianIntervalActivation (-x) ∂gaussianReal 0 1) =
        ∫ x, gaussianIntervalActivation x ∂gaussianReal 0 1 :=
      (measurePreserving_neg_gaussianReal 1).integral_comp
        measurableEmbedding_neg gaussianIntervalActivation
    _ = gaussianIntervalActivationMass :=
      integral_gaussianIntervalActivation

theorem integral_gaussianAffineActivation (a : ℝ) :
    ∫ x, gaussianAffineActivation a x ∂gaussianReal 0 1 =
      gaussianIntervalActivationMass := by
  unfold gaussianAffineActivation
  split_ifs
  · exact integral_gaussianIntervalActivation
  · exact integral_gaussianIntervalActivation_neg

theorem gaussianAffineActivation_le_sq_sub (a x : ℝ) :
    gaussianAffineActivation a x ≤ (x - a) ^ 2 := by
  unfold gaussianAffineActivation gaussianIntervalActivation
  by_cases ha : a ≤ 0
  · rw [if_pos ha]
    by_cases hx : x ∈ Icc (1 : ℝ) 2
    · rw [Set.indicator_of_mem hx]
      have hxa : 1 ≤ x - a := by linarith [hx.1]
      nlinarith [sq_nonneg (x - a - 1)]
    · rw [Set.indicator_of_notMem hx]
      positivity
  · rw [if_neg ha]
    by_cases hx : -x ∈ Icc (1 : ℝ) 2
    · rw [Set.indicator_of_mem hx]
      have hxa : x - a ≤ -1 := by linarith [hx.1]
      nlinarith [sq_nonneg (x - a + 1)]
    · rw [Set.indicator_of_notMem hx]
      positivity

/-- Affine stable-rank Gaussian lower tail, uniform in every deterministic
centre.  No determinant or smallest singular value is used. -/
theorem measure_pi_gaussian_weighted_shifted_sq_sum_le
    {I : Type*} [Fintype I] (weight : I → ℝ≥0)
    (center : I → ℝ) {θ : ℝ}
    (hθ : θ ≤ gaussianIntervalActivationMass) :
    (Measure.pi fun _ : I => gaussianReal 0 1).real
        {x | ∑ i, (weight i : ℝ) * (x i - center i) ^ 2 ≤
          θ * ∑ i, (weight i : ℝ)} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i, (weight i : ℝ)) ^ 2 /
          ∑ i, (weight i : ℝ) ^ 2) := by
  let B : I → (I → ℝ) → ℝ :=
    fun i x => gaussianAffineActivation (center i) (x i)
  have hindep : iIndepFun B (Measure.pi fun _ : I => gaussianReal 0 1) := by
    exact iIndepFun_pi fun i =>
      (gaussianAffineActivation_measurable (center i)).aemeasurable
  have hmeas : ∀ i, AEMeasurable (B i)
      (Measure.pi fun _ : I => gaussianReal 0 1) := by
    intro i
    exact ((gaussianAffineActivation_measurable (center i)).comp
      (measurable_pi_apply i)).aemeasurable
  have hbound : ∀ i, ∀ᵐ x ∂(Measure.pi fun _ : I => gaussianReal 0 1),
      B i x ∈ Icc (0 : ℝ) 1 := by
    intro i
    exact Filter.Eventually.of_forall fun x =>
      gaussianAffineActivation_mem_Icc (center i) (x i)
  have hmean : ∀ i, ∫ x, B i x
      ∂(Measure.pi fun _ : I => gaussianReal 0 1) =
        gaussianIntervalActivationMass := by
    intro i
    rw [MeasureTheory.integral_comp_eval
      (gaussianAffineActivation_measurable (center i)).aestronglyMeasurable]
    exact integral_gaussianAffineActivation (center i)
  have hbern := measure_weightedBernoulli_sum_le_of_iIndepFun
    hindep hmeas hbound hmean hθ weight
  apply (measureReal_mono ?_).trans hbern
  intro x hx
  have hsum :
      ∑ i, (weight i : ℝ) *
          gaussianAffineActivation (center i) (x i) ≤
        ∑ i, (weight i : ℝ) * (x i - center i) ^ 2 := by
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left
        (gaussianAffineActivation_le_sq_sub (center i) (x i))
        (weight i).coe_nonneg
  exact hsum.trans hx

/-- Coordinate-free affine lower tail for a positive symmetric quadratic
form under standard Gaussian measure. -/
theorem stdGaussian_measure_symmetric_shifted_quadratic_le
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℝ E = n)
    (hpos : ∀ i, 0 ≤ hT.eigenvalues hn i) (z : E) {θ : ℝ}
    (hθ : θ ≤ gaussianIntervalActivationMass) :
    (stdGaussian E).real
        {v | inner ℝ (v - z) (T (v - z)) ≤
          θ * ∑ i, hT.eigenvalues hn i} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i, hT.eigenvalues hn i) ^ 2 /
          ∑ i, (hT.eigenvalues hn i) ^ 2) := by
  let b := hT.eigenvectorBasis hn
  let weight : Fin n → ℝ≥0 :=
    fun i => ⟨hT.eigenvalues hn i, hpos i⟩
  let center : Fin n → ℝ := fun i => b.repr z i
  have hsynth : Measurable (fun x : Fin n → ℝ => ∑ i, x i • b i) := by
    fun_prop
  have hevent :
      (fun x : Fin n → ℝ => ∑ i, x i • b i) ⁻¹'
          {v | inner ℝ (v - z) (T (v - z)) ≤
            θ * ∑ i, hT.eigenvalues hn i} =
        {x | ∑ i, (weight i : ℝ) * (x i - center i) ^ 2 ≤
          θ * ∑ i, (weight i : ℝ)} := by
    ext x
    simp only [mem_preimage, mem_setOf_eq]
    rw [real_inner_apply_eq_sum_eigenvalues hT hn]
    have hsynth_eq : (∑ j, x j • b j) =
        b.repr.symm (WithLp.toLp 2 x) := by
      simpa using b.sum_repr_symm (WithLp.toLp 2 x)
    have hcoord : ∀ i,
        (hT.eigenvectorBasis hn).repr
            ((∑ j, x j • b j) - z) i = x i - center i := by
      intro i
      change b.repr ((∑ j, x j • b j) - z) i =
        x i - b.repr z i
      rw [map_sub, hsynth_eq]
      simp
    have hleft :
        (∑ i, hT.eigenvalues hn i *
          ((hT.eigenvectorBasis hn).repr
            ((∑ j, x j • b j) - z) i) ^ 2) =
        ∑ i, (weight i : ℝ) * (x i - center i) ^ 2 := by
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
    have hcoe : ∀ i, (weight i : ℝ) = hT.eigenvalues hn i :=
      fun _ => rfl
    simpa only [Measure.real, hcoe] using
      measure_pi_gaussian_weighted_shifted_sq_sum_le
        weight center hθ
  · exact measurableSet_le (by fun_prop) (by fun_prop)

/-- Every affine target has a least-squares domain centre whose homogeneous
residual is no larger than the original residual. -/
theorem exists_linearMap_translate_norm_le_affine_norm
    {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) (y : F) :
    ∃ z : E, ∀ x : E, ‖A (x - z)‖ ≤ ‖A x - y‖ := by
  let S : Submodule ℝ F := A.range
  let py : S := S.orthogonalProjectionOnto y
  obtain ⟨z, hz⟩ := py.property
  refine ⟨z, fun x => ?_⟩
  have hproj : S.orthogonalProjectionOnto (A x - y) =
      ⟨A (x - z), A.mem_range_self (x - z)⟩ := by
    apply Subtype.ext
    change S.starProjection (A x - y) = A (x - z)
    rw [map_sub]
    have hAx : S.starProjection (A x) = A x :=
      S.starProjection_mem_subspace_eq_self ⟨A x, A.mem_range_self x⟩
    rw [hAx]
    change A x - (py : F) = A (x - z)
    rw [← hz]
    simp
  calc
    ‖A (x - z)‖ = ‖S.orthogonalProjectionOnto (A x - y)‖ := by
      simp [hproj]
    _ ≤ ‖A x - y‖ := S.norm_orthogonalProjectionOnto_apply_le _

/-- Uniform affine stable-rank lower tail for every target of an arbitrary
finite-dimensional linear observer map. -/
theorem stdGaussian_measure_linearMap_affine_norm_sq_le
    {n : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →ₗ[ℝ] F) (y : F) (hn : Module.finrank ℝ E = n)
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (stdGaussian E).real
        {v | ‖A v - y‖ ^ 2 ≤
          θ * ∑ i,
            A.isSymmetric_adjoint_comp_self.eigenvalues hn i} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i,
              A.isSymmetric_adjoint_comp_self.eigenvalues hn i) ^ 2 /
          ∑ i,
            (A.isSymmetric_adjoint_comp_self.eigenvalues hn i) ^ 2) := by
  obtain ⟨z, hz⟩ := exists_linearMap_translate_norm_le_affine_norm A y
  have hquad := stdGaussian_measure_symmetric_shifted_quadratic_le
    A.isSymmetric_adjoint_comp_self hn
    (fun i => A.isPositive_adjoint_comp_self.nonneg_eigenvalues hn i)
    z hθ
  apply (measureReal_mono ?_).trans hquad
  intro v hv
  simp only [mem_setOf_eq] at hv ⊢
  have hnormsq : ‖A (v - z)‖ ^ 2 ≤ ‖A v - y‖ ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (hz v) 2
  have hinner : inner ℝ (v - z) ((A.adjoint ∘ₗ A) (v - z)) =
      ‖A (v - z)‖ ^ 2 := by
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right,
      real_inner_self_eq_norm_sq]
  rw [hinner]
  exact hnormsq.trans hv

theorem stdGaussian_measure_linearMap_affine_norm_sq_le_singularValues
    {n : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →ₗ[ℝ] F) (y : F) (hn : Module.finrank ℝ E = n)
    {θ : ℝ} (hθ : θ ≤ gaussianIntervalActivationMass) :
    (stdGaussian E).real
        {v | ‖A v - y‖ ^ 2 ≤
          θ * ∑ i : Fin n, A.singularValues i ^ 2} ≤
      Real.exp
        (-2 * (gaussianIntervalActivationMass - θ) ^ 2 *
            (∑ i : Fin n, A.singularValues i ^ 2) ^ 2 /
          ∑ i : Fin n, A.singularValues i ^ 4) := by
  have h := stdGaussian_measure_linearMap_affine_norm_sq_le A y hn hθ
  have hpow : ∀ i : Fin n,
      (A.singularValues i ^ 2) ^ 2 = A.singularValues i ^ 4 := by
    intro i
    ring
  simpa only [← A.sq_singularValues_fin hn, hpow] using h

theorem stdGaussian_measure_linearMap_affine_norm_sq_le_halfActivation
    {n : ℕ} {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →ₗ[ℝ] F) (y : F) (hn : Module.finrank ℝ E = n) :
    (stdGaussian E).real
        {v | ‖A v - y‖ ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i : Fin n, A.singularValues i ^ 2} ≤
      Real.exp
        (-(gaussianIntervalActivationMass ^ 2 / 2) *
          ((∑ i : Fin n, A.singularValues i ^ 2) ^ 2 /
            ∑ i : Fin n, A.singularValues i ^ 4)) := by
  have h := stdGaussian_measure_linearMap_affine_norm_sq_le_singularValues
    A y hn (θ := gaussianIntervalActivationMass / 2)
    (by linarith [gaussianIntervalActivationMass_pos])
  apply h.trans_eq
  congr 1
  ring

/-- Complete finite affine circuit-tube union.  Every target centre is allowed;
the sole quantitative invariant is a common Gram stable-rank floor. -/
theorem stdGaussian_measure_iUnion_linearMap_affine_norm_sq_le_halfActivation
    {n : ℕ} {C E F : Type*} [Fintype C]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : C → E →ₗ[ℝ] F) (target : C → F)
    (hn : Module.finrank ℝ E = n) (stableFloor : ℝ)
    (hstable : ∀ c,
      stableFloor ≤
        (∑ i : Fin n, (A c).singularValues i ^ 2) ^ 2 /
          ∑ i : Fin n, (A c).singularValues i ^ 4) :
    (stdGaussian E).real
        (⋃ c, {v | ‖A c v - target c‖ ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i : Fin n, (A c).singularValues i ^ 2}) ≤
      (Fintype.card C : ℝ) *
        Real.exp
          (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
  calc
    (stdGaussian E).real
        (⋃ c, {v | ‖A c v - target c‖ ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i : Fin n, (A c).singularValues i ^ 2}) ≤
      ∑ c, (stdGaussian E).real
        {v | ‖A c v - target c‖ ^ 2 ≤
          (gaussianIntervalActivationMass / 2) *
            ∑ i : Fin n, (A c).singularValues i ^ 2} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : C,
        Real.exp
          (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
      apply Finset.sum_le_sum
      intro c _
      refine
        (stdGaussian_measure_linearMap_affine_norm_sq_le_halfActivation
          (A c) (target c) hn).trans ?_
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonpos_left (hstable c)
        (neg_nonpos.mpr (by positivity))
    _ = (Fintype.card C : ℝ) *
        Real.exp
          (-(gaussianIntervalActivationMass ^ 2 / 2) * stableFloor) := by
      simp

end

end GaloisForLFunctions.HTGeometry
