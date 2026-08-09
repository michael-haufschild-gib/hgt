import Mathlib

/-!
# The propagator of a self-adjoint operator

The exponential of an operator acts on each of its eigenvectors by the exponential of the
eigenvalue: the series is evaluated one term at a time and collapses to the scalar series.  So the
propagator of a self-adjoint generator fixes every eigenline of that generator.

A real multiple of `-i` times a self-adjoint operator is skew-adjoint, which is the hypothesis
mathlib's unitarity criterion for the exponential wants.
-/

open scoped InnerProductSpace

noncomputable section

namespace HTGeometry

/-- **The exponential acts on an eigenvector by the exponential of the eigenvalue.** -/
theorem exp_apply_of_eigen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (A : E →L[ℂ] E) (μ : ℂ) (ψ : E) (h : A ψ = μ • ψ) :
    (NormedSpace.exp A) ψ = Complex.exp μ • ψ := by
  have hpow : ∀ n : ℕ, (A ^ n) ψ = μ ^ n • ψ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, mul_apply_eq_comp, h, map_smul, ih, smul_smul, pow_succ,
          mul_comm]
  have hsum : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ • (A ^ n)) (NormedSpace.exp A) :=
    (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) A).congr_fun fun n =>
      (NormedSpace.expSeries_apply_eq (𝕂 := ℂ) A n).symm
  have happ := (ContinuousLinearMap.apply ℂ E ψ).hasSum hsum
  have hval : HasSum (fun n : ℕ => (((n.factorial : ℂ))⁻¹ * μ ^ n) • ψ)
      ((NormedSpace.exp A) ψ) := by
    refine happ.congr_fun fun n => ?_
    show (((n.factorial : ℂ))⁻¹ * μ ^ n) • ψ = ((n.factorial : ℂ))⁻¹ • (A ^ n) ψ
    rw [hpow n, smul_smul]
  have hscal : HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * μ ^ n) (Complex.exp μ) := by
    have h := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) μ).congr_fun fun n =>
      (NormedSpace.expSeries_apply_eq (𝕂 := ℂ) μ n).symm
    rw [← congrFun Complex.exp_eq_exp_ℂ μ] at h
    simpa [smul_eq_mul] using h
  exact hval.unique (hscal.smul_const ψ)

/-- A real multiple of `-i` times a self-adjoint operator is skew-adjoint. -/
theorem neg_I_smul_mem_skewAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ) :
    (-(t : ℂ) * Complex.I) • H ∈ skewAdjoint (E →L[ℂ] E) := by
  rw [skewAdjoint.mem_iff, star_smul, hH.star_eq]
  rw [show star (-(t : ℂ) * Complex.I) = (t : ℂ) * Complex.I by
    simp [star_mul', Complex.conj_I]]
  rw [← neg_smul]
  congr 1
  ring

/-! ## The rational base for the operator exponential

Mathlib's unitarity criterion for the exponential is stated over `ℚ`, and the operator algebra of a
complex normed space carries no rational structure by default — not even a `SMul ℚ`.  There is
therefore no diamond to avoid: the rational algebra can be defined outright, through the complex
scalars, and the norm inequality is the complex one.  The instances are scoped, so a module opts in
rather than having them imposed. -/

namespace RationalOperatorScalars

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Rational scalars on the operator algebra, through the complex ones. -/
scoped instance ratAlgebraCLM : Algebra ℚ (E →L[ℂ] E) :=
  Algebra.compHom _ (algebraMap ℚ ℂ)

theorem ratSMul_eq (q : ℚ) (A : E →L[ℂ] E) : q • A = ((q : ℂ)) • A := by
  rw [Algebra.smul_def]
  show ((algebraMap ℂ (E →L[ℂ] E)) ((algebraMap ℚ ℂ) q)) * A = ((q : ℂ)) • A
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  norm_cast

theorem norm_ratCast_complex (q : ℚ) : ‖((q : ℚ) : ℂ)‖ = ‖q‖ := by
  rw [show ((q : ℚ) : ℂ) = ((q : ℝ) : ℂ) by norm_cast, Complex.norm_real, Rat.norm_cast_real]

/-- The rational scalars are a normed algebra. -/
scoped instance ratNormedAlgebraCLM : NormedAlgebra ℚ (E →L[ℂ] E) where
  norm_smul_le q A := by
    rw [ratSMul_eq, norm_smul, norm_ratCast_complex]

end RationalOperatorScalars

open scoped RationalOperatorScalars in
/-- **The propagator of a self-adjoint generator is unitary.** -/
theorem exp_neg_I_smul_mem_unitary {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ) :
    NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) ∈ unitary (E →L[ℂ] E) :=
  NormedSpace.exp_mem_unitary_of_mem_skewAdjoint (neg_I_smul_mem_skewAdjoint hH t)

/-- A unitary continuous linear map preserves norms. -/
theorem norm_apply_of_mem_unitary {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {U : E →L[ℂ] E}
    (hU : U ∈ unitary (E →L[ℂ] E)) (x : E) : ‖U x‖ = ‖x‖ := by
  have hstar : (ContinuousLinearMap.adjoint U) * U = 1 := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact hU.1
  have hinner : (⟪U x, U x⟫_ℂ) = ⟪x, x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    have h := congrArg (fun T : E →L[ℂ] E => T x) hstar
    simp only [mul_apply_eq_comp, one_apply_eq_self] at h
    rw [h]
  have hsq : ‖U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), hinner]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

open scoped RationalOperatorScalars in
/-- The propagator of a self-adjoint generator, as a linear isometry. -/
def selfAdjointPropagator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ) : E →ₗᵢ[ℂ] E where
  toLinearMap := (NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) : E →L[ℂ] E)
  norm_map' x := norm_apply_of_mem_unitary (exp_neg_I_smul_mem_unitary hH t) x

@[simp] theorem selfAdjointPropagator_apply {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ)
    (x : E) :
    selfAdjointPropagator hH t x = NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) x := rfl

/-- **The propagator fixes every eigenline of its generator.** -/
theorem selfAdjointPropagator_apply_eigen {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] {H : E →L[ℂ] E} (hH : IsSelfAdjoint H) (t : ℝ)
    (μ : ℂ) (ψ : E) (h : H ψ = μ • ψ) :
    selfAdjointPropagator hH t ψ = Complex.exp ((-(t : ℂ) * Complex.I) * μ) • ψ := by
  rw [selfAdjointPropagator_apply]
  refine exp_apply_of_eigen _ _ ψ ?_
  rw [smul_apply, h, smul_smul]

end HTGeometry

end
