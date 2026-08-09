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

end HTGeometry

end
