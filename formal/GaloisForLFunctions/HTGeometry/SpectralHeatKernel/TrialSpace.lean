import GaloisForLFunctions.HTGeometry.SpectralHeatKernel.MinMax

/-!
# Trial spaces of orthogonal functions

Proposition 6.1 of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues of the
Laplacian* (arXiv:2509.06151v2), bounds the small eigenvalues by exhibiting `N` trial functions with
pairwise disjoint supports, unit norm, and Dirichlet energy at most `K/log|s|⁻¹`.  Disjoint supports
make the family orthogonal, hence linearly independent, so its span has dimension `N`; the min–max
principle then bounds `λ_{N−1}`.

This file supplies the dimension step: an orthogonal family of nonzero vectors spans a space of the
expected dimension, and therefore certifies the eigenvalue bound.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Normalizing an orthogonal family of nonzero vectors gives an orthonormal family. -/
theorem orthonormal_normalize {ι : Type*} {ψ : ι → E}
    (hne : ∀ i, ψ i ≠ 0) (horth : ∀ i j, i ≠ j → (inner ℂ (ψ i) (ψ j) : ℂ) = 0) :
    Orthonormal ℂ fun i => ((‖ψ i‖ : ℂ))⁻¹ • ψ i := by
  constructor
  · intro i
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hne i))
  · intro i j hij
    rw [inner_smul_left, inner_smul_right, horth i j hij, mul_zero, mul_zero]

/-- An orthogonal family of nonzero vectors is linearly independent. -/
theorem linearIndependent_of_orthogonal {ι : Type*} {ψ : ι → E}
    (hne : ∀ i, ψ i ≠ 0) (horth : ∀ i j, i ≠ j → (inner ℂ (ψ i) (ψ j) : ℂ) = 0) :
    LinearIndependent ℂ ψ := by
  have hon := (orthonormal_normalize hne horth).linearIndependent
  have hunits : ∀ i, ((‖ψ i‖ : ℂ)) ≠ 0 := fun i => by
    simpa using norm_ne_zero_iff.mpr (hne i)
  have hsmul : (fun i => ((‖ψ i‖ : ℂ)) • (((‖ψ i‖ : ℂ))⁻¹ • ψ i)) = ψ := by
    funext i
    rw [smul_smul, mul_inv_cancel₀ (hunits i), one_smul]
  rw [← hsmul]
  exact hon.units_smul fun i => Units.mk0 _ (hunits i)

/-- The span of an orthogonal family of `n` nonzero vectors has dimension `n`. -/
theorem finrank_span_of_orthogonal {n : ℕ} {ψ : Fin n → E}
    (hne : ∀ i, ψ i ≠ 0) (horth : ∀ i j, i ≠ j → (inner ℂ (ψ i) (ψ j) : ℂ) = 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range ψ)) = n := by
  have h := finrank_span_eq_card (R := ℂ) (linearIndependent_of_orthogonal hne horth)
  simpa using h

/-- **Proposition 6.1's certificate.**

An orthogonal family of `k+1` nonzero trial vectors on whose span the spectral quadratic form is at
most `M‖v‖²` forces `λ_k ≤ M`. -/
theorem spectral_eigenvalue_le_of_orthogonal_trial
    (b : HilbertBasis ℕ ℂ E) {lam : ℕ → ℝ} (hmono : Monotone lam)
    {k : ℕ} {ψ : Fin (k + 1) → E}
    (hne : ∀ i, ψ i ≠ 0) (horth : ∀ i j, i ≠ j → (inner ℂ (ψ i) (ψ j) : ℂ) = 0)
    {M : ℝ}
    (hsum : ∀ v ∈ Submodule.span ℂ (Set.range ψ),
      Summable fun n => lam n * ‖(inner ℂ (b n) v : ℂ)‖ ^ 2)
    (hQ : ∀ v ∈ Submodule.span ℂ (Set.range ψ), spectralQuadratic b lam v ≤ M * ‖v‖ ^ 2) :
    lam k ≤ M := by
  have hdim : Module.finrank ℂ (Submodule.span ℂ (Set.range ψ)) = k + 1 :=
    finrank_span_of_orthogonal hne horth
  refine spectral_eigenvalue_le_of_trial b hmono (V := Submodule.span ℂ (Set.range ψ)) ?_ hsum hQ
  rw [hdim]
  omega

end GaloisForLFunctions.HTGeometry
