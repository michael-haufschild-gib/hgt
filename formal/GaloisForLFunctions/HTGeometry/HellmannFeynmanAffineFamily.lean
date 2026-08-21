import GaloisForLFunctions.HTGeometry.HellmannFeynmanUnconditional

/-!
# Hellmann–Feynman for the affine family `H(λ) = H₀ + λ V`

This is the theorem in the form physics states it.  For a Hamiltonian depending affinely on a coupling,

```text
H(λ) = H₀ + λ V,       H₀, V self-adjoint,
```

with a simple isolated eigenvalue `nu_0` at the normalized state `psi_0`, there is a differentiable branch of
normalized eigenstates through `psi_0`, its energy is a real-valued differentiable function of the coupling,
and

```text
dE/dλ = ⟪psi_0, V psi_0⟫.
```

Every hypothesis is a property of `H₀`, `V` and the eigenpair; in particular the strict differentiability of
the family — an awkward input in the general statement — is *proved* here, since an affine family is its own
derivative.  In finite dimensions the isolation hypothesis is dropped as well: a simple eigenvalue of a
finite-dimensional Hermitian family is automatically isolated, so simplicity alone gives the theorem.
-/

noncomputable section

open scoped InnerProductSpace
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **An affine family is strictly differentiable**, with the perturbation as its derivative datum:
`(dH/dλ) psi_0 = V psi_0`. -/
theorem hasStrictFDerivAt_affineFamily (A₀ B : E →L[𝕜] E) (c₀ : ℝ) (ψ₀ : E) :
    HasStrictFDerivAt (fun q : ℝ × E => (A₀ + q.1 • B) q.2)
      (familyDerivRC (A₀ + c₀ • B) (B ψ₀)) (c₀, ψ₀) := by
  have hsnd : HasStrictFDerivAt (fun q : ℝ × E => q.2) (ContinuousLinearMap.snd ℝ ℝ E) (c₀, ψ₀) :=
    hasStrictFDerivAt_snd
  have hfst : HasStrictFDerivAt (fun q : ℝ × E => q.1) (ContinuousLinearMap.fst ℝ ℝ E) (c₀, ψ₀) :=
    hasStrictFDerivAt_fst
  have h1 : HasStrictFDerivAt (fun q : ℝ × E => A₀ q.2)
      ((A₀.restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E)) (c₀, ψ₀) :=
    (A₀.restrictScalars ℝ).hasStrictFDerivAt.comp (c₀, ψ₀) hsnd
  have hB : HasStrictFDerivAt (fun q : ℝ × E => B q.2)
      ((B.restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E)) (c₀, ψ₀) :=
    (B.restrictScalars ℝ).hasStrictFDerivAt.comp (c₀, ψ₀) hsnd
  have h2 : HasStrictFDerivAt (fun q : ℝ × E => q.1 • B q.2)
      (c₀ • ((B.restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E)) +
        (ContinuousLinearMap.fst ℝ ℝ E).smulRight (B ψ₀)) (c₀, ψ₀) := hfst.smul hB
  have hsum := h1.add h2
  have hEq : ((A₀.restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E) +
      (c₀ • ((B.restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ ℝ E)) +
        (ContinuousLinearMap.fst ℝ ℝ E).smulRight (B ψ₀)))
      = familyDerivRC (A₀ + c₀ • B) (B ψ₀) := by
    refine ContinuousLinearMap.ext fun q => ?_
    simp [familyDerivRC]
    abel
  rw [hEq] at hsum
  exact hsum

/-- **An affine family of symmetric operators is symmetric at every coupling.** -/
theorem isSymmetric_affineFamily {A₀ B : E →L[𝕜] E}
    (hA₀ : ∀ u v : E, ⟪A₀ u, v⟫_𝕜 = ⟪u, A₀ v⟫_𝕜)
    (hB : ∀ u v : E, ⟪B u, v⟫_𝕜 = ⟪u, B v⟫_𝕜) (c : ℝ) :
    ∀ u v : E, ⟪(A₀ + c • B) u, v⟫_𝕜 = ⟪u, (A₀ + c • B) v⟫_𝕜 := by
  intro u v
  simp only [add_apply, smul_apply, inner_add_left,
    inner_add_right, RCLike.real_smul_eq_coe_smul (K := 𝕜), inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal, hA₀, hB]

/-- **The Hellmann–Feynman theorem for `H(λ) = H₀ + λ V`.**  For self-adjoint `H₀` and `V`, a simple isolated
eigenvalue at a normalized state has a differentiable branch of normalized eigenstates whose energy is real
and satisfies

```text
dE/dλ (λ_0) = ⟪psi_0, V psi_0⟫.
```
-/
theorem exists_real_branch_affine_deriv_eq_re_expectation [CompleteSpace E]
    {A₀ B : E →L[𝕜] E} {c₀ : ℝ} {ν₀ : 𝕜} {ψ₀ : E} {γ : ℝ}
    (hA₀ : ∀ u v : E, ⟪A₀ u, v⟫_𝕜 = ⟪u, A₀ v⟫_𝕜)
    (hB : ∀ u v : E, ⟪B u, v⟫_𝕜 = ⟪u, B v⟫_𝕜)
    (heig : (A₀ + c₀ • B) ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, (A₀ + c₀ • B) φ = ν₀ • φ → ∃ s : 𝕜, φ = s • ψ₀)
    (hγ : 0 < γ)
    (hgap : ∀ φ : E, ⟪ψ₀, φ⟫_𝕜 = 0 → γ * ‖φ‖ ≤ ‖(A₀ + c₀ • B) φ - ν₀ • φ‖) :
    ∃ (ψ : ℝ → E) (ε : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ((ε c₀ : ℝ) : 𝕜) = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, (A₀ + c • B) (ψ c) = ((ε c : ℝ) : 𝕜) • ψ c ∧ ⟪ψ c, ψ c⟫_𝕜 = 1) ∧
      HasDerivAt ε (RCLike.re (⟪ψ₀, B ψ₀⟫_𝕜)) c₀ :=
  exists_real_branch_deriv_eq_re_expectationRC (A := fun c => A₀ + c • B)
    (hasStrictFDerivAt_affineFamily A₀ B c₀ ψ₀)
    (Filter.Eventually.of_forall fun c => isSymmetric_affineFamily hA₀ hB c)
    heig hnorm hker hγ hgap

/-- **The Hellmann–Feynman theorem for `H(λ) = H₀ + λ V` in finite dimensions**, from simplicity alone. -/
theorem exists_branch_affine_deriv_eq_expectation_finiteDimensional [FiniteDimensional 𝕜 E]
    {A₀ B : E →L[𝕜] E} {c₀ : ℝ} {ν₀ : 𝕜} {ψ₀ : E}
    (hA₀ : ∀ u v : E, ⟪A₀ u, v⟫_𝕜 = ⟪u, A₀ v⟫_𝕜)
    (hB : ∀ u v : E, ⟪B u, v⟫_𝕜 = ⟪u, B v⟫_𝕜)
    (heig : (A₀ + c₀ • B) ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, (A₀ + c₀ • B) φ = ν₀ • φ → ∃ s : 𝕜, φ = s • ψ₀) :
    ∃ (ψ : ℝ → E) (ν : ℝ → 𝕜), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, (A₀ + c • B) (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_𝕜 = 1) ∧
      HasDerivAt ν ⟪ψ₀, B ψ₀⟫_𝕜 c₀ :=
  exists_normalized_branch_deriv_eq_expectation_of_finiteDimensionalRC (A := fun c => A₀ + c • B)
    (hasStrictFDerivAt_affineFamily A₀ B c₀ ψ₀)
    (isSymmetric_affineFamily hA₀ hB c₀) heig hnorm hker

/-! ## The quantum-mechanical statement -/

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The Hellmann–Feynman theorem, quantum-mechanical form.**  For `H(λ) = H₀ + λ V` on a complex Hilbert
space with self-adjoint `H₀` and `V`, and a simple isolated energy level `E₀` with normalized state `psi_0`,
the level is a real differentiable function of the coupling near `λ_0` with a normalized eigenstate branch,
and

```text
dE/dλ = ⟪psi_0, V psi_0⟫.
```
-/
theorem exists_real_branch_affine_deriv_eq_re_expectation_complex [CompleteSpace H]
    {A₀ B : H →L[ℂ] H} {c₀ : ℝ} {ν₀ : ℂ} {ψ₀ : H} {γ : ℝ}
    (hA₀ : ∀ u v : H, ⟪A₀ u, v⟫_ℂ = ⟪u, A₀ v⟫_ℂ)
    (hB : ∀ u v : H, ⟪B u, v⟫_ℂ = ⟪u, B v⟫_ℂ)
    (heig : (A₀ + c₀ • B) ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_ℂ = 1)
    (hker : ∀ φ : H, (A₀ + c₀ • B) φ = ν₀ • φ → ∃ s : ℂ, φ = s • ψ₀)
    (hγ : 0 < γ)
    (hgap : ∀ φ : H, ⟪ψ₀, φ⟫_ℂ = 0 → γ * ‖φ‖ ≤ ‖(A₀ + c₀ • B) φ - ν₀ • φ‖) :
    ∃ (ψ : ℝ → H) (ε : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ((ε c₀ : ℝ) : ℂ) = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, (A₀ + c • B) (ψ c) = ((ε c : ℝ) : ℂ) • ψ c ∧ ⟪ψ c, ψ c⟫_ℂ = 1) ∧
      HasDerivAt ε (⟪ψ₀, B ψ₀⟫_ℂ).re c₀ :=
  exists_real_branch_affine_deriv_eq_re_expectation hA₀ hB heig hnorm hker hγ hgap

/-- **The Hellmann–Feynman theorem for a finite-dimensional quantum system**, with no isolation hypothesis:
simplicity of the level is all that is required. -/
theorem exists_branch_affine_deriv_eq_expectation_complex_finiteDimensional [FiniteDimensional ℂ H]
    {A₀ B : H →L[ℂ] H} {c₀ : ℝ} {ν₀ : ℂ} {ψ₀ : H}
    (hA₀ : ∀ u v : H, ⟪A₀ u, v⟫_ℂ = ⟪u, A₀ v⟫_ℂ)
    (hB : ∀ u v : H, ⟪B u, v⟫_ℂ = ⟪u, B v⟫_ℂ)
    (heig : (A₀ + c₀ • B) ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_ℂ = 1)
    (hker : ∀ φ : H, (A₀ + c₀ • B) φ = ν₀ • φ → ∃ s : ℂ, φ = s • ψ₀) :
    ∃ (ψ : ℝ → H) (ν : ℝ → ℂ), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, (A₀ + c • B) (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_ℂ = 1) ∧
      HasDerivAt ν ⟪ψ₀, B ψ₀⟫_ℂ c₀ :=
  exists_branch_affine_deriv_eq_expectation_finiteDimensional hA₀ hB heig hnorm hker

end Complex

end GaloisForLFunctions.HTGeometry

end
