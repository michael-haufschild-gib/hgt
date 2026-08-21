import GaloisForLFunctions.HTGeometry.HellmannFeynmanAffineFamily

/-!
# A witness that the Hellmann–Feynman hypotheses are satisfiable

A gap hypothesis is worthless if nothing satisfies it.  This file exhibits, on **every** inner product space
carrying a unit vector — finite- or infinite-dimensional — an affine family for which every hypothesis of
`exists_real_branch_affine_deriv_eq_re_expectation` holds with a genuine nonzero gap, and computes the
Hellmann–Feynman derivative for it.

The family is built from the two projectors attached to a unit vector `psi_0`:

```text
P y = ⟪psi_0, y⟫ psi_0        (onto the eigendirection),
Q y = y - ⟪psi_0, y⟫ psi_0    (onto its orthogonal complement),
```

as the two-level Hamiltonian

```text
H(λ) = nu_0 + delta • Q + λ • P.
```

`psi_0` is an eigenvector of energy `nu_0`, the transverse space carries the constant energy `nu_0 + delta`,
so the level is simple and isolated with gap `|delta|` exactly when `delta ≠ 0`, and the coupling `P` moves it
at unit rate:

```text
dE/dλ (0) = ⟪psi_0, P psi_0⟫ = 1.
```
-/

noncomputable section

open scoped InnerProductSpace
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The projector onto the direction of `ψ₀`. -/
def eigenProj (ψ₀ : E) : E →L[𝕜] E := (innerSL 𝕜 ψ₀).smulRight ψ₀

@[simp] theorem eigenProj_apply (ψ₀ y : E) :
    (eigenProj ψ₀ : E →L[𝕜] E) y = ⟪ψ₀, y⟫_𝕜 • ψ₀ := rfl

/-- The projector onto the orthogonal complement of `ψ₀`. -/
def transverseProj (ψ₀ : E) : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E - (eigenProj ψ₀ : E →L[𝕜] E)

@[simp] theorem transverseProj_apply (ψ₀ y : E) :
    (transverseProj ψ₀ : E →L[𝕜] E) y = y - ⟪ψ₀, y⟫_𝕜 • ψ₀ := rfl

theorem isSymmetric_eigenProj (ψ₀ : E) (u v : E) :
    ⟪(eigenProj ψ₀ : E →L[𝕜] E) u, v⟫_𝕜 = ⟪u, (eigenProj ψ₀ : E →L[𝕜] E) v⟫_𝕜 := by
  rw [eigenProj_apply, eigenProj_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem isSymmetric_transverseProj (ψ₀ : E) (u v : E) :
    ⟪(transverseProj ψ₀ : E →L[𝕜] E) u, v⟫_𝕜 = ⟪u, (transverseProj ψ₀ : E →L[𝕜] E) v⟫_𝕜 := by
  rw [transverseProj_apply, transverseProj_apply, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- The two-level Hamiltonian `nu_0 + delta • Q`, whose eigenvector `psi_0` carries energy `nu_0` and whose
transverse space carries the constant energy `nu_0 + delta`. -/
def twoLevelBase (ψ₀ : E) (ν₀ δ : ℝ) : E →L[𝕜] E :=
  ((ν₀ : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E + ((δ : ℝ) : 𝕜) • (transverseProj ψ₀ : E →L[𝕜] E)

theorem twoLevelBase_apply (ψ₀ : E) (ν₀ δ : ℝ) (y : E) :
    (twoLevelBase ψ₀ ν₀ δ : E →L[𝕜] E) y
      = ((ν₀ : ℝ) : 𝕜) • y + ((δ : ℝ) : 𝕜) • (y - ⟪ψ₀, y⟫_𝕜 • ψ₀) := by
  simp [twoLevelBase]

theorem isSymmetric_twoLevelBase (ψ₀ : E) (ν₀ δ : ℝ) (u v : E) :
    ⟪(twoLevelBase ψ₀ ν₀ δ : E →L[𝕜] E) u, v⟫_𝕜
      = ⟪u, (twoLevelBase ψ₀ ν₀ δ : E →L[𝕜] E) v⟫_𝕜 := by
  rw [twoLevelBase_apply, twoLevelBase_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal, RCLike.conj_ofReal]
  have h : ⟪u - ⟪ψ₀, u⟫_𝕜 • ψ₀, v⟫_𝕜 = ⟪u, v - ⟪ψ₀, v⟫_𝕜 • ψ₀⟫_𝕜 :=
    isSymmetric_transverseProj ψ₀ u v
  rw [h]

/-- **The Hellmann–Feynman hypotheses are satisfiable, with a genuine gap.**  On any inner product space with a
unit vector `psi_0` and any `delta ≠ 0`, the affine family `H(λ) = nu_0 + delta • Q + λ • P` has a
differentiable branch of normalized eigenstates through `psi_0` whose energy is real and moves at unit rate:

```text
dE/dλ (0) = 1.
```
-/
theorem exists_twoLevel_branch_deriv_eq_one [CompleteSpace E]
    {ψ₀ : E} (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1) (ν₀ δ : ℝ) (hδ : δ ≠ 0) :
    ∃ (ψ : ℝ → E) (ε : ℝ → ℝ), ψ 0 = ψ₀ ∧ ε 0 = ν₀ ∧
      (∀ᶠ c in 𝓝 (0 : ℝ),
        ((twoLevelBase ψ₀ ν₀ δ : E →L[𝕜] E) + c • (eigenProj ψ₀ : E →L[𝕜] E)) (ψ c)
            = ((ε c : ℝ) : 𝕜) • ψ c ∧ ⟪ψ c, ψ c⟫_𝕜 = 1) ∧
      HasDerivAt ε 1 0 := by
  set A₀ : E →L[𝕜] E := twoLevelBase ψ₀ ν₀ δ with hA₀def
  set B : E →L[𝕜] E := eigenProj ψ₀ with hBdef
  have hA₀app : ∀ y : E, A₀ y = ((ν₀ : ℝ) : 𝕜) • y + ((δ : ℝ) : 𝕜) • (y - ⟪ψ₀, y⟫_𝕜 • ψ₀) := by
    intro y
    rw [hA₀def]
    exact twoLevelBase_apply ψ₀ ν₀ δ y
  have hcollapse : ∀ φ : E, (A₀ + (0 : ℝ) • B) φ = A₀ φ := by
    intro φ
    simp
  -- the base point eigenrelation
  have hzero : (A₀ + (0 : ℝ) • B) ψ₀ = ((ν₀ : ℝ) : 𝕜) • ψ₀ := by
    rw [hcollapse, hA₀app, hnorm, one_smul, sub_self, smul_zero, add_zero]
  -- simplicity of the level
  have hker : ∀ φ : E, (A₀ + (0 : ℝ) • B) φ = ((ν₀ : ℝ) : 𝕜) • φ → ∃ s : 𝕜, φ = s • ψ₀ := by
    intro φ hφ
    rw [hcollapse, hA₀app] at hφ
    have hcancel : ((ν₀ : ℝ) : 𝕜) • φ + ((δ : ℝ) : 𝕜) • (φ - ⟪ψ₀, φ⟫_𝕜 • ψ₀)
        = ((ν₀ : ℝ) : 𝕜) • φ + 0 := by
      rw [add_zero]
      exact hφ
    have h : ((δ : ℝ) : 𝕜) • (φ - ⟪ψ₀, φ⟫_𝕜 • ψ₀) = 0 := add_left_cancel hcancel
    have hδ' : ((δ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hδ
    have h2 : φ - ⟪ψ₀, φ⟫_𝕜 • ψ₀ = 0 := by
      rcases smul_eq_zero.mp h with h3 | h3
      · exact absurd h3 hδ'
      · exact h3
    exact ⟨⟪ψ₀, φ⟫_𝕜, by rw [← sub_eq_zero]; exact h2⟩
  -- the gap
  have hgap : ∀ φ : E, ⟪ψ₀, φ⟫_𝕜 = 0 →
      |δ| * ‖φ‖ ≤ ‖(A₀ + (0 : ℝ) • B) φ - ((ν₀ : ℝ) : 𝕜) • φ‖ := by
    intro φ hφ
    have h0 : (A₀ + (0 : ℝ) • B) φ - ((ν₀ : ℝ) : 𝕜) • φ = ((δ : ℝ) : 𝕜) • φ := by
      rw [hcollapse, hA₀app, hφ, zero_smul, sub_zero]
      abel
    rw [h0, norm_smul]
    simp
  obtain ⟨ψ, ε, hψ0, hε0, hev, hderiv⟩ :=
    exists_real_branch_affine_deriv_eq_re_expectation (A₀ := A₀) (B := B) (c₀ := (0 : ℝ))
      (fun u v => by rw [hA₀def]; exact isSymmetric_twoLevelBase ψ₀ ν₀ δ u v)
      (fun u v => by rw [hBdef]; exact isSymmetric_eigenProj ψ₀ u v)
      hzero hnorm hker (abs_pos.mpr hδ) hgap
  have hexp : ⟪ψ₀, B ψ₀⟫_𝕜 = 1 := by
    rw [hBdef, eigenProj_apply, inner_smul_right, hnorm, mul_one]
  refine ⟨ψ, ε, hψ0, ?_, hev, ?_⟩
  · exact_mod_cast hε0
  · rw [hexp] at hderiv
    simpa using hderiv

end GaloisForLFunctions.HTGeometry

end
