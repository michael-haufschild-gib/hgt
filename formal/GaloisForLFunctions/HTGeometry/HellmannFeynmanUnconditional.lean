import GaloisForLFunctions.HTGeometry.SimpleEigenvalueBranchRCLike
import GaloisForLFunctions.HTGeometry.HellmannFeynmanRCLike
import GaloisForLFunctions.HTGeometry.SimpleEigenvalueGapInverse
import GaloisForLFunctions.HTGeometry.SimpleEigenvalueBranch

/-!
# Hellmann–Feynman with no auxiliary data

This file assembles the unconditional form of the Hellmann–Feynman theorem: for a differentiable family of
symmetric operators on a `𝕜`-Hilbert space with a **simple, gapped** eigenvalue, a differentiable normalized
eigenpair branch *exists*, and its eigenvalue derivative is the expectation of the family's motion,

```text
nu'(c_0) = ⟪psi_0, w⟫,      w = (dA/dc) psi_0.
```

Nothing is assumed beyond structure that can be checked on the operator itself.  In particular the
pseudo-inverse of `A c_0 - nu_0`, which the bordered implicit function theorem needs and which earlier layers
took as an input, is *constructed* here from the spectral gap
(`SimpleEigenvalueGapInverse.exists_pseudoInverse_of_gap`).  In finite dimensions even the gap is free:
simplicity alone suffices.

The layers combined here are

* `SimpleEigenvalueBorderedRCLike` — the bordered system and its explicit inverse over `𝕜`;
* `SimpleEigenvalueBranchRCLike` — the implicit function theorem producing the branch;
* `SimpleEigenvalueGapInverse` — the pseudo-inverse from a transverse coercivity bound;
* `HellmannFeynmanRCLike` — the derivative law itself, including the reality of the eigenvalue.

The final theorems record the physicist's statement over an arbitrary `RCLike` field and over `ℂ`: the
eigenvalue branch is real-valued near the base point and its derivative is `re ⟪psi_0, w⟫`.
-/

noncomputable section

open scoped InnerProductSpace
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Hellmann–Feynman for a simple eigenvalue of a differentiable family over `𝕜`**, with no branch input at
all: the branch is constructed, and its eigenvalue derivative is the expectation of the family's motion. -/
theorem exists_normalized_branch_deriv_eq_expectationRC [CompleteSpace E]
    {A : ℝ → E →L[𝕜] E} {R : E →L[𝕜] E} {c₀ : ℝ} {ν₀ : 𝕜} {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : E, ⟪A c₀ u, v⟫_𝕜 = ⟪u, A c₀ v⟫_𝕜)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : 𝕜, φ = s • ψ₀)
    (hR : ∀ y : E, A c₀ (R y) - ν₀ • R y = y - ⟪ψ₀, y⟫_𝕜 • ψ₀)
    (hRψ : ∀ y : E, ⟪ψ₀, R y⟫_𝕜 = 0) :
    ∃ (ψ : ℝ → E) (ν : ℝ → 𝕜), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_𝕜 = 1) ∧
      HasDerivAt ν ⟪ψ₀, w⟫_𝕜 c₀ := by
  obtain ⟨ψ, ν, hψ0, hν0, hdψ, hdν, hev⟩ :=
    exists_differentiable_normalized_simple_eigen_branchRC hA hsymm heig hnorm hker hR hRψ
  refine ⟨ψ, ν, hψ0, hν0, hev, ?_⟩
  set ψ' := deriv ψ c₀ with hψ'
  have hψd : HasDerivAt ψ ψ' c₀ := hdψ.hasDerivAt
  have hνd : HasDerivAt ν (deriv ν c₀) c₀ := hdν.hasDerivAt
  have hcurve : HasDerivAt (fun t : ℝ => (t, ψ t)) (1, ψ') c₀ := (hasDerivAt_id c₀).prodMk hψd
  have hA' : HasFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ c₀) := by
    rw [hψ0]
    exact hA.hasFDerivAt
  have hAψ : HasDerivAt (fun t => A t (ψ t)) (w + A c₀ ψ') c₀ := by
    have h := hA'.comp_hasDerivAt c₀ hcurve
    simpa [Function.comp_def] using h
  have hnorm' : ⟪ψ c₀, ψ c₀⟫_𝕜 = 1 := by rw [hψ0]; exact hnorm
  have hsa : ⟪ψ c₀, A c₀ ψ'⟫_𝕜 = ⟪A c₀ (ψ c₀), ψ'⟫_𝕜 := by
    rw [hψ0]
    exact (hsymm ψ₀ ψ').symm
  have hsa0 : ⟪ψ c₀, A c₀ (ψ c₀)⟫_𝕜 = ⟪A c₀ (ψ c₀), ψ c₀⟫_𝕜 := by
    rw [hψ0]
    exact (hsymm ψ₀ ψ₀).symm
  have hkey := hellmann_feynman_rclike_eventually (A := fun t => (A t : E → E)) hnorm' hsa hsa0
    hνd hψd hAψ (hev.mono fun c hc => hc.1)
  rw [hψ0] at hkey
  rw [hkey] at hνd
  exact hνd

/-- **Hellmann–Feynman from a spectral gap.**  The pseudo-inverse is no longer an input: a transverse
coercivity bound on `A c_0 - nu_0` — i.e. isolation of the eigenvalue — produces it.  So the whole hypothesis
list is structure of the operator family: strict differentiability, symmetry at the base point, the
eigenrelation, normalization, simplicity, and the gap. -/
theorem exists_normalized_branch_deriv_eq_expectation_of_gapRC [CompleteSpace E]
    {A : ℝ → E →L[𝕜] E} {c₀ : ℝ} {ν₀ : 𝕜} {ψ₀ w : E} {γ : ℝ}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : E, ⟪A c₀ u, v⟫_𝕜 = ⟪u, A c₀ v⟫_𝕜)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : 𝕜, φ = s • ψ₀)
    (hγ : 0 < γ)
    (hgap : ∀ φ : E, ⟪ψ₀, φ⟫_𝕜 = 0 → γ * ‖φ‖ ≤ ‖A c₀ φ - ν₀ • φ‖) :
    ∃ (ψ : ℝ → E) (ν : ℝ → 𝕜), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_𝕜 = 1) ∧
      HasDerivAt ν ⟪ψ₀, w⟫_𝕜 c₀ := by
  have hν₀real : (starRingEnd 𝕜) ν₀ = ν₀ := by
    have h1 : ⟪ψ₀, A c₀ ψ₀⟫_𝕜 = ν₀ := by rw [heig, inner_smul_right, hnorm, mul_one]
    have h2 : ⟪A c₀ ψ₀, ψ₀⟫_𝕜 = (starRingEnd 𝕜) ν₀ := by
      rw [heig, inner_smul_left, hnorm, mul_one]
    have h3 := hsymm ψ₀ ψ₀
    rw [h1, h2] at h3
    exact h3
  set T : E →L[𝕜] E := A c₀ - ν₀ • ContinuousLinearMap.id 𝕜 E with hTdef
  have hT : ∀ x : E, T x = A c₀ x - ν₀ • x := by
    intro x
    simp [hTdef]
  have hTψ : T ψ₀ = 0 := by rw [hT, heig, sub_self]
  have hTsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜 := by
    intro u v
    rw [hT, hT, inner_sub_left, inner_sub_right, hsymm u v, inner_smul_left, inner_smul_right,
      hν₀real]
  have hTker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ₀ := by
    intro φ hφ
    rw [hT, sub_eq_zero] at hφ
    exact hker φ hφ
  have hTgap : ∀ φ : E, ⟪ψ₀, φ⟫_𝕜 = 0 → γ * ‖φ‖ ≤ ‖T φ‖ := by
    intro φ hφ
    rw [hT]
    exact hgap φ hφ
  obtain ⟨R, hR, hRψ⟩ := exists_pseudoInverse_of_gap hTsymm hTψ hnorm hTker hγ hTgap
  refine exists_normalized_branch_deriv_eq_expectationRC hA hsymm heig hnorm hker ?_ hRψ
  intro y
  rw [← hT]
  exact hR y

/-- **Hellmann–Feynman in finite dimensions, from simplicity alone.**  A simple eigenvalue of a
finite-dimensional symmetric family is automatically isolated, so no gap has to be supplied. -/
theorem exists_normalized_branch_deriv_eq_expectation_of_finiteDimensionalRC
    [FiniteDimensional 𝕜 E]
    {A : ℝ → E →L[𝕜] E} {c₀ : ℝ} {ν₀ : 𝕜} {ψ₀ w : E}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : E, ⟪A c₀ u, v⟫_𝕜 = ⟪u, A c₀ v⟫_𝕜)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : 𝕜, φ = s • ψ₀) :
    ∃ (ψ : ℝ → E) (ν : ℝ → 𝕜), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_𝕜 = 1) ∧
      HasDerivAt ν ⟪ψ₀, w⟫_𝕜 c₀ := by
  have hν₀real : (starRingEnd 𝕜) ν₀ = ν₀ := by
    have h1 : ⟪ψ₀, A c₀ ψ₀⟫_𝕜 = ν₀ := by rw [heig, inner_smul_right, hnorm, mul_one]
    have h2 : ⟪A c₀ ψ₀, ψ₀⟫_𝕜 = (starRingEnd 𝕜) ν₀ := by
      rw [heig, inner_smul_left, hnorm, mul_one]
    have h3 := hsymm ψ₀ ψ₀
    rw [h1, h2] at h3
    exact h3
  set T : E →L[𝕜] E := A c₀ - ν₀ • ContinuousLinearMap.id 𝕜 E with hTdef
  have hT : ∀ x : E, T x = A c₀ x - ν₀ • x := by
    intro x
    simp [hTdef]
  have hTψ : T ψ₀ = 0 := by rw [hT, heig, sub_self]
  have hTsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜 := by
    intro u v
    rw [hT, hT, inner_sub_left, inner_sub_right, hsymm u v, inner_smul_left, inner_smul_right,
      hν₀real]
  have hTker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ₀ := by
    intro φ hφ
    rw [hT, sub_eq_zero] at hφ
    exact hker φ hφ
  haveI : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  obtain ⟨γ, hγ, hgap⟩ := exists_gap_of_finiteDimensional hTsymm hTψ hnorm hTker
  refine exists_normalized_branch_deriv_eq_expectation_of_gapRC hA hsymm heig hnorm hker hγ ?_
  intro φ hφ
  have h := hgap φ hφ
  rwa [hT] at h

omit [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] in
/-- **The branch eigenvalue is real.**  If the family is symmetric near the base point, the eigenvalue of a
normalized eigenpair branch is a real scalar there. -/
theorem eventually_conj_eq_self_of_normalized_branch
    {A : ℝ → E →L[𝕜] E} {ψ : ℝ → E} {ν : ℝ → 𝕜} {c₀ : ℝ}
    (hsymm : ∀ᶠ c in 𝓝 c₀, ∀ u v : E, ⟪A c u, v⟫_𝕜 = ⟪u, A c v⟫_𝕜)
    (hbranch : ∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_𝕜 = 1) :
    ∀ᶠ c in 𝓝 c₀, (starRingEnd 𝕜) (ν c) = ν c := by
  filter_upwards [hsymm, hbranch] with c hs hb
  exact eigenvalue_conj_eq_self_of_symmetric_at hb.2 (hs (ψ c) (ψ c)).symm hb.1

/-- **The real eigenvalue branch and its Hellmann–Feynman derivative.**  For a family that is symmetric near
the base point, the eigenvalue branch is a *real-valued* differentiable function of the aperture, and its
derivative is the real expectation `re ⟪psi_0, w⟫`.  This is the physicist's Hellmann–Feynman theorem: an
energy level of a differentiably varying self-adjoint Hamiltonian moves at the rate of the expectation of the
Hamiltonian's own motion in the instantaneous state. -/
theorem exists_real_branch_deriv_eq_re_expectationRC [CompleteSpace E]
    {A : ℝ → E →L[𝕜] E} {c₀ : ℝ} {ν₀ : 𝕜} {ψ₀ w : E} {γ : ℝ}
    (hA : HasStrictFDerivAt (fun q : ℝ × E => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ᶠ c in 𝓝 c₀, ∀ u v : E, ⟪A c u, v⟫_𝕜 = ⟪u, A c v⟫_𝕜)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_𝕜 = 1)
    (hker : ∀ φ : E, A c₀ φ = ν₀ • φ → ∃ s : 𝕜, φ = s • ψ₀)
    (hγ : 0 < γ)
    (hgap : ∀ φ : E, ⟪ψ₀, φ⟫_𝕜 = 0 → γ * ‖φ‖ ≤ ‖A c₀ φ - ν₀ • φ‖) :
    ∃ (ψ : ℝ → E) (ε : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ((ε c₀ : ℝ) : 𝕜) = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ((ε c : ℝ) : 𝕜) • ψ c ∧ ⟪ψ c, ψ c⟫_𝕜 = 1) ∧
      HasDerivAt ε (RCLike.re (⟪ψ₀, w⟫_𝕜)) c₀ := by
  have hsymm₀ : ∀ u v : E, ⟪A c₀ u, v⟫_𝕜 = ⟪u, A c₀ v⟫_𝕜 := hsymm.self_of_nhds
  obtain ⟨ψ, ν, hψ0, hν0, hev, hderiv⟩ :=
    exists_normalized_branch_deriv_eq_expectation_of_gapRC hA hsymm₀ heig hnorm hker hγ hgap
  have hreal := eventually_conj_eq_self_of_normalized_branch hsymm hev
  refine ⟨ψ, fun c => RCLike.re (ν c), hψ0, ?_, ?_, ?_⟩
  · have h : (starRingEnd 𝕜) (ν c₀) = ν c₀ := hreal.self_of_nhds
    rw [RCLike.conj_eq_iff_re] at h
    rw [h, hν0]
  · filter_upwards [hev, hreal] with c hc hr
    have h : ((RCLike.re (ν c) : ℝ) : 𝕜) = ν c := RCLike.conj_eq_iff_re.mp hr
    rw [h]
    exact hc
  · have h := (RCLike.reCLM (K := 𝕜)).hasFDerivAt.comp_hasDerivAt c₀ hderiv
    simpa [Function.comp_def] using h


/-! ## The real case, in the packaging of `SimpleEigenvalueBranch` -/

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Over `ℝ` the two family-derivative packagings agree, so the `RCLike` layer specializes to the real one. -/
theorem familyDerivRC_eq_familyDeriv (S : F →L[ℝ] F) (w : F) :
    familyDerivRC S w = familyDeriv S w := rfl

/-- **Hellmann–Feynman for a gapped simple eigenvalue of a real symmetric family.**  This is
`exists_normalized_branch_deriv_eq_expectation` of `SimpleEigenvalueBranch` with the pseudo-inverse
*constructed* from the spectral gap rather than assumed. -/
theorem exists_normalized_branch_deriv_eq_expectation_of_gap [CompleteSpace F]
    {A : ℝ → F →L[ℝ] F} {c₀ ν₀ : ℝ} {ψ₀ w : F} {γ : ℝ}
    (hA : HasStrictFDerivAt (fun q : ℝ × F => A q.1 q.2) (familyDeriv (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : F, ⟪A c₀ u, v⟫_ℝ = ⟪u, A c₀ v⟫_ℝ)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_ℝ = 1)
    (hker : ∀ φ : F, A c₀ φ = ν₀ • φ → ∃ s : ℝ, φ = s • ψ₀)
    (hγ : 0 < γ)
    (hgap : ∀ φ : F, ⟪ψ₀, φ⟫_ℝ = 0 → γ * ‖φ‖ ≤ ‖A c₀ φ - ν₀ • φ‖) :
    ∃ (ψ : ℝ → F) (ν : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_ℝ = 1) ∧
      HasDerivAt ν ⟪ψ₀, w⟫_ℝ c₀ := by
  refine exists_normalized_branch_deriv_eq_expectation_of_gapRC (𝕜 := ℝ) ?_ hsymm heig hnorm hker
    hγ hgap
  rw [familyDerivRC_eq_familyDeriv]
  exact hA

/-- **Hellmann–Feynman in finite dimensions over `ℝ`, from simplicity alone.** -/
theorem exists_normalized_branch_deriv_eq_expectation_of_finiteDimensional
    [FiniteDimensional ℝ F]
    {A : ℝ → F →L[ℝ] F} {c₀ ν₀ : ℝ} {ψ₀ w : F}
    (hA : HasStrictFDerivAt (fun q : ℝ × F => A q.1 q.2) (familyDeriv (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : F, ⟪A c₀ u, v⟫_ℝ = ⟪u, A c₀ v⟫_ℝ)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_ℝ = 1)
    (hker : ∀ φ : F, A c₀ φ = ν₀ • φ → ∃ s : ℝ, φ = s • ψ₀) :
    ∃ (ψ : ℝ → F) (ν : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_ℝ = 1) ∧
      HasDerivAt ν ⟪ψ₀, w⟫_ℝ c₀ := by
  refine exists_normalized_branch_deriv_eq_expectation_of_finiteDimensionalRC (𝕜 := ℝ) ?_ hsymm
    heig hnorm hker
  rw [familyDerivRC_eq_familyDeriv]
  exact hA

end Real

/-! ## The complex case: the quantum-mechanical Hellmann–Feynman theorem -/

section Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The Hellmann–Feynman theorem on a complex Hilbert space.**  Let `A` be a family of operators, strictly
differentiable in the aperture with derivative datum `w = (dA/dc) psi_0`, self-adjoint near `c_0`, and let
`nu_0` be a simple eigenvalue at the unit vector `psi_0`, isolated in the sense of the transverse coercivity
bound.  Then there is a differentiable branch of normalized eigenvectors through `psi_0`, its energy `ε` is a
real-valued differentiable function of the aperture, and

```text
ε'(c_0) = re ⟪psi_0, w⟫ = ⟪psi_0, (dA/dc) psi_0⟫.
```
-/
theorem exists_real_branch_deriv_eq_re_expectation_complex [CompleteSpace H]
    {A : ℝ → H →L[ℂ] H} {c₀ : ℝ} {ν₀ : ℂ} {ψ₀ w : H} {γ : ℝ}
    (hA : HasStrictFDerivAt (fun q : ℝ × H => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ᶠ c in 𝓝 c₀, ∀ u v : H, ⟪A c u, v⟫_ℂ = ⟪u, A c v⟫_ℂ)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_ℂ = 1)
    (hker : ∀ φ : H, A c₀ φ = ν₀ • φ → ∃ s : ℂ, φ = s • ψ₀)
    (hγ : 0 < γ)
    (hgap : ∀ φ : H, ⟪ψ₀, φ⟫_ℂ = 0 → γ * ‖φ‖ ≤ ‖A c₀ φ - ν₀ • φ‖) :
    ∃ (ψ : ℝ → H) (ε : ℝ → ℝ), ψ c₀ = ψ₀ ∧ ((ε c₀ : ℝ) : ℂ) = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ((ε c : ℝ) : ℂ) • ψ c ∧ ⟪ψ c, ψ c⟫_ℂ = 1) ∧
      HasDerivAt ε (⟪ψ₀, w⟫_ℂ).re c₀ :=
  exists_real_branch_deriv_eq_re_expectationRC hA hsymm heig hnorm hker hγ hgap

/-- **The quantum-mechanical Hellmann–Feynman theorem in finite dimensions**, from simplicity alone: no gap
hypothesis is needed, because a simple eigenvalue of a finite-dimensional Hermitian family is automatically
isolated. -/
theorem exists_branch_deriv_eq_expectation_complex_finiteDimensional
    [FiniteDimensional ℂ H]
    {A : ℝ → H →L[ℂ] H} {c₀ : ℝ} {ν₀ : ℂ} {ψ₀ w : H}
    (hA : HasStrictFDerivAt (fun q : ℝ × H => A q.1 q.2) (familyDerivRC (A c₀) w) (c₀, ψ₀))
    (hsymm : ∀ u v : H, ⟪A c₀ u, v⟫_ℂ = ⟪u, A c₀ v⟫_ℂ)
    (heig : A c₀ ψ₀ = ν₀ • ψ₀) (hnorm : ⟪ψ₀, ψ₀⟫_ℂ = 1)
    (hker : ∀ φ : H, A c₀ φ = ν₀ • φ → ∃ s : ℂ, φ = s • ψ₀) :
    ∃ (ψ : ℝ → H) (ν : ℝ → ℂ), ψ c₀ = ψ₀ ∧ ν c₀ = ν₀ ∧
      (∀ᶠ c in 𝓝 c₀, A c (ψ c) = ν c • ψ c ∧ ⟪ψ c, ψ c⟫_ℂ = 1) ∧
      HasDerivAt ν ⟪ψ₀, w⟫_ℂ c₀ :=
  exists_normalized_branch_deriv_eq_expectation_of_finiteDimensionalRC hA hsymm heig hnorm hker

end Complex

end GaloisForLFunctions.HTGeometry

end
