import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The bordered system of a simple eigenvalue, over an arbitrary `RCLike` field

This is the `RCLike` companion of `SimpleEigenvalueBordered`, which treats only real inner product spaces.
Quantum mechanics lives over `ℂ`, and the complex case is *not* a corollary of the real one: a complex Hilbert
space viewed as a real one turns a simple complex eigenvalue into a two-dimensional real eigenspace, so real
simplicity fails and the real bordered system is not invertible.  The bordered system has to be built over `𝕜`
directly, and that is what this file does.

Instead of inverting `T = A - nu` — impossible, since `T` kills the eigenvector — one inverts the bordered map

```text
S (phi, t) = (T phi - t • psi, ⟪psi, phi⟫)
```

on `E × 𝕜`.  From a pseudo-inverse `R` of `T` modulo the eigendirection the inverse is explicit,

```text
S⁻¹ (y, a) = (R y + a • psi, -⟪psi, y⟫),
```

so no completeness and no open mapping theorem enter.  Note that no complex conjugation appears anywhere: the
eigenvector always occupies the *first* inner-product slot and the scalars always the second, and the inner
product is linear there.

The last theorem restricts scalars to `ℝ`.  That is the form perturbation theory consumes: the aperture
parameter is real, so the eigen-residual is only an `ℝ`-differentiable map and the implicit function theorem
needs its partial derivative inverted over `ℝ`.
-/

noncomputable section

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The bordered map of a symmetric operator at an eigenvector, over `𝕜`. -/
def borderedMapRC (T : E →L[𝕜] E) (ψ : E) (p : E × 𝕜) : E × 𝕜 :=
  (T p.1 - p.2 • ψ, ⟪ψ, p.1⟫_𝕜)

/-- The candidate inverse, built from a pseudo-inverse `R` of `T` modulo the eigendirection. -/
def borderedInvRC (R : E →L[𝕜] E) (ψ : E) (q : E × 𝕜) : E × 𝕜 :=
  (R q.1 + q.2 • ψ, -⟪ψ, q.1⟫_𝕜)

/-- The eigendirection is orthogonal to the range of a symmetric operator killing it. -/
theorem inner_eigen_apply_eq_zeroRC {T : E →L[𝕜] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜) (hTψ : T ψ = 0) (φ : E) :
    ⟪ψ, T φ⟫_𝕜 = 0 := by
  have h := hsymm ψ φ
  rw [hTψ, inner_zero_left] at h
  exact h.symm

/-- **The pseudo-inverse is a left inverse modulo the eigendirection.**  This is where simplicity enters:
`T (R (T phi) - phi) = 0`, so the difference lies in the eigendirection, and pairing with `psi` pins its
coefficient. -/
theorem borderedInvRC_left {T R : E →L[𝕜] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜)
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫_𝕜 = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫_𝕜 • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫_𝕜 = 0)
    (φ : E) : R (T φ) = φ - ⟪ψ, φ⟫_𝕜 • ψ := by
  have hTφψ : ⟪ψ, T φ⟫_𝕜 = 0 := inner_eigen_apply_eq_zeroRC hsymm hTψ φ
  have hzero : T (R (T φ) - φ) = 0 := by
    rw [map_sub, hR (T φ), hTφψ]
    simp
  obtain ⟨s, hs⟩ := hker _ hzero
  have hpair : ⟪ψ, R (T φ) - φ⟫_𝕜 = s := by
    rw [hs, inner_smul_right, hnorm, mul_one]
  have hpair2 : ⟪ψ, R (T φ) - φ⟫_𝕜 = -⟪ψ, φ⟫_𝕜 := by
    rw [inner_sub_right, hRψ, zero_sub]
  have hsval : s = -⟪ψ, φ⟫_𝕜 := by rw [← hpair, hpair2]
  have hdiff : R (T φ) - φ = (-⟪ψ, φ⟫_𝕜) • ψ := by rw [hs, hsval]
  have h := sub_eq_iff_eq_add.mp hdiff
  rw [h, neg_smul]
  abel

/-- **The candidate inverse is a right inverse.** -/
theorem borderedMapRC_borderedInvRC {T R : E →L[𝕜] E} {ψ : E}
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫_𝕜 = 1)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫_𝕜 • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫_𝕜 = 0) (q : E × 𝕜) :
    borderedMapRC T ψ (borderedInvRC R ψ q) = q := by
  obtain ⟨y, a⟩ := q
  have h1 : T (R y + a • ψ) - (-⟪ψ, y⟫_𝕜) • ψ = y := by
    rw [map_add, hR y, map_smul, hTψ]
    simp
  have h2 : ⟪ψ, R y + a • ψ⟫_𝕜 = a := by
    rw [inner_add_right, hRψ, inner_smul_right, hnorm]
    ring
  rw [borderedMapRC, borderedInvRC]
  exact Prod.ext h1 h2

/-- **The candidate inverse is a left inverse.**  This is the direction that consumes simplicity. -/
theorem borderedInvRC_borderedMapRC {T R : E →L[𝕜] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜)
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫_𝕜 = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫_𝕜 • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫_𝕜 = 0) (p : E × 𝕜) :
    borderedInvRC R ψ (borderedMapRC T ψ p) = p := by
  obtain ⟨φ, t⟩ := p
  have hTφψ : ⟪ψ, T φ⟫_𝕜 = 0 := inner_eigen_apply_eq_zeroRC hsymm hTψ φ
  have h1 : R (T φ - t • ψ) + ⟪ψ, φ⟫_𝕜 • ψ = φ := by
    rw [map_sub, map_smul, borderedInvRC_left hsymm hTψ hnorm hker hR hRψ φ]
    have hRψzero : R ψ = 0 := by
      have hTRψ : T (R ψ) = 0 := by
        rw [hR ψ, hnorm]
        simp
      obtain ⟨s, hs⟩ := hker _ hTRψ
      have h : ⟪ψ, R ψ⟫_𝕜 = s := by rw [hs, inner_smul_right, hnorm, mul_one]
      rw [hRψ ψ] at h
      rw [hs, ← h, zero_smul]
    rw [hRψzero]
    simp
  have h2 : -⟪ψ, T φ - t • ψ⟫_𝕜 = t := by
    rw [inner_sub_right, hTφψ, inner_smul_right, hnorm]
    ring
  rw [borderedInvRC, borderedMapRC]
  exact Prod.ext h1 h2

/-- The bordered map as a continuous `𝕜`-linear map. -/
def borderedCLMRC (T : E →L[𝕜] E) (ψ : E) : (E × 𝕜) →L[𝕜] (E × 𝕜) :=
  (T.comp (ContinuousLinearMap.fst 𝕜 E 𝕜) -
      ContinuousLinearMap.smulRight (ContinuousLinearMap.snd 𝕜 E 𝕜) ψ).prod
    ((innerSL 𝕜 ψ).comp (ContinuousLinearMap.fst 𝕜 E 𝕜))

@[simp] theorem borderedCLMRC_apply (T : E →L[𝕜] E) (ψ : E) (p : E × 𝕜) :
    borderedCLMRC T ψ p = borderedMapRC T ψ p := by
  simp [borderedCLMRC, borderedMapRC]

/-- The explicit inverse, as a continuous `𝕜`-linear map. -/
def borderedInvCLMRC (R : E →L[𝕜] E) (ψ : E) : (E × 𝕜) →L[𝕜] (E × 𝕜) :=
  (R.comp (ContinuousLinearMap.fst 𝕜 E 𝕜) +
      ContinuousLinearMap.smulRight (ContinuousLinearMap.snd 𝕜 E 𝕜) ψ).prod
    (-(innerSL 𝕜 ψ).comp (ContinuousLinearMap.fst 𝕜 E 𝕜))

@[simp] theorem borderedInvCLMRC_apply (R : E →L[𝕜] E) (ψ : E) (q : E × 𝕜) :
    borderedInvCLMRC R ψ q = borderedInvRC R ψ q := by
  simp [borderedInvCLMRC, borderedInvRC]

/-- **The bordered map is a continuous linear equivalence at a simple eigenvalue**, with the explicit
inverse. -/
def borderedEquivRC {T R : E →L[𝕜] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜)
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫_𝕜 = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫_𝕜 • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫_𝕜 = 0) : (E × 𝕜) ≃L[𝕜] (E × 𝕜) :=
  ContinuousLinearEquiv.equivOfInverse (borderedCLMRC T ψ) (borderedInvCLMRC R ψ)
    (fun p => by simp [borderedInvRC_borderedMapRC hsymm hTψ hnorm hker hR hRψ p])
    (fun q => by simp [borderedMapRC_borderedInvRC hTψ hnorm hR hRψ q])

@[simp] theorem borderedEquivRC_coe {T R : E →L[𝕜] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜)
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫_𝕜 = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫_𝕜 • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫_𝕜 = 0) :
    ((borderedEquivRC hsymm hTψ hnorm hker hR hRψ : (E × 𝕜) ≃L[𝕜] (E × 𝕜)) :
        (E × 𝕜) →L[𝕜] (E × 𝕜)) = borderedCLMRC T ψ := rfl

/-- **The bordered map is invertible at a simple eigenvalue.** -/
theorem borderedCLMRC_isInvertible {T R : E →L[𝕜] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜)
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫_𝕜 = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫_𝕜 • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫_𝕜 = 0) :
    (borderedCLMRC T ψ).IsInvertible :=
  ⟨borderedEquivRC hsymm hTψ hnorm hker hR hRψ, rfl⟩

/-- **The `ℝ`-linear restriction of the bordered map is invertible.**  This is the form the implicit function
theorem consumes, the aperture parameter being real. -/
theorem borderedCLMRC_restrictScalars_isInvertible [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
    {T R : E →L[𝕜] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫_𝕜 = ⟪u, T v⟫_𝕜)
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫_𝕜 = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : 𝕜, φ = s • ψ)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫_𝕜 • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫_𝕜 = 0) :
    ((borderedCLMRC T ψ).restrictScalars ℝ).IsInvertible := by
  refine ⟨(borderedEquivRC hsymm hTψ hnorm hker hR hRψ).restrictScalars ℝ, ?_⟩
  ext p <;> rfl

end GaloisForLFunctions.HTGeometry

end
