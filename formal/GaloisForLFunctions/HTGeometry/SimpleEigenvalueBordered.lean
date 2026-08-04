import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The bordered system of a simple eigenvalue

Perturbation theory for a simple eigenvalue runs through the *bordered* system: instead of inverting
`T = A - nu` — which is impossible, since `T` kills the eigenvector — one inverts

```text
S (phi, t) = (T phi - t • psi, ⟪psi, phi⟫)
```

on `E × ℝ`.  That is the operator whose invertibility the implicit function theorem needs in order to produce a
differentiable eigenvalue branch, and it is invertible exactly when the eigenvalue is simple.

This file proves the direction perturbation theory consumes, *constructively*: from a pseudo-inverse `R` of `T`
modulo the eigendirection, the inverse of the bordered map is written down explicitly,

```text
S⁻¹ (y, a) = (R y + a • psi, -⟪psi, y⟫).
```

The structural inputs are symmetry of `T`, `T psi = 0`, normalization `⟪psi, psi⟫ = 1`, and simplicity in the
form `ker T ⊆ span psi`.  Nothing else — no compactness, no completeness, no continuity of the inverse — so the
statement applies verbatim to the band operator of the constrained CCM layer.
-/

noncomputable section

open RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The bordered map of a symmetric operator at an eigenvector. -/
def borderedMap (T : E →L[ℝ] E) (ψ : E) (p : E × ℝ) : E × ℝ :=
  (T p.1 - p.2 • ψ, ⟪ψ, p.1⟫)

/-- The candidate inverse, built from a pseudo-inverse `R` of `T` modulo the eigendirection. -/
def borderedInv (R : E →L[ℝ] E) (ψ : E) (q : E × ℝ) : E × ℝ :=
  (R q.1 + q.2 • ψ, -⟪ψ, q.1⟫)

/-- The eigendirection is orthogonal to the range of a symmetric operator killing it. -/
theorem inner_eigen_apply_eq_zero {T : E →L[ℝ] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫ = ⟪u, T v⟫) (hTψ : T ψ = 0) (φ : E) :
    ⟪ψ, T φ⟫ = 0 := by
  have h := hsymm ψ φ
  rw [hTψ, inner_zero_left] at h
  exact h.symm

/-- **The pseudo-inverse is a left inverse modulo the eigendirection.**  This is where simplicity enters:
`T (R (T phi) - phi) = 0`, so the difference lies in `ker T = span psi`, and pairing with `psi` pins the
coefficient. -/
theorem borderedInv_left {T R : E →L[ℝ] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫ = ⟪u, T v⟫)
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫ = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : ℝ, φ = s • ψ)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫ • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫ = 0)
    (φ : E) : R (T φ) = φ - ⟪ψ, φ⟫ • ψ := by
  have hTφψ : ⟪ψ, T φ⟫ = 0 := inner_eigen_apply_eq_zero hsymm hTψ φ
  have hzero : T (R (T φ) - φ) = 0 := by
    rw [map_sub, hR (T φ), hTφψ]
    simp
  obtain ⟨s, hs⟩ := hker _ hzero
  have hpair : ⟪ψ, R (T φ) - φ⟫ = s := by
    rw [hs, real_inner_smul_right, hnorm, mul_one]
  have hpair2 : ⟪ψ, R (T φ) - φ⟫ = -⟪ψ, φ⟫ := by
    rw [inner_sub_right, hRψ, zero_sub]
  have hsval : s = -⟪ψ, φ⟫ := by
    rw [← hpair, hpair2]
  have hdiff : R (T φ) - φ = (-⟪ψ, φ⟫) • ψ := by
    rw [hs, hsval]
  have := sub_eq_iff_eq_add.mp hdiff
  rw [this, neg_smul]
  abel

/-- **The bordered map is bijective at a simple eigenvalue**, with the explicit inverse
`(y, a) ↦ (R y + a • psi, -⟪psi, y⟫)`.  Both composites are computed directly; the left inverse uses the
simplicity input through `borderedInv_left`. -/
theorem borderedMap_bijective {T R : E →L[ℝ] E} {ψ : E}
    (hsymm : ∀ u v : E, ⟪T u, v⟫ = ⟪u, T v⟫)
    (hTψ : T ψ = 0) (hnorm : ⟪ψ, ψ⟫ = 1)
    (hker : ∀ φ : E, T φ = 0 → ∃ s : ℝ, φ = s • ψ)
    (hR : ∀ y : E, T (R y) = y - ⟪ψ, y⟫ • ψ)
    (hRψ : ∀ y : E, ⟪ψ, R y⟫ = 0) :
    Function.Bijective (borderedMap T ψ) := by
  have hright : ∀ q : E × ℝ, borderedMap T ψ (borderedInv R ψ q) = q := by
    intro q
    obtain ⟨y, a⟩ := q
    have h1 : T (R y + a • ψ) - (-⟪ψ, y⟫) • ψ = y := by
      rw [map_add, hR y, map_smul, hTψ]
      simp
      abel
    have h2 : ⟪ψ, R y + a • ψ⟫ = a := by
      rw [inner_add_right, hRψ, real_inner_smul_right, hnorm]
      ring
    rw [borderedMap, borderedInv]
    exact Prod.ext h1 h2
  have hleft : ∀ p : E × ℝ, borderedInv R ψ (borderedMap T ψ p) = p := by
    intro p
    obtain ⟨φ, t⟩ := p
    have hTφψ : ⟪ψ, T φ⟫ = 0 := inner_eigen_apply_eq_zero hsymm hTψ φ
    have h1 : R (T φ - t • ψ) + ⟪ψ, φ⟫ • ψ = φ := by
      rw [map_sub, map_smul, borderedInv_left hsymm hTψ hnorm hker hR hRψ φ]
      have hRψzero : R ψ = 0 := by
        have hTRψ : T (R ψ) = 0 := by
          rw [hR ψ, hnorm]
          simp
        obtain ⟨s, hs⟩ := hker _ hTRψ
        have : ⟪ψ, R ψ⟫ = s := by
          rw [hs, real_inner_smul_right, hnorm, mul_one]
        rw [hRψ ψ] at this
        rw [hs, ← this, zero_smul]
      rw [hRψzero]
      simp
    have h2 : -⟪ψ, T φ - t • ψ⟫ = t := by
      rw [inner_sub_right, hTφψ, real_inner_smul_right, hnorm]
      ring
    rw [borderedInv, borderedMap]
    exact Prod.ext h1 h2
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

end GaloisForLFunctions.HTGeometry

end
