import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The Hellmann–Feynman theorem over an arbitrary `RCLike` field

`HellmannFeynman` proves the eigenvalue-derivative law for *real* inner product spaces.  The theorem physics
actually uses lives over `ℂ`, and the complex statement is not a corollary of the real one: over `ℂ` the
cancellation of the eigenvector's own motion produces a **conjugated** eigenvalue,

```text
⟪psi, A psi'⟫ = ⟪A psi, psi'⟫ = ⟪nu • psi, psi'⟫ = conj(nu) ⟪psi, psi'⟫,
```

so the mechanism only closes once one knows `conj(nu) = nu`.  That reality is not an extra assumption: it is
forced by symmetry of `A` against the eigenvector together with normalization, and is proved here first.

The conclusion is the Hellmann–Feynman law

```text
nu'(c) = ⟪psi(c), (dA/dc) psi(c)⟫,
```

in which the derivative datum of the family is the vector `w` playing the role of `(dA/dc) psi`.  As in the
real case only the value at the single point `c` is used, and the eigenrelation is only needed near `c`; the
eigenvector's own motion cancels, so no information about `psi'` is needed beyond its existence.

The last theorems are the physicist's form: a real eigenvalue function, whose derivative is the (automatically
real) expectation `re ⟪psi, w⟫`, and its specialization to a complex Hilbert space.
-/

noncomputable section

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **An eigenvalue at a normalized eigenvector is real.**  Only symmetry of the operator against the
eigenvector itself is used. -/
theorem eigenvalue_conj_eq_self_of_symmetric_at
    {ψ : E} {A : E → E} {ν : 𝕜}
    (hnorm : ⟪ψ, ψ⟫_𝕜 = 1)
    (hsa : ⟪ψ, A ψ⟫_𝕜 = ⟪A ψ, ψ⟫_𝕜)
    (hrel : A ψ = ν • ψ) :
    (starRingEnd 𝕜) ν = ν := by
  have h1 : ⟪ψ, A ψ⟫_𝕜 = ν := by
    rw [hrel, inner_smul_right, hnorm, mul_one]
  have h2 : ⟪A ψ, ψ⟫_𝕜 = (starRingEnd 𝕜) ν := by
    rw [hrel, inner_smul_left, hnorm, mul_one]
  rw [h1, h2] at hsa
  exact hsa.symm

variable [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Hellmann–Feynman over `𝕜`, local form.**  Let `psi` be a differentiable curve of vectors, normalized at
the point `c`, let `nu` be a differentiable scalar function with `A t (psi t) = nu t • psi t` for `t` near `c`,
and suppose the curve `t ↦ A t (psi t)` is differentiable at `c` with derivative split as `w + A c (psi' c)`.
If `A c` is symmetric against `psi' c` and against `psi c` then

```text
nu'(c) = ⟪psi c, w⟫.
```
-/
theorem hellmann_feynman_rclike_eventually
    {ψ : ℝ → E} {ψ' : E} {A : ℝ → E → E} {ν : ℝ → 𝕜} {νp : 𝕜} {w : E} {c : ℝ}
    (hnorm : ⟪ψ c, ψ c⟫_𝕜 = 1)
    (hsa : ⟪ψ c, A c ψ'⟫_𝕜 = ⟪A c (ψ c), ψ'⟫_𝕜)
    (hsa0 : ⟪ψ c, A c (ψ c)⟫_𝕜 = ⟪A c (ψ c), ψ c⟫_𝕜)
    (hν : HasDerivAt ν νp c)
    (hψ : HasDerivAt ψ ψ' c)
    (hAψ : HasDerivAt (fun t => A t (ψ t)) (w + A c ψ') c)
    (hrel : ∀ᶠ t in nhds c, A t (ψ t) = ν t • ψ t) :
    νp = ⟪ψ c, w⟫_𝕜 := by
  -- the eigenrelation makes the two curves agree near `c`, so the derivatives agree
  have hsmul : HasDerivAt (fun t => ν t • ψ t) (ν c • ψ' + νp • ψ c) c := hν.smul hψ
  have hAψ' : HasDerivAt (fun t => ν t • ψ t) (w + A c ψ') c :=
    hAψ.congr_of_eventuallyEq (hrel.mono fun t ht => ht.symm)
  have hderiv : w + A c ψ' = ν c • ψ' + νp • ψ c := hAψ'.unique hsmul
  -- pair with `psi c`
  have hpair : ⟪ψ c, w⟫_𝕜 + ⟪ψ c, A c ψ'⟫_𝕜 = ν c * ⟪ψ c, ψ'⟫_𝕜 + νp := by
    have h := congrArg (fun v : E => ⟪ψ c, v⟫_𝕜) hderiv
    simp only [inner_add_right, inner_smul_right] at h
    rw [hnorm, mul_one] at h
    exact h
  -- the eigenvalue is real, so the eigenvector's own motion cancels
  have hνreal : (starRingEnd 𝕜) (ν c) = ν c :=
    eigenvalue_conj_eq_self_of_symmetric_at hnorm hsa0 hrel.self_of_nhds
  have hcancel : ⟪ψ c, A c ψ'⟫_𝕜 = ν c * ⟪ψ c, ψ'⟫_𝕜 := by
    rw [hsa, hrel.self_of_nhds, inner_smul_left, hνreal]
  rw [hcancel, add_comm (ν c * ⟪ψ c, ψ'⟫_𝕜) νp] at hpair
  exact (add_right_cancel hpair).symm

/-- **Hellmann–Feynman over `𝕜`.**  The global-eigenrelation form, with a symmetric operator at the base
point. -/
theorem hellmann_feynman_rclike
    {ψ : ℝ → E} {ψ' : E} {A : ℝ → E → E} {ν : ℝ → 𝕜} {νp : 𝕜} {w : E} {c : ℝ}
    (hnorm : ⟪ψ c, ψ c⟫_𝕜 = 1)
    (hsymm : ∀ u v : E, ⟪A c u, v⟫_𝕜 = ⟪u, A c v⟫_𝕜)
    (hν : HasDerivAt ν νp c)
    (hψ : HasDerivAt ψ ψ' c)
    (hAψ : HasDerivAt (fun t => A t (ψ t)) (w + A c ψ') c)
    (hrel : ∀ t, A t (ψ t) = ν t • ψ t) :
    νp = ⟪ψ c, w⟫_𝕜 :=
  hellmann_feynman_rclike_eventually hnorm (hsymm (ψ c) ψ').symm (hsymm (ψ c) (ψ c)).symm
    hν hψ hAψ (Filter.Eventually.of_forall hrel)

/-- **Hellmann–Feynman for a real eigenvalue function.**  The expectation `⟪psi, w⟫` is then automatically
real, being the derivative of a real quantity. -/
theorem hellmann_feynman_rclike_ofReal
    {ψ : ℝ → E} {ψ' : E} {A : ℝ → E → E} {ν : ℝ → ℝ} {νp : ℝ} {w : E} {c : ℝ}
    (hnorm : ⟪ψ c, ψ c⟫_𝕜 = 1)
    (hsymm : ∀ u v : E, ⟪A c u, v⟫_𝕜 = ⟪u, A c v⟫_𝕜)
    (hν : HasDerivAt ν νp c)
    (hψ : HasDerivAt ψ ψ' c)
    (hAψ : HasDerivAt (fun t => A t (ψ t)) (w + A c ψ') c)
    (hrel : ∀ t, A t (ψ t) = ((ν t : ℝ) : 𝕜) • ψ t) :
    ((νp : ℝ) : 𝕜) = ⟪ψ c, w⟫_𝕜 := by
  have hν' : HasDerivAt (fun t => (((ν t : ℝ)) : 𝕜)) (((νp : ℝ)) : 𝕜) c := by
    have h := hν.smul_const (1 : 𝕜)
    simpa [Algebra.algebraMap_eq_smul_one] using h
  exact hellmann_feynman_rclike hnorm hsymm hν' hψ hAψ hrel

/-- **Hellmann–Feynman, the physicist's statement.**  The derivative of a real eigenvalue branch is the real
part of the expectation of the family's motion — and that expectation is real. -/
theorem hellmann_feynman_rclike_re
    {ψ : ℝ → E} {ψ' : E} {A : ℝ → E → E} {ν : ℝ → ℝ} {νp : ℝ} {w : E} {c : ℝ}
    (hnorm : ⟪ψ c, ψ c⟫_𝕜 = 1)
    (hsymm : ∀ u v : E, ⟪A c u, v⟫_𝕜 = ⟪u, A c v⟫_𝕜)
    (hν : HasDerivAt ν νp c)
    (hψ : HasDerivAt ψ ψ' c)
    (hAψ : HasDerivAt (fun t => A t (ψ t)) (w + A c ψ') c)
    (hrel : ∀ t, A t (ψ t) = ((ν t : ℝ) : 𝕜) • ψ t) :
    νp = RCLike.re (⟪ψ c, w⟫_𝕜) ∧ ((RCLike.re (⟪ψ c, w⟫_𝕜) : ℝ) : 𝕜) = ⟪ψ c, w⟫_𝕜 := by
  have h := hellmann_feynman_rclike_ofReal hnorm hsymm hν hψ hAψ hrel
  constructor
  · have := congrArg RCLike.re h
    simpa using this
  · have := congrArg RCLike.re h
    rw [RCLike.ofReal_re] at this
    rw [← this]
    exact h

end GaloisForLFunctions.HTGeometry

end
