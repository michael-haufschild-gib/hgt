import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The Hellmann–Feynman derivative

For a differentiable family of self-adjoint operators with a differentiable normalized eigenvector, the
eigenvalue derivative is the expectation of the operator derivative:

```text
nu'(c) = ⟪psi, (dA/dc) psi⟫.
```

The mechanism is that the eigenvector's own motion cancels: differentiating `A_t psi_t = nu_t • psi_t` and
pairing with `psi` produces `⟪psi, A psi'⟫` on the left and `nu ⟪psi, psi'⟫` on the right, and these agree by
self-adjointness together with the eigenrelation — so no information about `psi'` is needed beyond its
existence.  Only the value at the single point `c` is used, and self-adjointness is only needed against the
single vector `psi'(c)`.

mathlib has no Hellmann–Feynman lemma.  This file supplies it in the form the endpoint-response identity of
the constrained CCM layer consumes: the derivative datum of the family is the vector `w` playing the role of
`(dA/dc) psi`.
-/

noncomputable section

open RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

/-- **Hellmann–Feynman, local form.**  Let `psi` be a differentiable curve of vectors, normalized at the
point `c`, let `nu` be a differentiable function with `A t (psi t) = nu t • psi t` for all `t` near `c`, and
suppose the curve `t ↦ A t (psi t)` is differentiable at `c` with derivative split as `w + A c (psi' c)` — `w`
being the contribution of the family's own motion, i.e. `(dA/dc) psi`.  If `A c` is self-adjoint against
`psi' c` then

```text
nu'(c) = ⟪psi c, w⟫.
```

Only a neighbourhood of `c` is used, because a derivative is a local object. -/
theorem hellmann_feynman_eventually {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ψ : ℝ → E} {ψ' : E} {A : ℝ → E → E} {ν : ℝ → ℝ} {νp : ℝ} {w : E} {c : ℝ}
    (hnorm : ⟪ψ c, ψ c⟫ = 1)
    (hsa : ⟪ψ c, A c ψ'⟫ = ⟪A c (ψ c), ψ'⟫)
    (hν : HasDerivAt ν νp c)
    (hψ : HasDerivAt ψ ψ' c)
    (hAψ : HasDerivAt (fun t => A t (ψ t)) (w + A c ψ') c)
    (hrel : ∀ᶠ t in nhds c, A t (ψ t) = ν t • ψ t) :
    νp = ⟪ψ c, w⟫ := by
  -- the eigenrelation makes the two curves agree near `c`, so the derivatives agree
  have hsmul : HasDerivAt (fun t => ν t • ψ t) (ν c • ψ' + νp • ψ c) c := hν.smul hψ
  have hAψ' : HasDerivAt (fun t => ν t • ψ t) (w + A c ψ') c :=
    hAψ.congr_of_eventuallyEq (hrel.mono fun t ht => ht.symm)
  have hderiv : w + A c ψ' = ν c • ψ' + νp • ψ c := hAψ'.unique hsmul
  -- pair with `psi c`
  have hpair : ⟪ψ c, w⟫ + ⟪ψ c, A c ψ'⟫ = ν c * ⟪ψ c, ψ'⟫ + νp := by
    have h := congrArg (fun v : E => ⟪ψ c, v⟫) hderiv
    simp only [inner_add_right, real_inner_smul_right] at h
    rw [hnorm, mul_one] at h
    exact h
  -- the eigenvector's own motion cancels
  have hcancel : ⟪ψ c, A c ψ'⟫ = ν c * ⟪ψ c, ψ'⟫ := by
    rw [hsa, hrel.self_of_nhds, real_inner_smul_left]
  rw [hcancel] at hpair
  linarith [hpair]

/-- **Hellmann–Feynman.**  The global-eigenrelation form: for a differentiable curve of normalized vectors
with `A t (psi t) = nu t • psi t` for every `t`, the eigenvalue derivative is the expectation of the family's
motion. -/
theorem hellmann_feynman {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {ψ : ℝ → E} {ψ' : E} {A : ℝ → E → E} {ν : ℝ → ℝ} {νp : ℝ} {w : E} {c : ℝ}
    (hnorm : ⟪ψ c, ψ c⟫ = 1)
    (hsa : ⟪ψ c, A c ψ'⟫ = ⟪A c (ψ c), ψ'⟫)
    (hν : HasDerivAt ν νp c)
    (hψ : HasDerivAt ψ ψ' c)
    (hAψ : HasDerivAt (fun t => A t (ψ t)) (w + A c ψ') c)
    (hrel : ∀ t, A t (ψ t) = ν t • ψ t) :
    νp = ⟪ψ c, w⟫ :=
  hellmann_feynman_eventually hnorm hsa hν hψ hAψ (Filter.Eventually.of_forall hrel)


/-! ## Commuting operators on a simple eigenspace

If two operators commute and one of them has a simple eigenvalue, the other acts on that eigenvector as a
scalar.  This is the mechanism that turns the band eigenrelation into the finite-Fourier eigenrelation: the
transform commutes with the band operator, so on a one-dimensional eigenspace it can only multiply. -/

/-- **A commuting operator acts as a scalar on a simple eigenvector.**  No topology and no linearity of `Q` is
needed — only that `F` commutes with `Q`, is homogeneous, and that the `nu`-eigenspace of `Q` is spanned by
`psi`. -/
theorem exists_scalar_of_commuting_of_simple {E : Type*} [AddCommGroup E] [Module ℝ E]
    {Q F : E → E} {ν : ℝ} {ψ : E}
    (hcomm : ∀ φ, F (Q φ) = Q (F φ))
    (hQψ : Q ψ = ν • ψ)
    (hFsmul : ∀ (t : ℝ) (φ : E), F (t • φ) = t • F φ)
    (hsimple : ∀ φ, Q φ = ν • φ → ∃ t : ℝ, φ = t • ψ) :
    ∃ μ : ℝ, F ψ = μ • ψ := by
  have hFeig : Q (F ψ) = ν • F ψ := by
    rw [← hcomm ψ, hQψ, hFsmul]
  exact hsimple (F ψ) hFeig


end GaloisForLFunctions.HTGeometry

end
