import GaloisForLFunctions.RHTower.AsymptoticSelfAdjointness

/-!
# Compression cannot manufacture asymptotic self-adjointness

The asymptotic criterion asks for approximants whose anti-Hermitian defect tends to zero in norm.
The natural hope is that compressing a source operator to an exhausting family of subspaces achieves
this — that the defect is compact, and compressions of a compact operator are small.  It does not.

**The defect commutes with compression.**  For a self-adjoint projection `P`,
`(P A P)* = P A* P`, so the anti-Hermitian part of the compression is the compression of the
anti-Hermitian part:

```text
Im (P A P)  =  P (Im A) P .
```

Compression therefore never reduces the defect below what compressing `Im A` gives; it cannot create
self-adjointness that the source lacks.

**Compactness is the wrong hypothesis.**  If `P_n ↑ I`, then for any vector `x` fixed by every `P_n`
whose image `H x` is also fixed, `‖P_n H P_n‖ ≥ ‖H x‖ / ‖x‖`, a positive constant independent of `n`.
So `‖P_n H P_n‖` does **not** tend to zero — indeed it tends up to `‖H‖`.  Compactness of `H` says
the *tail* `(I - P_n) H` is small, which is a statement about what is discarded, not about what is
kept.

> **A construction cannot become asymptotically self-adjoint by truncation.  The defect must be
> vanishing by construction: `A_n = S_n + K_n` with `S_n` self-adjoint and `‖K_n‖ → 0`.  Compactness
> of a fixed defect is not enough, and neither is any compression scheme.**

This closes the natural reading of the corpus's Calkin-rigidity results as a positive input: the
commutator being compact places the defect in the Calkin algebra's kernel, but the *finite stages*
retain its full norm.

This file formalizes the compression identity for the defect and the lower bound that blocks decay.
-/

open ContinuousLinearMap Filter Topology

noncomputable section

namespace RHTower

section CompressionAdjoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The defect commutes with compression.**  For a self-adjoint `P`, the adjoint of the compression
is the compression of the adjoint, so the anti-Hermitian part of `P A P` is `P (Im A) P`. -/
theorem adjoint_compression (A P : E →L[ℂ] E) (hP : adjoint P = P) :
    adjoint (P ∘L (A ∘L P)) = P ∘L (adjoint A ∘L P) := by
  rw [adjoint_comp, adjoint_comp, hP]
  rfl

/-- Consequently the compression of a self-adjoint operator is self-adjoint, and no compression of a
non-self-adjoint operator is self-adjoint unless its defect is annihilated. -/
theorem compression_selfAdjoint_of_selfAdjoint (A P : E →L[ℂ] E)
    (hP : adjoint P = P) (hA : adjoint A = A) :
    adjoint (P ∘L (A ∘L P)) = P ∘L (A ∘L P) := by
  rw [adjoint_compression A P hP, hA]

end CompressionAdjoint

section CompressionNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Compression cannot shrink the defect below what it does to a fixed vector.**  If `x` and `H x`
are both fixed by `P`, the compression has norm at least `‖H x‖ / ‖x‖`. -/
theorem compression_norm_lower_bound (H P : E →L[ℂ] E) {x : E}
    (hPx : P x = x) (hPHx : P (H x) = H x) :
    ‖H x‖ ≤ ‖P ∘L (H ∘L P)‖ * ‖x‖ := by
  have hval : (P ∘L (H ∘L P)) x = H x := by
    simp only [coe_comp', Function.comp_apply, hPx, hPHx]
  calc ‖H x‖ = ‖(P ∘L (H ∘L P)) x‖ := by rw [hval]
    _ ≤ ‖P ∘L (H ∘L P)‖ * ‖x‖ := le_opNorm _ _

/-- **Compactness does not make compressions vanish.**  If every stage fixes `x` and `H x`, the
compression norms are bounded below by a positive constant, so they cannot tend to zero. -/
theorem compression_norms_not_tendsto_zero (H : E →L[ℂ] E) (P : ℕ → (E →L[ℂ] E)) {x : E}
    (hx : x ≠ 0)
    (hPx : ∀ n, P n x = x) (hPHx : ∀ n, P n (H x) = H x) :
    ∀ n, ‖H x‖ / ‖x‖ ≤ ‖P n ∘L (H ∘L P n)‖ := by
  intro n
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [div_le_iff₀ hxpos]
  exact compression_norm_lower_bound H (P n) (hPx n) (hPHx n)

/-- The lower bound is strictly positive, so no compression scheme of this kind can supply the
asymptotic criterion. -/
theorem compression_lower_bound_pos (H : E →L[ℂ] E) {x : E} (hx : x ≠ 0) (hHx : H x ≠ 0) :
    0 < ‖H x‖ / ‖x‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  exact div_pos (norm_pos_iff.mpr hHx) hxpos

end CompressionNorm

/-- **What is actually required.**  The defect norms must vanish along the sequence; then the
imaginary parts of the zeros vanish with them, and the asymptotic criterion applies. -/
theorem defect_vanishing_suffices {ε : ℕ → ℝ} {Fn : ℕ → ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn XiC atTop)
    (hFn : ∀ᶠ n in atTop, Differentiable ℂ (Fn n))
    (hzero : ∀ᶠ n in atTop, ∀ w, Fn n w = 0 → |w.im| ≤ ε n)
    (hε : Tendsto ε atTop (nhds 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_asymptotically_real_zeros hconv hFn hzero hε

end RHTower
