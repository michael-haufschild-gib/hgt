# Separable Haar carriers cannot have continuous dilations

- **ID:** SEPARABLE-HAAR-CONTINUITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Finite-index Mautner rigidity](../1-in-progress/finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** If `p` is positive definite with integer successor and `ψ` is a Hermitian slope kernel, then continuity at one of the dilation reading of `p+ψ∘slope` forces its negative index to be infinite.

## Dependency-closed paper proof

Write `q=r/d` in lowest terms. If `q≠1`, the integer `r−d` is nonzero, hence `d|q−1|=|r−d|≥1`. Also `|r|≥1`, so `1≤height(q)|q−1|`. The proved Hecke bound therefore gives `|p(D_q)|²≤|q−1|` for every nonidentity rational unit.

For `a=0,…,n`, take distinct positive rational units `u_(m,a)=1+a/(m+1)`. Every off-diagonal ratio tends to one without equalling one, so the carrier Gram matrices converge to the identity. If the total dilation reading is continuous at one, the slope Gram matrices converge to `(1+ψ(1))J−I`. The injective coefficient map `c↦(−Σc,c)` has zero-sum image; on that image the limiting form is `−|Σc|²−Σ|c_a|²`, strictly negative away from zero. Matrix index semicontinuity gives `n≤κ(ψ)` for every `n`. The positive-carrier index law transfers infinite index to the affine kernel.

No normalization of `ψ(1)` is needed. The [exact index law](../3-formalized/positive-haar-carriers-preserve-the-index-of-slope-corrections.md) is the positive structural statement behind this obstruction. General finite-index affine kernels need not have the asserted separable decomposition; that remains the O5 gap.

## Lean certificate

`AdelicKreinGeometry/Haar/ContinuousDilationsNeedInfiniteIndex.lean` proves:

- `normSq_dilation_le_abs_sub_one`.
- `negIndex_slope_eq_top_of_continuous_dilation`.
- `negIndex_add_slope_eq_top_of_continuous_dilation`.
- `negIndex_add_slope_eq_top_of_weil_dilation`, using the proved continuity of Weil's spline correlation.

The direct `lake --old env lean` leaf check passed. All four transitive axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. The AdelicKreinGeometry umbrella imports the leaf.
