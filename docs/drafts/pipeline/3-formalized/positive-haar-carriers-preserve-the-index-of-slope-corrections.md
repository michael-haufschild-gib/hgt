# Positive Haar carriers preserve the index of slope corrections

- **ID:** POSITIVE-HAAR-SLOPE-INDEX
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Finite-index Mautner rigidity](../1-in-progress/finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** For every positive-definite affine kernel `p` with integer successor and every Hermitian `ψ : ℚˣ → ℂ`, `κ(p+ψ∘slope)=κ(ψ)`.

## Dependency-closed paper proof

Fix a finite slope family `u_a` and its dilation lifts `x_a`. For each `N>0`, the proved arithmetic escape construction gives shifts `t_i` such that distinct translates `T_(t_i)x_a` are Haar-orthogonal. For fixed `a`, their pairwise quotients are translations, so the integer successor gives exactly the same orthogonality for `p`.

Compress the Gram matrix of `p` by coefficients `c_a/N` on each translated copy. The resulting matrix `P_N` is positive semidefinite and has every diagonal entry equal to `1/N`. Semidefinite Cauchy–Schwarz gives `|P_N(a,b)|≤1/N`. The same compression of `p+ψ∘slope` equals `P_N+A`, where `A_ab=ψ(u_a⁻¹u_b)`. Its negative index is bounded by `κ(p+ψ∘slope)`.

The matrices `P_N+A` converge entrywise to the Hermitian matrix `A`. The proved lower semicontinuity of matrix index gives `ν(A)≤κ(p+ψ∘slope)`. Taking the supremum over the finite slope families proves the lower bound. Positivity of `p` and pullback monotonicity give the reverse bound.

Haar orthogonality selects the translation averages. The carrier needs only positivity and the prescribed successor; no Hecke support or continuity is assumed. No novelty claim is made for semidefinite Cauchy–Schwarz or index semicontinuity.

## Continuity consequence

The [formalized continuity obstruction](separable-haar-carriers-cannot-have-continuous-dilations.md)
forces infinite index whenever the total dilation reading extends continuously at one. In
particular, no finite-index kernel in this class carries Weil's spline correlation.

## Verification

`AdelicKreinGeometry/Haar/IndexPreservation.lean` proves
`negIndex_add_slope_of_integer_successor`; `negIndex_haar_add_slope` is its Haar corollary.
The direct `lake --old env lean` check passed. The new theorem's transitive axiom closure is
exactly `propext`, `Classical.choice`, and `Quot.sound`. The umbrella import is present.
