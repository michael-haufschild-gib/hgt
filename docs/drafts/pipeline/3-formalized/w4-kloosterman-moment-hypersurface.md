# W4 — Kloosterman moments as a torus hypersurface

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every moment of the existing Kloosterman family is an additive-character sum on an explicit torus hypersurface.

## Exact claim

For a finite field `F`, primitive additive character `ψ`, `b ∈ F`, and `m ≥ 0`, put `K(a,b) = Σ_{x≠0} ψ(ax+b/x)`. Then

`Σ_{a∈F} K(a,b)^m = #F · Σ_{x∈(F×)^m, Σx_j=0} ψ(b Σx_j⁻¹)`.

For `b ≠ 0`, restricting the family to `a ≠ 0` subtracts `(-1)^m`. Every `K(a,b)` is real, so every even moment over any set of parameters is nonnegative.

## Proof mechanism

Expand the power into ordered nonzero tuples, combine characters, and interchange finite sums. Orthogonality in `a` kills tuples with nonzero coordinate sum and contributes `#F` on the remaining hypersurface. No numerical evaluation or purity bound is used.

## Role in W4

This specifies a genuine finite-field family and the variety carrying its global tensor moments. The factor `#F` comes from the one-dimensional parameter space independently of `m`. The remaining character sum still requires cancellation; the identity alone does not prove the fixed tensor loss or construct a family containing ζ.

## Formalization

`ArithmeticKunnethTheory/WeightFamilies/KloostermanMomentHypersurface.lean`:

- `kloosterman_tensor_expansion`, `kloosterman_moment_hypersurface`.
- `kloosterman_punctured_moment_hypersurface`: exact correction at the singular parameter.
- `kloosterman_conj`, `kloosterman_even_trace_nonneg`, `kloosterman_even_moment_nonneg`.

Checked with `lake --old env lean`.
