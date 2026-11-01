# Seven classical theorem formalizations

- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM
- **Goal:** Unconditional, dependency-audited Lean proofs of all seven requested theories.
- **Acceptance:** Literal mathematical objects and conclusions; no assumed analytic input,
  custom axioms, placeholders, native evaluation, or raised elaboration limits.

| Target | Required endpoint | Current evidence / remaining core |
|---|---|---|
| Lax–Phillips scattering | Translation representations, scattering operator, associated contraction semigroup | Corpus `lagariasSuzuki_ne_zero` is a related Eisenstein line law, not the scattering theorem. Full endpoint remains. |
| Voronoi summation | Summation identity with arithmetic coefficients, transformed test function, convergence and main terms | Corpus `GammaRCubeVoronoiL2` supplies a transform, not a summation identity. Full endpoint remains. |
| Zwegers indefinite theta | Convergence and modular transformation of completed signature `(r−1,1)` theta series | [Zwegers thesis, Chapter 2](https://arxiv.org/abs/0807.4834). No complete corpus proof found. |
| CKS limiting Hodge structures | Limiting mixed Hodge structure and multivariable nilpotent/SL₂ orbit results | [Cattani–Kaplan–Schmid](https://annals.math.princeton.edu/1986/123-3/p02). No complete corpus proof found. |
| Affine-group expanders | Explicit affine action with uniform spectral gap | Auditing MGG on `(ℤ/nℤ)²`: normalized nonconstant spectral radius ≤ `5√2/8`. This supplies a specific affine family; broader affine-group statements remain separate. |
| Björner squarefree complex | Literal prime-support complex, Euler characteristic/Mertens identity, homotopy and Betti-number results | [Björner](https://arxiv.org/abs/1101.5704). No complete corpus proof found. |
| Logarithmic Chowla | Logarithmic two-point Liouville/Möbius cancellation for distinct nonproportional affine forms | Corpus averaged-Chowla interface assumes cancellation; almost-everywhere twisted results do not imply the untwisted theorem. Full endpoint remains. |

## Reuse audit

GitHub searches covered all seven names. Concrete affine-expander candidate:
[`girving/aks`](https://github.com/girving/aks), revision
`c7fb62ed80a4a610f87f34db0082cadbd7c00c9f`, Apache-2.0.
`AKS/MGG/Spectral.lean::spectralGap_mgg` has a substantive Fourier/weighted-Young proof;
upstream `AKS/MGG/Axioms.lean` asserts only standard Lean axioms.
Local verification is still required. Upstream DFT raises `maxHeartbeats`; this must be removed
and its proof optimized. Unused reflexive stand-in `abs_one_add_rootOfUnity` must be omitted.
Only the MGG dependency closure is relevant, not the repository's native certificate path.

Additional candidate: [`openai/math`, scope 007](https://github.com/openai/math/blob/main/lean/docs/007.md),
HEAD `4eaee87548250b2682affda7d05d947c05554bae`.
Apache-2.0; upstream Lean `v4.34.1` differs from local `v4.32.2`.
`lean/OAI/NumberTheory/TwoPointCorrelations/FinalMain.lean` exports
`liouville_log_saving` from `TwoPoint/Main.lean::liouvilleLogSaving`.
The latter invokes `liouvilleLogSaving_of_mrt mrtLiouvilleShortInput`.
Required audit: transitive short-interval input and the entire ordinary-correlation proof;
then partial summation for logarithmic Liouville cancellation. The comparator challenge's
placeholders are specification files, not reusable proofs. Möbius cancellation needs its own
dependency check. No result from this candidate has been integrated or kernel-verified locally.

[Huang's mock-theta formalization](https://infsup.com/en/breaking-through-mock-theta/)
proves a formal Hahn-series identity, expressly without analytic convergence or modular forms;
it does not discharge the Zwegers endpoint.

## Affine expander proof

The eight edges are four affine maps `(x+2y,y)`, `(x,2x+y)`,
`(x+2y+1,y)`, `(x,2x+y+1)` and their inverses. Rotation is involutive,
so the normalized walk is self-adjoint and preserves constants.
The two-dimensional finite Fourier transform converts the Rayleigh form to shear correlations
weighted by `|cos(πa/n)|`. Weighted Young inequalities, with reciprocal weights determined by
distance to the axes, bound the nonzero-frequency form by `5√2/4` times Fourier energy.
Parseval and walk normalization give `5√2/8`; the self-adjoint Rayleigh characterization gives
the operator-norm bound. All intermediate arithmetic and trigonometric inequalities require
local kernel verification before this row closes.

**Novelty verdict:** BRIDGE. These are requested classical formalizations; no new mathematical
theorem or research novelty is claimed.
