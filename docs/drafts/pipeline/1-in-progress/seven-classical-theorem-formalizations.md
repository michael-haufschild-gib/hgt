# Seven classical theorem formalizations

- **Stage:** 1-in-progress (paused)
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
| Affine-group expanders | Explicit affine action with uniform spectral gap | `HTGeometry.mggAffine_expander_family` and `mggAffine_centered_norm_le` prove the native MGG family has contraction factor `5√2/8 < 1`. See [formalized theorem](../3-formalized/margulis-gabber-galil-affine-expanders.md). |
| Björner squarefree complex | Literal prime-support complex, Euler characteristic/Mertens identity, homotopy and Betti-number results | `RHTower.sum_primeSets_neg_one_pow` gives the Mertens identity. `HTGeometry.primeTwoComplementEquiv` identifies complementary facets with odd squarefree `N/2 < m ≤ N`; every proper subface lies in the prime-two star. [Wedge and homology proof remains incomplete](bjorner-squarefree-complex.md). |
| Logarithmic Chowla | Logarithmic two-point Liouville/Möbius cancellation for distinct nonproportional affine forms | Corpus averaged-Chowla interface assumes cancellation; almost-everywhere twisted results do not imply the untwisted theorem. Full endpoint remains. |

The existing `RHTower.pm_tendsto_harmonic_average_of_mean` transfers Cesàro convergence
to logarithmic convergence. Applying it to Chowla still requires a proved correlation theorem.
