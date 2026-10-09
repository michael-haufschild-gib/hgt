# JAS goal loop (route JAS — joint ancestry)

- **ID:** jas-loop-2026-10-09
- **Stage:** 1-in-progress
- **Type:** CONJECTURE loop ledger
- **Statement:** Develop route JAS toward an unconditional Lean proof of RH by conjecture → proof/kill → next.

## Big picture (from the Lean corpus, 2026-10-09)
- Every JAS invariant in the 31 `JointAncestry*` modules is position-only: it is a function of
  `Re ρ` (prime-Poisson reflection sewing ⇔ Kakutani ⇔ `Re ρ = 1/2`; Haar vacuum ⇔ `σ > 1/2`;
  boundary flux ∝ `Im z`; half-density residue a function of `|2β−1|`). None consumes `ξ(ρ)=0`.
- The only zero-consuming objects near JAS: the theta kernel operator `B` (HS, nonzero spectrum
  `{-1/z : Ξ_C z = 0}`) and its source modes; integer anomalies with profile `shiftMultiplier·XiC`.
- Theta source = Gamma profile ⋆ Euler measure: `k(x) = Σ n^{-1/2} g(x + log n)`; evenness of `k` is
  modularity; prime-Poisson `μ_s` averages the Bohr lift to the `s`-shifted Euler source.
- Wall: prime-Poisson / Haar / 𝓗² structure sees `ζ` only where the Euler series converges
  (probability-cone wall); zero information must enter through modularity (theta).

## Ledger
| # | Conjecture | Verdict | Lean |
|-|-|-|-|
| 1 | Pole gluing: `μ_s ∗ (−)_*μ_{1−s̄} = μ_1` for every strip point; grade creation = convolution by `μ_1`; `μ_s ∗ (−)_*μ_s = μ_1 ⇔ σ = 1/2` | PROVED; zero-blind (positive survivor of superselection) | H:TorusPoissonConvolutionSemigroup; R:JointAncestryPoleGluing |
