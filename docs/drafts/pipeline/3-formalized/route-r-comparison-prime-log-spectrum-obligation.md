# Route R comparison forces the prime-logarithm spectrum

- **ID:** `route-r-comparison-prime-log-spectrum-obligation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — necessary condition + no-go on finite models
- **Source:** follows `trace-derivation-cyclic-cocycle-transport-law`; motivated by the
  Hilbert–Pólya framing surveyed in arXiv 2606.09096 (*Weil's quadratic form via the screw
  function*), which conjectures a self-adjoint operator with the zeta zeros as spectrum
- **Statement:** any ℂ-linear multiplicative comparison of the rational adelic cyclic source that
  intertwines the derivations and pulls back the zero-adele trace forces `± log p` into the point
  spectrum of the target derivation for every prime `p`, with nonzero eigenvectors; consequently the
  target is infinite-dimensional.

## Goal

The transport law reduced the Route R comparison obligation to two intertwining identities. This
card extracts what those identities *cost*: a necessary spectral condition on the target, checkable
before any construction is attempted.

## Gates

- [x] 0 → 1 in-progress: hypotheses frozen as ℂ-linear multiplicative `f`, target `(B, τ_B, D_B)`
- [x] 1 → 2 fully-proven: eigenvalue transport plus distinctness of prime logarithms
- [x] 2 → 3 formalized: Lean module below, axiom audit `[propext, Classical.choice, Quot.sound]`,
      non-vacuity certified by the identity comparison
- [ ] 3 → 4 publication-ready: not intended as standalone publication

## The theorem

Let `f : S →ₗ[ℂ] B` be multiplicative on the rational adelic cyclic source `S`, with
`D_B ∘ f = f ∘ ∂_ℓ` and `τ_B ∘ f = ε₀`. Then for every prime `p`:

1. `D_B (f u_p) = (log p) · f u_p` and `f u_p ≠ 0`;
2. `D_B (f u_{p⁻¹}) = (-log p) · f u_{p⁻¹}` and `f u_{p⁻¹} ≠ 0`;
3. hence `± log p ∈ point spectrum of D_B`;
4. the family `{f u_p}_p` is linearly independent, since the eigenvalues `log p` are pairwise
   distinct;
5. therefore `B` is not a finite ℂ-module.

Non-erasure in 1 and 2 is not assumed: it is the conclusion of `primeAtom_not_erased`, which
follows from the same two intertwining identities.

## Consequence for the producer

The remaining Route R producer — exhibit `(B, τ_B, D_B)` reading the fixed Xi physical residue plus
an `f` with `D_B ∘ f = f ∘ ∂_ℓ` and `τ_B ∘ f = ε₀` — now has a cheap necessary test:

> **The target's derivation must already have `{± log p : p prime}` in its point spectrum.**

Any candidate whose derivation has finite rank, compact resolvent with the wrong spectrum, or a
finite-dimensional model is excluded immediately. This is the exact spectral signature of the
Hilbert–Pólya / Connes trace-formula targets, so the constraint is a discriminator, not a
prohibition: it says the comparison can only land in an object whose derivation is already
arithmetically calibrated.

Read together with `adelic-phase-defect-character-blindness-law`, the situation is:

| Layer | Verdict |
|---|---|
| coboundary-defect / reciprocity data | provably blind to `Re ρ` |
| phase / cocycle data, transported | non-erasure free, but forces the prime-log spectrum |
| finite-rank target | excluded |

## Non-vacuity

The identity comparison `(S, ε₀, ∂_ℓ, id)` satisfies every hypothesis, so no result here is
vacuous; specialising to it yields `cyclicSource_not_module_finite`.

## Lean

`formal/GaloisForLFunctions/RHTower/RouteRComparisonPrimeSpectrumObligation.lean`

- `ccmKummerDerivAdd_primeAtomForward`, `ccmKummerDerivAdd_primeAtomBackward`
- `primeLog_injective`
- `hasEigenvector_primeAtomForward`, `hasEigenvector_primeAtomBackward`, `hasEigenvalue_primeLog`
- `linearIndependent_primeAtomForward_image`, `not_module_finite_of_comparison`
- `cyclicSource_not_module_finite`

## Falsifier

Exhibit a finite-dimensional `(B, τ_B, D_B)` and a ℂ-linear multiplicative `f` satisfying both
intertwining identities. Item 5 excludes it.

## Log

- 2026-08-05 — created directly at stage 3
