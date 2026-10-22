# HB charged-KMS source-fidelity dichotomy

- **ID:** HB-KMS-FIDELITY-DICHOTOMY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB source-faithful neutral-sector localization
- **Statement:** `[LEAN-PROVED]` For every actual nonneutral charged double-KMS pair and every swap-equivariant partial response history, each time slice either preserves a scalar-detectable ordered-coordinate distinction or collapses the pair only by losing injectivity; a universal constant equivariant eraser realizes collapse at every charge.

## Goal

Kill reporter-only oriented repair and output-equality neutralization in the HB chain
`real theta source → charged-sector selection → occupation-aligned double KMS → RH`.
If true, source-faithful neutral localization must break swap in domain/evolution or derive actual
charge annihilation; adding an oriented reporter or observing equal outputs cannot suffice.

## Gates

- [x] 0 → 1  in-progress: corpus-defined charged pair, swap, partial response, and alignment endpoint
- [x] 1 → 2  fully-proven: complete paper proof, `[PAPER-PROVED]`, no open dependency
- [x] 2 → 3  formalized: exact unconditional Lean theorem, target build and axiom audit pass
- [ ] 3 → 4  publication-ready: not targeted

## Approach

Use actual visible state `v`, partner `Sv`, and equivariance `E_n(Sv)=S(E_n v)`.
At each time, equality of the two outputs contradicts pairwise source fidelity when `v≠Sv`;
inequality is detected by one ordered occupation-coordinate evaluation. Construct zero response on
the full domain to prove that output equality without fidelity is available at every charge.

## Exact proof chain

- `[CORPUS]` `v` and `Sv` are the actual normalized charged thermofield vectors.
- `[CORPUS]` nonzero horizon charge implies failure of occupation alignment.
- `[CORPUS]` every swap-equivariant history preserves the partner relation.
- `[PAPER-PROVED]` Actual vector equality implies equality of every squared occupation coefficient,
  hence occupation alignment and zero horizon charge. Conversely, zero charge makes the two KMS
  ratios equal, so the two ordered tensor half-densities coincide.
- `[PAPER-PROVED]` Let `v` be visible state, `Sv` partner, and `E_n` time-`n` response. Equivariance
  gives `E_n(Sv)=S(E_n v)`. If `E_n v=E_n(Sv)` off wall, `E_n` is not injective because `v≠Sv`.
  If outputs differ, extensionality of `lp` supplies an ordered occupation coordinate where their
  values differ; evaluation there is a complex-linear scalar reporter separating them.
- `[PAPER-PROVED]` Therefore, under injectivity, response neutralization is equivalent exactly to
  zero horizon charge. On the full domain, the constant-zero response is swap-equivariant and
  neutralizes at the first step for every charge, proving noninjective neutralization is nonselective.
- `[PAPER-PROVED]` The exact visible/partner inner product is the square of the one-mode geometric
  Hellinger affinity, by the corpus tensor-inner and geometric-half-density formulas. This supplies
  the positive invariant behind the dichotomy rather than only its negation.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingHBSourceFaithfulEquivariantNeutralizationNoGo`
- Route kill: `RHTower.d4HBSourceFaithfulSwapEquivariantNeutralizationRouteKilled`
- RH equivalence: `RHTower.d4HBEveryInjectiveSwapEquivariantResponseNeutralizes_iff_riemannHypothesis`
- Direct `lake env lean` and target-only `lake build` pass.
- Axiom audit: only Lean foundations `propext`, `Classical.choice`, `Quot.sound`.

## Hostile audit

- General pure-state fidelity and Holevo--Helstrom discrimination are literature.
- Charged TFD factorization into positive/negative sectors is literature.
- Exact HB route consequence, with actual theta ratios and partial histories, was not found in
  corpus or exact-term literature searches. Novelty remains route-specific pending expert review.

## Log

- 2026-09-01 — Stage 1 conjecture opened after corpus and primary-literature audit.
