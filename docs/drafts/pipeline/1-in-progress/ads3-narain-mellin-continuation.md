# Actual Narain Mellin continuation and arithmetic poles

- **ID:** W11-NC
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [W11](ads3-scalar-modular-bootstrap.md)
- **Statement:** The literal scalar Narain Mellin transform continues as
  `2N(u,ρ)N(u,σ)/[u(1+2u)ξ(1+2u)]`, where `s=1/2+u`.
  At every arithmetic resonance, suitable moduli on any prescribed pair of
  horocycles retain the full pole multiplicity. The double horocycle mean
  retains that multiplicity at every pair of positive heights.

## Proof target

On `Re u>1/2`, the completed-zeta factorization gives
`N(u,z)=u(1+2u) lineModel(u,z)`. Actual-to-canonical Fourier uniqueness
identifies `lineModel(u,z)=Λ(1+2u)E(1/2+u,z)`. The already formalized scalar
Mellin formula then yields the quotient above, including its normalization.
Each factor is meromorphic. At an arithmetic resonance `−1/2<Re u<0`,
the elementary multiplier `2/[u(1+2u)]` is analytic and nonzero, so the
proved product-detector orders transfer unchanged.

At unit target heights the constant terms also give, with
`L₊=Λ(1+2u)` and `L₋=Λ(2u)`, the exact mean
`2L₊+4L₋+2L₋²/L₊`. Thus all Whittaker tails disappear while every arithmetic
pole remains. This isolates a source for the remainder problem whose
vertical bounds require only Gamma and zeta estimates.

The regularized fundamental-domain overlap, modular inversion and the
small-height remainder are separate obligations.

## Gates

- [x] 0 → 1: exact source identity and noncancellation mechanism identified.
- [ ] 1 → 2: dependency-closed proof checked against Lean statements.
- [ ] 2 → 3: direct Lean check, axiom audit and umbrella import.
