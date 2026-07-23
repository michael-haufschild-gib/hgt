# Square-dilated Möbius finite-window prime-mass universality law

- **ID:** square-dilated-mobius-finite-window-prime-mass-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus closure of square-supported Möbius prime mass, Steinhaus diagonal
  exactness, and deterministic sinc-error transference
- **Statement:** The quarter-weighted square-dilated Möbius cutoff carries the full reciprocal
  prime mass through its square-root cutoff both in its exact independent Steinhaus second moment
  and in every deterministic symmetric finite window after one explicit sinc-collision deduction.

## Goal

Connect the concrete square-supported Möbius carrier to the corpus's abstract power-supported
finite-window transference theorem, retaining both exact random diagonal and deterministic
finite-window lower bound.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: tree source and exact `lake env lean` passed; final axiom audit pending
- [ ] 3 → 4 publication-ready: post-proof literature audit pending

## Corpus inputs

- `powerSupportedPrimeMass_randomExact_deterministicWindowLowerBound`
- `sqrtPart_apply_sq`
- `ArithmeticFunction.moebius_apply_prime`
- `natCast_sq_rpow`
- `primeMass_le_sqrtQuarter_diagonal`

## Proof

`[PROVED HERE]` Put
`b(n) = sqrtMoebiusCoeff(n) n⁻¹/⁴`, use support `1 ≤ n ≤ y`, prime set
`p < sqrt(y)+1`, power order two, and forcing constant one.  Every selected prime satisfies
`p² ≤ y`, so its square lies in the support.  At a prime square,
`|sqrtMoebiusCoeff(p²)| = |μ(p)| = 1`, while `(p²)⁻¹/⁴ = p⁻¹/²`.  Hence the abstract
power-supported forcing hypothesis is exact at every selected prime.

The power-supported transference theorem now supplies all three conclusions at once: exact
Steinhaus second-moment diagonal, domination of the reciprocal prime sum, and deterministic
symmetric-window survival after subtracting the explicit sinc off-diagonal energy.

No numerical computation is used.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.SquareDilatedMobiusFiniteWindowPrimeMassUniversalityLaw`
- Main theorem:
  `RHTower.sqrtQuarterWindow_primeMass_randomExact_deterministicWindowLowerBound`
- Exact source check:
  `lake env lean GaloisForLFunctions/RHTower/SquareDilatedMobiusFiniteWindowPrimeMassUniversalityLaw.lean`
  passed on 2026-07-23.
- Imported by `GaloisForLFunctions/RHTower.lean`.
- Final axiom audit and module build deferred to final audit.

## Novelty protocol

No literature search before exact Lean proof.

## Post-proof literature audit

Performed only after exact Lean source check passed.

- Benatar, Nishry, and Rodgers, *Moments of polynomials with random multiplicative coefficients*
  ([arXiv:2012.15507](https://arxiv.org/abs/2012.15507)), studies moments of Rademacher and
  Steinhaus random multiplicative polynomials.  It is adjacent to the random-diagonal component,
  but does not identify this square-dilated Möbius prime-mass packet or its deterministic sinc
  lower bound.
- Heap and Lindqvist, *Moments of random multiplicative functions and truncated characteristic
  polynomials* ([arXiv:1505.03378](https://arxiv.org/abs/1505.03378)), gives higher-moment
  asymptotics for Steinhaus sums, not the exact random/deterministic finite-window transference
  proved here.
- Montgomery and Vaughan, *Hilbert's Inequality*
  ([DOI:10.1112/jlms/s2-8.1.73](https://doi.org/10.1112/jlms/s2-8.1.73)), is classical parent
  theory for finite-interval Dirichlet-polynomial mean-square error control.  It does not contain
  the square-supported Möbius specialization with the exact reciprocal-prime lower mass.
- Montgomery, *Mean and Large Values of Dirichlet Polynomials*
  ([EuDML record](https://eudml.org/doc/141991)), supplies broader deterministic mean-value
  background, not the combined Steinhaus/sinc/Möbius law.

No exact source was found combining the quarter-weighted square-dilated Möbius coefficient,
complete prime mass through `sqrt(y)`, exact Steinhaus diagonal, and every finite symmetric
deterministic window with its explicit sinc collision deduction.  Door 2 remains open rather than
claimed closed.

## Log

- 2026-07-23 — scan connected square-supported carrier coefficients to the abstract
  power-supported random/deterministic finite-window law.
- 2026-07-23 — exact Lean source check passed; post-proof literature audit found separate random
  multiplicative and deterministic Dirichlet-polynomial parent theories, not the exact synthesis.
