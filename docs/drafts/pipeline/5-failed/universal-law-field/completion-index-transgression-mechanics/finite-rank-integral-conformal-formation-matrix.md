# Finite-rank integral conformal formation matrix

- **ID:** `ULF-ICFC-1`
- **Stage:** 5-failed
- **Type:** falsified source realization

## Proposal

Construct integral rank-two matrices `M_n`, independently of a spectral character, whose
complexified eigenvalues at a character `s` are `n^(2 Re s)` and `n^(2-2 Re s)`.  Their integral
traces plus `ULF-ICTR-1` would force criticality.

## Exact killing mechanism

Scalar extension of one fixed integral matrix preserves its characteristic polynomial.  Its trace
is the same integer at every complex character and its eigenvalues cannot vary with `s`.  If the
entries instead lie in a character ring so specialization can vary the eigenvalues, the source
trace lies in that ring, not in `Z`; integrality after specialization is again the missing premise.

Therefore a finite rank-two integral matrix cannot simultaneously provide source-side trace
integrality and spectral-character-dependent weights.  This was a hidden circularity in the first
form of `ICFC-1`.

## Strongest positive survivor

The source object must be infinite/pro-integral before completion.  One fixed integral
Frobenius--Verschiebung correspondence can have different analytic characters/completions, while a
Fredholm or Lefschetz comparison can transport an integer from finite formation stages.  The
completion comparison—not a chosen finite lattice—is the possible selector.

## New insight

Horizontal grade is a completion index: it measures failure of integral algebraic supertrace to
agree with analytic parity trace.  See `ULF-FVCS-1`.

## Status

No Lean theorem needed beyond scalar-extension trace preservation; the realization is killed at
the type level.  Positive survivor has a separate construction card and a new formalized scalar
ledger/rigidity theorem.

## Log

- 2026-09-02 -- retired during hostile source-realization audit.
