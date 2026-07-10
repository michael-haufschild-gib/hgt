# One-prime Euler Fredholm seam

- **ID:** one-prime-euler-fredholm-seam
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / source-index route obstruction
- **Source:** concrete Hardy--Titchmarsh Euler transport; Sonin Euler-corner noncompactness
- **Statement:** `[PROVED IN LEAN]` For every `p>1`, the concrete one-prime Euler local factor
  `1-p^(-1/2)U_p*` and its positive Gram are invertible, but the Gram's commutator with every
  positive-cutoff Hardy--Titchmarsh boundary projection is noncompact.  Hence the natural
  compact-commutator Toeplitz/Fredholm index mechanism is outside its domain already at one prime.

## Goal

Test the remaining height-free, no-jet integer-index route against the actual infinite-Euler source
carrier rather than a divisor-fed Krein matrix.  A Toeplitz or projection-pair index requires an
essentially invariant polarization: the source multiplier must commute with the carrier projection
modulo compact operators.  The existing source model already provides the exact local factor, its
positive Gram, the canonical projection, and a theorem that the lower cross-boundary corner is not
compact.

## Theorems

In `HardyTitchmarshEulerConcrete.lean`:

- `RHTower.evenPrimeLocalFactor_isUnit`: the physical factor
  `I-p^(-1/2)U_p*` is a unit.  Since `U_p*` is unitary and `p^(-1/2)<1`, its inverse is the
  norm-convergent geometric series.
- `RHTower.archimedeanPrimeLocalFactor_isUnit`: the concrete weighted-spectral factor is a unit by
  exact unitary transport.
- `RHTower.archimedeanPrimeEulerGram_isUnit`: the positive Gram `T_p* T_p` is a unit.
- `RHTower.archimedeanPrimeEuler_projectionCommutator_not_isCompactOperator`: if
  `[Pi_a,G_p]` were compact, then its lower corner `(1-Pi_a)[Pi_a,G_p]` would be compact.  The
  identity

  ```text
  (1-Pi_a) G_p Pi_a = -(1-Pi_a)[Pi_a,G_p]
  ```

  would then make the Euler cross-boundary corner compact, contradicting
  `archimedeanPrimeEulerCorner_not_isCompactOperator`.

All four declarations pass direct build and have only the standard axioms
`[propext, Classical.choice, Quot.sound]`.

## Consequence for the source index

`[PROVED NO-GO]` The obstruction is not failure of the local Euler symbol to be invertible.  It is
failure of essential invariance of the canonical source polarization.  Therefore the usual
Toeplitz/Fredholm construction cannot attach a faithful integer to the one-prime Euler action on
this carrier.

This is stronger than the earlier measured-index blindness theorem in one precise direction:
before normalization can destroy the integer, the concrete local source already fails the compact
commutator condition needed to define the ordinary index.  Adding more prime factors does not by
itself repair that missing hypothesis; a proof would need a new renormalized all-prime
polarization and a theorem that its total commutator is compact or belongs to a specified index
ideal despite each local obstruction.

## Research classification

`[BRIDGE]` Invertibility by a Neumann series and extraction of a noncompact corner from a
commutator are standard functional analysis.  The direct application to the project's concrete
Euler carrier is useful and formally new to the repository, but it does not clear the
novelty-by-significance gate and does not increase the verified zero range.

`[OPEN CORE]` Construct a genuinely all-prime renormalized source action `G_E` and polarization
`Pi_E` for which:

1. `[Pi_E,G_E]` lies in a source-specified compact or summable ideal;
2. the resulting Fredholm or relative index is invariant under every fixed reflection orbit; and
3. one free reflection orbit changes the index by a nonzero integer.

The construction must not be obtained from the residual zero divisor.  Without item 1, the index is
undefined; without items 2 and 3, it is not the required orbit selector.

## Gates

- [x] 0 -> 1 in-progress: one-prime source-index test isolated.
- [x] 1 -> 2 fully-proven: invertibility and noncompact-commutator proofs completed.
- [x] 2 -> 3 formalized: direct module build and axiom audit pass.
- [ ] 3 -> 4 publication-ready: not applicable without an all-prime renormalization theorem.

## Log

- 2026-07-10 -- One-prime Fredholm seam formalized and classified as a not-new source-index
  obstruction.
