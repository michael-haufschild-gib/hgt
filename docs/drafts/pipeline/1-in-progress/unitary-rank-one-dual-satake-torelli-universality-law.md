# Unitary rank-one dual--Satake--Torelli universality law

Status: Lean source written; exact audit pending.

## Lean-source inputs

- `HTGeometry/RankOneDuality.lean`: rank-one dual multiplier is inversion.
- `RHTower/LocalFactorDuality.lean`: inversion-closed Satake multisets have dual-invariant local factors.
- `RHTower/SatakeReality.lean`: conjugation-closed spectra have real secular moments.
- `RHTower/FiniteSatakeRealityTorelliUniversalityLaw.lean`: for an `n`-point spectrum, reality of the first `n` moments is equivalent to conjugation closure.
- Mathlib's `Circle.coe_inv_eq_conj`: inversion and conjugation coincide on unitary complex multipliers.

## Universal law

For every finite family `f : Fin n → Circle`, abstract rank-one dual closure is equivalent to
reality of its first `n` secular moments.  In this phase all secular moments are real and every
local Euler factor is invariant under dualization.

This identifies the previously separate dual functional-equation and Satake-reality phases through
the unitary carrier, without labelled conjugate pairs.

## Novelty audit

Pending post-formalization primary-source literature search.  Corpus search found each component
law but no theorem identifying all three phases on a finite unitary rank-one spectrum.

## Verification

- Development command: pending `lake env lean GaloisForLFunctions/RHTower/UnitaryRankOneDualSatakeTorelliUniversalityLaw.lean`.
- Final module build, axiom audit, and lint: pending exhaustion pass.
