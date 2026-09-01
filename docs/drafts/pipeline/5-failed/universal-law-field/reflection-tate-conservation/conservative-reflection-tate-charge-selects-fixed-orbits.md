# Conservative reflection-Tate charge selects fixed orbits

- **ID:** `ULF-RTC-001`
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** `[FALSIFIED]` A source charge retained by integral reflection-Tate cohomology
  excludes every free functional-equation orbit and therefore selects the critical line.

## Big-picture higher law attempted

Fuse integral orbit charge, functional-equation reflection, and source recovery. Fixed orbits carry
nonzero mod-two Tate charge while free pairs are norms, so a source-forced conserved charge appeared
capable of excluding every off-line pair.

## Corpus audit before the conjecture

- `[CORPUS]` The integral unit extension separates fixed from free reflection orbits: fixed charge
  survives and the invariant residue of a free pair is a norm.
- `[CORPUS]` Signed-reflection Tate cohomology is exactly finitely supported parity on the fixed
  locus; its boundaries are exactly the kernel of fixed-point parity.
- `[CORPUS]` A charge lattice admits a conservative reflection-Tate reporter iff every charge in it
  is already fixed-supported.
- `[CORPUS]` Existence of a Xi conormal landing with a conservative reporter is equivalent to RH.

## Exact RH closure that was attempted

Map every Xi occurrence marker to a nonzero integral Tate class and prove source recovery preserves
that marker. Since a free reflected pair is a boundary, preservation would force each occurrence to
be fixed and the existing reflection-fixed dictionary would prove RH.

## No-go closure

- **Exact killing theorem/mechanism:** `isReflectionTateConservative_iff` classifies conservative
  reporters as exactly fixed-supported charge lattices. Consequently
  `riemannHypothesis_iff_exists_reflectionTateConservative_landing` proves that the needed Xi landing
  plus conservativity is precisely RH, not a weaker source theorem.
- **Verdict:** `FALSE` as a source-derived selection mechanism.
- **Strongest positive survivor:** Tate cohomology gives a complete fixed/free orbit quotient and a
  sharp test for whether a proposed reporter has silently assumed fixed support.
- **New insight:** A viable quotient-charge law must explain before divisor specialization why the
  literal source marker cannot be exported into a free-orbit norm or boundary.
- **Status:** Killing classification and survivor are Lean-proved in
  `IntegralOrbitTateExtension`, `ReflectionTateAnomaly`,
  `ReflectionTateConservativeClassification`, and
  `IntegralCyclicReflectionTateOrbitUniversalityLaw`. No new dependency-closed theorem remains.

## Relentless-interrogation replacement

> Which pre-divisor formation law makes one arithmetic occurrence marker non-boundary before any
> reflection orbit or Xi zero is chosen?

## Log

- 2026-09-01 — killed by exact conservativity/fixed-support classification; retired.
