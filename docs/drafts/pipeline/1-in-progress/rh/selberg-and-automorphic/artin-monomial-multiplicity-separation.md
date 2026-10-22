# Monomial-multiplicity separation of finite virtual characters

- **ID:** `artin-monomial-multiplicity-separation`
- **Stage:** 1-in-progress
- **Type:** THEOREM (finite-character infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** for a finite group, the complete family of integral multiplicities against
  induced linear characters determines a concrete virtual character.

## Goal

Formalize the exact finite detection theorem needed to distinguish character-space separation
from the still-open integral Brauer lattice.  This must use actual induced linear characters,
restriction, multiplicities, and cyclic Fourier expansion; it may not introduce a
`MonomialSeparates` proposition or imply any analytic effectivity.

## Paper proof

Let `theta` and `eta` have equal monomial-multiplicity profiles.  For every `g` in `G`, restrict
to the cyclic subgroup `H = <g>`.  Virtual Frobenius reciprocity identifies the multiplicity of
each linear character of `H` in the restriction with the corresponding global monomial
multiplicity.  Pairing symmetry puts that coefficient in the orientation used by the integral
finite-abelian Fourier formula.  All Fourier coefficients of the two restrictions agree, so the
restrictions agree.  Evaluating at `g` gives `theta(g) = eta(g)`; hence `theta = eta`.

This is a dependency-closed finite-group proof after the existing virtual Frobenius reciprocity
and finite-abelian integral Fourier theorems.

## Anti-theatre boundary

Injectivity says monomial data separates virtual characters over the concrete character carrier.
It does **not** say every virtual character is an integral linear combination of monomial
characters, and does not prove Brauer induction.  It supplies neither a global Artin Euler
product nor continued-divisor effectivity.  Thus it cannot be cited as progress on Artin
holomorphy beyond a required finite-character bridge.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinMonomialMultiplicitySeparation.lean` passed.
- `lake build GaloisForLFunctions.RHTower.Artin.ArtinMonomialMultiplicitySeparation` passed; this was
  the targeted leaf build, not an umbrella or full build.
- `/tmp/ArtinMonomialMultiplicitySeparationAxioms.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for both exported theorems.
- The leaf is wired into `formal/GaloisForLFunctions/RHTower.lean`; the umbrella was deliberately
  not built.
- The formal lint was run without `--build`.  It currently fails on concurrent unrelated
  unreachable-module errors (`XiShiftedHardEdgePaleyWiener`, several `XiWardCubic*` modules,
  `HTGeometry.SymmetricGaugeProbe`, and `HTGeometry.SymmetricPassportPolynomial`); this leaf is
  not among the errors.  It remains Stage 1 until that repository-wide gate is green.

## Log

- 2026-08-15 — opened after the virtual Frobenius reciprocity and integral finite-abelian Fourier
  bridges made the paper proof dependency-closed.
- 2026-08-15 — source-checked, target-built, axiom-audited, and wired.  Repository-wide lint is
  blocked by unrelated concurrent modules, so the card remains in Stage 1 rather than claiming a
  completed global formal gate.
