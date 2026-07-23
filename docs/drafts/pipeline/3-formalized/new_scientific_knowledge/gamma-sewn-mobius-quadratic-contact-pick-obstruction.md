# Gamma-sewn Möbius quadratic-contact Pick obstruction

- **ID:** `gamma-sewn-mobius-quadratic-contact-pick-obstruction`
- **Stage:** 3-formalized
- **Scientific status:** `[UNCONDITIONAL] [LEAN-FORMALIZED] [AXIOM-AUDITED]`
  `[SOURCE-SPECIFIC NOVELTY CANDIDATE] [NOT RH]`
- **Paper proof:** `../../2-fully-proven/new_scientific_knowledge/gamma-sewn-mobius-quadratic-contact-pick-obstruction.md`

## Lean modules

- `formal/GaloisForLFunctions/HTGeometry/QuadraticContactPickObstruction.lean`
- `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusPickObstruction.lean`

Formal theorem chain:

```text
tendsto_pickTwoPointDeterminant_of_boundaryContact
eventually_pickTwoPointDeterminant_neg_of_boundaryContact
  -> tendsto_gammaSewnMobius_pickDiagonalDefect_nhdsGT_zero
  -> eventually_gammaSewnMobiusPickTwoPointDeterminant_neg
  -> gammaSewnMobiusApertureCrossDefectDeterminant_eq
  -> eventually_gammaSewnMobiusApertureCrossDefectDeterminant_neg
```

Last theorem is source-level conclusion: for every prime and every fixed positive aperture, actual
fixed-prime Gamma-sewn Möbius aperture Gram-loss determinant is negative at every sufficiently
small positive second aperture.

## Audit

- `lake build GaloisForLFunctions.RHTower.GammaSewnMobiusPickObstruction`: passed.
- `lake env lean GaloisForLFunctions/RHTower/GammaSewnMobiusPickObstruction.lean`: passed.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py lint`: passed.
- No `sorry`, `admit`, project axiom, computation, RH premise, or unproved source hypothesis.

## No-repeat consequence

Pointwise `gammaSewnMobiusValuationContractionMultiplier < 1` cannot be promoted to packet
contractivity. Scalar Gamma sewing is formally dead. Only non-diagonal source completion survives.
