# Failed route: FZZ joint natural radial-phase divisor landing

- **Route:** Pair the literal positive-scale Fermi radial clock with the fixed-quintic phase at one scale, then identify this joint report with the canonical norm/normalized-phase decomposition of each centered dyadic Mellin divisor character.
- **Status:** RETIRED — unconditional Lean no-go.
- **Exact killing theorem:** `RHTower.fzzCigarParityJointQuinticNaturalRadialPhaseRouteKilled`.

## Why it fails

Every positive-scale source radius is strictly below one. Every critical-line centered Mellin character has radius exactly one. Hardy's unconditional theorem supplies actual critical-line zeta zeros above every height, and exact FZZ/zeta divisor comparison makes each one a literal parity-Mellin mode. Therefore cofinally many genuine modes miss the full joint report at every positive scale, even with arbitrary mode-dependent scale choices.

## Strongest positive survivor

`RHTower.fzzCigarParityJointQuinticNaturalRadialIncident_iff` proves that radial incidence occurs exactly in `Re(rho)<1/2`; `RHTower.existsUnique_fzzCigarParityJointQuinticNaturalRadialIncident` proves its positive scale is unique.

Thus the joint Fermi/quintic report is a canonical one-sided left-chamber chart. A surviving FZZ-P construction must supply a unit-seam state plus a reflected expanding chart, or derive a different radial target from literal dynamics before seeing the divisor. Reusing the centered Mellin norm as target radius is terminal.

## Verification

Module `GaloisForLFunctions.RHTower.FZZCigarParityJointNaturalRadialPhaseDivisorNoGo` passes direct Lean checking and targeted `lake build`; audited theorem dependencies use only standard Lean quotient/classical axioms. Frontier map was not modified.
