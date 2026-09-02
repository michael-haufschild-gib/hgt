# FZZ pre-correlator support-motion selector

- **ID:** FZZ-PSMS
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** Torus separation support motion or its full prime-form/Jacobian record selects zero physical radial momentum.

## Goal

Proposed chain:
`pre-correlator support motion/Jacobian → replica-area Ward law → divisor-mode passivity → Mellin completeness → RH`.

## No-go closure

- **Exact killing theorem/mechanism:** Hikida--Schomerus (C.11)--(C.18) separation kinematics omit radial spin `j`; the complete moving-support record and every postprocessing are constant across `j(P)=-1/2+iP`. Lean: `fzzTorusSeparationKinematicSupportRadialBlindness_noGo`.
- **Strongest positive survivor:** adjoining the source-exact charge-even external-BRST modulus makes the full signature injective in `P` for every `k>2`.
- **New insight:** radial information first enters through correlator/modulus weights, not support motion or separation Jacobian. Surviving FZZ-P branch must couple moving support to `j`-dependent amplitude weights or use higher replica order.
- **Status:** paper and Lean closed; direct Lean PASS; targeted module build PASS; standard axioms only; corpus/literature novelty audit found no prior all-observable classification.
