# The completed source returns to shifted heat coordinates

- **ID:** xi-theta-heat-reparametrization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), [PROVED]
- **Date:** 2026-07-10
- **Module:** GaloisForLFunctions.RHTower.XiThetaHeatReparametrization
- **Paper proof:** ../../2-fully-proven/new/xi-theta-heat-reparametrization.md

## Formal surface

- thetaLogToShiftedHeat: removes the critical weight and applies y=exp(u)-1.
- thetaUnshiftedHeatAtom: the ordinary heat exponential at rate pi m squared.
- thetaBoundaryShiftedHeatAtom: the x greater than one boundary-shifted atom.
- thetaLogToShiftedHeat_squareAtom: exact full atom reparametrization.
- thetaLogToShiftedHeat_positiveSquareAtom: exact strict positive-half identity away from the
  measure-zero endpoint.
- thetaBoundaryShiftedHeatAtom_deboundary: exp(pi m squared) exactly removes the boundary shift.
- expSubOne: the positive logarithmic-to-heat coordinate map.
- integral_sq_thetaLogToShiftedHeat: exact weighted L2 norm identity.

## Certificate

- Direct source check passed.
- Targeted module build passed through job 8602 of 8602.
- Axiom audit: propext, Classical.choice, Quot.sound only.
- No full or umbrella build.
- No sorry, admit, axiom, opaque, or unsafe declaration.
- Generated API refreshed; formal lint passed.

## Scope

This supplies the atom-level composite bridge and its exact source/heat Hilbert topology. It does
not yet construct the infinite Hardy-space biorthogonal reader or compose that reader with the
balanced Perron seam.
