# Right-half-plane holomorphy of the theta square-rate reader

- **ID:** xi-theta-square-rate-hardy-holomorphy
- **Stage:** 3-formalized
- **Type:** BRIDGE THEOREM (Lean), [PROVED]
- **Date:** 2026-07-11
- **Module:** GaloisForLFunctions.RHTower.XiThetaSquareRateHardy
- **Paper proof:** ../../2-fully-proven/not_new_scientific_knowledge/xi-theta-square-rate-hardy-reader.md

## Formal surface

- `thetaSquareBlaschkeSymbol_differentiableOn_rightHalfPlane`: the explicit square-zero symbol is
  holomorphic on the open right half-plane; its hyperbolic-sine denominator cannot vanish there.
- `thetaSquareBlaschkeReaderSymbol_differentiableOn_rightHalfPlane`: the normalized reader is
  holomorphic on the whole open right half-plane, including its selected removable node.
- `thetaHeatRateReaderSymbol_differentiableOn_rightHalfPlane`: the physical-rate reader remains
  holomorphic after the `s / pi` rescaling.

## Certificate

- Targeted build passed:
  `lake build GaloisForLFunctions.RHTower.XiThetaSquareRateHardy` (8603 jobs).
- Axiom audit passed for all three holomorphy theorems and the existing exact physical boundary
  energy; only `propext`, `Classical.choice`, and `Quot.sound` occur.
- No Hardy-membership proposition or project-local analytic hypothesis is introduced.
- No full or umbrella build.
- No sorry, admit, axiom, opaque, or unsafe declaration in the new module.

## Scope

This discharges the analytic half of the right-half-plane Hardy interface that is local to the
explicit reader: holomorphy, including the removable singularity. The remaining formal gap is the
uniform interior-line L2 supremum and the half-plane Paley-Wiener unitary surface; boundary L2 energy
is already unconditional in `XiThetaSquareRateBoundary`.
