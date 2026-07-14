# Real-mesh improper antitone Riemann sum

- **ID:** `real-mesh-improper-antitone-riemann-sum`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED IN LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For a nonnegative antitone integrable function on the positive half-line, the
  mesh Riemann sums converge to its improper integral as the mesh tends to zero.

## Result

`HTGeometry.tendsto_realMesh_antitone_Ioi` proves the exact squeeze between lower and upper
translated mesh sums.  The theorem is the analytic input for the positive-shift power-tail
asymptotic and contains no zeta or divisor assumption.

## Lean

`formal/GaloisForLFunctions/HTGeometry/ImproperAntitoneRiemannSum.lean`, imported by the
`HTGeometry` umbrella.

## Gates

- [x] statement proved
- [x] imported by the area umbrella
- [x] consumed by the Hurwitz shifted-power asymptotic
