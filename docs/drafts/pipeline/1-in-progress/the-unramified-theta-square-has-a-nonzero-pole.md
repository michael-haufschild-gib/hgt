# Isolate the unramified squarefree theta pole

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** O2, evaluation of the signed long-column main term.
- **Statement:** The actual unramified squarefree series `SpectralTheoryOfTheCubicCover.twistedSquarefreeSeries 1` has meromorphic continuation near `w=2/3` with a nonzero simple pole and an explicit residue.

## Connection

The row root number is a bounded-conductor phase times the square of the cubic theta coefficient. The spectral theory of the cubic cover already continues the completed square and its rotated correlation, with double-pole residues in ratio two to one. Their arithmetic decompositions contain nine twists indexed by units modulo sign and ramified valuation modulo three. The missing connection is the ramified Fourier law that isolates the untwisted squarefree series.

## Existing facts and gap

- `thetaSqDirichlet_double_pole`: full theta square has a nonzero double pole.
- `thetaSqDirichlet_eq_zeta_mul`: cube frequencies factor out, leaving a ramified combination of squarefree series.
- `threeLayerCombination_simple_pole`: the rotated three-divisible correlation has a nonzero simple pole after cube removal.
- `sourceCoefficient_unit_mul_lambda`, `sourceCoefficient_unit_eq`: valuation one vanishes; the unramified unit layer has only signs.

The rotated correlation weights `T(ωh)T(h)`, not `T(h)²`. Its half-residue cannot simply be subtracted to extract the unramified part. Required: an actual ramified coefficient identity or a local Hecke relation, followed by the analytic separation. A pole alone does not supply the column-uniform remainder or a contour-shift asymptotic.

## Scope and status

No new theorem or contribution counted. Internal corpus comparison only; no external literature checks. The exact residue and continuation domain remain to be proved before Lean formalization. A successful isolation would identify an actual arithmetic main term missing from O2, rather than restate the already formalized mixed pole.
