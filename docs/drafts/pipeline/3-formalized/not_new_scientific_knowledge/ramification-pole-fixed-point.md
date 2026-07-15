# Expansion forces a periodic eigenvolume singularity to be logarithmic

- **ID:** ramification-pole-fixed-point
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), BRIDGE
- **Source:** stable-coframe log-Calabi--Yau rigidity theorem
- **Statement:** If an integral divisor order `c` is fixed by the ramification pullback law
  `c=e*c+(e-1)` with natural ramification index `e>1`, then `c=-1`.

## Goal

Formalize the exact local arithmetic step which turns a recurrent eigenvolume singularity into a
simple logarithmic pole.

## Gates

- [x] 0 -> 1 in-progress: shifted ramification law isolated
- [x] 1 -> 2 fully-proven: integral-domain fixed-point proof complete
- [x] 2 -> 3 formalized: scratch check and targeted build pass
- [ ] 3 -> 4 publication-ready: supporting certificate for the full divisor theorem

## Lean certificate

File: `formal/GaloisForLFunctions/HTGeometry/RamificationPoleFixedPoint.lean`

Declarations:

- `ramificationShift_fixed_eq_neg_one`
- `ramificationPoleOrder_fixed_eq_neg_one`
- `ramificationPluriPoleOrder_fixed_eq_neg_weight`

Targeted verification:

`lake build GaloisForLFunctions.HTGeometry.RamificationPoleFixedPoint`

All declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.

The first theorem proves that `c+1=e*(c+1)` and `e>1` imply `c+1=0`.  The second converts the
canonical-divisor form `c=e*c+(e-1)` to that shifted equation.

The weighted theorem treats a rational `k`-canonical eigen-density.  Its ramification law is
`c=e*c+k*(e-1)`, and expansion forces `c=-k`; normalized per canonical weight, the pole order is
again exactly `-1`.

## Mathematical use

For a rational eigenvolume `Omega` and a periodic ramification prime `E`, canonical-divisor
pullback supplies the premise with `c=ord_E(Omega)`.  An int-amplified map forces `e>1`, so the
formal theorem excludes a zero, regular degeneracy, and every higher-order pole.  The only
possible horizon singularity is `ord_E(Omega)=-1`.

The geometric derivation of the coefficient equation and the global log-Calabi--Yau conclusion
remain paper-level; neither is postulated as a Lean axiom.

## RH impact audit

The theorem would constrain the boundary of a full-rank rational first-order RH tail if such a
tail were constructed.  No such construction is currently proved, so there is no direct RH
consequence.

## Log

- 2026-07-15 -- shifted and unshifted ramification fixed-point laws formalized.
