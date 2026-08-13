# Hedenmalm--Sonin cofinal reciprocal-gauge rigidity

- **Label:** `P-G134`
- **Route:** P
- **Parents:** `P-G131`, `P-G133`, `XiHadamardFactorization`, `XiSpectralSupportCriterion`
- **Status:** theorem proved in Lean; umbrella integration complete

## Conjecture tested

P-G133 says finite discrete analyticity is vacuous unless one adds cofinal compatibility.  Test a
source-native compatibility stronger than a generic growth bound: determinant-one reciprocity
under the centered functional-equation reflection `z -> -z`.

Weyl cancellation is reflection-even, while a scalar determinant-one gauge must be reciprocal.
Conjecture that these two transformation laws are compatible exactly at neutral Cartan rapidity.

## Scientific decision gate

- **Success:** compute the reflected Weyl product on the literal Xi divisor and prove its unit
  locus.  Then classify existence of one cofinal entire reciprocal cancellation gauge.
- **Failure:** reject if reciprocity is only imposed pointwise after selecting an orientation or if
  the argument does not use the actual Xi functional-equation involution.
- An RH equivalence identifies a hard gate, not a proof of RH.  Next work must derive reciprocity
  from source geometry rather than assume it.

## Prior-research audit

- 2026-08-13 — P-G131 proves the two Burnol orientation legs have product one before Weyl
  minimization.
- 2026-08-13 — P-G133 proves arbitrary finite Xi-support values admit entire interpolation.
- 2026-08-13 — `XiHadamardFactorization` proves functional-equation reflection sends the centered
  Xi spectral coordinate to its negative.
- 2026-08-13 — No prior Route-P theorem compares reflection-even Weyl lower gain with reciprocal
  determinant-one scalar transport on the full divisor.

## Conjecturing log

- 2026-08-13 — C1 proved in scratch: actual Burnol Weyl lower gain is invariant under Xi
  functional-equation reflection.
- 2026-08-13 — C2 proved in scratch: its reflected product is exactly
  `exp(-2 log(r) |Re(rho)-1/2|)` and is strictly below one exactly off critical line.
- 2026-08-13 — C3 proved in scratch: unit reflected product at every divisor support point is
  equivalent to RH.
- 2026-08-13 — C4 proved in scratch: for every `c>0`, existence of one entire gauge satisfying
  `g(-z)g(z)=1` globally and exact Sonin cancellation modulus on every Xi support point is
  equivalent to RH.  Analyticity is not used in the forward implication; reciprocity alone closes
  the cofinal compatibility gap.

## Verification log

- 2026-08-13 — Direct foreground check passed:
  `lake env lean GaloisForLFunctions/RHTower/HedenmalmSoninCofinalReciprocalGaugeRigidity.lean`.
- 2026-08-13 — Imported by `GaloisForLFunctions/RHTower.lean`.
- 2026-08-13 — Exact module build passed:
  `lake build GaloisForLFunctions.RHTower.HedenmalmSoninCofinalReciprocalGaugeRigidity`
  (`12962/12962`).
- 2026-08-13 — Axiom audit passed for every new theorem; dependencies are exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

## Result and pivot

- Uniform growth/type is not the minimal missing input.  Full-divisor reflection reciprocity is
  already rigid enough because Weyl cancellation is even, not reciprocal.
- Exact obstruction is scalarization: vector Burnol legs are determinant-one by exchanging
  reciprocal orientations, whereas Weyl minimization forgets which leg must invert.  Off wall,
  reflected lower gains multiply to a strict loss rather than one.
- Remaining producer is now sharply stated: construct a source-derived scalar channel that both
  retains determinant-one reciprocity and realizes the Weyl cancellation modulus.  P-G134 proves
  that successful construction would close RH; it does not yet construct it.
