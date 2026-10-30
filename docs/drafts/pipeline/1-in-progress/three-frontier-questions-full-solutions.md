# Joint edge payment, source orientation, and the heat count

- **ID:** three-frontier-questions
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/review-3010/obstacles-summary.md` §2.3
- **Statement:** Resolve Q1–Q3 and every listed subquestion by unconditional Lean theorems.

## Required conclusions

| Question | Required mathematical conclusion | Status |
|---|---|---|
| Q1 | All-vector logarithmic defect reserve for the complete Weil form; defect-relative conductor decomposition | Open |
| Q1/A1 | Top-band joint cancellation, then top-band perturbations of Ramanujan modes | Pole-vector case formalized in `TheShellsAndThePoleCancelOnTheTopBand`; conductor perturbations open |
| Q1/A2 | Growing Euler heads and joint head–pole–tail cancellation | Open |
| Q1/O1 | Ramanujan–Plancherel decomposition of the shell block | Open |
| Q2 | Equality of the two actual Ξ source polarizations | Open; corpus theorem identifies this with RH |
| Q2/defect | Theta–prime expression for `(σ − 1/2)S(s) − Re(ξ′/ξ)(s)`, at some `σ > 1` | Exact available identities under inspection |
| Q2/charge | Theta-prefix reading of window collision charge with explicit error | Open |
| Q2/calibration | Integer analogue of the calibrated explicit-formula Rosati pairing | Exact available identities under inspection |
| Q3 | Actual growth law for the de Bruijn–Newman nonreal count at zero | Open |
| Q3/flux | Consequence of summing the actual localized outer flux over heights | Open |
| Q3/tower | Arithmetic ceiling for a nonblind prime tower | Open |
| Q3/functional | Global monotone functional for the actual zero dynamics | Open |

## Proof discipline

Existing criteria, bounds and obstructions are inputs, not substitutes for these conclusions.
Every claimed solution requires the exact theorem, dependency audit and successful
`lake --old env lean` check. No unproved sign or analytic input may enter a premise.

## Mathematical inputs

- `riemannHypothesis_iff_xiResolvent_sourcePolarizations_eq`: exact orientation receiver.
- `exists_card_deep_le_mul_nonrealZeroCount`: transfers a heat-count law to deep-zero counts.
- `exists_abs_jointWitnessCoefficient_le`: the pole and shells cancel on the pole-vector
  top-band witness; the constant depends on overlap, so this does not settle Q1.

## Gates

- [x] Full requested conclusions fixed.
- [ ] Dependency-closed paper proofs of every conclusion.
- [ ] Exact Lean formalizations, umbrella imports and axiom audits.
