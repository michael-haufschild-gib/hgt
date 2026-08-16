# Unit-Riesz outgoing charge as Suzuki Green curvature

- **ID:** `ccm-unit-riesz-suzuki-green-producer-classification`
- **Stage:** 3-formalized
- **Type:** EXACT SOURCE WELD / RH-EQUIVALENT PRODUCER CLASSIFICATION
- **Lean:** `GaloisForLFunctions/RHTower/CCMUnitRieszSuzukiGreenProducerClassification.lean`
- **Status:** `[LEAN FORMALIZED] [LEAF BUILT] [WIRED] [NOT AN RH PROOF]`

## Formalized result

Literal completed outgoing unit-Riesz charge is exactly finite-window Green functional of
Suzuki multiplicity-exact Xi screw plus explicit polar and Gamma corrections. Lean proves

```text
RH iff unit-Riesz critical resolvent is globally bounded
   iff it is bounded on integer logarithms
   iff literal completed outgoing HG energies are uniformly bounded.
```

Reporter, prime-atom match, Green integration by parts, exact polar cancellation, Gamma bound,
integer-log interpolation, and analytic converse are all unconditional Lean theorems. Sharp
constant classification is recorded separately in `ccm-unit-riesz-sharp-pole-classification`.

## Audit

- [x] `lake env lean GaloisForLFunctions/RHTower/CCMUnitRieszSuzukiGreenProducerClassification.lean`
- [x] exact leaf build
- [x] umbrella wiring
- [x] capstone axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
