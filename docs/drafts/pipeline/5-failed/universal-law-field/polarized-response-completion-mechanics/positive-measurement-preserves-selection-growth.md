# Positive measurement preserves selection growth

- **ID:** ULF-PRCM-FAIL-2
- **Stage:** 5 — falsified
- **Type:** FALSIFIED FIELD CONJECTURE
- **Statement:** A natural positive measurement of a noncommutative formation preserves the decay
  exponent of local Fisher response and the growth grade of reflected information work.

## Exact countermodel

ULF-PRCM-2 uses the noncommuting qubit family

\[
 \rho_t=\frac{\exp(tZ+bX)}{\operatorname{Tr}\exp(tZ+bX)},
 \qquad b>0.
\]

Its complete BKM response and reflected Jeffreys work satisfy

\[
 I_Q(t)\sim b^2t^{-3},
 \qquad
 J_Q(\rho_t,\rho_{-t})\sim4t.
\]

After projective measurement of `Z`, the observed Bernoulli family satisfies

\[
 I_Z(t)\sim b^2t^{-4},
 \qquad
 J_Z(t)\sim4\log t.
\]

Thus positive observation loses one full response power and changes linear work to logarithmic
work.  Its information deficit remains asymptotically linear.

## No-go closure

- **Exact killing theorem/mechanism:** ULF-PRCM-2, Theorems 4.1 and 5.1.  Measurement preserves
  neither response exponent nor global work grade, despite data-processing positivity.
- **Strongest positive survivor:** the exact formulas
  `I_Z=I_Q^2/(1-m^2)` and
  `J_Z=2m log((1+m)/(1-m))`, plus asymptotically complete migration of linear work into the
  noncommutative information-deficit fibre.
- **New insight:** an unbounded positive observer is not necessarily selection-faithful.  Selection
  needs work-grade conservation or a sufficiency theorem, not merely nonzero/unbounded response.
- **Status:** paper proof dependency-closed in ULF-PRCM-2; Lean formalization remains open, so the
  no-go is not formally closed under the project standard.

## Log

- 2026-08-12 — killed by the transverse Pauli exponential family; survivor promoted to Stage 2.

