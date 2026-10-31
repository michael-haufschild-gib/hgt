# Gamma dilation changes L² energy by a bounded form

- **ID:** gamma-dilation-changes-l2-energy-by-a-bounded-form
- **Stage:** 3-formalized
- **Statement:** A constant `C>0` bounds the Gamma-symbol dilation form by
  `C |log r| ‖f‖²` for every positive scale `r` and every complex `L²` function `f`.

## Proof

The proved pointwise bound `|γ(rt)−γ(t)|≤C|log r|` dominates the integrand
by `C|log r| |f(t)|²`. The latter is integrable by the `L²` hypothesis.
The norm-of-integral inequality and integration of this pointwise bound
produce the claimed form bound. No Gamma-domain assumption is needed for
the difference form.

## Lean

`ArithmeticIncidencePositivity/GammaHasALogarithmicDilationModulus.lean`:
`exists_gammaHardyPhaseRate_L2_dilation_bound` passed direct
`lake --old env lean` checking. Its transitive axioms are exactly
`propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
