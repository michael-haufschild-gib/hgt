# Xi Jensen real-rootedness

Every fixed degree has an explicit shift horizon. The finite expression
`xiJensenRealRootednessHorizon d` uses Hermite roots and their endpoint values,
finite positive recurrences, an exponential and a ceiling. It selects no
threshold from qualitative convergence.

- `ExplicitConcentration.lean`: the score exceeds the saddle cube; normalized
  centered moments are bounded by explicit constants divided by saddle height.
  All fluctuation moments through degree `d` are controlled by
  `sqrt (xiJensenFluctuationBound d / thetaJensenSaddle n)`.
- `HermiteErrorBounds.lean`: the exact mixed Laguerre recurrence gives a uniform
  evaluation error for `xiJensenHermitePolynomial`, including denominator error.
- `HermiteSignMargins.lean`: reciprocal sums of finite root gaps and endpoint
  values give separated sign intervals and a positive explicit margin.
- `ExplicitRealRootednessHorizon.lean`:
  `xiJensenPoly_splits_of_horizon_le` proves that the actual degree-`d` ξ Jensen
  polynomial splits over `ℝ` at every shift above the stated horizon.

`EveryFixedDegreeIsEventuallyRealRooted.lean` supplies the earlier qualitative
theorem. Neither result asserts real-rootedness uniformly over degrees at a
fixed shift.
