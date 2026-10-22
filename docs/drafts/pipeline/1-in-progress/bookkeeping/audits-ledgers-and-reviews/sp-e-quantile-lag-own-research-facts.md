# SP-E quantile--lag weld: own research facts

- For every `N`, the fully labelled completed quantile--Riesz transport at aperture `N + 2`
  is exactly
  `2 * (coherentSelbergIntegerLagMean N + coherentSquareRootPolarLatticeDefect (N + 2))`.
  This is closed as
  `speCompletedQuantileRieszTransport_eq_two_mul_integerLagMean_add_polar` in
  `SuzukiIntegerLagMeanCriterion.lean`.  The proof retains the lower-edge correction, terminal
  seam, moving endpoint, signed interior, and polar term; it takes no absolute value.

- Consequently, completed quantile transport introduces no independent SP-E cancellation gate.
  After the explicitly retained source-free polar term, it is the same signed integer-lag
  current.  The exact remaining gate is the uniform normalized signed lag bound already
  characterized as RH-equivalent by
  `riemannHypothesis_iff_coherentSelbergIntegerLagMeanBounded`.

- Both the source transport-to-Abel equality and the transport-to-lag weld were checked with
  `lake env lean`; a scratch axiom audit of the full source chain reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
