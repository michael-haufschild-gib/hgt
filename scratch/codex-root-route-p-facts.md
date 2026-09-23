# Route P facts (root)

- Literal matched-centroid excess atom is
  `w_n (centroid_n - 2 sqrt(n))`, with `w_n = Λ(n)/sqrt(n)`.
  From `centroid_n² = 4n + w_n²/4`, it is nonnegative and at most
  `w_n³/(16 sqrt(n)) ≤ log(n)³/(16 n²)` for `n>0`.
- The atom sequence is summable. The existing finite Route P
  `ccmActualHeadMatchedCentroidChebyshevExcess K` equals its prefix through
  `K+2`, is bounded by its total sum, and converges to that finite sum.
  Lean: `SPEQuantileRieszRoutePTerminalCentroidExcessSummability.lean`.
- Whole-route implication: at physical ratio one the nonnegative geometric
  correction is a finite constant, not a growing reservoir. The exact barrier
  remains `4 chebyshevError(x) + (mass-2 sqrt(x))² + 4 mass + O(1)`;
  its sign and the ordered-history graph intertwiner are still open.
