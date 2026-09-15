# SP-E current research facts

This file records only corpus-verified frontier facts, proved no-gos, and new closed bridges from
the current SP-E investigation. It is not a route history.

## Verified corpus frontier

- Normalized prime wall laws converge to the unit exponential law. Complete ordered-tuple
  Fredholm coefficients, one summable Hadamard majorant on each closed disc, and locally uniform
  convergence of the wall entire determinant are already proved in
  `RoutePPrimitiveGammaJuliaStokesWallAtomicFredholmLimit` and
  `RoutePPrimitiveGammaJuliaStokesWallRealZeroClosure`.
- The physical Hellinger cofinal kernel is Hilbert--Schmidt and self-adjoint, retains every finite
  physical determinant, has an entire regularized determinant with only real zeros, and its
  summable diagonal is the completed prime--Gamma current. This is closed in
  `RoutePPrimitiveGammaJuliaPhysicalStokesHellingerCofinalDeterminant`.
- Direct identification of the balanced exponential-wall ordinary Fredholm divisor with centered
  completed Xi is false. Equality of divisors would force equality of normalized even order-one
  entire functions, contradicted by the exact quadratic jets `-32/35` and
  `-thetaCuspNormalizedEvenMoment 1`. This no-go is closed in
  `RoutePPrimitiveGammaJuliaStokesApertureWallXiDivisorNoGo`.
- Consequently, generic wall convergence and source-side real-rootedness are not open SP-E gates.
  Any surviving landing must change the divisor-bearing source operator itself; a zero-free scalar
  correction or direct canonical wall identification cannot work.

## New closed bridge

- `PrimeArchThetaThirdCumulantProductKernel` identifies the sixth reciprocal trace with one signed
  triple-product theta integral, preserving the cancellation lost by independent moment boxes.
- The same module identifies the normalized degree-three Xi square-coordinate jet with the
  normalization of the corpus's actual `xiCTaylorEvenMagnitudePolynomial 3`.
- If `A_3` is that normalized jet, then
  `normalizedPrimeArchMoment 2 = 6 * [u^3] log A_3` exactly.
- Therefore the order-24 cap is exactly
  `[u^3] log A_3 < 1/20000000`, and this logarithmic-coefficient inequality is equivalent to the
  signed product-kernel inequality. These are algebraic identities, not numerical approximations.
- The order-24 cap itself was already unconditionally closed in
  `XiCenteredOrderTwentyFourSixthTraceClosure`. Hence the product-kernel identity is a new
  representation of a closed finite-order result, not the live SP-E frontier. The live frontier is
  all-order/cofinal incidence.

## Cross-route frontier facts

- The signed mixed center hierarchy is already complete through strict rank six. Rank-seven PSD is
  equivalent to the native successor integral in `ThetaCuspCenterMixedSuccessorSource`; the
  canonical degree-six minimizer and its signed norm are identified in
  `ThetaCuspCenterMixedCutoffPolynomial`.
- `PolynomialODEEvenCompactGapCoefficient4`, `PolynomialODEEvenCompactGapCoefficient5`, and
  `PolynomialODEEvenCompactGapCoefficient6`, and `PolynomialODEEvenCompactGapCoefficient7` now
  prove the previously missing degree-four through degree-seven coefficients of the exact even
  compact incidence identity. Each degree is split into
  seven independently certified cofactor sectors; this avoids the documented monolithic
  determinant-expression blowup. Coefficients 8 through 11 and extensional assembly remain open.
- `compactGapCofactorHigherCertified%` retains the equality proof already produced by higher-slice
  normalization instead of discarding it and rerunning normalization in the theorem. Degree-five
  head and cofactor sectors close under default heartbeat with this representation.
- A moving-cusp/Möbius Gamma--Hankel covariance and the route-E Kloosterman response defect live on
  different parameter spaces. Corpus search exposes no canonical identity between them; treating
  them as the same covariance is unsupported and cannot currently bridge the routes.
- `PrimeArchFinitePrefixSubcriticalScheduleNoGo` sharpens the D2 finite-prefix schedule obstruction:
  for every real `c > 42`, any eventually positive depth schedule satisfying
  `c * depth(n)^(3/4) ≤ log n` has log-height defect cofinally below every real floor. Thus `42`,
  not the earlier sufficient constant `84`, is the exact boundary exposed by the current absolute
  Chebyshev envelope. More sharply, the defect has the exact pointwise upper envelope
  `42 * depth(n)^(3/4) - log n`, and it tends to minus infinity whenever the residual slack
  `log n - 42 * depth(n)^(3/4)` tends to plus infinity. Any surviving D2 truncation must therefore
  keep this additive slack bounded above cofinally or exploit prime-phase cancellation unavailable
  to the envelope argument; the bounded-slack critical regime remains open.
- Weighted reflection gives
  `reflect 20 evenCompactGapDetPolynomial = evenCompactGapReversedDetPolynomial`; it does not make
  the determinant self-reciprocal. Therefore existing high-degree coefficient theorems do not imply
  degrees 7 through 11. The pending whole reversed-degree-11 proof is subject to the documented
  lower-reversed-coefficient resource no-go and must be split before checking.

## No-gos and scope boundaries

- A logarithmic coefficient built only from the first theta atom is mathematically valid but does
  not by itself address the refined SP-E landing gate; higher-atom perturbations remain. The useful
  invariant is the full normalized Xi coefficient above.
- The new logarithmic bridge supplies a source-native coefficient target and falsifier for changed
  determinant carriers. It does not prove trace class, ordinary determinant restoration, a changed
  source operator, or Xi-divisor identification.
- The compact coefficient-four/five closures are exact algebraic progress toward rank seven, but do
  not establish the full polynomial identity, the integrated successor sign, or RH.
