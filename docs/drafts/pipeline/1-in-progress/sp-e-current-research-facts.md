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

## No-gos and scope boundaries

- A logarithmic coefficient built only from the first theta atom is mathematically valid but does
  not by itself address the refined SP-E landing gate; higher-atom perturbations remain. The useful
  invariant is the full normalized Xi coefficient above.
- The new logarithmic bridge supplies a source-native coefficient target and falsifier for changed
  determinant carriers. It does not prove trace class, ordinary determinant restoration, a changed
  source operator, or Xi-divisor identification.
