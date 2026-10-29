# Actual source control through the touching ratio

## Result

For every fixed nonzero smooth unit-interval profile, the actual archimedean
cross replacement and the actual non-ratio prime source have estimates uniform
over every width ratio `0<c<=1`. No prime or completion term is omitted.

The seven modules in
`formal/GaloisForLFunctions/CriticalArithmeticCorrelationTheory/` are
`BoundaryVanishingControlsTheTouchingAutocorrelation`,
`EndpointDecayRemovesTheCrossKernelGapLoss`,
`TheTouchingCrossMatrixHasAUniformErrorBudget`,
`TheChargeDeficitKeepsAUniformPrimeReserve`,
`OverlapLengthControlsTheTouchingCrossError`,
`OnlyTheBoundaryStarEntersAtTouching`, and
`TheBoundaryPrimeStarVanishesAfterNormalization`.

## Mechanisms and exact gains

1. Endpoint decay gives `|G_g(z)| <= L^2*w*(w-|z|)^2/4`. Multiplying this by
   the singular density increment before integration gives raw cross error
   at most `19*L^2*w^3`. The normalized reciprocal-square constant no longer
   diverges as the support gap shrinks.
2. The resulting whole cross budget is `4*C*c^2*norm(x)^2`; every bounded
   pole profile has square residual at most `(36*C*A*c^2)^2`.
3. A height-only refinement gives raw error `B^2*w*(1+w/2)`. For unit-profile
   dilates of width at most one, a reciprocal-square coefficient is
   `(152*(integral abs(phi))^2+6*B^2)/M`. Every smooth plateau with
   `0<eta<=1/4` shares coefficient316.
4. The actual charge satisfies `q=(integral phi)^2/M<1`. This leaves the
   prime-defect fraction `(1-q)/4` and one mass floor independent of each
   fixed `c<1`; this theorem alone still allows a c-dependent horizon.
5. For `N>=2`, an unequal positive integer pair with log gap at most `1/N`
   and one endpoint in `1..N` must be `N,N+1`. The full non-ratio source is
   therefore exactly the star
   `2*G_g(log(N+1)-log N)*x_N*sum_{km=N+1,k>=2} Lambda(k)/sqrt(k)*x_m`.
6. The divisor identity pays the star weight by `log(N+1)`. At ratio one,
   normalized absolute source is at most `(2*B^2/M)*log(N+1)/N*sum(x_m^2)`.
   For all `0<c<=1`, one bound with coefficient `4*B^2/M` works. Every actual
   smooth profile produces its finite height bound. Hence one horizon makes
   the whole normalized source arbitrarily small, simultaneously in c and x.

## Formal status

All seven files passed final individual `lake --old env lean` checks without
output artifacts, with no warnings. Printed capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`. They are imported by the
own umbrella. Required dependency artifacts were built individually only
for new importing modules. No full or umbrella build was run.

## Scope

These results supply actual endpoint source estimates. The full endpoint
matrix decomposition, common-horizon coercivity, and exhaustive spectral
transfer remain in formalization on `cact-touching-profile-boundary.md`.
For `c>1`, the atom Gram overlaps and further arithmetic interactions enter.
The indicator limit also sends `q` to one, so the fixed-profile reserve is
not uniform in that limit. RH, an improved census, and finite off-line
support do not follow from this source estimate alone.
