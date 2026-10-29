# Complete arithmetic source through touching

## Question

Can one horizon control the actual complete Weil matrix simultaneously for every width ratio `0<c<=1`, while retaining all prime lags, both poles, and Gamma completion?

## Proved source inputs

The following own modules passed final individual Lean audits with standard axioms and no warnings, and are wired into the own umbrella. Exact commands/results are recorded in `logs/critical-arithmetic-correlation/final-audits.txt`. Their completed source result is recorded in `../3-formalized/cact-critical-touching-source-control.md`.

- `BoundaryVanishingControlsTheTouchingAutocorrelation`: quadratic endpoint decay of autocorrelation.
- `EndpointDecayRemovesTheCrossKernelGapLoss`: actual cross-integral error with one reciprocal-square constant for all positive support gaps.
- `TheTouchingCrossMatrixHasAUniformErrorBudget`: whole cross form and bounded pole-profile residual uniformly for `0<c<=1`.
- `TheChargeDeficitKeepsAUniformPrimeReserve`: strict profile charge `q<1`; one prime-defect coefficient and mass floor for each fixed `c<1`. Its eventual horizon may depend on `c`.
- `OverlapLengthControlsTheTouchingCrossError`: height-based estimate, with common scalar coefficient316 for all smooth plateaus `0<eta<=1/4`.
- `OnlyTheBoundaryStarEntersAtTouching`: the exact non-ratio prime source is the star `km=N+1`, including all prime powers.
- `TheBoundaryPrimeStarVanishesAfterNormalization`: its actual normalized form is bounded by `(4B^2/M)*log(N+1)/N*sum(x^2)` simultaneously for all `0<c<=1`. Every smooth compact profile produces its own height bound; one eventual horizon pays any prescribed positive error.

Distinct internal integer log gaps exceed `1/N`. Thus atom supports remain strictly disjoint at the endpoint ratio, but prime products just outside the horizon contribute the boundary star. The old separated source formula cannot be used without this term.

## Formalized complete argument

A. `TheActualArchimedeanMatrixReachesTouching`: exact raw and normalized entries retaining the literal prime pairing.
B. `TheNonRatioMatrixIsTheActualPrimeCorrection`: actual prime-pairing matrix minus ratio kernel; its quadratic form equals normalized non-ratio source.
C. `TheCompleteWeilMatrixKeepsItsBoundaryCorrection`: complete matrix and energy decomposition through ratio1, with the negative non-ratio correction.
D. `TheSelfAndPoleErrorsStayUniformAtTouching`: actual self and two-pole remainders through ratio1.
E. `OnePrimeDefectReserveCoversEveryRatioThroughTouching`: one mass floor, one prime-defect fraction `(1-q)/4`, and one eventual horizon for all `0<c<=1`.
F. `OneRamanujanFamilyDetectsAllBoundedEnergiesThroughTouching`: one finite arithmetic family detects all bounded-energy unit vectors throughout the same range.

G. `TheReplacementErrorsVanishUniformlyThroughTouching`: one normalized residual horizon for the actual self, center, cross, and two-pole errors.
H. `RamanujanQuasimodesAreUniformThroughTouching`: the complete six-term norm residual, including the boundary prime matrix, uniformly for all ratios through one.
I. `OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching`: finite coordinate detection excludes every eigenvalue below the completed endpoint shape; a near-unit-mass plateau then gives one positivity horizon for all `0<c<=1`.

All nine files passed individual final no-output Lean checks and are wired into the programme umbrella. Their capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`. Exact final commands are recorded in `logs/critical-arithmetic-correlation/final-audits.txt`. The prime-matrix theorem also converts its actual quadratic-form budget into an operator-action budget by the Hermitian eigenbasis identity.

## Spectral mechanism

The formalized argument combines: prime residual independent of `c`, scalar self error `O(1/N)`, center linear in bounded charge, uniformly square-bounded cross/pole errors divided by logarithmic mass, and small actual non-ratio operator. A fixed finite coordinate certificate then excludes all eigenvalues below the endpoint conductor-one energy. For a detecting set of size `k`, choose residual tolerance `delta/(6*(k+1))`; total coordinate cost is below `1/18`, contradicting detection. The resulting theorem produces a single smooth plateau and a single eventual horizon for every ratio `0<c<=1`, with every complete eigenvalue at least any prescribed `b<2-log(2*pi)` and profile mass above `1-epsilon`. The horizon may depend on the profile and `b`, but not on `c`.

## Boundary of the result

The neighbouring TransMetzlerWeilPositivity programme already proves genuine first-overlap positivity for an explicit profile. For general `c>1`, the atom Gram overlaps and additional non-ratio interactions enter. They must be compared jointly with the logarithmic self term. A separated cross formula alone cannot cover that regime. The strict charge reserve also vanishes as smooth plateaus approach the indicator; fixed-profile uniformity does not give uniform spectral exhaustion in that limit. RH, improved census, and finite exceptional zeros remain open.
