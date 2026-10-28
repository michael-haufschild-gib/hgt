# Ramanujan spectral law for the complete Weil form at the spacing

- **ID:** complete-weil-spacing-ramanujan-spectral-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** full-prime Ramanujan quasimodes; bounded-defect finite-span approximation; exact archimedean atom pairing; actual two-pole rows
- **Statement:** For every fixed `0<c<1`, the actual complete normalized Weil matrix at width `w=c/N` has Ramanujan norm quasimodes, eventual exact bounded spectral counts, and convergence of its simple eigenlines to Ramanujan lines.
- **Count:** uncounted; one full spectral package, with its support results and weaker packet-form corollaries included.

## Gates

- [x] Exact actual carrier, normalization, and separated entries verified in Lean
- [ ] All analytic estimates and the assembled paper argument verified in Lean
- [ ] Ramanujan norm quasimodes, exact bounded spectral counts, simple eigenline convergence
- [ ] Final individual source checks, transitive axiom checks, umbrella imports, foundational documentation, scratch cleanup

No novelty audits or web searches are part of this task, per user instruction.
README integration must remain crisp and foundational; proof details, module
inventories, and verification history stay on this card and in audit logs.
The complete spectral statement remains unproved until its Lean endpoints pass.
The argument below records the exact intended theorem and constants; generic
support hypotheses must be discharged on the literal matrix.

## Exact carrier and conclusion

Fix real `C²` function `phi` supported in `[0,1]`, with
`M2=integral(phi²)>0`, `I=integral(phi)`, and `0<c<1`.
Set `w=c/N`, `g(u)=phi(u/w)`, and `G=integral(g²)=w*M2`.
On the atoms centered at `log(n)`, `1<=n<=N`, define

`W_N=(atomicMarkovGram(g,N)
 + row0(atomPoleRow(g,N)) outer row1(atomPoleRow(g,N))
 + row1(atomPoleRow(g,N)) outer row0(atomPoleRow(g,N)))/G`.

The exact finite-index equivalence `primeHorizonFinEquiv` transports the
existing `Fin N` carrier to `PrimeHorizonIndex N`. Polarization and
`polarDefect_atomic` identify this matrix's quadratic form with the actual
synthesized `weilQuad`. Both exponential pole moments are retained.
The supports are eventually separated: `atomSpacing(N)>=1/(N+1)` and
`N>c/(1-c)` imply `c/N<atomSpacing(N)`. The mass Gram is then `G*Id`.

Put

`sigma=log(1/(2*pi*c))+bumpRobin(phi,1)/M2`,
`alpha=c*I²/M2`,
`lambda_m=sigma+log(m)+tameDifferent(m)+alpha*[m=1]`, for `m>=1`.

For the normalized Ramanujan profile
`v_(m,N)(n)=normalizedRamanujanMode_m(n)/sqrt(n*log(N))`, the target is
`norm((W_N-lambda_m*Id)v_(m,N))->0` and `norm(v_(m,N))->1`.
For every real threshold `T` distinct from all `lambda_m`, the number of
actual eigenvalues below `T`, counted with multiplicity, must eventually equal
`#{m>=1:lambda_m<T}`. Each fixed label has an isolating interval containing
exactly one eigenvalue eventually; its eigenvalue tends to `lambda_m`, and its
spectral projection captures `v_(m,N)` in norm. The claim concerns this
shrinking-atom family, without an assertion of arbitrary-test Weil positivity.

## Assembled argument; Lean verification incomplete

### 1. Literal matrix decomposition

Let `P_N` be the literal prime matrix, `s_n=1/sqrt(n)`, `t_n=sqrt(n)`,
`T_N=s outer t+t outer s`, and `Omega_N` have zero diagonal and
`Omega_N(n,j)=omega(abs(log(n)-log(j)))` off the diagonal, where
`omega(u)=exp(-u/2)/(1-exp(-2u))`.
The actual atom-pair formula and the exact exponential translations give

`W_N=(2*gammaHardyPhaseRate(0)+levyEnergy(g)/G)*Id
       -P_N-X_N/G+(Gminus*Gplus/G)*T_N`,

where `X_N` has the actual cross integrals off the diagonal and zero diagonal,
and `Gplus/minus=integral(g(u)*exp(plus/minus u/2))`.
The off-diagonal cross coefficient is minus one: the pair energy has twice
that off-diagonal contribution. The existing finite-part identity

`2*gammaHardyPhaseRate(0)+profileRobin(phi)+gamma
 =-log(2*pi)+bumpRobin(phi,1)/M2`

gives the exact decomposition

`W_N=(log(N)+sigma-gamma+selfError_N)*Id-P_N+B_N-Xerr_N+PoleErr_N`,
`B_N=(alpha/N)*(T_N-Omega_N)`.

Compact `C²` support implies the Lipschitz regularity needed by the existing
Robin remainder bound, so `abs(selfError_N)<=exp(1/2)*c/(2*N)`.
There is no added regularity premise.

### 2. Exact center-pole cancellation

For positive distinct integers, elementary exponential algebra gives

`Omega_N(n,j)/(sqrt(n)*sqrt(j))
 = (1/2)*(1/abs(n-j)+1/(n+j))`.

Finite harmonic sums, with `H_0=0`, therefore give

`(Omega_N*s)_n=sqrt(n)*((H_(N-n)+H_(N+n))/2-3/(4*n))`,
`(T_N*s)_n=N/sqrt(n)+H_N*sqrt(n)`.

Thus `B_N*s-alpha*s=(alpha/N)*sqrt(n)*R_n`, where
`R_n=H_N-(H_(N-n)+H_(N+n))/2+3/(4*n)`.
The exact harmonic-tail identities are

`sum_(n=1..N)(H_N-H_(N-n))=N`,
`sum_(n=1..N)(H_N-H_(N-n))²=2*N-H_N`.

They follow by finite reversal and the reciprocal harmonic increment, or by
expanding the square and counting pairs. Also `0<=H_(N+n)-H_N<=1`.
The elementary three-term square bound gives
`sum_(n=1..N)n*R_n²<=6*N²`; hence
`norm(B_N*s-alpha*s)²<=6*alpha²`.
The large harmonic row cancels through both pole terms before normalization.

### 3. Mean-zero periodic rows

A period-`q` sequence `a` with zero period sum has interval sums bounded by
`B=2*sum_(i<q)abs(a_i)`. Abel summation on translated and reflected intervals
gives the inverse-distance row bound `2*B`. The inverse-sum row, with its
diagonal removed, costs at most `B+A`, where `abs(a_n)<=A`.
Consequently

`abs((Omega_N*(a(n)/sqrt(n)))_n)<=(2*B+A)*sqrt(n)`,
`abs((T_N*(a(n)/sqrt(n)))_n)<=2*B*sqrt(n)`,
`norm(B_N*(a(n)/sqrt(n)))²<=alpha²*(4*B+A)²`.

Conductor one is constant. Every other normalized Ramanujan mode has zero
period mean, from exact Gram orthogonality with conductor one. Thus the
center correction has the required bounded raw residual in every fixed mode.

### 4. Literal cross-integral error

For `0<a<=b`, write `u=exp(-a/2)`, `v=exp(-b/2)`,
`q=exp(-2a)`, `r=exp(-2b)`, `D=1-q`, `E=1-r`.
Then `omega(a)-omega(b)=(u-v)/D+v*(q-r)/(D*E)`.
Exponential tangent bounds give `u-v<=(b-a)*u/2`, `q-r<=2*(b-a)*q`,
and `a²*q<=D²`. Together with `omega(a)*a²<=34`, this proves

`omega(a)-omega(b)<=19*(b-a)/a²`,
`omega(s-w)-omega(s+w)<=38*w/(s-w)²`.

For distinct positive integers `n,j<=N`, put `d=abs(n-j)`, `M=max(n,j)`.
The exact logarithmic gap gives
`abs(log(n)-log(j))-c/N >= (1-c)*d/M`.
The signed atom-pair estimate therefore gives

`abs(Xerr_N(n,j))<=Cx*w²*M²/d²`,
`Cx=38*A1²/(M2*(1-c)²)`, `A1=integral(abs(phi))`.

The two-sided inverse-square row sum is at most `4`. Splitting the weighted
row at `n/2` and `2*n` gives
`sum_(j!=n)max(n,j)²/(sqrt(j)*abs(n-j)²)<=36*N*sqrt(n)`.
Hence

`abs(<Xerr_N*x,x>)<=4*Cx*c²*norm(x)²`,
`norm(Xerr_N*(a(n)/sqrt(n)))²<=(36*Cx*A*c²)²`.

### 5. Both pole-moment errors

For `abs(t)<=1/2`, `0<=u<=w<=1`,
`abs(exp(t*u)-1)<=w*exp(1/2)/2` and `exp(t*u)<=exp(1/2)`.
Integrating against a signed atom yields

`abs(Gplus/minus-w*I)<=exp(1/2)*w²*A1/2`,
`abs(Gplus/minus)<=exp(1/2)*w*A1`.

Expanding the product error around `w*I` gives

`abs(Gminus*Gplus/G-w*I²/M2)<=Cp*w²`,
`Cp=exp(1/2)*(exp(1/2)+1)*A1²/(2*M2)`.

The elementary two-pole kernel bounds then imply

`abs(<PoleErr_N*x,x>)<=2*Cp*c²*norm(x)²`,
`norm(PoleErr_N*(a(n)/sqrt(n)))²<=4*Cp²*A²*c^4`.

All raw profile residuals above are uniformly bounded. Division by
`sqrt(log(N))` makes them vanish. Combining them with the existing prime norm
residual and the self-error limit proves the intended full-Weil quasimode.

### 6. Coercivity for every strict width ratio

The exact center row gives `(Omega_N*s)_n/s_n<=n*(H_N+1)`.
Weighted Schur retains this variable row potential. Since
`H_N<=log(N)+1` and `(n/N)*log(N/n)<=1`, division by `N` costs at most
`sum_n (n/N)*log(n)*x_n²+3*norm(x)²`.
For any `lam>0`, the existing parametric top-atom bound is

`sum_n (n/N)*log(n)*x_n²
 <=(1+1/lam)*D_N(x)+(1+lam)*psi*norm(x)²`,
`psi=log(4)+4/exp(1)`.

On the harmonic hyperplane the two-pole form vanishes, so

`<B_N*y,y> >= -alpha*(1+1/lam)*D_N(y)
              -alpha*((1+lam)*psi+3)*norm(y)²`.

Let `e=s/norm(s)`. The raw pole residual and `norm(s)>=1` imply
`norm(B_N*e)<=4*alpha`. Orthogonal pole removal preserves `D_N` and contracts
the norm. The symmetric-form projection identity bounds the change in the
center form by `12*alpha*norm(x)²`. Thus the whole-space mass constant is
`alpha*((1+lam)*psi+15)`.

Cauchy--Schwarz on `[0,1]` gives `0<=alpha<=c`. Set
`lam=2*c/(1-c)` and `kappa=(1-c)/4`, so
`alpha*(1+1/lam)<=(1+c)/2`.
The existing prime counterterm gives eventually
`log(N)*Id-P_N >= (gamma-kappa)*Id+(1-kappa)*D_N`.
Combining every literal error cost yields

`W_N[x]>=a*norm(x)²+kappa*D_N(x)`,
`a=sigma-kappa-exp(1/2)/2-alpha*((1+lam)*psi+15)
   -4*Cx*c²-2*Cp*c²`.

Here `kappa>0` for every `0<c<1`. Therefore unit vectors with energy at most
`T` have defect at most `max(0,(T-a)/kappa)`.

### 7. Exact spectral assembly

Prime-defect compactness gives a fixed finite Ramanujan approximation on each
bounded complete-Weil energy sublevel. The finite Gram limit supplies a
uniform detecting-coordinate mass of at least `1/18`.

The trial energies are proper and distinct. The ground shift satisfies
`alpha<1`, while every other arithmetic excitation is at least
`2*log(2)>=1`. Distinct positive non-ground conductors inherit the known
injectivity of arithmetic adjunction energy; logarithmic growth gives finite
sublevels.

Norm quasimodes give distinct actual eigenvalues near each fixed finite
packet, proving the lower count. At a threshold away from all trial energies,
residual-over-gap bounds make each detecting coordinate above the threshold
vanish uniformly on the low spectral subspace. The coordinate-mass certificate
and finite-dimensional rank give the matching upper count, including
multiplicity. Two isolating thresholds leave one eigenvalue near each label.
The complementary gap and the norm residual force its spectral projection to
capture the normalized Ramanujan vector.

## Verification checkpoint

The manifest `/tmp/WeilRamanujan-draft-manifest.json` records the active
forty-two-module graph. Each verified scratch endpoint has a retained
transitive axiom report in `logs/complete-weil-spacing-axioms-2026-10-28.log`;
only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The table below records scratch verification, installation, and first required
olean generation. Verified modules are imported by their owner
umbrellas; no umbrella was compiled. The SSHA density increment bound is
documented in its README. Final installed-source checks without output
generation remain outstanding.
The three main endpoints are still unchecked:

- `tendsto_completeWeilMatrix_ramanujan_residual_norm`
- `eventually_completeWeil_spectral_count_eq`
- `exists_simple_completeWeil_eigenline`

The initial combined import check exposed an existing collision between ACS
`TheScalingSurface.localPair` and `DistinctEffectiveCyclesMeetNonnegatively.localPair`
(they occupy the same namespace). The two center adapters were replaced with
minimal imports directly over the Levy density. The active source import graph
has no path through the incompatible branch. Static checks of all three owner
umbrellas likewise find no incompatible branch, both with and without the new
direct imports. Foreign sources were unchanged.
The superseded owned center modules and their build artifacts were removed.

| # | Owner/module | Current verification |
|---|---|---|
| 1 | `HTGeometry/HarmonicTailSquareIdentity` | Scratch verified; installed; first required olean built |
| 2 | `HTGeometry/FiniteReversedAbelBounds` | Scratch verified; installed; first required olean built |
| 3 | `RenormalizedArithmeticPotentialTheory/TheFullWeilMatrixIsTheActualAtomicForm` | Scratch verified; installed; first required olean built |
| 4 | `RenormalizedArithmeticPotentialTheory/TheLogarithmicCenterKernelIsHarmonic` | Scratch verified; installed; first required olean built |
| 5 | `HTGeometry/FiniteHarmonicRows` | Scratch verified; installed; first required olean built |
| 6 | `SpacingScaleHarmonicAnalysis/TheArchimedeanDensityHasQuadraticIncrementControl` | Scratch verified; installed; first required olean built |
| 7 | `HTGeometry/FiniteWeightedGroundStateBound` | Scratch verified; installed; first required olean built |
| 8 | `RenormalizedArithmeticPotentialTheory/TheSeparatedAtomPairingsAreThePrimeKernel` | Scratch verified; installed; first required olean built |
| 9 | `RenormalizedArithmeticPotentialTheory/TheSeparatedMarkovMatrixHasExactCrossEntries` | Scratch verified; installed; first required olean built |
| 10 | `RenormalizedArithmeticPotentialTheory/TheFullWeilMatrixSplitsAtTheSpacing` | Scratch verified; installed; first required olean built |
| 11 | `RenormalizedArithmeticPotentialTheory/TheLogarithmicCenterRowCancelsThePole` | Scratch verified; installed; first required olean built |
| 12 | `HTGeometry/HarmonicCenterBoundaryBounds` | Scratch verified; installed; first required olean built |
| 13 | `HTGeometry/IntegerLogarithmicWindowGap` | Scratch verified; installed; first required olean built |
| 14 | `HTGeometry/FiniteInverseSquareDistanceRows` | Scratch verified; installed; first required olean built |
| 15 | `HTGeometry/FinitePoleWeightedDistanceRows` | Scratch verified; installed; first required olean built |
| 16 | `RenormalizedArithmeticPotentialTheory/TheAtomCrossMatrixIsCloseToItsCenterKernel` | Scratch verified; installed; first required olean built |
| 17 | `HTGeometry/FiniteKernelErrorFromDistanceRows` | Scratch verified; installed; first required olean built |
| 18 | `RenormalizedArithmeticPotentialTheory/TheAtomCrossReplacementHasUniformErrors` | Scratch verified; installed; first required olean built |
| 19 | `RenormalizedArithmeticPotentialTheory/TheCenterCollarIsPaidByTheTopAtoms` | Scratch verified; installed; first required olean built |
| 20 | `RenormalizedArithmeticPotentialTheory/TheCompleteWeilTrialEnergiesAreSimpleAndProper` | Scratch verified; installed; first required olean built |
| 21 | `HTGeometry/FiniteShiftedHarmonicAbelBounds` | Scratch verified; installed; first required olean built |
| 22 | `RenormalizedArithmeticPotentialTheory/ThePoleMomentsHaveQuadraticDilationError` | Scratch verified; installed; first required olean built |
| 23 | `RenormalizedArithmeticPotentialTheory/TheMeanZeroCenterRowsAreUniformlyBounded` | Scratch verified; installed; first required olean built |
| 24 | `RenormalizedArithmeticPotentialTheory/TheCenterCorrectionHasBoundedPoleResidual` | Scratch verified; installed; first required olean built |
| 25 | `HTGeometry/SymmetricFormGroundProjection` | Scratch verified; installed; first required olean built |
| 26 | `HTGeometry/HermitianLowerSpectralWindows` | Scratch verified; installed; first required olean built |
| 27 | `RenormalizedArithmeticPotentialTheory/TheCompleteWeilSelfEnergyHasItsFinitePart` | Scratch verified; installed; first required olean built |
| 28 | `RenormalizedArithmeticPotentialTheory/TheCenterCorrectionSelectsTheConstantRamanujanMode` | Scratch verified; installed; first required olean built |
| 29 | `HTGeometry/FiniteTwoPoleKernelBounds` | Scratch verified; installed; first required olean built |
| 30 | `RenormalizedArithmeticPotentialTheory/TheTwoPoleReplacementHasUniformErrors` | Scratch verified; installed; first required olean built |
| 31 | `RenormalizedArithmeticPotentialTheory/TheCompleteWeilMatrixHasAnExactErrorDecomposition` | Scratch verified; installed; first required olean built |
| 32 | `RenormalizedArithmeticPotentialTheory/HorizonKernelEuclideanIdentities` | Scratch verified; installed; first required olean built |
| 33 | `RenormalizedArithmeticPotentialTheory/TheWeilReplacementErrorsVanishOnRamanujanModes` | Unchecked scratch |
| 34 | `RenormalizedArithmeticPotentialTheory/TheCompleteWeilMatrixHasRamanujanQuasimodes` | Unchecked scratch |
| 35 | `RenormalizedArithmeticPotentialTheory/ThePoleProjectionIsTheEuclideanGroundProjection` | Unchecked scratch |
| 36 | `RenormalizedArithmeticPotentialTheory/TheCenterCorrectionIsBoundedOnThePole` | Unchecked scratch |
| 37 | `RenormalizedArithmeticPotentialTheory/TheCenterCorrectionRetainsThePrimeDefect` | Unchecked scratch |
| 38 | `RenormalizedArithmeticPotentialTheory/TheCompleteWeilEnergyControlsThePrimeDefect` | Unchecked scratch |
| 39 | `RenormalizedArithmeticPotentialTheory/BoundedCompleteWeilEnergyHasFiniteRamanujanCoordinates` | Unchecked scratch |
| 40 | `RenormalizedArithmeticPotentialTheory/TheCompleteWeilMatrixRealizesFiniteAdjunctionPackets` | Unchecked scratch |
| 41 | `RenormalizedArithmeticPotentialTheory/TheBoundedCompleteWeilSpectrumIsTheAdjunctionSpectrum` | Unchecked scratch |
| 42 | `RenormalizedArithmeticPotentialTheory/TheSimpleCompleteWeilEigenlinesConvergeToRamanujanLines` | Unchecked scratch |

Unchecked rows above identify the remaining Lean checks. The actual matrix
assembly, coercivity, and three spectral endpoints must pass before the full
statement is marked proved. No unchecked draft is a completed contribution.
