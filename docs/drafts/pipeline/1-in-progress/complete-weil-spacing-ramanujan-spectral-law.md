# Ramanujan spectral law for the complete Weil form at the spacing

- **ID:** complete-weil-spacing-ramanujan-spectral-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** full-prime Ramanujan quasimodes; bounded-defect finite-span approximation; exact archimedean atom pairing; actual two-pole rows
- **Statement:** The complete normalized Weil matrix has Ramanujan quasimodes at every fixed separated width ratio, and its bounded spectrum is exhausted by their explicit simple energies throughout the separated regime (strengthened conjecture; exact separation interfaces still to prove).
- **Count:** uncounted; stronger extension of the packet-form candidate, not an additional count for its weaker corollaries

## Goal

Identify the bounded spectrum of the actual complete Weil form on a growing
log-lattice atom family. The target retains the prime, Gamma, and both pole
terms. It would supply a spectral tool beyond the existing lower bounds and
the proposed finite-packet quadratic-form limit. It does not assert positivity
on arbitrary Weil tests, unbounded overlap, or RH.

## Gates

- [ ] Exact carrier and normalization; full corpus and primary-literature novelty audit
- [ ] Dependency-closed paper proof of row estimates, quasimodes, and spectral exhaustion
- [ ] Lean realization, individual foreground checks, transitive axioms, umbrella wiring

## Exact proposed carrier and energies

Fix real C2 phi supported in [0,1], M2=integral(phi^2)>0, I=integral(phi),
and 0<c<1. Let w=c/N and g=atomDilate(phi,w). The proposed matrix is

`W_N=(atomicMarkovGram(g,N)
 + row0(atomPoleRow(g,N)) outer row1(atomPoleRow(g,N))
 + row1(atomPoleRow(g,N)) outer row0(atomPoleRow(g,N)))/(w*M2)`.

These are existing literal atom and pole matrices. The inspected theorem
`polarDefect_atomic` identifies their quadratic form with weilQuad of the
actual synthesized test. The atom basis has mass matrix w*M2 times identity
eventually, since the supports are separated. Reindexing Fin N to 1..N must
be proved when applying the existing prime-matrix package.

Put
`sigma=log(1/(2*pi*c))+bumpRobin(phi,1)/M2`,
`alpha=c*I^2/M2`, and
`lambda_m=sigma+log(m)+tameDifferent(m)+alpha*[m=1]` for m>=1.

Target: every fixed normalized Ramanujan vector has residual norm tending
to zero at lambda_m for W_N, for every 0<c<1. Every threshold away from
these energies has eventual exact spectral count, with multiplicity, equal to
the finite arithmetic count; each fixed eigenline is eventually simple and
captures its Ramanujan vector. The full-range coercivity argument below replaces
the original small-c restriction. No part of this spectral target is proved yet.

## The new cancellation to audit

Let s_n=1/sqrt(n), t_n=sqrt(n), and let Omega_N have zero diagonal and
off-diagonal entry archLevyDensity(|log(n)-log(j)|). The center-value
archimedean and two-pole correction is

`B_N=(alpha/N)*(s outer t+t outer s-Omega_N)`.

The actual density is exp(-u/2)/(1-exp(-2u)). Direct partial fractions give

`Omega_N(s)_n
 =sqrt(n)*((H_(N-n)+H_(N+n))/2-3/(4n))`,

where H_0=0 and H_k=sum_(j=1..k)1/j. Indeed, after dividing the row by
sqrt(n), each j<n contributes n/(n^2-j^2), and each j>n contributes
j/(j^2-n^2). Splitting both into their difference and sum denominators yields
the displayed harmonic identity. Meanwhile
`(s outer t+t outer s)s=N*s+H_N*t`. Therefore

`B_N s-alpha*s
 =(alpha/N)*sqrt(n)*(H_N-(H_(N-n)+H_(N+n))/2+3/(4n))` coordinatewise.

The large harmonic row cancels only after retaining both pole terms. This
offers a residual estimate, not merely the previously conjectured average
rank-one form correction. The identity and its exact normalizations still
require Lean verification.

The endpoint harmonic singularity has an elementary finite square bound:

`sum_(k=1..N)(H_N-H_(k-1))^2=2*N-H_N`.

Expand the square, interchange the finite sums, and count k<=min(i,j).
The diagonal contributes H_N; the two strict triangles contribute
2*sum_(j=1..N)(j-1)/j. This controls the displayed remainder uniformly in
Euclidean norm, using n<=N and H_(N+n)-H_N<=1. Division by sqrt(log N)
then makes the normalized pole residual tend to zero. No numerical check is
used for either finite identity.

For any fixed zero-mean periodic a, partial sums on every interval are
uniformly bounded. Abel summation therefore bounds uniformly the shifted
harmonic sums in the row of Omega_N(a(n)/sqrt(n)), giving absolute row
at most C_a*sqrt(n). Both sum a(n) and sum a(n)/n are bounded as well.
Consequently B_N applied to that unnormalized profile has bounded Euclidean
norm, hence vanishing residual after division by sqrt(log N). Positive
conductor Ramanujan modes other than one have zero period mean. The required
uniform reversed and shifted harmonic-sum lemmas remain to formalize.

## Actual atom integrals, not only their center values

The pair estimate `abs_crossTerm_sub_le` bounds the difference between the
literal atom integral and its center-density approximation. The associated
packet-form card derives a candidate bound

`(omega(s-w)-omega(s+w))/sqrt(n*j)
 <= C_c*w*max(n,j)/(n-j)^2`.

For a fixed periodic pole profile bounded in pole gauge, divide the pair error
by w*M2 and sum a row. Its absolute value is bounded by
`C*w^2*N*sqrt(n)`, since sum of reciprocal difference squares is at most two
on each side. Its Euclidean norm is uniformly bounded when w=c/N. Thus its
normalized profile residual tends to zero. The actual pole scalar
`(integral g*exp(-u/2))*(integral g*exp(u/2))/(w*M2)` differs from
w*I^2/M2 by O(w^2); the corresponding row estimate also vanishes after
normalization. Exact inequalities and integrability proofs remain.

The Robin self-energy error is O(w), while the existing prime residual tends
to zero. Combining these with the preceding rows would prove the first target.
The weaker packet-form limit would then be a corollary of these actual
quasimodes, not a separately counted contribution.

## Earlier small-ratio argument, superseded by the full-range mechanism

`eventually_markovEnergy_ge_defect` and
`two_mul_abs_poleMoments_le_defect` in ALG were inspected. After division by
w*M2 they imply a lower bound on W_N with defect coefficient

`1-epsilon-(32*exp(2)+poleConstant*exp(w/2))*c`.

Choose epsilon=1/4 and c smaller than both markovOverlapBound and
`1/(4*(32*exp(2)+poleConstant*exp(1/2)))`, as well as 1/2. The coefficient
is then at least 1/2 for w<=1. The remaining scalar coefficient has a fixed
lower bound depending only on phi and c. Thus bounded W_N energy would bound
the same literal prime defect. The newly checked finite-Ramanujan
approximation can supply the detecting-coordinate certificate exactly as in
the prime spectral-exhaustion project. The low-window residual/rank argument
would then give exact counts and simple eigenlines for this actual matrix.

Cauchy--Schwarz on [0,1] gives 0<=alpha<=c<1/2. The ground energy shift is
therefore separated from every positive excitation, since log(m)>=log(2)>=1/2
for m>=2. The established injectivity of adjunction energies separates all
other labels, and logarithmic growth gives properness. These deductions and
their precise strict inequalities still need verification.

The repository's atomSpacing is log(1+1/N), not 1/N. The inspected
`inv_succ_le_atomSpacing` bounds it below by 1/(N+1); for c<1/2 this gives
w<=atomSpacing(N)/2 eventually. No all-horizon spacing inequality is assumed.

## Audit status

Inspected sources include ALG `TheAtomicFormIsMetzlerBelowTheSpacing.lean`
at its literal matrix definitions and `polarDefect_atomic` (lines 282-320 and
417-505), the exact exponential row translations, the RAPT signed diagonal
identity, and the SSHA pair estimate. The first two corpus searches for this
full-Weil Ramanujan spectral law returned existing prime spectra, pole rows,
and overlap/harmonic-hyperplane results; no matching theorem was identified
among those inspected statements. This is not an exhaustive novelty claim.
The small-aperture Suzuki and numerical-study exclusions on the packet-form
card remain relevant, but a dedicated external audit is still required.

Further primary-source audit: Groskin, [A finite Guinand--Weil dictionary and
archimedean tail order](https://arxiv.org/html/2607.02828v3), introduction and
Section 2 through Theorem 2.5, was inspected. Its finite matrices use integer
Fourier modes on a fixed interval and divided differences of source functions.
Its proved dictionary identifies their quadratic values with exact zero sums;
its stated tail theorem controls an omitted archimedean integral. The proposed
carrier here instead uses shrinking atoms at logarithms of integers, with a
jointly growing spatial horizon. No Ramanujan eigenline or corresponding
bounded-spectrum exhaustion theorem was identified in the inspected material.
This is a carrier-level distinction, not an exhaustive literature claim.

The shifted-harmonic search surfaced the exact existing generic inputs:
`RenormalizedBiarithmeticGeometry.abs_sum_range_le_of_periodic` and
`RHTower.Sieve.abs_sum_mul_le_of_bounded_partial`, plus the tail version in
`Sieve/AbelTail.lean`. Their source statements and proofs were inspected.
The newer SAHT quantitative Gram file has a private harmonic discrepancy proof;
its bounded-partial-sum mechanism is baseline and need not be duplicated.
For a mean-zero periodic sequence, let D bound partial sums on every interval
and A bound its values. The lower and upper difference-denominator sums in
Omega's row are at most D each by Abel, including reversed lower intervals.
The full sum-denominator sum is at most D/(n+1), and deleting its diagonal
costs at most A/(2n). Thus the row divided by sqrt(n) is bounded by
`D+D/(2*(n+1))+A/(4*n)`. The remaining adapters must instantiate these exact
finite inequalities and prove the reversal/reindexing identities.

The Robin remainder is already quantitative in the exact required carrier:
`SpacingScaleHarmonicAnalysis.abs_levyEnergy_atomDilate_sub_le` gives normalized
error at most exp(1/2)*w/2. Its source proof and the exact dilation mass and
bumpRobin identities were inspected. Its Lipschitz premise can be discharged
from compact C2 support using the previously inspected compact-source theorem.
No additional regularity assumption or conjectural asymptotic is needed there.

For the pole-vector remainder, put A_n=H_N-H_(N-n) and
B_n=H_(N+n)-H_N. Then A_n>=0, 0<=B_n<=1, and
`sum_(n=1..N) A_n^2=2*N-H_N`. The harmonic bracket in the exact row is
`(A_n-B_n)/2+3/(4*n)`. Squaring with the elementary three-term inequality,
using n<=N, sum A_n^2<=2N, and sum_(n<=N)1/n<=N bounds its weighted
square sum by a constant times N^2. Multiplication by (alpha/N)^2 gives the
uniform Euclidean residual bound before logarithmic normalization.
The harmonic square identity can alternatively be proved by induction:
its first-moment sum is N, and adding the new reciprocal term changes the
square sum by 2-1/(N+1). Both proofs are exact finite algebra.

The scalar normalization was rechecked directly against
`RenormalizedArithmeticPotentialTheory/TheArchimedeanFinitePartIsMinusLogTwoPi.lean`.
Its exact `finitePart_profileRobin_eq` states
`2*gammaHardyPhaseRate(0)+profileRobin(phi)+gamma
 =-log(2*pi)+bumpRobin(phi,1)/M2`.
With log(1/w)-log(N)=-log(c), this is precisely the proposed sigma.
The evaluated Robin/Gamma identity is existing input, not part of the new claim.

The pole-factor transfer needs only a bounded unnormalized error. With
A1=integral(abs(phi)), support and the elementary exponential increment bound
give `|Gpm-w*I|<=C*w^2*A1` and `|Gpm|<=exp(1/2)*w*A1` for w<=1.
Hence `|Gminus*Gplus/(w*M2)-w*I^2/M2|<=C_phi*w^2`.
On u_n=a(n)/sqrt(n), with |a|<=A, the two rank-one factors give
`(sum a)*s+(sum a/n)*t`; their norm is at most
`A*N*sqrt(H_N)+A*H_N*N`. Using H_N<=N and w=c/N already bounds the
coefficient-error action uniformly in N. Division by sqrt(log N) therefore
kills it. No quantitative asymptotic for the atom moments or log(N)/N estimate
is needed for the residual theorem. The diagonal Robin error and the summed
pair replacement error can be treated by the same bounded-error principle.

For exact assembly, polarization of the existing signed finite-atom quadratic
identity should identify the matrix entries as a scalar diagonal minus the
literal prime matrix, minus the off-diagonal positive-center cross integrals,
plus the two pole outer products. Distinct-atom support removes the mass cross
term, and of the two signed center lags only the positive one meets the Levy
integral. Reindexing Fin N by i+1 gives PrimeHorizonIndex N and therefore the
same actual carrier used in the prime spectral package. This exact equality,
including its factor two, remains an explicit Lean obligation.

Further corpus baseline: RAPT `TheArchimedeanPlacePaysTheArithmeticPoint.lean`
was inspected through its joint-germ definitions and matched Cesaro counterterm.
It already identifies conductor one as the unique periodic mode coupled to a
constant archimedean mode. This algebraic rank-one mechanism is excluded novelty.
The present target still requires the literal atom-integral matrix, cancellation
of its boundary rows, actual norm residuals, and bounded spectral exhaustion.

The row argument naturally has a stronger intermediate form for every fixed
periodic a, not only individual Ramanujan modes. Split a=mean(a)+b, with b of
mean zero. The exact pole row and the shifted Abel bounds give
`norm(B_N*(a(n)/sqrt(n))-alpha*mean(a)*s)<=C_a` uniformly in N.
The actual atom-pair and pole-factor errors obey the same uniform bound.
After division by sqrt(log N), the actual off-diagonal archimedean-plus-pole
correction therefore tends in norm to alpha times the constant periodic
component. This supplies the full residual control missing from a scalar
rank-one form limit. Applying it to each Ramanujan mode would then reduce the
full-Weil quasimode theorem to the already proved prime residual theorem.
The generic periodic row statement and its transfer remain unformalized and
are support for the same single spectral contribution.

The exact harmonic-tail first and second moments now have an unchecked draft
`/tmp/HarmonicTailSquareIdentity.lean`. It uses the standard rational harmonic
numbers cast to reals and the common reciprocal increment; no computation or
new analytic premise is involved. It is support for this candidate, not a
separate contribution. The full matrix proof remains incomplete.

An unchecked finite/reversed Abel adapter is retained at
`/tmp/FiniteReversedAbelBounds.lean`. It reuses the existing quantitative Abel
inequality after truncating the sequence, then reflects a finite interval.
These elementary adapters are baseline support, not a separate contribution.
Completed API outputs retained for cleanup:
`/tmp/WeilRamanujan-harmonic-reversal-mathlib-search.json`,
`/tmp/WeilRamanujan-interval-reflection-search.json`,
`/tmp/WeilRamanujan-interval-subtraction-search.json`,
`/tmp/WeilRamanujan-interval-reflection-mathlib-search.json`, and
`/tmp/WeilRamanujan-interval-subtraction-mathlib-search.json`.

A direct carrier adapter can define the complete matrix on `PrimeHorizonIndex N`
by the literal `markovPair(atom g n,atom g j)` plus the two products of actual
exponential atom moments. The explicit bijection `n -> n-1` to `Fin N` then
identifies it entrywise with the existing ALG Gram and pole rows. This avoids
assuming any matrix model for Weil's form; the existing `polarDefect_atomic`
identity can be transported by the same finite reindexing. The adapter and its
quadratic identity remain unproved.

The exact scalar assembly has now been checked on paper. Put
`G=integral(g^2)`, `Gpm=integral(g*exp(plus/minus u/2))`,
`T_N=s outer t+t outer s`, and let X_N have zero diagonal and actual atom
cross integrals off the diagonal. At separated supports the literal matrix is

`W_N=(2*gammaHardyPhaseRate(0)+levyEnergy(g)/G) I
       -P_N-X_N/G+(Gminus*Gplus/G)*T_N`.

The pair theorem `levyEnergy_atom_pair` confirms the off-diagonal coefficient
minus one: its quadratic cross contribution is minus twice the cross integral.
The two actual exponential moments give the displayed rank-two term exactly.
The scalar diagonal minus log(N) tends to sigma-gamma, so the prime energy
E(m)=gamma+log(m)+tame(m) gives precisely lambda_m after adding the rank-one
limit. The carrier equality still requires Lean; no model matrix is assumed.

More explicitly, the inspected defect and pole inequalities give eventually
`W_N[x]>=a_phi_c*norm(x)^2+(1/2)*D_N(x)` for the proposed small c, where a
valid fixed scalar is
`a_phi_c=2*rate(0)+log(1/c)+profileRobin(phi)+gamma-1/4
 -exp(1/2)/2-markovCrossConstant*c-2*poleConstant*exp(1/2)*c`.
Here w<=1 and wN=c. Thus the existing uniform finite-Ramanujan approximation
applies to every bounded-energy vector, with no sign restriction on phi.
This scalar is only a coercivity aid, not a claimed sharp constant.

The literal full-Weil carrier now has an unchecked scratch draft,
`/tmp/TheFullWeilMatrixIsTheActualAtomicForm.lean`: the Markov Gram plus both
pole products, its exact polar-defect identity, the positive-integer/Fin index
bijection, and equality of its Euclidean form to the actual synthesized Weil
functional. It is not installed, checked, or counted. This is source transport,
not the new spectral conclusion.

Refreshed ALG and SSHA searches returned existing fixed-fraction positivity,
restricted negative-index laws, and local Frobenius Ramanujan bounds. The local
factor module's introduction was inspected: its Ramanujan parameter is a
finite-field normalized trace, not the present integer-horizon excitation.
The newer profile-free window module was inspected at its introduction and
final support/positivity endpoints. None of those inspected statements asserts
this common-profile full-Weil spectral law. Generic positivity is excluded
novelty. A separate, unproved larger window-sector conjecture is recorded at
`../0-backlog/complete-weil-window-arithmetic-profile-spectrum.md`.

The exact center-density formula is already formalized in ACS
`CrossTowerCollarAndFiniteEulerLatticePositivity`: `collarWeight_eq_of_lt`
and `archLevyDensity_log_div_nat` were inspected in source. The new unchecked
scratch `/tmp/TheArchimedeanCenterKernelIsAHarmonicKernel.lean` only converts
that formula to the inverse-difference plus inverse-sum row in pole gauge.
This adapter is supporting baseline reuse, not new counted mathematics.

Additional primary-source audit: Suzuki, [Spectral convergence associated with
Weil's quadratic form](https://arxiv.org/html/2610.32704v1), introduction and
Theorems 1.1–1.2, assumes RH for convergence of distinguished differentiation
extensions to distinct zeta-zero ordinates. This is a different operator and
a conditional convergence theorem; it is not an input or a matching result
for the present unconditional shrinking-atom Gram spectrum.

New unchecked generic scratch `/tmp/FiniteHarmonicRows.lean` supplies the exact
inverse-difference and inverse-sum row identities, including deletion of the
diagonal. It supports the literal collar cancellation and is not counted.

### Simpler exact-integral error mechanism

A derivative-free alternative avoids shifted logarithmic exponential algebra.
For 0<a<=b, put u=exp(-a/2), v=exp(-b/2), q=exp(-2a), r=exp(-2b),
D=1-q, E=1-r. Then

`omega(a)-omega(b)=(u-v)/D+v*(q-r)/(D*E)`.

The exponential tangent inequality gives
`u-v<=(b-a)*u/2` and `q-r<=2*(b-a)*q`. Also
`a*exp(-a)<=1-exp(-2a)`, since exp(a)-exp(-a)>=a.
Squaring gives `a^2*q<=D^2`. The existing CHMD theorem
`archLevyDensity_mul_sq_le` bounds `omega(a)*a^2<=34`.
Using v<=1 and E>=D yields

`omega(a)-omega(b)<=19*(b-a)/a^2`,
`omega(s-w)-omega(s+w)<=38*w/(s-w)^2`.

The existing CHMD source and its proof were inspected. New unchecked scratch
`/tmp/TheArchimedeanDensityHasQuadraticIncrementControl.lean` formalizes this
argument without differentiation or additional analytic assumptions.

For positive distinct integer n,j<=N, d=abs(n-j), M=max(n,j), and w=c/N,
`abs(log(n/j))-w >= (1-c)*d/M`, since log(M/min)>=d/M
and w<=c*d/M. The actual pair replacement error on a bounded pole profile
is therefore at most `C_phi,c*w^2*M^2/(sqrt(j)*d^2)` per row entry.
Split the row at n/2 and 2n. In the middle, M<=2n and
1/sqrt(j)<=2/sqrt(n), so the sum is at most
`32*C_phi,c*w^2*N*sqrt(n)`, using each one-sided reciprocal-square sum<=2.
Outside that interval M^2/d^2<=4 and 1/sqrt(j)<=1; the row contributes
at most `4*C_phi,c*w^2*N`, also <=the same scale times sqrt(n).
Consequently the whole row is bounded by
`36*C_phi,c*w^2*N*sqrt(n)` and its squared Euclidean norm by
`(36*C_phi,c)^2*w^4*N^4`. At w=c/N this is uniform.
This supplies the required bounded unnormalized error by elementary finite
sums; it does not require a sharper weighted density derivative estimate.
These row and transfer inequalities still require their exact Lean proofs.

### Stronger conjecture exposed by the row argument: the entire separated regime

The original small-c exhaustion restriction may be removable. This is a
strengthened conjecture requiring a fresh paper and novelty audit, not a proved
extension. The proposed final range is **0<c<1**, with w=c/N<atomSpacing(N)
eventually. The existing exact prime and mass interfaces must be checked and,
where their stated half-spacing restriction is stronger than their mechanism,
proved on the full strictly separated range. No such relaxation is assumed.

Let Omega be the symmetric nonnegative center-density matrix, s_n=1/sqrt(n),
t_n=sqrt(n), and B=(alpha/N)(s tensor t+t tensor s-Omega). The exact row
identity gives `(Omega s)_n/s_n <= n*(H_N+1)`: use H_(N-n)<=H_N
and H_(N+n)-H_N<=1. Weighted Schur then gives, on x orthogonal to s,

`<Bx,x> >= -alpha*sum_n (n/N)*(H_N+1)*x_n^2`.

Since H_N<=log(N)+1 and `(n/N)*log(N/n)<=1`, the weighted sum on the
right is at most `sum_n (n/N)*log(n)*x_n^2 + 3*mass(x)`.
The already inspected `sum_top_le_poleDefect` yields coefficient 2 in front
of D, sufficient for all c<1/2. The refreshed search additionally surfaced
ALG `TheArchimedeanCrossEnergyIsOneSided.sum_top_le_poleDefect_param`:
its statement and edge/Chebyshev proof were inspected. It yields coefficient
`1+1/lam` for any lam>0, with a finite mass constant. This input is baseline
and its independent source/axiom verification must be obtained before use.

The pole has exactly zero prime defect. Write any vector as x=a*e+y, e=s/||s||,
y orthogonal to e. Then D(y)=D(x). The ground-row identity and harmonic square
bound give ||Be|| uniformly bounded. The cross and ground terms in <Bx,x>
therefore cost only a constant times ||x||^2. Consequently, on the whole space,

`<Bx,x> >= -alpha*(1+1/lam)*D(x)-C_lam*mass(x)`.

The actual cross-integral replacement error has a stronger uniform operator
bound as well: each absolute entry is at most
`C_phi,c*w^2*max(n,j)^2/(n-j)^2`, hence every absolute row sums to at most
`4*C_phi,c*w^2*N^2`. The symmetric Schur bound gives a uniform matrix norm
at w=c/N. The actual two-pole coefficient error is O(w^2), while the outer
product norm is at most 2*N*sqrt(H_N)<=2*N^(3/2), so that error is uniformly
bounded too. The actual self-energy remainder is already bounded.

Since alpha<=c<1, choose lam=2c/(1-c) and epsilon=(1-c)/4 in the prime
counterterm estimate. This leaves defect coefficient at least (1-c)/4>0
in the complete Weil matrix. Thus the same arithmetic compactness mechanism
should give spectral exhaustion for every strictly separated c, without a
smallness condition tied to the existing crude cross/pole estimates.

The ground shift alpha<1 remains below every nontrivial arithmetic excitation
(log(m)+tameDifferent(m)>1 for m>=2); this sharper elementary separation
needs its own exact proof or a checked existing lemma. All other energies
retain the established injectivity. This is one stronger target for the same
prospective contribution, not a numerical improvement counted separately.

Exact separation check: AES `primeSum_atomicTest` and RAPT
`integral_sub_shift_sq_atomicTest_eq` already assume only w<atomSpacing(N);
SSHA `levyEnergy_atom_pair` assumes only w<s. Their source statements and
relevant proofs were inspected. Thus their half-spacing relaxation is not an
outstanding gap: the full separated range is already supported by these inputs.
The identity for the synthesized mass still needs its exact named interface.

New programme baseline: SMAP README was read through its questions/tools, and
`TheConductorTwoIsTheFirstExcitation.lean` was inspected. Its
`ramanujanAdjunctionEnergy_sub_one_ge` proves the sharp first excitation
2*log(2), attained only at conductor two. It imports the completed quasimodes.
Its selective gap-transfer and Garding results are baseline, not a new claim
here. The proper shifted-energy ordering can reuse that exact gap. The
finite weighted Schur proof in HTGeometry was also inspected; a variable
diagonal version or existing ground-state identity is needed for the n-weighted
center row. The scalar Schur theorem alone would lose this essential weight.

Further exact baseline reuse: SMAP `TheSelectiveGardingInequality` was
inspected through `harmonicSum_poleProj`, `sum_sq_poleProj`, and
`poleDefect_sub_pole`. It already proves the projection and defect invariance
needed above. The new unchecked generic support draft
`/tmp/FiniteWeightedGroundStateBound.lean` retains the exact variable Schur
row potential; it is an adapter of the inspected weighted-AMGM argument.
No full-Weil Liouville sign claim is being inferred from global mean
cancellation: the required local harmonic convolution is a separate input.

Two additional unchecked support drafts, `TheSeparatedAtomPairingsAreThePrimeKernel` and `TheSeparatedMarkovMatrixHasExactCrossEntries`, give entrywise exact prime and Markov pairings at full spacing. The actual mass interface is AES `integral_atomicTest_sq`, already requiring only w<atomSpacing(N). These drafts are not installed, checked, or counted. Nine scratch drafts now support the strengthened target; the full spectral endpoint remains unproved.

Two further unchecked drafts now assemble the exact complete normalized entries (`TheFullWeilMatrixSplitsAtTheSpacing`) and the exact center row on the pole (`TheArchimedeanCenterRowCancelsThePole`). The pole rows reuse ALG `atomPoleRow_zero_apply` and `atomPoleRow_one_apply`, inspected in source. Eleven scratch drafts exist; none has passed Lean or been installed.

The new unchecked generic draft `/tmp/HarmonicCenterBoundaryBounds.lean` combines the exact harmonic-tail square identity with the upper increment bound to prove the explicit weighted boundary estimate `sum n*R_n^2 <= 6*N^2`. Twelve scratch drafts now exist; none is verified or installed.

Refreshed concurrent baseline: `TheArchimedeanCrossTermsVanishOnPeriodicProfiles.lean` was inspected at its exact expansion and periodic endpoint. Its quadratic-form estimate assumes a nonnegative common bump and `4*w<=atomSpacing(N)`, and bounds the archimedean interaction on mean-zero periodic pole profiles. Its independent compilation/axiom audit is not claimed here. Such quadratic-form vanishing is excluded from the novelty of this candidate. The target here requires actual norm residuals, both pole terms and the shifted ground energy, signed profiles, and complete bounded spectral counts/eigenlines for every `0<c<1`.

The exact inverse-square error mechanism now has three further unchecked generic drafts: `IntegerLogarithmicWindowGap`, `FiniteInverseSquareDistanceRows`, and `FinitePoleWeightedDistanceRows`. Their statements retain `(1-c)` in every shifted logarithmic gap, give the two-sided reciprocal-square bound 4, and give the weighted row bound `36*N*sqrt(n)`. They are supporting estimates, not separate contributions. Fifteen candidate drafts remain unchecked and uninstalled.

### Current exact support drafts

Eighteen unchecked scratch modules now cover the following support graph. None is installed or verified, and the complete spectral endpoint is still unproved. Generic bounds will be discharged on the literal kernels; they are not substitute analytic premises.

- `HTGeometry/HarmonicTailSquareIdentity`: unchecked `/tmp/HarmonicTailSquareIdentity.lean`.
- `HTGeometry/FiniteReversedAbelBounds`: unchecked `/tmp/FiniteReversedAbelBounds.lean`.
- `RenormalizedArithmeticPotentialTheory/TheFullWeilMatrixIsTheActualAtomicForm`: unchecked `/tmp/TheFullWeilMatrixIsTheActualAtomicForm.lean`.
- `RenormalizedArithmeticPotentialTheory/TheArchimedeanCenterKernelIsAHarmonicKernel`: unchecked `/tmp/TheArchimedeanCenterKernelIsAHarmonicKernel.lean`.
- `HTGeometry/FiniteHarmonicRows`: unchecked `/tmp/FiniteHarmonicRows.lean`.
- `SpacingScaleHarmonicAnalysis/TheArchimedeanDensityHasQuadraticIncrementControl`: unchecked `/tmp/TheArchimedeanDensityHasQuadraticIncrementControl.lean`.
- `HTGeometry/FiniteWeightedGroundStateBound`: unchecked `/tmp/FiniteWeightedGroundStateBound.lean`.
- `RenormalizedArithmeticPotentialTheory/TheSeparatedAtomPairingsAreThePrimeKernel`: unchecked `/tmp/TheSeparatedAtomPairingsAreThePrimeKernel.lean`.
- `RenormalizedArithmeticPotentialTheory/TheSeparatedMarkovMatrixHasExactCrossEntries`: unchecked `/tmp/TheSeparatedMarkovMatrixHasExactCrossEntries.lean`.
- `RenormalizedArithmeticPotentialTheory/TheFullWeilMatrixSplitsAtTheSpacing`: unchecked `/tmp/TheFullWeilMatrixSplitsAtTheSpacing.lean`.
- `RenormalizedArithmeticPotentialTheory/TheArchimedeanCenterRowCancelsThePole`: unchecked `/tmp/TheArchimedeanCenterRowCancelsThePole.lean`.
- `HTGeometry/HarmonicCenterBoundaryBounds`: unchecked `/tmp/HarmonicCenterBoundaryBounds.lean`.
- `HTGeometry/IntegerLogarithmicWindowGap`: unchecked `/tmp/IntegerLogarithmicWindowGap.lean`.
- `HTGeometry/FiniteInverseSquareDistanceRows`: unchecked `/tmp/FiniteInverseSquareDistanceRows.lean`.
- `HTGeometry/FinitePoleWeightedDistanceRows`: unchecked `/tmp/FinitePoleWeightedDistanceRows.lean`.
- `RenormalizedArithmeticPotentialTheory/TheAtomCrossMatrixIsCloseToItsCenterKernel`: unchecked `/tmp/TheAtomCrossMatrixIsCloseToItsCenterKernel.lean`.
- `HTGeometry/FiniteKernelErrorFromDistanceRows`: unchecked `/tmp/FiniteKernelErrorFromDistanceRows.lean`.
- `RenormalizedArithmeticPotentialTheory/TheAtomCrossReplacementHasUniformErrors`: unchecked `/tmp/TheAtomCrossReplacementHasUniformErrors.lean`.

The last two assemblies give the exact uniform quadratic-form cost and bounded unnormalized pole-profile residual for the actual cross-integral replacement. The complete center action on mean-zero periodic profiles, pole-moment error, full-range coercivity, and spectral assembly remain to formalize.

Two further unchecked drafts complete the current twenty-module support inventory: `TheCenterCollarIsPaidByTheTopAtoms` and `TheCompleteWeilTrialEnergiesAreSimpleAndProper`. The former keeps the diagonal `n(H_N+1)` through weighted Schur and reduces it to the top-atom potential plus three masses. The latter reuses ALG `sq_integral_abs_le` and SMAP `ramanujanAdjunctionEnergy_sub_one_ge`; both exact source statements were inspected. The elementary lower bound `1<=2*log(2)` suffices, since the profile charge shift is strictly below one. Needed foreign dependency oleans exist; their axioms will be audited transitively through the new endpoints. None of these twenty drafts is installed or checked.
