# Ramanujan spectral law for the complete Weil form at the spacing

- **ID:** complete-weil-spacing-ramanujan-spectral-law
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** full-prime Ramanujan quasimodes; bounded-defect finite-span approximation; exact archimedean atom pairing; actual two-pole rows
- **Statement:** The complete normalized Weil matrix has Ramanujan quasimodes at every fixed separated width ratio, and its bounded spectrum is exhausted by their explicit simple energies at a sufficiently small fixed ratio.
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
and 0<c<1/2. Let w=c/N and g=atomDilate(phi,w). The proposed matrix is

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

First target: every fixed normalized Ramanujan vector has residual norm tending
to zero at lambda_m for W_N, for every 0<c<1/2. Second target: for an explicit
positive profile-independent c_star and 0<c<c_star, every threshold away from
these energies has eventual exact spectral count, with multiplicity, equal to
the finite arithmetic count; each fixed eigenline is eventually simple and
captures its Ramanujan vector. Neither target is proved yet.

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

## Exhaustion route at a fixed small ratio

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
