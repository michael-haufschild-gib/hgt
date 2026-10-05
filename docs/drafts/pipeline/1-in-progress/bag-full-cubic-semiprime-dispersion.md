# BAG full cubic through semiprime dispersion

- **ID:** BAG-C28.56w
- **Stage:** 1-in-progress
- **Target:** complete source-weighted noncontracting Gaussian cubic is
  o(N/log(N)^2), preserving the RH/BAG goal.
- **Status:** paper attack; no new cancellation theorem claimed.

## Source basis

ChiPrimeGaussianCubicMain defines the full entry

  2pi V(p/N)V(q/N)conj(V(r/N))/r W(pq/(rN)) exp(2pi i pq/r).

All three variables range over the full actual prime band (N,2N]. The two
contraction families p=r and q=r are removed with their overlap retained once.
The complete physical error is already o(N/log(N)^2).
ChiPrimeGaussianCubicPrimeOnlyVaughan retains these exact weights/masks in one
joint row. Fixed rational and near-integer complete-row estimates in the
corpus do not control the bulk by summing norms. C28.56v now refutes generic
promotion of all-real quadratic mixing to cubic control even on actual primes.

## New attack, keeping all three variables

Group p,q by the actual product n=pq, with its complete V-weighted multiplicity.
Then n lies in(N^2,4N^2], r~N is at the square-root scale of n, and the physical
window is W(n/(rN)). The signed phase is exp(2pi i n/r), not an arbitrary test
on a single prime. The contraction exclusions are exactly the source factors
r|n, since p,q,r are prime. Any dispersion argument must remove those factors
exactly rather than treating them as a generic diagonal or dropping them.

Candidate: prove joint cancellation for the balanced prime-product sequence
against this reciprocal-modulus family, with the source moving W/V weights.
The principal density contribution suggests the smaller N/log(N)^3 scale, but
this is a conjectural guide, not a proved asymptotic. Search and audit the
corpus's convolution-distribution and product moment estimates for the exact
square-root-modulus regime and the signed additive test.

## Failed first estimates and what they teach

1. Pointwise full Fourier norm plus absolute sum over r loses the signed
   interaction of moduli; the corpus's complete-row obstructions already
   prevent using it as the final estimate.
2. Direct large sieve for reciprocal frequencies1/r at product lengthN^2 has
   spacing~N^-2. With prime-product coefficient square mass~N^2/log(N)^2,
   its raw L2 cost followed by Cauchy in r is of orderN^(3/2) after the1/r
   factor. It cannot reach N/log(N)^2. This is only a paper cost audit;
   no estimate is silently inserted as a premise.
3. Merely bounded/local-density coefficients are not yet a producer. The exact
   prime convolution and full signed reciprocal family must remain in the proof.

This card is NOT a new receiver or a retirement of BAG. Continue the joint
arithmetic problem; do not formalize only this regrouping identity as progress.


## C28.56w continued: what was learned, without claiming closure

The main BAG log already proposed this semiprime organization at C28.41.
Rediscovering it is not new progress. Source inspection of the later Watt
product/numerator-range theorems confirms that they retain the literal
product-length comparison; their two unit-coefficient factors also do not
match the three prime-weighted factors here. They have not closed this gap.
No general Watt theorem is inferred from the restricted-range names.

A second paper test kept the complete trilinear phase and introduced additive
modes a,b,c. For r>0 its exact simultaneous factorization is

    pq/r-a*p-b*q+c*r = (p-b*r)*(q-a*r)/r+(c-a*b)*r.

Consequently an interior stationary ray has q=a*r, p=b*r, c=a*b. The two
transverse curvatures have opposite signs. The original weights on that ray
are V(b*r/N)*V(a*r/N)*conj(V(r/N))*W(a*b*r/N)/r;
they cannot be replaced by an unweighted count of rational modes. The actual
band intersection and both sharp endpoints also remain. This identity is
paper geometry, not a prime Poisson formula or an estimate of the mode sum.

The tempting claim that the rational stationary coefficients all have the
same sign is false already at the reduced-residue arithmetic level. The
source primeGaussianRationalProfileMean is the signed reduced-residue mean;
KloostermanRamanujanDivisorSum supplies its finite divisor formula. Write
m(x)=c_D(A)/phi(D) for x=A/D, allowing an unreduced fraction. For distinct
prime Q,R, Q not dividing A, R not dividing B, the paper coefficient identity is

    m(A/Q)*m(B/R)*m(A*B/(Q*R))
      = c_Q(B)*c_R(A)/((Q-1)^2*(R-1)^2),

where c_l(n)=l-1 if l divides n and -1 otherwise. This follows by CRT for
c_(QR), followed by the two prime divisibility tests; numerator cancellations
in the product fraction are essential. For example a=6/5, b=5/7, c=6/7
has coefficient -1/144. Its stationary ray meets the actual band and W
plateau at r/N=3/2: p/N=15/14, q/N=9/5, pq/(r*N)=9/7.
By contrast a=6/5, b=8/7, c=48/35 gives coefficient +1/576 and meets the
same physical support, e.g. r/N=21/20. No assertion is made that these isolated
mode coefficients are asymptotic contributions of the full prime source.
These are symbolic paper deductions, not numerical experiments or Lean audits.

A complete-residue averaging shortcut also fails to transfer automatically:
for one prime l, the constraint l|A*B with the third coefficient evaluated at
A*B/l has period l^2 in the numerators. The physical slope box has width of
order l, so averaging a full l^2 cell would enlarge the source. The useful
surviving object is the SIGNED, amplitude-weighted rational product trace on
the original slope box, including numerator cancellations and boundary terms.
No standalone identity leaf is being counted as frontier advancement.

The reciprocal-variable B-process is a further proof candidate, not a proved
transfer. In a literal Vaughan Type-I denominator r=d*m, Poisson phase
pq/(d*m)+h*m has saddle m=sqrt(pq/(d*h)), dual phase2sqrt(pq*h/d),
and h of order d. It would leave a bilinear square-root phase on the original
prime numerator sequences. Replacing the prime denominator directly by its
continuous density would omit the same contraction-sized arithmetic response
identified by C28.56l. A valid construction must retain the signed Vaughan
coefficients, Type-II branch, m-dependent weights, exact masks, endpoint
terms, and all dual h. Neither the full Poisson/Vaughan transfer nor the needed
prime-restricted square-root-phase estimate is presently proved here.

Evaluation: no hard cancellation estimate was closed in C28.56w and no new
Lean production declaration was added. The rational sign correction changes
the next attempted producer: attack the coupled signed product trace, or its
fully justified reciprocal B-process, rather than assuming positivity,
summing row norms, or adding another regrouping wrapper. The full cubic,
growing moments, moving cofactors, positive self-target recurrence and RH
remain open. BAG is not retired.

## 2026-10-05 continuation01a4 — finite-height correction must remain signed

The target remains the literal C28.44 full prime cubic, with its original
V/W amplitudes, both contraction families and their overlap. No hard cubic
estimate was closed in this continuation. The following checks do not count
as a new frontier theorem.

The proposed joint Vaughan attack must combine its actual signed terms before
estimating them. Its prime-only identity is already exact; recombining the
coefficient alone merely recovers the original prime indicator. Likewise,
using the semiprime organization with an ordinary reciprocal-frequency large
sieve repeats the already recorded conductor loss. The available medium
Mobius factor theorem concerns logarithmic phases and includes its actual
contour/frequency restrictions. It does not remove the Mellin-transform cost
or bound the coupled q,r carrier by substitution. These are applicability
failures of these proposed estimates, not obstructions to all Vaughan proofs.

The simultaneous additive-mode identity recorded above leaves the phase
`(p-b*r)*(q-a*r)/r+(c-a*b)*r`. The already audited complete rational trace
evaluates c=a*b. A finite physical height also resolves c-a*b at scale 1/N.
The grouped Ramanujan expansion is absolutely convergent at each fixed
positive damping and fixed integer; its separate reduced-residue expansion
has not thereby acquired an absolutely summable three-frequency majorant.
The original incomplete determinant aggregate remains to be estimated.

A new calibration check follows directly from the completed uniform square
law and the existing small-damping second-density theorem. Write

    M = integral bagPhysicalHeightWindow,
    A(e,X) = (1/X) sum_n D_e(n)^2 W(n/X),
    H(e) = pmPowerDampedSecondDensity e,
    L = log X.

For each C>0, uniformly over 0<e<=C/L, these two audited source theorems imply
the following PAPER consequence:

    (A(e,X)-H(e)*M)/e + exp(-2*e*L)*M/2 -> 0.

Proof: write the square-law error as
`R(e,X)=A(e,X)/(e^2*L)-Psi(e*L)*M`. The displayed expression is exactly

    (e*L)*R(e,X) + (1/2-H(e)/e)*M.

The first term tends uniformly to zero because 0<e*L<=C; the second does
because H(e)/e tends to 1/2 and the entire damping interval shrinks to zero.
No lower bound on e*L is used. In particular the normalized defect tends to
-M/2 when e*L->0, rather than zero. This is a constraint on an attempted
finite-height replacement by its fixed-damping Haar mean. It is NOT yet an
identification or estimate of a selected near-resonant frequency subfamily,
and is NOT a full cubic theorem. No new Lean declaration is claimed for this
paper consequence.

Consequently the next cubic conjecture must retain the complete finite-height
correction together with the actual contractions. An argument that evaluates
the exact rational trace and discards the remaining signed correction
uniformly in this damping range is not justified by the known square law.
The concrete hard obligation remains cancellation of the complete physical
noncontracting cubic after all source terms are restored, or a proved
three-frequency finite-height transfer yielding that same estimate. A scalar
residue identity or a new conditional receiver would leave that obligation
unchanged.
