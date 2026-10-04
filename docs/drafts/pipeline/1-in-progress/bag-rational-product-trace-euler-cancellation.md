# BAG complete rational-product trace and Euler cancellation

- **ID:** BAG-C28.56x
- **Stage:** 1-in-progress
- **Target:** evaluate the complete signed rational-product resonance exposed by
  C28.56w, then control its finite-height neighborhood with the original V/W
  profile. This is work on the full BAG cubic; RH is not proved.
- **Status:** the full balanced positive-rational sum, absolute mass and
  fixed-dilation orthogonality are formalized in C28.56ab, P3
  `bag-complete-rational-cubic-orthogonality.md`. C28.56y/aa close the weighted
  arithmetic trace and its compact-test critical boundary. C28.56ac proves
  frequency-weighted rational/tested identification and termwise integration.
  Global Schwartz/growing-profile control and physical transfer remain open. Earlier
  conjecture calculations below are retained as the research history.

## Corpus basis

PMPowerDampedMobiusRamanujanExpansion proves the absolutely convergent GROUPED
Ramanujan expansion of pmPowerDampedDivisorCoeff. The Weights source identifies
its coefficient as density times mu(q)/prod_(p|q)(p^(1+epsilon)-1), and DivisorHaar
identifies the arithmetic coefficient as prod_(p|n)(1-p^(-epsilon)).
The finite divisor formula for c_q and the exact physical cubic are already
sources. No Weyl bound, prime Poisson formula, RH or Weil positivity is assumed.

## Complete signed resonance: new paper calculation

Put sigma=1+epsilon>1 and let m_sigma(a), for positive rational a, be mu(den a)
divided by prod_(p|den a)(p^sigma-1). For each prime let z=p^(-sigma),
b=(1-z)/z, and c(i)=1 for i>=0, c(-1)=-1/b, c(i)=0 for i<-1.
The full rational resonance c=a*b has local weight

    c(i)c(j)c(i+j) x^i y^j,   x=p^(-s), y=p^(-t).

Its COMPLETE local sum is

    E=1/((1-x)(1-y)) + (1/x+1/y)/b^2
        - (y/(x*(1-y))+x/(y*(1-x)))/b.

No individual signed sector has been omitted. In its absolute-convergence
region the positive quadrant is geometric; only the two strips i=-1 or j=-1
remain, with their actual negative signs and the prohibited (-1,-1) corner.

The exact algebraic decomposition is

    E=(1-z)^(-2) *
      [1+(x-z)(y-z)*(x+y-x*y)/(x*y*(1-x)*(1-y))].

In particular E=(1-z)^(-2) whenever x=z OR y=z, not only when both do.
More strongly, summing over i with x=z annihilates every nonzero fixed j:

    sum_i c(i)c(i+j) z^i = 0              (j!=0),
    sum_i c(i)^2 z^i = (1-z)^(-2)        (j=0).

For j>0 the single i=-1 term cancels the entire i>=0 geometric tail;
negative j follows by translating the same absolutely convergent sum.
The corresponding normalized sequence g(-1)=-sqrt(z),
g(i)=(1-z)*z^(i/2) for i>=0 has orthonormal integer translates.
This is the arithmetic source of the cancellation, not an assumed random law.

At s=t=sigma the sum of ABSOLUTE local weights is

    (1+4*z)/(1-z)^2,

whereas the signed local sum is (1-z)^(-2). Thus both complete global sums
converge for sigma>1. The proposed global signed resonance identity is

    sum_(a,b positive rationals)
      m_sigma(a)m_sigma(b)m_sigma(a*b) a^(-sigma)b^(-sigma)
      = zeta(sigma)^2.

The absolute sum is zeta(sigma)^2*prod_p(1+4*p^(-sigma)). Finite prime
factorization plus absolutely convergent Euler products should prove both
statements and the global rational-dilation orthogonality. The production
leaf now proves the complete directed finite-prime trace limit: every prime
set retains all countably many integer valuation pairs, the signed and
absolute limits are evaluated, and a literal two-axis mask is evaluated as
1-zeta(sigma)^2. Reindexing this as one unordered positive-rational double
tsum and the stronger fixed-dilation orthogonality are not yet Lean theorems.

## Hard continuation and limits

For general complex s,t the local factor has first-order terms corresponding
to four zeta factors zeta(s), zeta(t), zeta(2sigma-s), zeta(2sigma-t), divided
by zeta(sigma+t-s)zeta(sigma+s-t), times a locally uniformly convergent Euler
remainder. This factorization and any distributional limiting statement still
require proofs. The expected singular contributions concern the contraction
rays; they must be evaluated with the actual smooth physical profile.

The original finite-height integral also resolves NEAR resonances c-a*b of
size1/N. Exact-resonance orthogonality does not control them. Moreover the
source proves absolute convergence only after each Ramanujan residue sum is
grouped; expanding every residue into a separate frequency is not an automatic
absolutely convergent Fubini interchange at small damping. Retain grouped
finite cutoffs until their full signed limit is justified. The coupled
N->infinity/epsilon->0 source approximation, every contraction subtraction,
moving V/W amplitudes, and near-resonant remainder remain explicit obligations.
Do not call the arithmetic identity a proof of full cubic cancellation or RH.

## Contraction subtraction and the weighted boundary (paper, in progress)

Global orthogonality, if established with the absolute convergence above, gives
the exact Mellin-balanced connected trace 1-zeta(sigma)^2: subtract the a=1
and b=1 rays and restore their intersection. It does NOT give zero.

For sigma=1+epsilon and s=sigma+i*u, t=sigma+i*v, write the complete
two-variable Mellin trace as

    Z_sigma(u,v) = |zeta(sigma+i*u)|^2 |zeta(sigma+i*v)|^2
                    / |zeta(sigma+i*(u-v))|^2 * H_sigma(u,v).

The local remainder defining H is E times the four numerator inverse factors
divided by the two denominator inverse factors. After cancellation of all
first-order prime terms its difference from 1 and each fixed u,v derivative
are O_k((log p)^k/p^(2*sigma)), uniformly for real u,v and sigma>=1.
This is an algebraic estimate to be proved, not an appeal to a conjectural
prime estimate. The exact identities H_sigma(u,0)=H_sigma(0,v)=1 follow
from the local factorization already displayed.

The single contraction has transform

    D_sigma(u)=|zeta(sigma+i*u)|^2 K_sigma(u),
    K_sigma(u)=prod_p [1-z^2*(1-exp(i*u*log p))^2/(1-z)^2],
    z=p^(-sigma).

This expression comes from the COMPLETE local square coefficient sum
1/(1-y)+z^2/(y*(1-z)^2), y=z*exp(-i*u*log p). In particular K_sigma(0)=1
and K_sigma'(0)=0. Both are important: losing the second identity would
lose a principal-value contribution.

Set J_sigma(u)=(epsilon^2+u^2)|zeta(sigma+i*u)|^2 and

    a_sigma=J_sigma(0),
    A_sigma(u,v)=J_sigma(u)J_sigma(v)H_sigma(u,v)/J_sigma(u-v),
    B_sigma(u,v)=(A_sigma(u,v)-a_sigma)/(u*v),
    M_sigma(u)=(J_sigma(u)K_sigma(u)-a_sigma)/u^2.

At the axes the quotients mean their smooth extensions, whose existence follows
from the two exact axis identities and the zero first derivative above. Local
smoothness and convergence as epsilon decreases to zero require the ordinary
pole removal and nonvanishing of zeta on Re(s)=1 away from s=1. No RH is used.
These inputs must be checked against the corpus before claiming a closed proof.

An EXACT decomposition of Z_sigma-D_sigma(u)-D_sigma(v)+1 follows by using

    (epsilon^2+(u-v)^2)/((epsilon^2+u^2)(epsilon^2+v^2))
      = 1/(epsilon^2+u^2) + 1/(epsilon^2+v^2)
        - epsilon^2/((epsilon^2+u^2)(epsilon^2+v^2))
        - 2*u*v/((epsilon^2+u^2)(epsilon^2+v^2)).

Consequently the candidate limit in distributions, initially with compactly
supported frequency tests, is

    -pi^2 delta_(0,0) - 2 PV(1/u) tensor PV(1/v)
      + v*B_1(u,v)*PV(1/u) + u*B_1(u,v)*PV(1/v)
      - 2*B_1(u,v) - M_1(u) - M_1(v) + 1.

Here a_sigma -> 1. The epsilon^2*u*v term tends to zero; the
epsilon^2/((epsilon^2+u^2)(epsilon^2+v^2)) term gives the point mass and
must NOT be dropped. The other two-variable term gives the product principal
value. This is a proposed proof mechanism with explicit obligations, not yet
a formalized distributional theorem. Extending from compact frequency tests
to Fourier transforms of the actual compactly supported V/W profile needs
uniform growth bounds. Even a completed weighted exact-resonance theorem does
not bound the finite-height near-resonances or justify the coupled damping
limit of the original prime cubic.

The notation J_1 at u=0 means the smooth pole-removed limit with value 1,
NOT u^2 times mathlib's assigned value of riemannZeta at s=1. The checked
source inputs are `riemannZeta_residue_one`,
`GaloisForLFunctions.HTGeometry.analyticAt_riemannZeta`, the meromorphic
proof in that module, and mathlib's `riemannZeta_ne_zero_of_one_le_re`
in LSeries/Nonvanishing. The compact-frequency boundary argument therefore
needs no assumption about zeros inside the critical strip.

Further transfer audit: the arithmetic FREQUENCY axes a=1 and b=1 are not
yet identified with the literal discrete prime diagonals p=r and q=r. The
stationary equations suggest that identification, but their neighborhoods
and damping-dependent multiplicities also contribute. For example the
weighted square-coefficient trace has a 1/epsilon distributional pole,
whereas the physical diagonal has its own log(N) scale. Matching those
scales belongs to the unresolved coupled-limit argument. Do not replace
the physical diagonal by these arithmetic axes without proving that match.
