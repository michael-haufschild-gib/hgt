# Prime-square sign wall for the continued Euler Gram

- **ID:** stc-prime-square-positivity-wall
- **Stage:** 2-fully-proven (paper)
- **Routes:** STC, RHist
- **Status:** [PROVED ON PAPER] [LEAN FORMALIZATION PENDING] [NOT AN RH PROOF]
- **Novelty:** Exact sign consequence for the continued depth-zero log-square source; literature novelty unverified.

## Conjecture tested and result

A natural attempt to transport the positive Euler prime Gram toward the critical strip is to analytically continue its scalar kernel while retaining positive definiteness. The attempt fails for a universal arithmetic reason before an Xi zero is encountered.

Let F(s) be the analytic continuation of the literal prime log-square series

    sum_p (log p)² p^(-s),     Re s>1,

obtained as minus the derivative of the continued prime-log current Q(s). On the real axis as s decreases to 1/2,

    F(s) = -2/(2s-1)² + O(1).                                (1)

In particular, F(s)<0 for all real s>1/2 sufficiently close to 1/2. Hence the analytically continued kernel

    K(w,z)=F(w+conj(z)-1)

cannot be positive semidefinite on the whole half-plane Re w>3/4: choosing real w close to 3/4 gives K(w,w)=F(2w-1)<0. It also cannot be the Gram kernel of ordinary Hilbert vectors on that entire domain. This is a precise no-go for **positivity-preserving analytic continuation of the unchanged prime-only Gram**, not for a renormalized or Xi-coupled transport.

## Proof and exact surviving structure

The existing corpus has the prime-log current Q, its meromorphic continuation, and the valuation decomposition on Re s>1/2:

    Q(s) = A(s) - Q(2s) - H_≥3(s),                           (2)

where A(s)=-ζ'(s)/ζ(s) and H_≥3 is holomorphic across a neighbourhood of s=1/2. The decomposition is in XiPrimeLogHigherValuationCriticalBoundary.lean. Zeta has no real zero in (0,1), so A is holomorphic at 1/2. At its pole s=1, ζ(s)=h(s)/(s-1), with h holomorphic and h(1)=1. The prime-log current is therefore

    Q(s)=1/(s-1)+holomorphic near s=1,

because its higher-valuation correction is holomorphic there. Substitute 2s for s in (2):

    Q(s)=-1/(2s-1)+holomorphic near s=1/2.

Differentiate and use F=-Q' on Re s>1, then by analytic continuation wherever both sides are regular:

    F(s)=-2/(2s-1)²+holomorphic near s=1/2.

This proves (1). The coefficient -2 is the positive **survivor** of the failed positivity conjecture: it is the exact universal prime-square boundary charge. It comes from valuation two; all valuation-three-and-higher rows and the regular zeta factor contribute only a holomorphic remainder. In the Gram variable w the wall is Re w=3/4.

The negative diagonal does not depend on RH and does not detect an off-line zero. A viable continuation must subtract or otherwise account for this prime-square charge; doing so changes the original positive Euler Gram and requires a separate proof of what positivity or zero-specific information survives. The source-to-Xi-divisor transport remains the hard gate.

## Lean gate

The new STCPrimeHeightFiberAbel.lean checks F=-Q' in the Euler half-plane. Existing XiPrimeLogHigherValuationCriticalBoundary.lean checks the valuation-two/three-plus split, and the real prime pole is checked in PrimeTraceCriticalEnergyBudget.lean and PrimeLogPowZetaAbelPole.lean. The Laurent expansion and negative diagonal conclusion are paper-proved here but not yet assembled in Lean.
