# Route PM: complete-band spectral escape

- **ID:** pm-ramanujan-band-spectral-escape
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / proof attempt
- **Source:** actual complete denominator band, joint residue, critical zeta zeros, raw Mobius moving-window obstruction.
- **Goal relevance:** identify and control the residual moving energy after the proved complementary cancellation. Global small-damping admission remains the final hard producer.

## Question and scope

For S_X(N)=sum_(X<q<=2X) a_epsilon(q) P_q(N), fixed-N profile convergence does not decide whether X^epsilon S_X converges in the original anchored Hilbert norm. Test the conjecture that a nonzero component of this normalized energy escapes to N comparable with X. No selected prime or cofactor lower bound will suffice: every term of S_X must remain.

The sufficient RH producer only needs a positive damping margin, for example energy of S_X minus its fixed-coordinate profile bounded by C_epsilon X^(-epsilon). Strong convergence of the normalized remainder is not required. Neither a spectral escape theorem nor that upper bound is currently proved here.

## Exact two-variable mechanism to establish

Write alpha=1/zeta(1+epsilon), J_s(q)=sum_(d|q) mu(q/d)d^(1-s). For q>1 the finite fractional-part identity should give

    integral_0^infinity P_q(floor(1/t)) t^(s-1) dt
      = zeta(s) J_s(q)/s,       0<Re(s)<1.

Keep X continuous and its literal natural band (floor X, floor(2X)]. Define the moving vector B_X(x)=X^(epsilon-1/2) S_X(floor(X*x)). Its squared L2(dx/x^2) norm is X^(2epsilon) times the original band energy. Put z=w+1/2 and r=epsilon+s-z. In the initial absolute domain Re(z)>1, 0<Re(s)<1, its two-variable Mellin expression is predicted to be

    alpha * zeta(s)/s * (1-2^(-r))/r
      * [zeta(1+z-s)/zeta(z) * H_epsilon(z,s) - 1].

The subtraction of 1 retains exclusion of q=1. The apparent r=0 singularity is removable. This expression still needs all Fubini, floor and convergence justifications.

The local factor is exact algebra. For prime p let

    a=p^(-1-epsilon), b=p^(s-z-1), c=p^(-z).
    H_p = (1-a+b-c)(1-b)/[(1-a)(1-c)]
        = 1 + (b-a)(c-b)/[(1-a)(1-c)].

Near Re(z)=Re(s)=1/2 the correction is O(p^(-3/2)) (with a positive epsilon-dependent margin). This suggests a normally convergent analytic Euler factor. At s=z=rho on the critical line, b=1/p and |c|=1/sqrt(p), while 1-a+b>1; hence no local numerator vanishes. The product/nonvanishing and analytic statements are not yet formalized.

The z=s pole from zeta(1+z-s) represents the stationary fixed-coordinate profile. After removing that pole, zeros of zeta(z) may retain a moving spectral contribution. At a critical zero rho, zeta(s)zeta(1+rho-s)H_epsilon(rho,s) is not identically zero as a function of s near rho: the zero and pole at s=rho reduce its vanishing order by one, rather than killing the whole germ. This is a proposed analytic route to a full-band escape profile, not yet a proof of a norm floor.

## Hard obligations

1. Establish the literal primitive/band Mellin identity, then the actual two-variable Euler quotient with its product boundary.
2. Justify the Hilbert or compact-test continuation through the stationary pole; scalar formal Euler algebra alone is insufficient.
3. Prove a nonzero moving-profile contribution using the existing critical-zero machinery, retaining all complementary terms.
4. Return to the upper-bound producer with the escaped component included. An obstruction to strong normalized convergence does not obstruct the weaker sufficient energy bound and does not prove or refute RH.

## Research log

2026-10-02: Previous complementary cancellation is audited progress. Search129 complete, inventory current at1188207, semantic coverage unmeasured; all returned candidates/source statements and ingredients inspected. It returned exact signed decompositions but no clock upper bound. Search130 complete with mixed freshness (coverage1188213/current1188214); its generated positivity ingredients are unrelated to the physical source and unusable. Direct corpus inspection supplies finite Nyman Mellin transforms and the existing critical Mertens log-tent mechanism. Search131 checks prior band/moving-shell work before new Lean code. No new mathematical bound is claimed.
