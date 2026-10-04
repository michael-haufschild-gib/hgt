# Route PM: continuation of the complete compactly tested band identity

- **ID:** pm-ramanujan-band-tested-continuation
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.

## Exact statement

Fix epsilon>0. Inside the proposed contradiction that the actual normalized complete-band Mellin vectors converge strongly to a fixed vector, let h be any L2 test supported almost everywhere on [a,b], with a>0. The actual zeta-cleared tested scale identity continues from Re(z)>1 to

    Re(z)>1/2, 0<Im(z)<a.

Its arithmetic side is the integral of conjugate(h(tau)) against the complete kernel

    K(z,tau)=alpha*zeta(s)/s * (1-2^(-r))/r
      * (zeta(1+z-s)*H_epsilon(z,s)-zeta(z)),
    s=1/2+i*tau, r=epsilon+s-z.

The compactly tested arithmetic kernel is holomorphic on the larger tube

    Re(z)>3/8, 0<Im(z)<a.

At an actual critical zero rho in that tube, K(rho,tau) is exactly the already formalized complete residue numerator. No zero-simplicity assumption is needed.

## Dependency-closed paper proof

For tau in [a,b] and z in the larger tube, tau>Im(z). Hence r is nonzero, and 1+z-s is not1. The critical point s is neither0 nor1. Also z is not1 because its imaginary part is positive. These facts avoid every explicit denominator and zeta pole. The existing Euler correction is jointly continuous on Re(z)>3/8, Re(s)<9/16 and holomorphic in z there; Re(s)=1/2 satisfies its condition. The displayed complete kernel is therefore jointly continuous and holomorphic in z.

At any parameter point in the tube, choose a closed ball contained in it. The product of that ball with [a,b] is compact. Joint continuity bounds the entire kernel there by a finite constant M. L2 admission makes h locally L1, hence integrable on [a,b]. The product M*|h|*indicator([a,b]) is an actual integrable majorant. The corpus Cauchy-dominated integral theorem proves holomorphy of the compactly tested kernel. No separate derivative estimate is postulated.

The tested-source leaf derives all measurability, integrability and the global source bound from the proposed strong convergence. Its reciprocal Mellin theorem makes the actual tested scale transform holomorphic on Re(z)>1/2. Multiplication by zeta preserves holomorphy on the smaller tube because Im(z)>0. There, support separation also discharges r!=0 wherever h is nonzero. The existing initial cleared identity thus identifies both sides on Re(z)>1 inside the tube.

The smaller tube is convex, hence connected. Both sides are analytic on a neighborhood of every point in it, and they agree near 2+i*a/2. Analytic uniqueness extends the equality throughout the tube. Substituting a zero in the complete kernel removes the exact subtracted zeta(z) term and gives the previously defined residue numerator, retaining all remaining factors.

## Scope and verification

2026-10-03 extension: `pmRamanujanBandTestedScale_cleared_continuation_of_bound` exposes the same complete identity directly from a bound on the actual moving source. The convergence theorem retains its signature and derives that bound. The new compact-profile contradiction can therefore supply it from total boundedness without assuming convergence. Nine exports total. Targeted old-mode leaf build passed (167 seconds); mandatory final actual-file Lean passed with no diagnostics. The new theorem and changed wrapper passed separate scratch axiom queries with only propext, Classical.choice and Quot.sound. This extension supplies no unconditional arithmetic upper bound. Profile Abel zero and fixed-profile escape are now audited in their own leaves.

This is the actual source identity needed for the proposed spectral-escape contradiction, conditional only on that contradiction's strong-convergence statement and the explicit compact test support. It does not prove convergence, spectral escape, a small-damping complete-energy ceiling or RH. The norm-null profile Abel remainder and final contradiction still need formalization. The complete scratch passed foreground Lean with exit0 and no diagnostics after explicit map typing repaired the joint-continuity composition. The eight-export leaf `PMRamanujanBandTestedContinuation.lean` is promoted and wired once. Targeted old-mode leaf build passed (185 seconds). Mandatory final actual-file `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandTestedContinuation.lean` passed with no diagnostics. All eight exports passed separate /tmp axiom queries, with only propext, Classical.choice and Quot.sound. Lint reports twelve unrelated unreachable modules, none own. No umbrella build or heartbeat change.
