# Route PM: literal cutoff Mellin identity

- **ID:** pm-ramanujan-band-cutoff-mellin
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Continuation:** `../1-in-progress/pm-ramanujan-band-spectral-escape.md`.
- **Statement:** The complete moving denominator band has an absolutely integrable cutoff transform equal to its actual Euler series with the exact q=1 subtraction.

## Exact statement

Let epsilon>0, Re(z)>1, Re(s)<9/16, r=epsilon+s-z nonzero, alpha=1/zeta(1+epsilon), and let a(q), J_s(q), H_epsilon(z,s) be the audited actual weight, primitive Mellin symbol and Euler correction. Put

    T_epsilon,s(X) = sum_(floor(X)<q<=floor(2X)) a(q)*J_s(q).

Then X -> T_epsilon,s(X)*X^(r-1) is integrable on [1,infinity), and

    zeta(z) * integral_(X>=1) T_epsilon,s(X)*X^(r-1) dX
      = alpha * (1-2^(-r))/r
          * [zeta(1+z-s)*H_epsilon(z,s) - zeta(z)].

The integrability statement holds under the weaker condition Re(s)<1 and also when r=0. No zero-free or RH hypothesis is used.

## Dependency-closed paper proof — [PROVED HERE]

For X>=1, membership floor(X)<q<=floor(2X) is equivalent to q/2<=X<q. Every such q is at least two. Conversely each q>=2 contributes precisely on [q/2,q), a subset of [1,infinity).

Set F_q(X)=a(q)*J_s(q)*X^(r-1) on this interval and zero elsewhere; also set F_0=F_1=0. Every F_q is integrable since its support is compact and separated from zero. Substitution X=q*u gives exactly

    integral |F_q(X)| dX
      = C(r) * |a(q)*J_s(q)*q^r|,
    C(r)=integral_(1/2<=u<1) |u^(r-1)| du.

The complete arithmetic majorant in `PMRamanujanBandEulerSeries` proves summability of the right side for Re(z)>1 and Re(s)<1. The integral of the sum of extended nonnegative norms is finite by Tonelli; the norm of the pointwise complex sum is bounded by that sum. Measurability follows from measurability of countable sums. Thus the actual sum is integrable, and integral and denominator sum commute.

For r nonzero, direct integration gives

    integral_(q/2<=X<q) X^(r-1) dX = q^r*(1-2^(-r))/r.

The q=0 term of the full arithmetic series is zero and its q=1 term is alpha. Hence the cutoff integral is (1-2^(-r))/r times the full arithmetic series minus alpha. Multiplying by zeta(z) and applying the audited cleared Euler-series identity proves the statement. All endpoints, signs, cofactors and the q=1 correction remain literal.

## Contribution and remaining hard problem

This identifies the actual cutoff transform and proves its integrability; it is not merely a formal Euler rearrangement or an equality of totalized integrals. It closes the cutoff/Fubini input of the proposed complete-band spectral escape argument. A bounded Hilbert frequency test and its analytic continuation still require proof. No complete small-damping signed-energy ceiling is obtained here, and RH remains unproved and unfalsified.

## Audit — 2026-10-02

- Complete scratch proof: exit 0, no diagnostics.
- `lake --old build GaloisForLFunctions.RHTower.PMRamanujanBandCutoffMellin`: exit 0; only the new leaf built (192 seconds).
- Final actual-file `lake env lean GaloisForLFunctions/RHTower/PMRamanujanBandCutoffMellin.lean`: exit 0, no diagnostics.
- All sixteen public declarations passed `/tmp` axiom queries; only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella wired once; no umbrella build. Global lint reports twelve unrelated unreachable modules, no finding for this leaf.
- No added axiom, sorry, RH premise, numerical experiment, heartbeat increase or subagent.

Search134 supplied generic interchange methods, with partial text/source retrieval; all twenty candidate statements, twenty source arguments and generated ingredient obligations were inspected. Applicability was verified by the complete Lean proof.
