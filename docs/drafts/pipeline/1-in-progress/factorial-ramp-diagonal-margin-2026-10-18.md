# Actual factorial ramp diagonal margin

- **Stage:** 1-in-progress
- **Route:** RW, with the WL factorial stencil retained exactly.
- **Objective:** Prove the actual optimized ramp energy nonnegative; a sufficient stronger target is eventually `factorialWeilGramError n <= factorialSpanWeil n 1 0`. Ultimate objective remains unconditional RH in Lean.
- **Predecessor:** `../3-formalized/factorial-weil-gram-decoupling-2026-10-18.md`.

## Plan

1. Audit current corpus for actual ramp diagonal, null-kernel truncation, and finite Mellin identities.
2. Derive the concrete ramp's transform or an equivalent physical-space cancellation with every pole/boundary term retained.
3. Conjecture and prove a diagonal lower bound strong enough for the verified mixed-term error; if an approach fails, identify and prove its nontrivial surviving statement.
4. Formalise only dependency-closed paper proofs; direct leaf audit, axioms, wiring, index and lint.

## Current verified frontier

For N=n+1 and the actual reflected ramp L and tent R, the entire source span satisfies Q(cL+dR)=c²A+d²D+cdM. The full signed coefficient obeys |M| <= (36 log N+26 log 5+14+2 log 1000000)/sqrt N. Eventually D>=N, and Q(cL+dR)>=c²(A-E_N²/(2N))+(D/2)d². All these statements were checked in Lean in the previous turn. The exact remaining sign is A-M²/(4D). No sign of A or of the span has been proved.

## Initial mechanism audit

The source definition is a finite sum of clamped exponential ramps:

    smoothFactorialLift epsilon K x
      = exp(x/2) sum_(1<=j<=K) clampedRamp epsilon (j exp(x)/K),
    rampBiNull epsilon N
      = (lift_(4N)-4 lift_(2N)+4 lift_N)/sqrt N.

This suggests an exact finite Mellin transform, not an assumed identification with the positive theta Riemann kernel. For Re(s)>0, a direct substitution in each finite summand should give

    integral exp((s-1/2)x) rampBiNull epsilon N x dx
      = M_epsilon(s)/sqrt N *
          ((4N)^s H_(4N)(s)-4(2N)^s H_(2N)(s)+4N^s H_N(s)),
    H_K(s)=sum_(1<=j<=K) j^(-s),
    M_epsilon(s)=((1+epsilon)^(s+1)-1)/(epsilon s(s+1)).

The formula needs a source-level proof of integrability, change of variables and the clamped-ramp Mellin factor. At the actual critical frequencies the condition Re(s)>0 is automatic. No limiting zeta identity is asserted.

An infinite floor-profile/null-source route is only an exploratory conjecture. Pole values and arithmetic tails can have nonuniform truncation defects, so pointwise or L² convergence does not license passing the full Weil functional to the limit. Existing positive theta-kernel truncation theorems do not identify this factorial source. Do not drop either polar branch or assume a null-source formula.

## Status

Previous turn classified as progress: four leaf modules and all seventeen public endpoints verified, giving quantitative Gram decoupling. Whole-corpus searches for the ramp diagonal, null-kernel truncation and dyadic Fermi/Hurwitz identities terminated successfully and were audited against current source. They give no applicable identification with the theta kernel. Coverage is partial in the semantic sense; compiler coverage is not a substitute for checking individual endpoints. No numerical experiment, web search or external novelty claim.

## Exact physical-space cancellation: paper proof

For any weight w on positive integers that vanishes above K, and M>=K,

    sum_(1<=m<=M) Lambda(m) sum_(1<=j<=K) w(j*m)
      = sum_(1<=k<=K) log(k) w(k).

First discard m>K: every product j*m exceeds K. For each remaining m, discard j>K/m for the same reason. Reindex the resulting hyperbola by k=j*m. Its fibre sum is sum_(m|k) Lambda(m)=log(k). This is a finite exact identity, with no estimate on prime distribution.

Apply it to w(k)=clampedRamp epsilon (k/v). If v>0, epsilon>0, and (1+epsilon)v<=K+1, the weight vanishes for every integer k>K, including equality at the collar endpoint. For the actual source, v=K exp(-u), u>=0, K in {N,2N,4N}, epsilon=sourceFactorialCollar N. The already-proved collar budget epsilon K<=1 and exp(-u)<=1 discharge the support condition. The actual prime cutoff 10N+2 exceeds all three K.

Thus the translated prime field on the whole nonzero support of the source is exactly its (1,-4,4) stencil of finite log-weighted clamp sums. Multiplication by the ramp and integration gives the actual prime quadratic pairing; the polar contribution must still be retained. This removes the prime-distribution estimate from that diagonal calculation. It does not establish the sign of the resulting archimedean/logarithmic expression.

Formalisation in progress. The Mellin route remains exploratory and is not used as a premise.

## Pole sign and exact diagonal: paper proof

For every compact continuous real source f, Fourier factorisation of its autocorrelation at i/2, followed by evenness, gives

    integral_(x>=0) 2 cosh(x/2) autocorr(f,x) dx
      = (integral exp(u/2) f(u) du) (integral exp(-u/2) f(u) du).

This argument needs continuity and compact support, not two derivatives. The existing exact ramp moments therefore give, for epsilon=sourceFactorialCollar N,

    P_N = -(1+epsilon/2) harmonicCorrection(N) chebyshevBiNullProducer(N) / N.

The last factor is nonnegative for all N. Indeed

    chebyshevBiNullProducer(N)
      = log binomial(4N,2N) - 2 log binomial(2N,N),
    binomial(4N,2N) = sum_(j=0)^(2N) binomial(2N,j)^2
                    >= binomial(2N,N)^2.

Together with the already-proved nonnegative harmonic correction, this proves P_N<=0. The existing moment envelopes also give |P_N| <= 2(5 log(4N+1)+1)/N. Thus the actual pole term lowers this diagonal and cannot be counted as a positive reserve.

Let G_N be the explicit (1,-4,4) combination of log-weighted factorial lifts, divided by sqrt N. Reflection preserves autocorrelation, so the pure reflected-ramp diagonal has the exact formula

    A_N = gammaBracket(0) autocorr(f_N,0) + biScaleLevyEnergy(f_N)
          - 2 integral f_N(u) G_N(u) du
          - 2(1+epsilon/2) harmonicCorrection(N) chebyshevBiNullProducer(N)/N.

The remaining task is a lower bound for this explicit archimedean/logarithmic expression stronger than the mixed Gram loss. The new identities do not prove that bound.
