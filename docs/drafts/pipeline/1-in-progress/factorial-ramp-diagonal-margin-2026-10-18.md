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

Previous turn classified as progress: four leaf modules and all seventeen public endpoints verified, giving quantitative Gram decoupling. Current whole-corpus searches: `factorial ramp autocorrelation Weil energy` (deep) and `Weil null kernel truncation energy`, saved under `/tmp/bsu-ramp-*-search.json`; both commands terminated successfully, results still to be audited. No new Lean file or active Lean process. No numerical experiment, web search or external novelty claim.
