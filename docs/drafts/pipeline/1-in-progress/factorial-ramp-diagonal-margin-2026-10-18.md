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

The exact logarithmic prime-field and signed-pole decomposition and the prior quantitative Gram decoupling remain verified; see the [exact-identity child card](../3-formalized/factorial-ramp-prime-log-diagonal-2026-10-18.md). The [polar-scale child card](../3-formalized/factorial-polar-loss-asymptotic-2026-10-18.md) records the exact normalized polar-loss limit `1/4` and the vanishing Gram-error-to-polar-loss ratio. The proposed absorption shortcut is retired. The [actual Müntz boundary repair](../3-formalized/factorial-muntz-boundary-repair-2026-10-18.md) additionally classifies the unique exponential correction restoring polar integrability, while the [uncorrected null-completion shortcut](../5-failed/factorial-muntz-boundary-pole-2026-10-18.md) is retired. The coupled lower bound for the actual optimized ramp diagonal remains open, so this parent stays in progress. Corpus searches have not supplied an applicable theta-kernel identification or a quantitative Weil truncation bound; their partial-search limitations are recorded below. No numerical experiment, web search or external novelty claim.

The new actual-source identities are `exp(-x/2)*F_n(x) -> -c_N` at negative infinity and `Integrable(exp(-x/2)*F_(n,c)) <-> c=c_N`, where `c_N=1/(2*sqrt(n+1))` and `F_(n,c)=F_n+1_(x<=0)*c*exp(x/2)`. The canonical correction has both polar moments integrable and exact readout `c_N/rho != 0` at every right-half-plane zeta zero. Its 18 new public theorems and five definitions passed direct checks, and all 24 audited declarations, including one repaired dependency theorem, use only standard axioms. This supplies no full-Weil-domain membership or coupled diagonal margin. The new child's verification section records the two unrelated global lint failures and pinned-dependency scope.

The subsequent [uniform analytic repair](../3-formalized/factorial-muntz-uniform-analytic-repair-2026-10-18.md) discharges the collar dependence: `K_n<=12/sqrt(n+1)`. Its corrected tail has weighted L1 readout bound `12/(sqrt(n+1)*(Re s+1))` throughout `Re s>-1`, including `s=0`; the actual corrected readout is analytic there, with an exact finite-part limit and original residue `-c_N` at zero. The literal compact-ramp readouts satisfy `|readout_n(rho)|<=13/sqrt(n+1)` uniformly over every right-half-plane zeta zero, without a height cutoff. Both new leaves passed direct checks; all 28 declarations (26 theorems and two definitions) use only standard axioms. The child card records formal-gate status. Uniform vanishing does not license exchanging the infinite Weil zero sum. The unsmoothed full-Weil limit and coupled diagonal margin remain open.

The [smooth Weil transfer](../3-formalized/factorial-muntz-smooth-weil-transfer-2026-10-18.md) constructs actual normalized convolutions `H_(n,k)=mollifier_k*G_n` and proves their `ExpDecayTest` membership. Thus every `H_(n,k)` satisfies the complete archimedean/polar/Abel-prime Weil identity with no remaining domain premise. Total mass is preserved, the sources converge to `G_n` almost everywhere, and each fixed exponential readout converges throughout `Re s>-1`, including both poles. The exact zero readout is `readout_rho(mollifier_k)*c_n/rho`, eventually nonzero at each fixed right-half-plane zeta zero. Both leaves and all 19 declarations (17 theorems, two definitions) passed direct/axiom checks. This package alone supplied no positivity or infinite zero-sum limit.

The [actual infinite zero-side limit](../3-formalized/factorial-muntz-zero-side-limit-2026-10-18.md) now discharges that summation obstruction. The exact corrected summand is `m_rho*c_n^2/(rho*(1-rho))`, with positive real part. Its norm is bounded by the summable majorant `2*c_n^2*m_rho/(1+normSq(gammaOf rho))`; multiplying by `exp(1)^2` bounds all normalized smoothings. Thus `W(H_(n,k),H_(n,k)) -> W(G_n,G_n)` and the complete physical difference converges to its strictly positive real part. Exact scaling by `c_n^2` yields one eventual range of `k` for which this physical difference is positive simultaneously for every `n`. Both new leaves and all 24 declarations (22 theorems, two definitions) passed direct/axiom checks. This is positivity of the corrected family, whose factorial indices share a single zero-readout profile at each smoothing scale. Quantitative transfer to the original compact ramp and the sufficient coupled bound `B_n >= 2*|P_n| + factorialWeilGramError n` remain open; no all-source RW or RH conclusion follows from this family alone.

The [uniform tail prime/polar budget](../3-formalized/factorial-muntz-tail-prime-polar-budget-2026-10-18.md) now controls the literal smoothed correction tail `U_(n,k)=mollifier_k*(G_n-r_n)`. Its global rate `3/2` survives smoothing with value constant `12*exp(3/2)/sqrt(n+1)`, independent of `k`, and its actual decay-class membership is proved. Autocorrelation decay at rate `5/4` gives an absolutely convergent ordinary prime sum, identified with the Abel pairing, bounded by a fixed `B/(n+1)`. Both polar branches contribute at most `144*exp(1)^2/(n+1)` in absolute value. Thus `|Re W(U,U)-Arch(U)| <= (B+144*exp(1)^2)/(n+1)`, and the prime-plus-pole absolute cost is uniformly negligible at scale `log(n+2)/(n+1)`, even for a smoothing schedule depending on `n`. Two leaves, 17 theorems and all 22 public declarations passed direct/axiom checks. The new work removes these tail-diagonal non-archimedean budgets; the archimedean lower bound, mixed-term control and original compact-ramp coupled margin remain open.

The [exact tail phase-cell mass](../3-formalized/factorial-muntz-tail-phase-mass-2026-10-18.md) supplies the missing quantitative mass lower bound. The actual collar obeys `(n+1)*epsilon<=1/12`. On each phase interval `j<= (n+1)/exp(x) <= j+1/16`, the three lattice sums are exactly `4j,2j,j`, so the repaired tail equals `exp(x/2)/(2*sqrt(n+1))`. Summing `n+1` disjoint cells proves `integral_[-log(2),0] T_n^2 >= 1/(256*(n+1))`. Actual normalized smoothings converge in squared mass; for each `n`, sufficiently fine smoothing retains `1/(512*(n+1))`. The prior prime/pole error is consequently bounded by one constant times actual source mass, independent of `n`. Two leaves, 17 theorems and all 18 public declarations passed direct/API/axiom checks. Frequency or weighted-primitive suppression is still needed for logarithmic archimedean growth, followed by mixed-term control for the original ramp. The child card records a concrete cubic-primitive conjecture; it is not yet a theorem.

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

Concretely, a sufficient target is

    gammaBracket(0) autocorr(f_N,0) + biScaleLevyEnergy(f_N)
      - 2 integral f_N G_N
      >= 2(1+epsilon/2) harmonicCorrection(N) C_N/N + E_N^2/(2N).

Here C_N is the explicit nonnegative binomial logarithm above. The coarse pole envelope is O(log N/N), whereas the verified Gram-loss envelope is O(log² N/N²). The sharp result below proves that the actual polar loss exceeds that Gram-error scale.

## Exact polar scale and the remaining coupled estimate

For `N=n+1` and the actual half-line polar integral `P_n`, four further verified leaf modules prove

`N*|P_n|/log(N+1) -> 1/4`,

`N*(2*P_n)/log(N+1) -> -1/2`,

and `factorialWeilGramError n/|P_n| -> 0`. In particular, eventually `factorialWeilGramError n < |P_n|`; the reverse eventual bound is false. The [failed-shortcut card](../5-failed/factorial-polar-loss-gram-obstruction-2026-10-18.md) contains the complete paper proof and the exact positive survivor. All 27 public declarations passed their axiom audits with only `propext`, `Classical.choice`, and `Quot.sound`.

Write the verified exact diagonal as `A_n = B_n - 2*|P_n|`, where `B_n` is its archimedean contribution minus its resummed prime contribution. The remaining sufficient margin is

`B_n >= 2*|P_n| + factorialWeilGramError n`.

This estimate must retain the polar term at scale `log(N+1)/N`. No such bound for `B_n`, no sign of the full ramp diagonal, and no unconditional RH theorem have been proved. Even positivity on this two-dimensional source span alone would not establish all-source RW.

## Exact-diagonal Lean verification

- `ClampedPrimeLogResummation.lean`: direct single-thread leaf compilation passed. All six public endpoints proved, including the actual collar/cutoff discharge.
- `CompactAutocorrelationPolarMoment.lean`: direct single-thread leaf compilation passed. General compact-continuous pole factorisation proved.
- `FactorialBiNullPolarSign.lean`: direct single-thread leaf compilation passed. All five public endpoints proved, including the binomial identity, producer sign, exact pole and quantitative bound.
- `FactorialRampDiagonalIdentity.lean`: passed direct leaf compilation after correcting support-argument and zero-integral proof shapes.
- All nineteen public theorems passed the `/tmp/biscale_ramp_diagonal_axioms.lean` audit, using only `propext`, `Classical.choice`, and `Quot.sound`. All four leaf logs are empty; the sequential final-leaf/audit command exited 0. Evidence and source hashes: `/tmp/bsu-ramp-diagonal-verification.json`; axiom output: `/tmp/bsu-ramp-diagonal-axioms.log`.
- All four modules are wired into the area umbrella. `scripts/formal_tools.py index` passed. Global `lint --check-generated` exited 1 on four unrelated missing umbrella imports: `EndpointCycleDeterminant`, `SharpCycleGramRealization`, `SharpGramDetectionOrder`, and `StationaryResolventMarkovPositivityAndNodalDefectProducer`. Full output: `/tmp/bsu-ramp-diagonal-lint.log`. No error names the four modules from this card.

Import-cache recovery: two unchanged dependencies (`DivisorSliceFixedPart.lean` and `WeilPositivityFiniteLevelExistence.lean`) passed direct compilation. During a separate build's cache replacements, the final leaf and audit selected 8,737 preserved dependency objects using Lean's `ModuleSetup.importArts` map through `--setup`; the source header imports and options were retained. The temporary copy-on-write dependency cache was removed after both checks passed. No dependency source was changed; this work launched no umbrella build and used one own Lean process at a time.

## Co-Poisson boundary-estimate search

The deep query `co-Poisson Muntz transform zeta Mellin null source truncation Weil diagonal boundary energy` returned partial results in `/tmp/bsu-ramp-copoisson-boundary-search.json`: source retrieval interrupted, decomposition worker disconnected, semantic coverage unmeasured, background index refresh incomplete. The available hits were inspected; this is not an exhaustive negative search.

- `BurnolCoPoissonIndicatorSeed.lean`, `memLp_two_burnolCoPoissonRightSum_coPoissonIndicatorSeed`, proves an actual co-Poisson indicator source is in `L²`. Its displayed proof uses a decay profile, not a Weil-form truncation estimate.
- `BurnolCoPoissonRawZeroAnnihilator.lean`, `burnolExtendedSoninEvaluationVector_mem_rawSource_orthogonal`, proves zero-evaluator annihilation of the closed **raw** source span. Its hypotheses include a right-strip zeta zero; it does not establish annihilation of the cosine-closed enlargement. No identification with this factorial ramp has been proved.
- `DeningerArithmeticPositiveCalderonKoszul.lean`, `deningerContinuousEnergy_zero_on_boundaryClosure`, requires continuity of the chosen energy and its vanishing on algebraic boundaries. It supplies neither obligation for the present Weil form.

These are source-level leads, not newly Lean-audited dependencies. None supplies the missing quantitative lower bound for the actual ramp diagonal. An `L²` limit, a pointwise Mellin limit, or raw-source annihilation alone does not discharge that bound.

The supplementary deep search `Euler Maclaurin finite zeta sum remainder critical strip` completed without reported execution errors (`/tmp/bsu-ramp-euler-maclaurin-search.json`). Semantic coverage is unmeasured. It returned real Euler–Maclaurin and Hurwitz continuation ingredients, not a verified uniform spectral estimate for this ramp. Fixed-frequency transform asymptotics alone cannot justify passing a Weil zero sum to a limit; high frequencies and the shrinking collar require separate control.

## Verified correction-tail primitive energy

The [actual tail primitive card](../3-formalized/factorial-muntz-tail-primitive-suppression-2026-10-18.md) now proves, for every actual normalized smoothing `U_(n,k)` of the canonical correction tail and `N=n+1`,

`norm(paperFT U_(n,k) tau) <= 360*exp(1)*(1+|tau|)/(N*sqrt(N))`,

and absolutely integrable weighted primitive mass at most `C/N^3`, where `C=32*(360*exp(1))^2*pi` is independent of `n,k`. The proof uses the exact dyadic lattice remainder, a bounded Bernoulli primitive, and integration by parts retaining the endpoint at zero. Together with the [exact phase-cell source mass](../3-formalized/factorial-muntz-tail-phase-mass-2026-10-18.md), it gives primitive mass at most `(512*C/N^2)` times physical squared mass, eventually in smoothing index for each fixed `n`. Four leaves and all 29 public declarations passed direct Lean/API/axiom checks with only standard axioms.

This discharges actual low-frequency suppression and relative primitive smallness. The existing compact-source logarithmic mass-ratio theorem still needs a justified domain bridge to these noncompact tails; the original ramp's mixed terms and sufficient diagonal margin above remain unproved. The parent stays in progress, and all-source RW/RH remain open.
