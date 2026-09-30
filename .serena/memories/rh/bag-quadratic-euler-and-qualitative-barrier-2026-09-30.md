# BAG F46 closed; C20.5 qualitative critical-mass attack OPEN

Scope remains exclusively independent recurrence producer; active RH goal unmet. Latest completed turn is verified progress.

## F46 final
`formal/GaloisForLFunctions/RHTower/SteinhausEulerQuadraticApprox.lean` (172 lines), namespace RHTower. Defines `steinhausEulerPrimeTerm s omega p = X p omega * p^(-s)`, `steinhausFiniteEulerProduct P s omega`, `steinhausQuadraticEulerLog P s omega = sum(z_p+z_p^2/2)`.
Six public theorems:
- `norm_steinhausEulerPrimeTerm_le`
- `steinhausFiniteEulerProduct_eq_exp`
- `log_norm_steinhausFiniteEulerProduct`
- `exists_steinhausEulerLog_quadratic_remainder_bound`
- `exists_log_norm_steinhausFiniteEulerProduct_sub_quadratic_le`
- `exists_steinhausFiniteEulerProduct_normSq_quadratic_bounds` (line152)
One C independent finite prime set P, all phases, all s with Re s>=1/2; norm of sum(-log(1-z)) minus quadratic sum <=C. Squared literal product lies between exp(2 Re quadratic -C) and exp(2 Re quadratic+C). Uses mathlib complex log cubic remainder and summability n^-3/2. No low-moment or recurrence assertion.
Final `lake --old env lean <leaf> -o <existing build path>` passes warning-free. Six axiom checks in `/tmp/BagQuadraticEulerAudit.lean`, log `/tmp/bag-quadratic-euler-axioms.log`, only standard axioms. Wired and exact-name index check total1. Global lint `/tmp/bag-quadratic-euler-lint.log` has15 unrelated unreachable modules, noBAG issue. Whitespace clean. Passing `/tmp/BagQuadraticEuler.lean` retained. No owned Lean/search process live.
F45 remains closed (see `mem:rh/bag-fixed-cofactor-upper-and-remainder-2026-09-30`). Removed concurrent stale 'uncertified' F45 clause and duplicate source reference from BAG frontier row using final audit evidence; F46 now added.

## Primary source audit this turn
- https://arxiv.org/pdf/2405.19151 (Gorodetsky–Wong,9pages): short Helson proof imports Gaussian chaos coupling/estimates; arithmetic reduction uses frozen-prefix conditional second moments, smooth/rough sieve, Mellin Parseval.
- https://arxiv.org/pdf/2604.05563 (Jad Hamdan,2026,23pages): section2 short proof uses level sets, Gaussian increment comparison/local approximation, barrier law, spatial maximum bound. Does not bypass all hard probability inputs.
C20.4 deterministic quadratic source above is common to these routes and now closed.

Search `/tmp/bag-euler-tilted-source-deep.json`, `/tmp/bag-poisson-tilt-moment-source.json` complete, partialfalse,noerrors, mostly stale/pending compiler metadata, semantic coverage unmeasured; refresh background_indexer_running. Inspected all candidate/source lists. Relevant exact source found below; no complete low-moment theorem.

## C20.5 new qualitative paper strategy (OPEN; do not assume)
Only qualitative decay is needed. Proposed proof replaces quantitative Gaussian ballot estimates by zero-one + moments:
1. For integer j, Y_j=floor exp(exp j), L_j(h)=log|F_Yj(1/2+i h)|. Deterministic M_j=Eexp(2L_j(0))=prod_{p<=Yj}(1-1/p)^-1; logM_j=j+O(1).
2. Tilt independent prime circles by K_r(z)=(1-r^2)/|1-rz|^2, r=p^-1/2. This consistent infinite product law is Poisson harmonic measure. Exact mean of -log|1-rz| under K_r is -log(1-r^2). Thus L_j(0)-log M_j is centered independent sum.
3. Centered factor bounded by C/sqrt p, variance >=c/p, fourth <=C/p^2. Variance grows ~j. Independence gives fourth moment of sum <=C*(variance)^2 eventually.
4. Positive-side anti-concentration WITHOUT symmetry: Holder gives E|Z|>=V^(3/2)/sqrt(EZ^4)>=c sqrtV. Mean zero implies EZ_+=E|Z|/2. Split at a sqrtV, apply Cauchy–Schwarz to tail => P(Z>a sqrtV)>=c'>0. Tilt is not half-turn symmetric.
5. Event exists finite A forallj centeredL_j<=A+2log(j+1) is unchanged by finitely many prime phases. Product zero-one =>measure0or1. If1 chooseA with measure>1-c'/2, then largej sqrtj>>A+logj contradict positive-side bound. Therefore eventnull. For each fixedA, finite-barrier survival probabilities tend0 by decreasing-event continuity.
6. Untilted global barrier failure: planar analytic L2 submean at radius delta~1/logY_j=e^-j, common rectangle around vertical [0,1], yields E sup_h |F_Yj(.5+ih)|^2 <= C e^(2j). Need local analytic version, not entire premise. Expected Euler product norm-square on rectangle differs from M_j by bounded factor since sum_{p<=Y}(p^(-1+2delta)-p^-1)<=2delta exp(2delta logY)sum(logp/p)=O(1).
7. Markov at threshold exp(logM_j+A+2log(j+1)) and unionj =>prob any barrier failure<=C e^-2A sum(j+1)^-4, uniformfinalscale.
8. Restricted normalized integrated Euler mass expectation equals tilted finite-barrier survival probability (phase rotation invariance+Fubini+finite product change of measure). On goodglobalbarrier mass equals restrictedmass. Markov then N->infinity thenA->infinity gives mass->0inprob. Unit mean => fractional moments q<1 vanish. Arithmetic smooth/rough+Mellin reduction then yields full multiplicative lowmoment after those dependencies actually formalized.

This is a derived proposal, NOT dependency-closed paper proof yet. Card has full outline and audit obligations. Do not replace it by a receiver assuming critical mass vanishing.

## Concrete next source/action
Exact Poisson mean is promising first formal target:
`formal/GaloisForLFunctions/HTGeometry/PoissonKernelBound.lean:49` exports
`GaloisForLFunctions.HTGeometry.circleAverage_poissonKernel_log_norm`:
 analyticOnNhd f closedBall cR, nonzero there, w in ball => circleAverage (poissonKernel c w • log norm f) cR =log norm f(w).
Take f(z)=1-r*z, c=0,R=1,w=(r:complex), 0<=r<1. Kernel on unitcircle equals (1-r^2)/|1-rz|^2; rightside log(1-r^2). Negate for exact tilted mean. Need prove equality kernel/literal density and conversion circleAverage -> integral on coordinate [0,1]. Existing `RandomEulerObservableFactor.lean` lines95–138 does circle-average to coordinate interval conversion for unweighted log factor.
Mathlib `DiffContOnCl.circleAverage_poissonKernel_smul` gives complex harmonic/analytic reproduction; harmonic variant in `Analysis/Complex/Harmonic/Poisson.lean:91`.
Product zero-one source `formal/GaloisForLFunctions/HTGeometry/FiniteModificationZeroOne.lean:111`: `measure_infinitePi_eq_zero_or_one_of_invariant`, general coordinate probability measures.
Spatial source `HTGeometry/HolomorphicBallMeanSq.lean:155` `normSq_value_mul_area_le_integral_ball` currently REQUIRES ENTIRE `Differentiable Complex F`. Cannot directly apply to finite Eulerproduct, which has poles on Re=0. Derive local analytic-disc version or audited entire quadratic surrogate. `HolomorphicBallL2Submean.lean` also entire premise.
`EulerTiltCovariance.eulerTiltMass` is Bernoulli weight p^-sigma/(1+p^-sigma)^2, NOT Poisson tilt; reject name-only reuse. It imports `Sieve/MertensSecondSharp`, `MertensPrimeWindowWeakConvergence`, which may supply true harmonic-prime arithmetic bounds.

No new analytic assumptions, numerical computations, full builds, commit/push, or subagents. Continue actual producer work, not other RH routes.