# GTA: positive-Hankel source with nonreal quantile-transform zeros

Goal ACTIVE: unconditional Lean RH via GTA. Read attachment /Users/michael/.codex/attachments/d9f4c500-46b8-4e46-b3e5-a43b604db5cb/pasted-text-1.txt every continuation. Use hgtl7 every turn. Corpus first, no web/external novelty, no old research markdown, no numerical experiments. Own log allowed. One foreground Lean process per agent; poll to terminal before next. No full/umbrella builds, no heartbeat increases. No subagents authorized. No commit/push.

Current hard user target: nonnormal transverse coupling must distinguish the critical wall. This turn CLOSED the proposed positive-Hankel Fourier-zero counterexample. It does NOT prove theta spectral rigidity or RH, and the pinned operator eigenmode still needs formalization.

## Newly audited leaf

formal/GaloisForLFunctions/RHTower/LogSineQuantileNonrealZeros.lean
351 lines,9 public declarations, namespace RHTower.
SHA256 d1c414c1c604d9c593811dcebe79390a666b95e954f44b801a8536fb9fead9df.
Wired once into RHTower.lean. Briefly created name LogSineClockNonrealZeros.lean was renamed/deleted; do not resurrect it.

Final direct leaf:
lake --old env lean GaloisForLFunctions/RHTower/LogSineQuantileNonrealZeros.lean
exit0, /tmp/gta-nonreal-leaf-audit.log.
Exact-source copy /tmp/gta-nonreal-axioms.lean exit0, all9 public declarations only propext, Classical.choice, Quot.sound. Prefix verified. Both logs have only an informational ring-normalization suggestion, no errors/warnings.
Index exit0 /tmp/gta-nonreal-index.log. Global lint exit1 ONLY foreign unreachable GaloisForLFunctions.RHTower.CHMDStage2KleinGordonTransmutationAndTContourBochner; no owned leaf flagged. Diffcheck, whitespace, one import, no adjacent olean/ilean verified. All owned jobs terminal. Scratch proof files removed; audit/search evidence retained.

Public declarations:
- tendstoUniformlyOn_logSineClockTransform: any d_n>=0 tending0 gives H_d_n -> H_0 uniformly on every real interval[-R,R]. R unrestricted.
- logSineClockTransform_zero_parameter: H_0(x)=pi/cosh(pi*x/2) for real x.
- exists_nonreal_zero_logSineClockTransform: exists eta>0, every0<delta<eta has z with H_delta(z)=0 and z.im!=0.
- logSineBaseCoordinate_image_univ: t0(R)=(0,1).
- logSineBaseCoordinate_injective.
- logSineQuantileTransform delta z = integral_(0,1) exp(i*z*Q_delta(t))dt.
- logSineQuantileTransform_eq_clockTransform hdelta z: F_delta(z)=H_delta(z/pi)/pi.
- exists_nonreal_zero_logSineQuantileTransform: same eventual nonreal zero for literal F.
- logSine_positive_hankel_nonreal_zero: unconditional eta>0 such that for each0<delta<eta the same profile is strictly concave on(0,1), every conductance a_(n+1)>0, every finite shifted conductance Hankel form nonnegative, and literal F has a nonreal zero.

## Family and exact proof

h_delta(t)=sin(pi*t)[1+delta*log(1+1/sin(pi*t))] on(0,1).
Q_delta(t)=integral_(1/2)^t 1/h_delta.
t0(u)=2*arctan(exp u)/pi,
P_delta(u)=integral_0^u 1/[1+delta log(1+cosh v)]dv,
Q_delta(t0(u))=P_delta(u)/pi.
H_delta(z)=integral_R exp(i*z*P_delta(u))/cosh(u)du.
H entire, even, H0=pi and order-one envelope fordelta>0 from prior audited leaf.
All conductances have an explicit positive Stieltjes/Hausdorff moment representation, yielding all shifted Hankel squares.

Weighted-L1 clock difference D_delta=integral |P_delta(u)-u|/cosh u ->0 by DCT, dominated by2|u|/cosh u. Phase inequality gives norm(H_delta(x)-H_0(x))<=|x|D_delta. Suppose arbitrarily small delta have only real zeros. Choose d_n<1/(n+1), apply existing even/order-one real-zero->LP classification and LP window compactness. Get entire g with g(x)=pi^2/cosh(pi*x/2)^2 on[-1,1]. Identity theorem gives g(z)cosh(pi*z/2)^2=pi^2 everywhere. z=i contradicts pi!=0. No numerical root location or variance/cumulant calculation.

Finite analytic order uses AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (note namespace).
LP classification in RHTower.OrderOneHadamard.laguerrePolya_of_even_of_realZeros.
Window theorem RHTower.IntervalLaguerrePolya.exists_subseq_reflectProduct_tendstoLocallyUniformly_of_window.
Identity theorem GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval.
Real phase inequality Real.norm_exp_I_mul_ofReal_sub_one_le.
Metric.tendstoUniformlyOn_iff uses dist(limit,sequence), so norm_sub_rev.
Tendsto.inf changes domain; for nhdsWithin use tendsto_inf.mpr with same-domain pair.
differentiable_const takes explicit constant.
Change of variables MeasureTheory.integral_image_eq_integral_abs_deriv_smul with MeasurableSet.univ. t0 image proved by inverse log(tan(pi*t/2)).

## Dependencies / build state

Prior leaves with hashes in mem:research/gta-log-sine-clock-pole-test-2026-10-15 and mem:research/gta-log-sine-hankel-test-2026-10-15.
Normal build oleans exist for LogSineQuantileProfile, LogSineStieltjesRepresentation, LogSineQuantileClock, LogSineClockTransform, and now LogSineConductanceMoments (needed dependency, built this turn exit0).
No olean for new LogSineQuantileNonrealZeros yet; only build it if next leaf imports it.
Earlier live handle54682 was unknown after compaction; process absent, empty dependency log, olean present. No owned overlap this turn.

## Next exact target: actual pinned quantile eigenmode

Own log docs/drafts/pipeline/1-in-progress/gta-arithmetic-core-loop-2026-10-15.md now contains full Cycle6 audit and Cycle7 paper proof.
Use direct quantile q_delta=1/h_delta. Avoid unnecessary inverse-clock density factory.
For F_delta(z)=0 set J(t)=integral_0^t exp(i*z*Q(s))ds,
g(t)=-exp(-i*z*Q(t))*J(t),
f(t)=-i*z*q(t)*g(t), with endpoints zero.
Interior g'=f-1. Existing profile lower bound implies t*q(t)->0 at0 and (1-t)q(t)->0 at1.
Fix epsilon=1/(2*(1+|Im z|)); near0 q(v)<=epsilon/v. Hence for0<s<=t small,
0<=Q(t)-Q(s)<=epsilon*log(t/s),
norm exp(i*z*(Q(s)-Q(t)))<=(t/s)^(1/2).
Integration gives |g(t)|<=2t. At1 use zero transform to replace prefix by suffix, obtaining |g(t)|<=2(1-t). Therefore f extends continuously to[0,1] with endpoints0; g also continuous with endpoints0. FTC gives integral f=1 and literal pinned primitive C f=g. Thus f inL2, nonzero, and i*q*C f=(-1/z)f, a nonreal eigenvalue.
The kernel i*q(t)*(1_{s<=t}-t) is Hilbert–Schmidt: squared norm integral q(t)^2*t*(1-t)dt. Near0 bounded by constant/[t*log(1/(pi*t))^2], integrable via primitive1/log(1/(pi*t)); symmetry handles1, continuity middle. This yields actual bounded compact pinned inverse, with no boundedness assumption onq.

Reuse generic C from HedenmalmPinnedVolterraBoundaryDefect.lean:
unitIntervalMeasure=volume.restrict(Icc0 1); H=Lp complex2; pinnedPrefix; pinnedMean; pinnedVolterraFun=prefix-t*mean; pinnedVolterra CLM.
Existing analogous source theorem in HedenmalmCompactSourceEigenmode.lean195–255:
divisorEigenvector, divisorEigenvector_ne_zero, compactSourceInverse_divisorEigenvector. But it requires PositiveDensitySource factory, so avoid this detour if direct q machinery works.
PositiveDensitySource requires continuous everywherepositive integrablek; constructing inverse P density is possible but not necessary.
Searches /tmp/gta-quantile-mode-search.json and /tmp/gta-profile-source-search.json complete snapshot, candidate applicability not checked; latter found no ready quantile-profile factory. Exact window lexical search useful; exact change-of-variable lexical query returned0, API verified by scratch and successful proof.

## Scope and audit

This kills bare concavity + all conductance Hankel positivity as sufficient for real transform zeros. Positive survivor is exact positive moment representation (already formalized). It does not yet establish operator nonreal mode, nor a theta counterexample. Family not shown to have theta Euler product, narrow zero strip, large zero-free central gap. No external novelty claim; known LP machinery reused. GTA's actual theta-specific nonnormal coupling remains OPEN. No work deferred for difficulty. Goal stays ACTIVE; never mark complete for this milestone.
