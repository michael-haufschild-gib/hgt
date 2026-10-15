# GTA log-sine source / positive Hankel sufficiency test

LATEST checkpoint: read `mem:research/gta-log-sine-clock-pole-test-2026-10-15` first. Exact clock and entire order-one transform are now audited; next proof uses the meromorphic-limit / LP-window pole obstruction, superseding variance/cumulant formalization.

Goal ACTIVE: unconditional fully Lean RH via GTA, per attachment /Users/michael/.codex/attachments/d9f4c500-46b8-4e46-b3e5-a43b604db5cb/pasted-text-1.txt (reread every continuation). Current user hard target: nonnormal transverse coupling distinguishes critical wall. No pivot to self-adjoint placement, no web/old markdown/numerical experiments. Use hgtl7/corpus first; own current working log allowed. No full builds, no heartbeat increases, one foreground Lean per agent, direct leaf final audits. Do not mark goal/no-go complete for these constituent theorems.

Authoritative current log: docs/drafts/pipeline/1-in-progress/gta-arithmetic-core-loop-2026-10-15.md, cycle5. Earlier exact parity bridge in mem:research/gta-nonnormal-feedback-frontier-2026-10-15 and dyadic obstruction in mem:research/gta-dyadic-metric-defect-and-core-2026-10-15.

## Research target and paper construction

Test proposed sufficiency of all-order positive conductance Hankel forms for literal pinned inverse spectrum. Generic concavity and individual conductance positivity are insufficient; actual all-order condition is now proved for this family.

For delta>0, r=sin(pi t), h_delta(t)=r[1+delta log(1+1/r)] on(0,1), Q_delta(t)=integral_(1/2)^t 1/h_delta, F_delta(z)=integral_0^1 exp(i z Q_delta(t))dt.
Scalar continuous lift x+delta[x log(1+x)-x log x].
Paper: h positive symmetric strictly concave, zero continuous endpoints. Q maps onto R; inverse T induces k(x)=h(T(x)), positive even smooth log-concave full-support density. q^2 t(1-t) integrable; B=i M_q V Hilbert-Schmidt.

Exact positive mixture:
f_delta(r)=integral_0^infty r^2/(r^2+s) rho_delta(s)ds,
rho_delta(s)=[1+(delta/2)log(1+1/s)]/(pi sqrt(s)).
Elementary negative cosine coefficient of sin^2(pi t)/(sin^2(pi t)+s) at n>=1 equals c(s)R(s)^n,
R(s)=(sqrt(s+1)-sqrt(s))^2 in(0,1), c=(1-R)/(1+R).
Thus a_(n+1)=integral_0^infty W_delta(s)R(s)^n ds,
W=rho*c*R>0 integrable, bounded above by rho/(1+s).
Every finite shifted Hankel form equals integral W R^shift(sum c_m R^m)^2>=0.

Optional paper change variable s=(1-R)^2/(4R) yields explicit [0,1] density:
a_n=1/(2pi) integral_0^1 R^(n-3/2)(1-R)[1+delta log((1+R)/(1-R))]dR.
This substitution and strict positive definiteness for nonzero polynomial are not formalized; the needed all-order NONNEGATIVITY and positive individual conductances ARE formalized by the pushforward representation.

## Three audited source leaves

1. formal/GaloisForLFunctions/RHTower/LogSineQuantileProfile.lean
24 public declarations (4 defs,20 theorems),209lines.
Exact scalar derivatives; positivity/reflection/continuous zero endpoints; strict concavity; bounds on 0<t<=1/2:
h_delta<=pi t[1+delta log(1/t)];
if pi t<1 then h_delta>=2delta t log(1/(pi t)).
Also sin(pi t)>=2t.
SHA dbf1c08be6bf33f6bcb056285946a237eb63178ec3f5d3a55bd47b895ebc863a.
Final leaf and exact-copy24 axiom audit passed. Relevant names:
logSineLift,logSineLift_eq,logSineProfile,logSineProfile_sine_pos,
logSineProfile_pos,continuousOn_logSineProfile,
strictConcaveOn_logSineProfile,logSineProfile_endpoint_upper/lower.
Compiled needed dependency this turn to normal .lake/build/lib/lean/...olean (not adjacent).

2. formal/GaloisForLFunctions/RHTower/LogSineStieltjesRepresentation.lean
7public declarations:
logSineStieltjesDensity
integrableOn_logSineStieltjes
logSineLift_eq_stieltjes
logSineStieltjesDensity_pos
logSineProfile_eq_stieltjes
integrable_logSineStieltjes_prod
logSineProfile_cosine_stieltjes.
Full scalar identity, joint integrability, cosine Fubini. Auxiliary kernel
r^2*v/[pi(r^2+s)sqrt(s)(s+v^2)], inner integral r/(r+v), exceptional v=r removed as nullsingleton.
Uses GaloisForLFunctions.integral_Ioi_one_div_add_mul_sqrt.
Final lake --old env lean <leaf> exit0 empty /tmp/gta-stieltjes-leaf-audit.log.
Exact-copy /tmp/gta-stieltjes-axioms.lean/log exit0 all7 only propext Classical.choice Quot.sound.
SHA c5d00d4a16a4a46abd1d1257918b7def1b62972e0b96331db57de609943b7904.
Also compiled -o normal build olean solely for nextleaf import.

3. formal/GaloisForLFunctions/RHTower/LogSineConductanceMoments.lean
15public declarations:
integral_unit_poissonKer_cos
logSinePoissonRadius
logSinePoissonRadius_pos/lt_one/relation
integral_sine_resolvent_cos
logSineConductance
logSineMomentWeight
logSineConductance_succ_eq_moment
logSineMomentWeight_pos
integrableOn_logSineMomentWeight
integrableOn_logSineMoment
logSineConductance_hankel_eq_integral
logSineConductance_hankel_nonneg
logSineConductance_succ_pos.
Actual profile coefficients, explicit positive finite moment representation, exact weighted-square identity ALL finite F and shifts, positive conductances.
Uses existing RHTower.WeilSingularArithmetic.integral_realPoissonKernel_fourier and HTGeometry.poissonKer_eq_poissonKernel.
Final lake --old env lean <leaf> exit0 empty /tmp/gta-moments-leaf-audit.log.
Exact-copy /tmp/gta-moments-axioms.lean/log exit0 all15 only propext Classical.choice Quot.sound.
SHA 5ad652a1ee7fbec4503f9ad9b5f4ceac5fbce879cbe50e85d95b3e0c50218c4e.
No built olean for this lastleaf yet; build only if needed import.

Both newleaves wired once into RHTower; indexexit0.
Global lint /tmp/gta-moments-lint.log exit1 only foreignunreachable:
HTGeometry.NormalSeriesStrictFDeriv; Hurwitz.AnchorLevelGraph,JointAnchorContinuity,JointAnchorRegularity.
Preserve concurrent work. Diffcheckpassed. Exactsource axiom prefixes/hash/publiccount checked. No adjacent olean/ilean.
All owned commandhandles terminal. Removed owned proof/API scratch; retained audits/searchlogs. No fullbuild, commit,push,numerics.

## Immediate next hard source theorem (not proved yet)

For all sufficiently small positive delta, F_delta has a nonrealzero, then an actual nonreal eigenmode of B. Complete this chain; do not retire bareHankel candidate solely from paper argument.

Simpler proof avoids exact sech moments entirely:
For0<t<=1/2, h_delta>=sin(pi t)>=2t fordelta>=0, so
0<=-Q_delta(t)<=0.5 log(1/(2t)).
Reflection gives integral Q_delta^2<=1/2, using integral_0^1 log(u)^2du=2.
On every compact subinterval, Q_delta tends to Q_0 asdelta↓0 by dominatedconvergence.
sin(pi t)<=pi t implies -Q_0(t)>=(1/pi)log(1/(2t)).
At Y=2pi, exp(-Y Q_0(t))>=(2t)^(-2) onlowerhalf, nonintegrable.
Hence F_delta(iY)→infinity asdelta↓0 (monotoneconvergence or finitecutoffs + compact DCT).
A normalized LP characteristic function has |F(iY)|^2<=exp(mu2 Y^2)<=exp(Y^2/2).
Thus smallpositive delta violate LP. Need actual source Q/F calculus + growth.
For delta>0, endpointlowerbound gives |Q|<=C_delta+(1/(2delta))loglog(1/(pi t)).
Hence all exponential moments and entire transform with envelope exp(K(1+|z|)log(2+|z|)).
Existing OrderOneHadamard.laguerrePolya_of_even_of_realZeros converts onlyrealzeros to LP, contradiction.
No pureimaginary zeros since positiveMGF.

Earlier paper alternative: Q0=(1/pi)logtan(pi t/2), limiting density sech(pi x),
mu2=1/4,mu4=5/16,kappa4=1/8; DCT implies positive fourthcumulant forsmall delta. This is unnecessary if simpler variance/MGF proof succeeds.

Then literal eigenmode at F_delta(z)=0:
g(t)=-exp(-izQ(t)) integral_0^t exp(izQ(s))ds,
f(t)=-iz q(t)g(t).
g'=f-1, g endpoints0, integral f=1, Vf=g, Bf=(-1/z)f.
Endpointloglog bounds show g=O(t), f=O(1/log1/t), so f inL2 nonzero.
Prove this for actualprofile; no arbitrary finite-matrix replacement.

## Corpus evidence / APIs for next continuation

/tmp/gta-quantile-endpoint-search.json completed partialFalse snapshotcoverage.
Forward quantiles found; no ready inverse-profileconstructor found.
PositiveDensityQuantile.lean symbolmap read (not fullfile), structure PositiveDensitySource, k continuouspositive integrable, normalized/cdf/quantile and measurepreservingtheorems.
HedenmalmQuantileNormalForm.lean symbolmap: sourceInverse_quantileFun346, quantileTransform_sourceInverse361, quantileSpeed263, inv_quantileSpeed422. Forward source law to quantile, not construction from h.

/tmp/gta-poisson-conductance-search.json partialTrue gave useful existing Fouriermoment used.

EvenRealRootedGaussianBounds.lean now read178–240:
lagRatio F=((derivF0)^2-F0*deriv(derivF)0)/(F0)^2;
tendsto_lagRatio (locallyuniform realpolynomialapproximants) hF0;
norm_sq_le_of_tendsto_even gives plane bound but requires evenapproximants.
For imaginaryaxis do NOT need evenapproximants: same limitproof applied to
LaguerrePolyaImaginaryAxisBounds.norm_sq_polyEvalC_I_mul_le.
Latter file full readpreviouscontexts; current first70 rechecked. Bounds use lagAtZero q=q'(0)^2-q(0)q''(0).
RiemannKernelLaguerrePolyaSymbol.lean250–315 shows exact coefficientlimit Gaussianbound pattern for arbitrary LP approximants.
XiIntervalLaguerrePolyaRH.lean1–90 newlyread:
RHTower.IntervalLaguerrePolya.exists_even_approx_reflectProduct gives even realrooted approximants to F(z)F(-z); not needed just for imaginarybound.
OrderOneEvenLaguerrePolya.lean1–165 readearlier; theorem114 exactonlyrealzeros+growth→LP.

## Scope honesty

Proposed counterexamplefamily is not shown to obey theta Eulerproduct or narrowzerostrip pluslargecentralgap. It refutes only sufficiency of listed genericprofileconditions, once fullchainformalized; doesn't refute thetaHankeltruth or arithmeticstrengthening. GTA fixed. Actual theta coupling producer and RH unresolved. No external noveltyclaim.
