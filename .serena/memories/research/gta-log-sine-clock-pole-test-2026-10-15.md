# GTA exact clock and pole obstruction: current continuation checkpoint

Goal ACTIVE, unconditional fully Lean RH through GTA. Read attachment every continuation:
/Users/michael/.codex/attachments/d9f4c500-46b8-4e46-b3e5-a43b604db5cb/pasted-text-1.txt.
User hard target: nonnormal transverse coupling distinguishes critical wall. No pivot, no web,
no old research markdown, no numerical experiments. hgtl7 every turn, corpus first.
Only direct needed-leaf Lean checks, one foreground Lean per agent, no full builds or heartbeat increases.
No subagents authorized. update_plan unavailable; own current working log carries plan.
Previous goal turn PROGRESS: exact source clock, entire order-one transform, verified audits.
Completion remains RH itself, not this model obstruction.

Working log: docs/drafts/pipeline/1-in-progress/gta-arithmetic-core-loop-2026-10-15.md.
Earlier details/positive Hankel proof: mem:research/gta-log-sine-hankel-test-2026-10-15.
Read this NEW memory first; it supersedes the variance/cumulant formalization plan.

## Same literal family, new exact coordinate

h_delta(t)=sin(pi t)[1+delta log(1+1/sin(pi t))].
Q_delta(t)=integral_(1/2)^t 1/h_delta(v)dv.
Earlier audited LogSineConductanceMoments proves ALL shifted Hankel nonnegativity and positive
conductances via a finite positive Hausdorff mixing measure. See old memory.

Exact fixed coordinate t0(u)=2 arctan(exp u)/pi:
t0'(u)=1/(pi cosh u), sin(pi t0(u))=1/cosh u.
P_delta(u)=integral_0^u 1/[1+delta log(1+cosh v)]dv.
Q_delta(t0(u))=P_delta(u)/pi (FORMALIZED).
P is odd, strictly increasing for delta>=0, |P_delta(u)|<=|u|.
For delta>0, |P_delta(u)|<=(2/delta)log(1+delta|u|/2).
P_delta(u)->u asdelta decreases to0 (nhdsWithin Ici0; FORMALIZED).

Use unnormalized/unscaled H_delta(z)=integral_R exp(i z P_delta(u))/cosh(u)du.
Original quantile transform F_delta(z)=H_delta(z/pi)/pi.
IMPORTANT: clock composition identity is formalized; whole-line integral substitution proving
F=H(z/pi)/pi is not yet formalized. Do not claim actual pinned inverse eigenmode from H alone.

H_delta is even, H_delta(0)=pi, positive delta gives entire analyticity and explicit order-one bound.
These are now fully checked source theorems, not assumptions.

## Two new audited modules

formal/GaloisForLFunctions/RHTower/LogSineQuantileClock.lean
299lines,27public declarations. Hash:
613a18e39f0d92f33704774967aa2c71d98844768263d12e82f5f75dfb5ab509
Publicnames:
logSineBaseCoordinate, logSineBaseCoordinate_mem/zero/neg,
hasDerivAt_logSineBaseCoordinate, sin_logSineBaseCoordinate,
logSineClockDenom, logSineProfile_baseCoordinate, logSineClockDenom_ge_one,
continuous_logSineClockDenom, logSineClock, continuous_logSineClockSpeed,
hasDerivAt_logSineClock, continuous_logSineClock,
logSineClock_zero/zero_parameter/neg, logSineClockSpeed_pos/le_one,
strictMono_logSineClock, logSineClock_nonneg, abs_logSineClock, abs_logSineClock_le,
logSineQuantileClock, logSineQuantileClock_baseCoordinate,
logSineClock_log_upper, tendsto_logSineClock_parameter_zero.
Final lake --old env lean GaloisForLFunctions/RHTower/LogSineQuantileClock.lean exit0
empty /tmp/gta-clock-leaf-audit.log.
Exact-copy /tmp/gta-clock-axioms.lean/log exit0 all27 only propext Classical.choice Quot.sound.
Compiled normal .lake/build/lib/lean/...olean as needed import; no adjacent artifacts.

formal/GaloisForLFunctions/RHTower/LogSineClockTransform.lean
348lines,16public declarations. Hash:
05626e5329189cf329f9f2264d510eb4c3892d635766d7f84a4740ee4064dff8
Publicnames:
logSineSech_exponential_bound: 1/cosh u<=2exp(-|u|)
integrable_logSineSech_abs_pow(n): Integrable |u|^n/cosh u
logSineExponentialEnvelope(delta,A)=2exp(p[log(max1(delta/2))+log(1+2p)]), p=A*(2/delta).
logSineClock_exponential_bound:
 exp(A|P|)/cosh <= E(delta,A) exp(-|u|/2), fordelta>0,A>=0.
integrable_logSineClock_exponential
logSineSechMeasure=volume.withDensity(ofReal(1/cosh))
integrable_logSineSechMeasure_iff(g): iff Integrable ((1/cosh) smul g)
integral_logSineSechMeasure(g): corresponding exact integral
logSineClock_integrableExpSet: ProbabilityTheory.integrableExpSet P mu=univ
logSineClockTransform
logSineClockTransform_eq_complexMGF(delta,z): H=complexMGF P mu (I*z)
analyticOnNhd_logSineClockTransform(hdelta): analytic everywhere
logSineClockTransform_zero: Hdelta0=pi
logSineClockTransform_even: Hdelta(-z)=Hdelta z (allreal delta)
norm_logSineClockTransform_le: normH<=4*E(delta,normz)
logSineClockTransform_order_one: existsK>=0 forallz normH<=exp(K(1+normz)log(2+normz)).
Final direct leaf exit0 empty /tmp/gta-transform-leaf-audit.log.
Exact-copy /tmp/gta-transform-axioms.lean/log exit0 all16 onlystandard3axioms.
NOT compiled to an olean yet. Compile this needed leaf -o normal build tree before importing it.
Do not run full or umbrella build.

Both leaves wired once into RHTower. indexexit0. Latest global lint exit1 ONLY foreignunreachable
GaloisForLFunctions.RHTower.CHMDStage1MultiplicativeResolventAndClampedBeam.
No error names ownednewleaves. Preserveforeignwork. Diffcheckpassed.
Exactprefix/hash/publiccount checked; no adjacentolean/ilean.
Owned /tmp/gta-logcosh-api.lean, gta-logcosh-clock.lean, gta-clock-exponential.lean removed;
retain audit/searchlogs. All owned jobs terminal, none currently running.
Workflow correction: one scratch and newer final audit briefly overlapped. Newer audit killed
by owned PIDs44619/44559, exit143 and absentPIDs confirmed, then rerun alone afterolder exit0.
Do not repeat; poll handles to terminal BEFORE launching next Lean. Never claim this turn
maintained uninterrupted oneprocessdiscipline. Root-cwd audit error also corrected by formal cwd.

## Next exact paper proof: pole obstruction, NOT variance/cumulant work

Target: exists eta>0 forall0<delta<eta, existsz H_delta(z)=0 and z.im!=0.
This is a genuine nonreal-zero theorem for the same all-order-Hankel-positive family.
Paper proof closed as follows:

1. H_delta -> H_0 uniformly on every bounded REAL interval asdelta↓0.
For realx:
 |H_delta(x)-H_0(x)| <= |x| D_delta,
 D_delta=integral_R |P_delta(u)-u|/cosh u du.
D_delta->0 by DCT: pointwise clockconvergence and
 |P_delta-u|/cosh <=2|u|/cosh, integrable by integrable_logSineSech_abs_pow1.
Normphase inequality:
 |exp(i a)-exp(i b)|<=|a-b|
factor exp(i b)[exp(i(a-b))-1], norm exp(i b)=1;
then use Real.norm_exp_I_mul_ofReal_sub_one_le (namespace REAL, not Complex).
This is in Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean260.
For a sequence d:Nat->Real with d_n>=0 and Tendsto d atTop(nhds0), obtain
Tendsto d atTop(nhdsWithin Ici0 0) by .inf / tendsto_principal and compose
tendsto_logSineClock_parameter_zero. Use generic DCT then Metric.tendstoUniformlyOn_iff.
No variance calculation needed.

2. Base transform H_0(x)=pi/Complex.cosh(pi*x/2) on real axis.
Use logSineClock_zero_parameter and
GaloisForLFunctions.HTGeometry.integral_cexp_div_cosh at z=-(x:Complex),
then cosh evenness. Existing exact theorem:
for |z.im|<1,
 integral exp(-(z*t)*I)/(cosh t:Complex)=pi/Complex.cosh(pi*z/2).
Source file SechComplexFourierTransform.lean136ff.
Real-window limit G(z)=pi/Complex.cosh(pi*z/2) is continuous/nonzero onrealaxis.
Complex.ofReal_cosh x : (Real.cosh x:Complex)=Complex.cosh(x:Complex).
Complex.cosh_mul_I : cosh(x*I)=cos x.
Need check Complex.cos_pi_div_two in scratch (not yet checked).

3. Suppose arbitrarily smallpositive delta have onlyrealzeros. Choose bad d_n with
0<d_n<1/((n:Real)+1). Squeeze using checked
tendsto_one_div_add_atTop_nhds_zero_nat.
Then each H_d_n is LP by existing
RHTower.OrderOneHadamard.laguerrePolya_of_even_of_realZeros.
EXACT binders:
(hK:0<=K)
(hf:AnalyticOnNhd Complex f univ)
(hf0:f0!=0)
(hf0re:(f0).im=0)
(hford:forallz analyticOrderAt f z != top)
(heven:forallz f(-z)=f z)
(hbound:forallz normf<=exp(K(1+normz)log(2+normz)))
(hreal:forallz f z=0 -> z.im=0).
Do not add hford asassumption: follows from nonzerovalue0 and checkedmathlib
analyticOrderAt_eq_top_iff_eq_zero (z) (hf:forallz AnalyticAt Complex f z),
located Analysis/Analytic/Order.lean682. If f=0, eval0 contradictspi_ne_zero.

4. Existing strong corpus theorem:
RHTower.IntervalLaguerrePolya.exists_subseq_reflectProduct_tendstoLocallyUniformly_of_window
in XiIntervalLaguerrePolyaRH.lean82ff:
{F:Nat->Complex->Complex}{G:Complex->Complex}
(hLP:foralln HTGeometry.LaguerrePolya(Fn)){epsilon:Real}
(heps:0<epsilon)
(hGc:ContinuousOn(fun s:Real=>G s)(Icc(-epsilon)epsilon))
(hGne:foralls,|s|<=epsilon -> G s!=0)
(hconv:TendstoUniformlyOn(fun n(t:Real)=>Fn t)(fun t:Real=>G t)atTop(Icc(-epsilon)epsilon))
gives exists sigma g, Tendsto sigma atTop atTop and Differentiable Complex g and
TendstoLocallyUniformly(fun k z=>F(sigma k)z*F(sigma k)(-z))g atTop and
forallt inIcc(-epsilon)epsilon,g t=G t*G(-(t:Complex)).
Choose epsilon=1. Thus entire g agrees onrealwindow with pi^2/cosh(pi*t/2)^2.

5. Entire identity theorem applied to g(z)*cosh(pi*z/2)^2-pi^2 gives identicallyzero.
Exact helper:
GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
(hG:Differentiable Complex G){t0 r:Real}(hr:0<r)
(h:forallt:Real,|t-t0|<r ->G(t:Complex)=0)(z:Complex):G z=0.
Defined CompactFourierEntire.lean226, imports mayalreadyinclude; verify neededolean.
Atz=I cosh(pi*I/2)=0, contradictionpi!=0. Therefore eventualnonrealzeros.

This is exact meromorphic-limit obstruction, no optimizingconstants ornewreal-spectrum premise.
Uniformlimit/currentnewzero theorem NOT formalized yet. Do this next; do not driftinto
variancebounds, genericnormalfamilywrappers, or anothermodel.

## After nonreal-zero theorem

Need exact whole-line changeofvariable linking H to originalF and then literalpinnedmode.
At F(z)=0, g(t)=-exp(-izQ(t)) integral_0^t exp(izQ(s))ds,
f(t)=-iz q(t)g(t). Then g'=f-1,endpoints0,integralf=1,Vf=g,Bf=(-1/z)f.
Endpointloglog bounds give g=O(t), f=O(1/log1/t), fL2 andnonzero.
HS finite from q^2 t(1-t) integrability. Lowerlogclockbound / onto R /inverse-density
construction notformalizedyet; contractionandupperlogboundonly.

This family has NOT been shown to have theta's Eulerproduct, narrowzerostrip andlargecentralgap.
Don't claim it refutes arithmeticstrengthening. Actual theta coupling producer andRH remainopen.
GTA fixed. BareHankel no-go notclosed until requiredsame-source spectralchainchecked.

## Search / API / tooling

This turn read hgtl7skill (requireduserinvocation overridesoldmarkdownban).
/tmp/gta-sech-clock-search.json complete; /tmp/gta-clock-entire-search.json partial;
/tmp/gta-meromorphic-window-search.json partial. Useful MGF machinery discovered via
EntireExponentialMomentPolynomialDensity.lean and checked ininstalled
Mathlib/Probability/Moments/ComplexMGF.lean. Noexternalnoveltyauditperuser.
Mathlib ProbabilityTheory.analyticAt_complexMGF follows interior integrableExpSet;
used withactualallrealtilts proved. Noextra measurefinite hypothesis required.
Integral reflection integral_neg_eq_self takes explicit function AND measure; use
simpa only[] using! (integral_neg_eq_self (fun u:Real=>...) volume) to avoidReal/Complex
instance diamonds. Similar using! fixed DCT nhdsWithindiamond.
Avoid guessing Continuous.exp (absent here); use Real.continuous_exp.comp.
Source finalmetadata hashes above authoritative.

Anti-theatre: these are formaldependencies of aconcrete sourcefalsification, nottheRHproducer.
No external scientificnoveltyclaimed. Noeffort-baseddeferral. Next exactpolecontradiction
is thehardselectedstep now.
