# Source-correlation absolute-envelope boundary

- **ID:** li-clock-source-correlation-envelope
- **Stage:** 2 — Fully proven on paper
- **Type:** Obstruction with positive survivors
- **Source:** `/tmp/li_current_theta_m15_source_correlation_attack.md`, 355 lines, SHA256 `9215912d5cfdb3d8a56afd0a9757cad6271c4401bcfe14d8639758a3447aa87f`.
- **Statement:** Compact marked positive and negative coefficient-carrier measures are separately independent of damping p>1. The absolute source-envelope cost/budget quotient tends to infinity, with an explicit lower bound that cancels the actual Borel derivative K.

## Goal

Determine the actual signed M15 source-correlation inequality. The envelope obstruction is auxiliary; actual M15 and RH remain open.

## Gates

- 0→1: PASS. Prior corpus searched; full source-correlated candidate and positive survivors written.
- 1→2: PASS. Author full proof check, root ALL355 mathematical review and independent Pole ALL355/ALL61 raw corpus/ALL27 primary blocks PASS. Root subsequently read ALL319 independent certificate, including complete origin-smoothness addendum, and ALL259 author evidence. Root does not claim a separate raw61 read.
- 2→3: PARTIAL. [Compact Gamma marking M01–M10](../3-formalized/li-clock-compact-gamma-marking.md) is locally Lean-final with all10 contracts and full gates; HistoryBarrier is now locally Lean-final, and approved source-envelope E01–E21 implementation is underway in separate private scratch packets.
- 3→4: PENDING.

## Subsequent finite-guard qualification

The dual-audited [terminal-history classification](li-clock-terminal-history-boundary.md) proves actual guarded-zero clocks form a finite set. Thus E19's eventual implication at guarded zeros is vacuous; it supplies no late actual witness. E17's unguarded whole-ray norm-majorant/envelope-budget ratio divergence and both quantitative lower bounds remain substantive. Complete compact signed-source identities are unchanged. Original proof/certificate bytes below remain historical and intact.

## Approach

Use the literal actual source and first-zero history; separate the signed cost from its absolute majorant. Integrate the exact kernel derivative over [ell,t−1], apply convexity and the source tail envelope, then cancel K from the quotient. Audit compact marked carriers as coefficientwise measures, not Jordan parts.

## No-go closure

- **Exact failed step:** Replacing the signed outer history by N_gamma and trying to prove N_gamma<=V_actual eventually; in fact N_gamma/V_gamma→∞ while V_actual<=V_gamma.
- **Strongest positive survivor:** Explicit actual-K-cancelling exponential quotient lower bound; independent terminal-lag lower bound; separate compact marked positive/negative carrier p-invariance.
- **New insight:** These absolute envelopes lose the needed signed source-cost correlation. Changing p does not change the compact marked target measures, but may still help prove estimates for that invariant target.
- **Paper status:** Dependency-closed PAPER PASS. Exact355 preserved; mandatory independent certificate §3 supplies every-order compact-majorant origin-smoothness proof. Complete319 certificate included below.
- **Lean status:** PARTIAL: complete compact Gamma marking M01–M10 formalized; source-envelope E01–E21 still OPEN. No failed-route closure or retirement claimed.
- **Excluded conclusions:** Does not show Cout>V_actual, actual M15 false, existence of a first zero, or RH false.

## Log

- 2026-10-01: Root read ALL355 and checked all proof constants, domains, actual gamma restriction and failure inference. Root review: `/tmp/li_root_theta_m15_source_correlation_review.md`. Deep retrieval b0e4e1f38e5179261a486def76dcf43e8373f1442055b4e973e4e30432d95fbb; lexical retrieval 0bea83da11c7f8f5a64d2c4d9fed7f63bd944fdf55afa564879d75b4619fbbd9. Historical Stage1 entry; superseded by final paper acceptance below. No formal claim.

- 2026-10-01: Independent Pole complete319 certificate SHA75c56ef7b7340f6da99a7eac9436cd50769b780728282a416a0f5978f7cfb599 PASS. Root read ALL319 (recovered a truncated coverage passage explicitly), checked exact proof/domain/constants and full smoothness admission. Author evidence259 SHA268a6bb2d65ba1090db24baf0005083ed95b09db6c82081f6a0f07fa056b8beb plus metadata5198 SHA88f6413e99cd517963143ac866c241e43db2eb18032590930f2213f9ff890954 retained. Independent review matched all56 primary hashes and all20 passage provenance hashes. Stage2 only; positive-survivor Lean and no-go closure remain OPEN. Actual M15/RH OPEN.

## Frozen complete paper

The following bytes reproduce the complete 355-line source paper exactly.

# Actual first-zero M15 correlation: source-specific envelope obstruction

Status: PAPER-ONLY. Actual M15 remains OPEN. Complete symbolic source proof below rejects a specific sufficient step based on a guard-aware absolute envelope. It also identifies exact compact damping invariance of both coefficientwise Gamma carriers. Neither result asserts a first zero exists, that actual correlation exceeds its budget, that M15 is false, or any RH conclusion. New survivors require full independent paper review before a Lean allocation.

## 1. Frozen inputs and scope

Read ALL 608 lines of `/tmp/li_producer_theta_undamped_cutoff_attack.md`, SHA `815457a785a910206e21ad479fad5c09c1834506f6e11ac2e77967dea374c9fc`. Reuse unchanged exhaustive independent reviews of ALL 683 `/tmp/li_pole_theta_moving_history_correlation_attack.md`, SHA `cf885634d37e11490bccba01b1ada3d8e9612deac2e400726709340fec5ec7d7`, and ALL 159 `/tmp/li_root_theta_history_slope_fraction_sharpening.md`, SHA `a57b0b262cddd87067ff7c3f7f4d59259fefafad1e00e1b44aaa958ee7eda186`. Read active `docs/drafts/pipeline/1-in-progress/li-clock-integrated-source-sign.md`. No input, source, card, or prior certificate was modified. No compiler, Lean probe, numerical experiment, mathematical computation job, or agent was launched.

The question is the ACTUAL outside correlation at a hypothetical first nonnegative-history zero. The frozen683 strict-continuation implication is retained: a nonstrict M15 bound ONLY at such zeros with t>20 would suffice, because the literal early source corridor supplies a strictly positive reserve. This conditional continuation is already paper-proved; the missing actual M15 bound is not supplied by the current search or estimates.

## 2. Literal source, normalization, factor ONE, and compact admission

Write `nu_j=thetaCuspNormalizedEvenMoment j`. Exactly

    R_j=2 integral_0^infinity x^(2j)*thetaCuspFullSource(x) dx,
    nu_j=R_j/R_0,  R_0>0,  nu_0=1,  nu_j>0 for EVERY j,
    B(t)=sum_(j>=0) nu_j*t^(2j)/((2j)!)^2,
    K=B',  b=K'(0)=nu_1/2=normalizedPrimeArchMoment 0/2>0.

Both factorials, the raw factor 2, full theta source, and single R_0 normalization are retained. No paired-eta or symmetrized-product normalization is substituted. Literal actual clock F and its two integrated quantities are

    F(t)=t*S(t^2/16),
    P(t)=integral_0^t F(u)du,  P(0)=0,  P'=F,
    D(t)=integral_0^t P(u)/u du,  D(0)=0,
    t*D'(t)=P(t) for t>0.

In particular D is NOT P/t. Full-copy cosine admission gives P=O(t^2) at zero. The quotient P(u)/u extends continuously by zero, so D is genuine compact L1 and smooth at the origin, with D=O(t^2). Complete source B/K derivatives are admitted by compact norm-summable series; K is smooth, K(0)=0, K'>=b, K''>=0, K>0 for t>0. Positive cubic coefficient nu_2/144 gives `t*K'(t)>K(t)` at every t>0. These are consequences of the entire actual coefficient family, not new premises.

The source-derived Volterra equation has factor ONE:

    P(t)+integral_0^t P(s)*K(t-s)ds=t*K(t),  t>=0.       (2.1)

Compact integration by parts with P(s)=sD'(s) gives

    P(t)=t*K(t)+integral_0^t D(s)*H_t(s)ds,
    H_t(s)=K(t-s)-s*K'(t-s).                            (2.2)

Every boundary product sD(s)K(t-s) vanishes: s=0 uses D(0)=0, s=t uses K(0)=0. Compact integrands are continuous after the origin filling; no totalized improper-integral evaluation or unproved global signed L1 is used.

Define the ACTUAL slope length

    ell(t)=K(t)/(4*K'(t)),  t>0.

Then 0<ell<t/4, and ell->infinity, because the certified actual `K'/K->0` is positive on the positive ray. This is a length, distinct from earlier notation `t*K'/K` for elasticity. For the proof below, neither `ell/t->0` nor subexponential K growth is needed.

## 3. Exact remaining M15 and the source orientation gap

Let (Z) mean t>20, D(t)=0, and D(s)>=0 for EVERY 0<=s<=t. Put

    J_t(s)=s*K'(t-s)-K(t-s)=-H_t(s),
    C_out(t)=integral_ell^t D(s)*J_t(s)ds,
    V_actual(t)=t*K(t)+(K(t)/2)*integral_0^ell D(s)ds.

The missing source-specific target is exactly

    (Z) implies C_out(t)<=V_actual(t).                 (M15)

The already-proved inner estimate H_t>=K(t)/2 on [0,ell], and its stronger H_t>=3K(t)/4 on [0,ell/2], retain a positive early source reserve. They justify strict continuation if M15 holds. They do not control C_out.

The exact outside identity, including its moving boundary term, is

    C_out=ell*D(ell)*K(t-ell)+integral_ell^t P(u)*K(t-u)du.  (3.1)

The full compact Gamma transport from frozen683 gives another exact expression. For p>1 let tau_p^+/- be the ACTUAL full positive/negative coefficientwise Gamma jump measures; mark their restrictions to (0,t] by exp(pu), obtaining eta_(p,t)^+/- . Genuine bounded-test L1 gives

    eta^+((0,x])-eta^-((0,x])=D(x),  0<=x<=t,
    C_out=integral psi_(t,ell)deta^+ - integral psi_(t,ell)deta^-,
    psi_(t,ell)(u)=ell*K(t-ell) for 0<u<=ell,
                      u*K(t-u) for ell<u<=t.             (3.2)

At (Z), the two full positive laws have equal positive mass and ordered cumulative distributions. Their ordered coupling does NOT orient psi: its right derivative at ell is H_t(ell)>=K(t)/2>0, while its derivative near t is negative (at t it is -t*b). The same cost has an increasing and a decreasing region. Thus first-order order cannot supply the required upper comparison. The signed primitive and moving boundary in (3.1) are exactly the missing mixed arithmetic information; replacing either carrier by the positive degree/CP order law changes the observable.

Sharp slope-fraction retention controls the UNWEIGHTED Q_t history law: frozen159 gives U_alpha<=2alpha-alpha^2 for 0<=alpha<=1, with a strict actual deficit for 0<alpha<=1 at positive clocks, and full-alpha optimal ceiling classification. At alpha=1/4 this gives Q_t([0,ell])<7/16. Its residual linear correction cancels against the exact unweighted first hinge moment. Multiplication by D(s) does not preserve that first-moment cancellation or the normalized Q_t moment identities. No D-weighted counterpart is proved. Applying the same residual after inserting D would require a new source-specific moment/correlation identity; treating the unweighted cancellation as still zero would be the failed step.

The exact raw score recurrence and raw Hankel positivity are genuine actual-source inputs, but concern positive raw theta moments. The log-cumulant recurrence alternates signed terms. Re-summing it supplies (2.1), (2.2), and (3.1); bounding the residual signed P integral still requires M15 information. Positivity of the raw theta Hankel matrix is not positivity of a D-weighted signed Gamma/history matrix. A complete weighted-Hankel characterization with ALL PSD inequalities supplied is a receiver for such a sign, not a producer of those inequalities. No new source orientation follows from these inspected interfaces.

## 4. Both marked coefficientwise Gamma carriers are damping-independent

This strengthens difference-only cancellation without a source replacement. For j>=1 set

    a_j=(-1)^(j-1)*normalizedPrimeArchMoment(j-1)/(2*j).

The literal public definitions give, for p>1 and u>0,

    ell_j(p)=liClockThetaLogJumpCoefficient p j=a_j/p^(2*j),
    row_(p,j)(u)=p^(2*j)*u^(2*j-1)*exp(-p*u)/(2*j-1)!,
    exp(p*u)*max(+/-ell_j(p),0)*row_(p,j)(u)
       =max(+/-a_j,0)*u^(2*j-1)/(2*j-1)!.              (4.1)

The scaling identity for max uses strictly positive p^(2*j). At j=0 the actual jump coefficient and both jump weights are ZERO. The Dirac row present in the general Gamma-row law therefore contributes exactly zero, not an omitted atom. At u<=0 every density row is zero; no negative-ray exponential domination is invoked.

For EACH p>1, complete positive-density admission and full coefficient absolute summability precede factoring exp(pu) through the sums. The source proof at SignedGammaJumps:683–719 gives 0<=row_(p,j)(u)<=p: write the row as p*exp(-pu)*(pu)^(2j-1)/(2j-1)! and use the positive exponential series; the j0 and nonpositive-u rows are zero. Thus each positive/negative row sum is pointwise dominated by p*|ell_j(p)|, a genuinely summable full family. For an explicit summable comparison at a fixed u, choose any fixed reference p_*>1; its admitted complete row family is multiplied by the finite scalar exp(p_*u). Equation (4.1) therefore identifies the whole sum, not only finite partial sums. On (0,t], marking is bounded by exp(pt), so both marked positive densities are genuine L1; public withDensity identification and bounded-test change of measure identify eta_(p,t)^+/- with those densities.

Consequently, for all p,q>1 and t>0,

    eta_(p,t)^+=eta_(q,t)^+ AND eta_(p,t)^-=eta_(q,t)^-. (4.2)

These are coefficientwise positive/negative Gamma carriers. They are NOT asserted to be Jordan positive/negative parts of the full signed P(u)/u density. Their difference is the same compact signed density P(u)/u. No GLOBAL marked measure is claimed finite. Changing p>1 does not change either marked marginal or its actual compact cost integral: the marks cancel separately and completely. This invariance does NOT rule out a p-dependent auxiliary estimate or another representation proving a better bound for the same invariant inequality; no universal no-go for all damping-based proof methods is asserted.

## 5. Actual strip envelope and the first-zero terminal anchor

Let `A_mass=xiShiftAbsoluteMass 0>0`, the COMPLETE reciprocal-square Xi-copy absolute mass, distinct from the history excess B-1. All copies and their multiplicities remain. Certified actual strip bound gives the source envelope at gamma=1/300:

    |P(u)|<=A_mass*u^2*exp(gamma*u)/2,  u>=0.          (5.1)

The following envelope calculation is meaningful for EVERY fixed gamma>0 and A_mass>0. Its application as source domination here uses (5.1) at gamma=1/300 (and also any larger gamma by monotonicity). No smaller source growth rate is asserted.

The origin filling and genuine compact FTC give, for s>=0,

    |D(s)|<=A_mass*s^2*exp(gamma*s)/4.                 (5.2)

Indeed |D(s)|<=A_mass/2*integral_0^s u*exp(gamma*u)du, and the last exponential is at most exp(gamma*s). At (Z), the zero endpoint additionally gives the guard-aware terminal anchor

    0<=D(s)=-integral_s^t P(u)/u du <= E_t(s),
    E_t(s):=A_mass/2*integral_s^t u*exp(gamma*u)du,
    0<=s<=t.                                         (5.3)

This uses signed P without assuming P>=0 or P<=0. The quotient is genuinely continuous/L1 on the compact interval, including the zero endpoint. Define the FULL nonnegative majorant, for every t>0,

    N_gamma(t)=integral_ell^t E_t(s)*max(J_t(s),0)ds,
    V_gamma(t)=K(t)*[t+(A_mass/24)*ell^3*exp(gamma*ell)]. (5.4)

All integrands in N_gamma are continuous on their true compact carriers; max(J,0) has the same admission. E_t is nonnegative there. Thus these are genuine finite real integrals, not formal manipulations of a totalized value. At (Z), pointwise D*J<=E_t*max(J,0) proves

    C_out<=N_gamma,  0<t*K(t)<=V_actual<=V_gamma.       (5.5)

The right bound follows from (5.2): integral_0^ell D<=A_mass*ell^3*exp(gamma*ell)/12, then multiply by K/2. Neither inequality determines whether C_out<=V_actual.

## 6. Strong source-specific lower bound for the FULL norm majorant

For every gamma>0 and A_mass>0, the SAME ACTUAL K and ell obey the following complete comparison. Assume

    t>=2,  ell>=max(1,4*K(1)/b).                      (6.1)

Because ell<t/4, the interval [ell,t-1] is nonempty. A genuine compact FTC calculation, using J_t=-(s*K(t-s))', gives exactly

    integral_ell^(t-1) J_t(s)ds
      =ell*K(t-ell)-(t-1)*K(1).                       (6.2)

Convex tangent at t, with t-ell>=0, gives

    K(t-ell)>=K(t)-ell*K'(t)=3*K(t)/4.                (6.3)

Since K(t)>=b*t, `(t-1)*K(1)<=K(t)*K(1)/b`. The threshold in (6.1) therefore yields

    integral_ell^(t-1) J_t >=[3*ell/4-K(1)/b]*K(t)
                             >=ell*K(t)/2,
    integral_ell^(t-1) max(J_t,0)>=ell*K(t)/2.          (6.4)

The last inequality uses J<=max(J,0); it does NOT claim J is pointwise positive throughout this interval. For every s in this interval, the whole terminal unit interval [t-1,t] lies inside [s,t]. Hence

    E_t(s)>=A_mass/2*integral_(t-1)^t u*exp(gamma*u)du
           >=A_mass*(t-1)*exp(gamma*(t-1))/2
           >=A_mass*t*exp(gamma*(t-1))/4.              (6.5)

Nonnegativity outside [ell,t-1], followed by (6.4), proves

    N_gamma(t)>=A_mass*t*ell*K(t)*exp(gamma*(t-1))/8.   (6.6)

This retains the FULL carrier and every endpoint. Restriction to the intermediate interval is used solely to lower-bound an already-admitted positive integral. No favorable signed cancellation is assumed, and the actual K(t) factor is kept until the next exact cancellation.

Divide (6.6) by the strictly positive V_gamma. Since ell>=1, ell<t/4, and t>=2,

    t+(A_mass/24)*ell^3*exp(gamma*ell)
      <=(1+A_mass/1536)*t^3*exp(gamma*t/4).

Therefore the explicit bound is

    N_gamma(t)/V_gamma(t)
      >= [A_mass*exp(-gamma)/(8*(1+A_mass/1536))]
           *exp(3*gamma*t/4)/t^2.                    (6.7)

Its constant is strictly positive. Exponential growth over a fixed polynomial tends to infinity. Actual ell->infinity supplies a fixed eventual threshold for (6.1), so

    N_gamma/V_gamma ->infinity as t->infinity,
    for EVERY fixed gamma>0 and A_mass>0.             (6.8)

The exact source K cancels. DISCARD as unnecessary the earlier possible prerequisites K(t)=exp(o(t)) and ell/t->0: only the certified positive-ray ell->infinity and global ell<t/4 are needed to reach the threshold and prove (6.7). No claim about their truth is retracted; this argument simply does not use them.

## 7. Independent terminal-lag lower bound, retained in full

The source-positive terminal mechanism is independently visible on the required lag interval r=t-s in [1/2,1]. Suppose

    t>=2,  t>=2*(1+K(1)/b).

Then s=t-r>=t-1, and K'(r)>=b, K(r)<=K(1) imply

    J_t(t-r)>=(t-1)*b-K(1)>=b*t/2.

This subinterval lies inside [ell,t], because ell<t/4. For r>=1/2 the interval [t-1/2,t] lies inside [s,t]; its length and t>=2 give

    E_t(s)>=A_mass/2*integral_(t-1/2)^t u*exp(gamma*u)du
            >=A_mass*t*exp(gamma*(t-1))/8.

The s-interval has length 1/2, so genuine integration gives

    N_gamma(t)>=A_mass*b*t^2*exp(gamma*(t-1))/32.      (7.1)

This full source terminal-lag bound is valid independently of (6.2)–(6.6). The stronger K-cancelling estimate (6.7) is chosen as the main survivor because it requires fewer asymptotic admissions. No terminal interval was silently removed from the audit.

## 8. Exact failure and surviving open premise

At any hypothetical sufficiently late (Z), (5.5) is true, while (6.7) implies N_gamma>V_gamma>=V_actual. Hence the sufficient absolute-envelope step `N_gamma<=V_actual` cannot prove M15 at such clocks. This is an obstruction to THAT bound, not a lower bound for C_out. We have only an UPPER estimate C_out<=N_gamma. It is invalid to reverse it or infer actual M15 failure, actual first-zero existence, or RH failure from N_gamma/V_gamma->infinity. The limit concerns explicit actual-source majorants defined on the whole positive ray, not an asserted sequence of actual zeros.

The stronger positive survivor is a fully quantified actual K cancellation law: (6.6), (6.7), and (6.8), together with exact compact p-independence (4.2). Its paper proof is complete here; independent review and any Lean allocation remain OPEN. Existing inner strict reserve/conditional continuation and full-alpha retention are preserved as previous paper survivors, not re-labelled new results.

What remains missing is an arithmetic orientation or cancellation estimate for the ACTUAL signed cost in (3.1)/(3.2) at every (Z). Unweighted Q ceilings, scalar score bounds, all positive raw moments, cumulative order, Gamma damping, and available absolute masses do not supply that mixed D-weighted inequality through any inspected mechanism. The precise remaining premise is M15 itself with full source and first-zero guard; no RH receiver is substituted for its proof. No finite-eta clock-window conclusion or growing-history inverse-positivity assertion is made.

## 9. Primary source evidence and full applicability checks

Paths below are under `formal/GaloisForLFunctions/` unless explicitly noted. Every relied new block was read, including proof bodies where the relevant property is private; previous unchanged full paper/source audits are reused rather than inferred from search metadata.

|Primary file / exact anchor|Checked role and boundary|
|---|---|
|`RHTower/LiEvenCrossActualClockBorelSource.lean:18–43`, `liEvenCrossActualClockBorelCoefficient`, `liEvenCrossActualClockBorelKernel`, `thetaCuspNormalizedEvenMoment_pos`, `_zero`|Actual full raw source, nu0=1, all-positive coefficients; both factorials and single R0.|
|`RHTower/LiEvenCrossActualClockBorelFlattening.lean:145–180`, `contDiff_liEvenCrossActualClockBorelKernel`, private `tf_nonneg`, `tf_K_lower`|Genuine all-order smoothness and complete positive derivative coefficients; K>=bt.|
|Same file:234–277, `tendsto_liEvenCrossActualClockBorel_second_div_deriv_zero` at241|K'/K->0 with positive K; gives actual ell->infinity, used in (6.8).|
|Same file:516–579, `tendsto_liEvenCrossActualClockBorel_deriv_logarithmicDegree_atTop` at558|Full weighted-series/prefix proof read; tK'/K->infinity is valid but unnecessary for new (6.7).|
|`RHTower/LiEvenCrossActualClockPrimitive.lean:177–218`, `_origin_even`, `abs_liEvenCrossActualClockPrimitive_le` at194|All Xi copies; genuine quadratic bound with exact actual strip gamma=1/300, including origin filling.|
|`RHTower/PrimeArchValuationSectorCones.lean:29–59`, `xiShiftAbsoluteMass`, `summable_xiShiftAbsoluteMass`, `_pos`|Full absolute mass is finite and strictly positive; no copy loss or invented supremum-strictness.|
|`RHTower/LiEvenCrossActualClockPrimitiveVolterra.lean:100–120`, `liEvenCrossActualClockPrimitive_volterra` at105|Exact factor-ONE identity (2.1), genuine continuous convolution.|
|`RHTower/LiClockThetaSignedGammaJumps.lean:24–54`|Literal ell_j, signed parts, both full measures/densities; degree0 zero weight.|
|Same file:591–674, `_LogJumpCoefficient_admission`, `_SignedGammaDensity_eq_primitive` at644|All p>1 coefficients/full row source; exact exp(-pu)P(u)/u and admitted complete sum before cancellation.|
|Same file:977–1008, `liClockThetaSignedGammaMeasure_admission`|All bounded measurable tests genuine L1 against BOTH carriers and signed density, including compact marks and costs.|
|Same file:683–719, private `sgWeighted_rowDensity_le`, `sgWeighted_density_summable`, and1202–1224, `liClockThetaGammaJumpDensity_admission`|Full genuine positive L1/withDensity and all-row norm sums; not asserted Jordan parts.|
|`RHTower/LiClockThetaGammaMixture.lean:37–63`, `liClockThetaGammaRowDensity`, `_GammaRowLaw`|Literal shape2j/ratep; j0 Dirac row retained then killed by actual jump weight; no rate/scale confusion.|
|`RHTower/PrimeArchThetaScoreMomentRecurrence.lean:92–154`|Actual scalar303 score recurrence; a raw moment bound, not signed history orientation.|
|`RHTower/PrimeArchThetaAllOrderCumulant.lean:84–135`, `normalizedPrimeArchMoment_recursive`|Actual Xi log recurrence with signed phase; no all-order positive-log inference.|
|`RHTower/PrimeArchThetaTwoAtomHankelDominance.lean:1–90`|Genuine full positive raw moment/Hankel carrier; differs from signed D/Gamma carrier.|
|`RHTower/CompleteHankelSignCone.lean:58–102,107–154`, `completeHankelCone_weightedMoment_iff_ae`|Finite measure, entire exp moments and bounded J hypotheses; ALL weighted-Hankel PSD iff sign. Those PSD hypotheses for actual signed history remain unproved.|
|`RHTower/ThetaRenewalIncrement.lean:84–132`|Different renewal primitive/origin, not literal P,D; its positive envelope cannot substitute.|
|`RHTower/ThetaCuspHawkingBMNativeCausalEquality.lean:197–232`, `covariance_volterra_unique`|Homogeneous vector P2 uniqueness, not positive inverse or M15.|
|`HTGeometry/VolterraConvolutionAlgebra.lean:18–34`, `volterraConv`|True orientation/continuous compact commutation; no signed correlation cone.|
|`RHTower/PrimeArchThetaRawMomentRatioVanishing.lean:102–128`|Actual arbitrary raw moment slope/fence; useful source admission, not log-sign bound.|
|Frozen683 C2–C6,C8–C14; frozen159 S1–S5; frozen608 U16–U18|Entire already-reviewed proofs/source domains reused unchanged. Their source correlation remains conditional/open; all endpoint terms and strict reserve kept.|

## 10. Corpus-first search and exhaustive retained-item dispositions

Direct commands, no help/source preparation:

```sh
scripts/formal_tools.py research "actual theta first zero signed Volterra D weighted outer history correlation source moment recurrence" --mode deep --budget-seconds 300 --json > /tmp/li_current_theta_m15_source_correlation_research.json
scripts/formal_tools.py research '"Volterra" "correlation"' --mode lexical --no-refresh --per-module 0 --explore 0 --json > /tmp/li_current_theta_m15_source_correlation_lexical_research.json
```

Owned deep session93764 TERMINAL exit0; elapsed84.908215709s. Capture183099 bytes, SHA `b0e4e1f38e5179261a486def76dcf43e8373f1442055b4e973e4e30432d95fbb`. Broadened lexical session44418 TERMINAL exit0; capture331 bytes, SHA `0bea83da11c7f8f5a64d2c4d9fed7f63bd944fdf55afa564879d75b4619fbbd9`.

ALL retained FULL records, statements/source statements, supplied proof excerpts, method objects and provenance were inspected: 20 candidate_lemmas C, 20 source_arguments S, one ingredient set I, 10 prose P, 10 source_passages T. No declarations, exploration, proof_ideas or markers were returned. One-based table indices below map exactly to JSON list order. There is no sampling. The secondary lexical report returned zero declarations/exploration/total/modules/eligible and empty markers; it has no coverage or compiler fields, so no missing semantic/compiler field is interpreted as exhaustive coverage.

Deep metadata: partial=false, errors=[], unfinished_stages=[], active_stage=finished; engine deep-5-coverage, FTS5 backend, retrieval_views=all. Eight round1 query traces were read: original query; actual theta; d weighted; moment recurrence; theta zero recurrence; signed Volterra correlation; weighted history moment; outer source recurrence. Original options AND/prefix expansion, per_module2, explore5, offset0, no module filter/exclusion, any=false, exact=false. All top-level fields, stage timings and runtime fields were read, including ready/available, Python/model versions/revisions/fingerprints/devices, offline/reason, running/PIDs/protocol/active/pending. No runtime service was operated.

Inventory63818/63818, pending_files0, indexed63818, inventory_complete=true, inventory_errors=[]; Lean53527/prose10291, declarations828548/documents2395365/vectors2243801. Index generation1172556; coverage snapshot generation1172565, current_generation1172566; snapshot_written_at1790843993.816101, status=snapshot, method_invalidation_pending=false, enrichment_counts_pending=true. Coverage compiler counts: compiled_snapshot43, error2, not_applicable10291, pending48129, stale2660, stale_snapshot38, umbrella_source_only1, unavailable2654. All 40 C/S records individually say file_status=indexed, compiler_status=source_only; compiled statements/axiom certificates are not supplied. Exact source used here was read directly; no compile validity is inferred from these records.

Warnings `coverage_snapshot_older_generation`, `semantic_coverage_unavailable`; semantic complete=null/status=not_measured/reason=reporting_budget; refresh complete=false/reason=background_indexer_running. First candidate7.000389959081076s. The automatic retrieval_assessment `model_suggests_sufficient_sources` is NOT accepted: I1 confuses prime Chebyshev theta_zero with actual theta and supplies generic moment definitions without the required bridge. Source applicability, not the model label, governs the verdict. No corpus-exhaustion, absence or novelty claim is made.

### C: all20 candidate lemmas

|Index|Exact source symbol and primary location returned|Disposition|
|---|---|---|
|C1|`RHTower.weightedMoment` — `formal/GaloisForLFunctions/RHTower/CompleteHankelSignCone.lean:62–66`|Generic signed weighted-moment definition. Fresh full primary sign-cone proof requires ALL weighted Hankel PSD inequalities; those actual D-history inequalities are missing. Receiver, not M15 producer.|
|C2|`Chebyshev.theta_zero` — `formal/.lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:160–163`|Prime-number Chebyshev theta at zero, not the actual completed theta kernel. Wrong observable; ingredient suggestion rejected.|
|C3|`GaloisForLFunctions.HTGeometry.weightMoment` — `formal/GaloisForLFunctions/HTGeometry/NonnegativeWeightMomentHankel.lean:25–28`|Generic nonnegative discrete weight moment. No literal signed D/history identification.|
|C4|`RHTower.fisherWeightedMoment` — `formal/GaloisForLFunctions/RHTower/FisherCurvatureMoment.lean:19–22`|Finite Fisher weight moment definition, different law; no source correlation orientation.|
|C5|`RHTower.deningerWeightedMomentFun` — `formal/GaloisForLFunctions/RHTower/DeningerWeightedMoment.lean:26–28`|Schwartz derivative-squared Deninger weighted moment, different quadratic positive carrier.|
|C6|`HTGeometry.ConstraintMotiveRelativity.weightMoment` — `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/MarkedMellinExchange.lean:633–637`|Marked Mellin character/log-atom moment, different operator and history.|
|C7|`RHTower.thetaXiPrimeModularCompactRecurrenceDescent_iff_index_zero` — `formal/GaloisForLFunctions/RHTower/IntegralCurvedTateFormationPropernessIndex.lean:195–203`|Properness/index-zero equivalence with source closure hypotheses; not a proof of this actual first-zero inequality.|
|C8|`RHTower.fisherWeightedTsumMoment` — `formal/GaloisForLFunctions/RHTower/FisherCurvatureMoment.lean:121–126`|Generic infinite Fisher-weight moment, no source bridge to D.|
|C9|`RHTower.thetaRenewalIncrement_zero` — `formal/GaloisForLFunctions/RHTower/ThetaRenewalIncrement.lean:114–125`|Renewal increment origin identity for a different P, origin Theta(1)/4. Fresh full source block read; not literal P(0)=0.|
|C10|`RHTower.thetaRenewalDriftCoord_zero` — `formal/GaloisForLFunctions/RHTower/ThetaRenewalSeamGerm.lean:206–209`|Renewal drift-coordinate origin identity, different clock.|
|C11|`RHTower.thetaLoopEnergy_zero` — `formal/GaloisForLFunctions/RHTower/ThetaRenewalFeedbackLoop.lean:262–265`|Renewal loop-energy origin identity, no D-weighted comparison.|
|C12|`RHTower.thetaRenewalLambdaCoord_zero` — `formal/GaloisForLFunctions/RHTower/ThetaRenewalSeamGerm.lean:203–206`|Renewal lambda-coordinate origin identity, different family.|
|C13|`RHTower.DeletionResidueMartingale.exists_historyProjection_eq_weighted_residue_quotient` — `formal/GaloisForLFunctions/RHTower/EulerDeletionWeightedResidueProjection.lean:149–172`|Finite weighted residue/history projection existence. Different residue carrier and conditional projection, not M15.|
|C14|`RHTower.deningerWeightedMomentMass` — `formal/GaloisForLFunctions/RHTower/DeningerAbelMajorant.lean:26–29`|Deninger Schwartz positive derivative-square mass, not the signed full primitive.|
|C15|`RHTower.weightedRawEvenMoment` — `formal/GaloisForLFunctions/RHTower/PrimeArchThetaTwoAtomHankelDominance.lean:36–39`|ACTUAL positive raw weighted theta moment. Full primary positive Hankel proof read; its raw carrier differs from D/Gamma history.|
|C16|`RHTower.HedenmalmThetaSource.thetaLpConj_zero` — `formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceDifferentialGreen.lean:2860–2867`|Hedenmalm Hilbert-conjugacy zero identity, not causal source sign.|
|C17|`RHTower.D4BMJointSource.covariance_volterra_unique` — `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeCausalEquality.lean:197–232`|Homogeneous vector covariance-Volterra uniqueness. Fresh full proof read; uniqueness does not preserve a signed inverse cone.|
|C18|`GaloisForLFunctions.HTGeometry.volterraConv` — `formal/GaloisForLFunctions/HTGeometry/VolterraConvolutionAlgebra.lean:19–23`|Exact generic Volterra orientation and continuous compact calculus. Admission only; primary definition/commutation read.|
|C19|`GaloisForLFunctions.HTGeometry.WeightedHistoryDatum.weightedHistoryAction` — `formal/GaloisForLFunctions/HTGeometry/WeightedHistoryCompletionBoundaryLaw.lean:299–303`|Finite graded weighted-history action definition, different history data.|
|C20|`RHTower.relVolterra_orientation` — `formal/GaloisForLFunctions/RHTower/LiClockPairedEtaPartitionRelativeVolterra.lean:187–195`|Exact paired-eta relative-clock orientation, different symmetrized normalization. Does not prove single-Xi actual M15.|

### S: all20 source arguments, including every supplied proof excerpt

|Index|Exact source symbol and primary location returned|Disposition|
|---|---|---|
|S1|`RHTower.l2Amplification_primeCoordinate_actualThetaPacket` — `formal/GaloisForLFunctions/RHTower/JointAncestryCriticalSingletonPrimeMultiplicationEscape.lean:210–223`|Tensor prime-coordinate actual-theta packet amplification, wrong observable.|
|S2|`GaloisForLFunctions.HTGeometry.gomesQubitOrbitDerivative` — `formal/GaloisForLFunctions/HTGeometry/GomesQubitOrbitConnection.lean:108–113`|Gomes qubit orbit derivative definition, wrong dynamical system.|
|S3|`RHTower.quantumStratonovichCayleyTransition_theta_eq` — `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingQuantumStratonovichBoundaryEndpoint.lean:242–254`|Theta quantum Stratonovich/Cayley transition, no literal P/D source inequality.|
|S4|`RHTower.HedenmalmThetaSource.thetaSourceSignedStageCorrection` — `formal/GaloisForLFunctions/RHTower/HedenmalmThetaActualStageGreenBalance.lean:22–26`|Finite signed theta-stage correction operator, not complete primitive/history.|
|S5|`GaloisForLFunctions.HTGeometry.gomesQubitOrbitBias` — `formal/GaloisForLFunctions/HTGeometry/GomesQubitOrbitTransport.lean:27–30`|Gomes qubit orbit bias, different carrier.|
|S6|`RHTower.thetaCuspComplexSource` — `formal/GaloisForLFunctions/RHTower/ThetaWignerCenterMix.lean:91–94`|Actual theta complex-source cast, analytic admission only.|
|S7|`RHTower.thetaCuspFullLogJetEight` — `formal/GaloisForLFunctions/RHTower/ThetaCuspFullReflectionEighthLogJets.lean:25–30`|Finite eighth full log-jet object; no all-order D-weighted bound.|
|S8|`RHTower.thetaCuspFullLogJetSix` — `formal/GaloisForLFunctions/RHTower/ThetaCuspFullReflectionSixthLogJets.lean:23–28`|Finite sixth full log-jet object; no moving history orientation.|
|S9|`RHTower.HedenmalmThetaSource.thetaSourceSignedStageFinMatrix` — `formal/GaloisForLFunctions/RHTower/HedenmalmThetaHermiteTraceFlag.lean:32–38`|Finite Hermite signed-stage matrix, different source operator.|
|S10|`GaloisForLFunctions.HTGeometry.gomesSSHCarrier` — `formal/GaloisForLFunctions/HTGeometry/GomesTwoBandAdjointMass.lean:22–26`|Gomes SSH two-band carrier, no theta D source.|
|S11|`RHTower.HedenmalmThetaSource.thetaSourceSignedStageMatrix` — `formal/GaloisForLFunctions/RHTower/HedenmalmThetaCanonicalSourceCellOddPoleCompletion.lean:35–40`|Canonical signed-stage matrix, not full P/history.|
|S12|`GaloisForLFunctions.HTGeometry.gomesFockPhase_vector_moments` — `formal/GaloisForLFunctions/HTGeometry/GomesFockQubitGauge.lean:27–37`|Full supplied Fock phase vector-moment proof excerpt; different Fock/gauge law.|
|S13|`GaloisForLFunctions.HTGeometry.gomesFockZeroPhase_vector_moments` — `formal/GaloisForLFunctions/HTGeometry/GomesFockQubitGauge.lean:60–70`|Full supplied Fock zero-phase proof excerpt; same mismatch.|
|S14|`RHTower.thetaBilateralLaplace` — `formal/GaloisForLFunctions/RHTower/ThetaTailFirstMomentKreinTransform.lean:20–24`|Actual bilateral theta Laplace definition, analytic admission only, no M15 sign.|
|S15|`RHTower.liEvenCrossActualClockBorelCoefficient` — `formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelSource.lean:18–22`|EXACT actual Borel coefficient with nu_j and squared factorial. Fresh primary definition read; source admission, no signed correlation bound.|
|S16|`GaloisForLFunctions.HTGeometry.egbFixedCharge_enthalpy_jump` — `formal/GaloisForLFunctions/HTGeometry/GaussBonnetCriticalEndpoint.lean:102–113`|Gauss-Bonnet fixed-charge enthalpy jump, different problem.|
|S17|`RHTower.continuous_thetaCuspSourceTerm_one` — `formal/GaloisForLFunctions/RHTower/ThetaCuspKernelLogConcavity.lean:870–876`|Actual first theta-atom continuity, source admission only.|
|S18|`RHTower.thetaCuspSchwartzReal_apply` — `formal/GaloisForLFunctions/RHTower/ThetaCuspSchwartz.lean:371–375`|Actual Schwartz representative identity, source admission only.|
|S19|`RHTower.ccmLocalPotentialLocalizationDefect_eq` — `formal/GaloisForLFunctions/RHTower/CCMThetaPhaseLocalPotential.lean:40–50`|Full ready IMS potential-localization method object, assumptions/steps/obligations/evidence read. It identifies a different quadratic Weil defect; no actual D-history comparison.|
|S20|`RHTower.ofReal_thetaCuspFullSourceReflectionEighthHankelCurvature_eq_generalModular` — `formal/GaloisForLFunctions/RHTower/ThetaCuspFullReflectionEighthGeneralModularClosure.lean:18–26`|Finite eighth general modular curvature identity, not full signed moving cost.|

### I: complete ingredient set

I1 `Theta zero identity and weighted moment definition`, status=not_verified: EVERY step read. It combines C2 prime Chebyshev theta_zero with C3 generic nonnegative weight moments, C4 Fisher moments and C5 Deninger derivative-square moments. These do not identify actual D, the full first-zero history, or psi. No input bound supplied is M15; no dependency-closed producer follows.

### P: all10 prose passages, full supplied text read

|Index|Exact returned passage|Disposition|
|---|---|---|
|P1|`docs/drafts/pipeline/2-fully-proven/theta/theta-compact-inverse-zero-jordan-history.md:2179–2263`|Archived compact theta inverse/core and tempered jets, different inverse; no M15 bound.|
|P2|`docs/drafts/pipeline/2-fully-proven/li-clock-cutoff-marking-boundary.md:492–562`|Prior actual cutoff-marking dispositions. Sign remains open, no new source producer.|
|P3|`docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md:3042–3131`|Recursive compact division/support localization metadata; no D-weighted source inequality.|
|P4|`docs/drafts/pipeline/2-fully-proven/theta/theta-compact-inverse-zero-jordan-history.md:3063–3148`|Full compact-history certification and unrelated two-Gaussian example. Different operator; not an actual-source counterexample to M15.|
|P5|`docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md:2720–2817`|Recursive Schwartz compact-test/support metadata; no orientation.|
|P6|`docs/drafts/pipeline/2-fully-proven/theta/theta-compact-inverse-zero-jordan-history.md:1688–1769`|Original compact theta inverse/core-extension metadata; different mechanism.|
|P7|`docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md:3662–3745`|Finite compact reconstruction cleanup, not actual moving correlation.|
|P8|`docs/drafts/pipeline/3-formalized/jas-critical-singleton-prime-multiplication-escape.md:1–42`|Prime Poisson multiplication/tensor escape, different observable.|
|P9|`docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md:6054–6141`|Recursive endpoint/source component reconciliation metadata; not M15.|
|P10|`docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md:5001–5091`|Generic tempered theta jet/core cleanup and global extension plan; no actual signed cost bound.|

### T: all10 source passages, full supplied text read

|Index|Exact returned passage|Disposition|
|---|---|---|
|T1|`formal/GaloisForLFunctions/HTGeometry/GomesFockQubitGauge.lean:1–77`|Full Fock phase/gauge moment block, different law.|
|T2|`formal/GaloisForLFunctions/RHTower/HedenmalmThetaActualFiniteDivisorRigidity.lean:1–72`|Finite-stage real-divisor rigidity. ASSUMES the real-divisor source law; RH receiver, not its producer.|
|T3|`formal/GaloisForLFunctions/HTGeometry/GomesFockQubitGauge.lean:73–149`|Full Fock zero-phase/rotation block, no literal D.|
|T4|`formal/GaloisForLFunctions/HTGeometry/GomesQubitOrbitTransport.lean:1–90`|Full Gomes qubit transport/Gibbs rotation block, wrong carrier.|
|T5|`formal/GaloisForLFunctions/RHTower/CCMThetaArithmeticLocalization.lean:165–179`|Weil IMS arithmetic localization block, a different quadratic source defect.|
|T6|`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalBaseCircleJets.lean:93–179`|Theta Hawking source-circle mixed derivatives/measurability; different observable.|
|T7|`formal/GaloisForLFunctions/RHTower/GomesClarkWeightedSource.lean:95–143`|Generic finite weighted Clark/Hausdorff source injectivity; no positive signed history orientation.|
|T8|`formal/.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean:235–335`|Mathlib weighted homogeneous polynomial algebra, no actual history bound.|
|T9|`formal/.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean:329–450`|Further homogeneous-component algebra, no source sign.|
|T10|`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalBaseCircleJets.lean:1–100`|Theta Hawking source-circle kinematics; no literal complete primitive inequality.|

## 11. Exhaustive target disposition and review boundary

|Target|Disposition|
|---|---|
|Literal actual single-Xi factorONE and D definition; full signed compact L1|Existing proved/source-read admission retained, no source substitution.|
|First-zero M15 itself|OPEN. No inspected corpus item, raw recurrence, unweighted Q residual or cost order closes actual mixed correlation.|
|Actual full-alpha Q retention/equality/strict deficit/optimal ceilings|Previously exhaustive paper audits reused unchanged; does not imply D-weighted retention.|
|Source compact Gamma correlation, both carriers and all endpoint terms|Exact existing683 identification retained; first-order order has a nonmonotone cost.|
|Both compact marked coefficientwise carriers independent of p>1|New exact paper identity (4.1)–(4.2), genuine full-sum/L1 admission supplied; independent review/Lean allocation pending.|
|Actual guard-aware terminal envelope and complete budget majorant|Dependency-closed paper (5.1)–(5.5), source gamma=1/300; independent review pending.|
|Strong K-cancelling majorant lower bound and explicit ratio infinity|Dependency-closed paper (6.1)–(6.8), EVERY gamma>0 for mathematical envelope comparison; independent review/Lean allocation pending.|
|Required terminal r in[1/2,1] mechanism|Complete admitted source bound (7.1), independent of stronger proof, explicit thresholds kept.|
|No-go for actual M15, existence of first zeros, RH or EVERY damping method|NOT claimed. Only this absolute-envelope sufficient step is rejected, plus exact damping invariance of marginals/costs.|
|Corpus applicability/coverage/compile validity/novelty|All61 retained records and all metadata processed; source-only qualifications explicit, no exhaustion or novelty claim.|

Final mathematical verdict: this direct source attack yields precise failure of its absolute-envelope mechanism and two nontrivial positive survivors, while the actual first-zero M15 correlation remains the sole unproved bound. No new Lean proof, route retirement, weaker receiver certification, or RH statement is made.

## Complete independent certificate and mandatory origin-smoothness clarification

# Independent complete M15 source-correlation paper/corpus audit

Verdict: **PASS for the exact dependency-closed paper survivors, with the explicit origin-smoothness clarification below. Actual M15, first-zero existence, literal undamped D sign and RH remain OPEN.** No Lean/formalization or failed-route closure is certified.

Independent reviewer: `/root/li_pole_audit`. Read-only audit; sole written artifact is this certificate. No compiler, new search, numerical experiment, source/tree/card edit or new agent. Symbolic constants were checked independently. Author evidence is evidence, not an independent certificate; this review supplies the independent gate.

## 1. Immutable scope and exhaustive coverage

Read ALL355 paper lines and every mathematical argument/equation in §§1–11; ALL61 complete unmodified raw research objects, including every supplied proof excerpt, full prose/Lean passage, ingredient step, generated method field and provenance/runtime/coverage field; ALL331 bytes of lexical report; ALL259 author-evidence lines; ALL27 complete retained primary blocks; and root's complete mathematical review after independent checks. No sampling. Previously independently audited unchanged full source bodies are reused under exact hashes, not inferred from index status.

The evidence companion was validated structurally in full: group its 61 `raw_record` objects by original section and position and merge `deep_full_metadata`; result equals the original parsed deep JSON exactly. Its lexical report equals original parsed lexical JSON. ALL6 frozen-input hashes/counts, ALL56 current file hashes/counts, ALL27 exact live-source slice bytes/block hashes and ALL20 passage provenance source hashes matched. The first metadata check reached all file/block checks before an optional-field KeyError at I1; a corrected optional-field check completed all20 provenance comparisons. This was metadata verification, not a proof or numerical experiment. No replacement research job was started.

Exact inputs:

|Artifact|Lines / bytes|SHA256|
|---|---:|---|
|`/tmp/li_current_theta_m15_source_correlation_attack.md`|355 / 39759|`9215912d5cfdb3d8a56afd0a9757cad6271c4401bcfe14d8639758a3447aa87f`|
|`/tmp/li_current_theta_m15_source_correlation_research.json`|1 / 183099|`b0e4e1f38e5179261a486def76dcf43e8373f1442055b4e973e4e30432d95fbb`|
|`/tmp/li_current_theta_m15_source_correlation_lexical_research.json`|1 / 331|`0bea83da11c7f8f5a64d2c4d9fed7f63bd944fdf55afa564879d75b4619fbbd9`|
|`/tmp/li_current_theta_m15_source_correlation_evidence.md`|259 / 52589|`268a6bb2d65ba1090db24baf0005083ed95b09db6c82081f6a0f07fa056b8beb`|
|`/tmp/li_current_theta_m15_source_correlation_evidence_metadata.json`|5198 / 362408|`88f6413e99cd517963143ac866c241e43db2eb18032590930f2213f9ff890954`|
|`/tmp/li_root_theta_m15_source_correlation_review.md`|35 / 5868|`38246b607a1942875c75b7f86381c26e4f506966b7a1338875b2fecb536ab3d0`|

Earlier full-paper scope reused without alteration: prior683 history-correlation paper `cf885634d37e11490bccba01b1ada3d8e9612deac2e400726709340fec5ec7d7`; full-alpha159 `a57b0b262cddd87067ff7c3f7f4d59259fefafad1e00e1b44aaa958ee7eda186`; undamped608 `815457a785a910206e21ad479fad5c09c1834506f6e11ac2e77967dea374c9fc`. All three current byte hashes match author evidence. These earlier proofs do not supply M15.

## 2. Section-by-section independent mathematical verdict

|Paper scope|Verdict and exact boundary|
|---|---|
|§1 frozen inputs/scope|PASS. Genuine source-specific investigation; no first-zero or RH assertion.|
|§2 literal definitions/origin/Volterra/retention|PASS with §3 clarification below. Raw factor2 and single R0 retained, ν0=1, two B factorials, K=B′, b=ν1/2=M0/2>0. D is integral of P/s, not P/t. Exact factorONE Volterra; no global signed-L1 assumption.|
|§3 actual M15/cost orientation gap|PASS. Guard (Z) is t>20, D(t)=0 and D(s)≥0 for every s∈[0,t]. Integration by parts retains complete outside history and its boundary. Nonmonotone cost blocks the inspected stochastic-order implication, not every possible correlated proof.|
|§4 separate compact marked-carrier invariance|PASS. All coefficient rows admitted before factoring; zero degree weight kills Dirac row. Both coefficientwise positive carriers invariant separately. Not Jordan parts; no global marked finite-mass claim; no universal ban on damping-dependent auxiliary estimates.|
|§5 actual envelope and terminal anchor|PASS. Actual complete-copy bound uses γ=1/300, A_mass=xiShiftAbsoluteMass0>0. Mathematical envelope calculations allow every γ>0; smaller γ is not asserted as a source bound. Genuine compact L1 before inequalities.|
|§6 complete K-cancelling lower bound|PASS. All thresholds, interval orientation, tangent, positive-part comparison, exact constants and K cancellation checked. ℓ→∞ suffices; no ℓ/t→0 or subexponential K premise.|
|§7 independent terminal-lag lower bound|PASS. Full interval r∈[1/2,1], both half-length factors and explicit t threshold retained. Independent of §6.|
|§8 inference/open premise|PASS. Lower bound is for Nγ, an upper envelope of Cout; cannot reverse Cout≤Nγ. Does not prove M15 false, any first zero exists or RH false.|
|§9 primary evidence|PASS, with exact C7/T2 precision in §7 below and full source/hash ledger. All applicable blocks read; previously complete-audited derivative/source bodies reused unchanged.|
|§10 corpus|PASS as scoped applicability ledger; automatic sufficient-source suggestion rejected. Complete raw61 read, compiler/semantic freshness limitations retained.|
|§11 status|PASS. New exact survivors PAPER-closed after this review; Lean remains unproved for this combination, actual sign remains OPEN.|

### Exact normalization, derivative and history checks

νj=Rj/R0, Rj=2∫₀∞x^(2j)k(x)dx, and B(t)=Σνj t^(2j)/[(2j)!]². Raw factor2 cancels only in ν, never changes the single-source normalizer or convolution factor. K(t) has first term bt with b=ν1/2; its cubic coefficient is ν2/144, so tK′−K has positive cubic contribution ν2 t³/72. Genuine entire derivative admissions and full coefficient positivity give K(0)=0, K′≥b, K″≥0, K(t)≥bt, K′ nondecreasing and strict tK′>K for t>0. Therefore 0<ℓ=K/(4K′)<t/4.

FINAL flattening gives K′/K→0, with K,K′>0 on t>0. Taking its positive reciprocal gives ℓ→∞. The stronger tK′/K→∞ is valid but unnecessary for §§6–7. A_mass is a full reciprocal-square multiplicity-copy absolute mass, not HistoryExcess B−1.

P′=F and P+P*K=tK. Substitute P(s)=sD′(s), integrate by parts on [0,t], and use D(0)=0,K(0)=0: boundary sD(s)K(t−s) vanishes at both endpoints. Thus

`P(t)=tK(t)+∫₀ᵗ D(s)[K(t−s)−sK′(t−s)]ds`.

At (Z), define J=sK′(t−s)−K(t−s). On [0,ℓ], convexity and nondecreasing K′ give K(t−s)−sK′(t−s)≥K(t)−2sK′(t)≥K(t)/2. Complete outside term Cout=∫ℓᵗD(s)J(s)ds is the missing signed cost. Integrating it by parts gives

`Cout=ℓD(ℓ)K(t−ℓ)+∫ℓᵗP(u)K(t−u)du`.

With compact marked carriers η±, cost ψ(u)=ℓK(t−ℓ) for 0<u≤ℓ and uK(t−u) for ℓ<u≤t, this equals ∫ψdη+−∫ψdη−. Each test is measurable, bounded after zero extension outside Ioc0t, and genuinely L1 against both finite marked carriers. At (Z), both masses coincide and are strictly positive; cumulative difference on [0,t] is D≥0. Yet ψ′(ℓ+)=H(ℓ)≥K(t)/2>0 whereas ψ′(t−)=−tb<0. The cost is not monotone. First-order dominance does not give its orientation; this does not exclude a source-specific mixed correlation proof.

## 3. Dependency-closed origin smoothness clarification (paper §2)

The displayed P=O(t²) alone proves a continuous filled quotient and C1 D, which already suffices for every integration by parts and compact admission used here. It does not alone prove C∞. Full claimed smoothness is nevertheless source-closed as follows.

FINAL `contDiff_liEvenCrossActualClockPrimitive` at Primitive168–175 proves the literal P is C∞ on all ℝ, from its entire complete cosine trace. FINAL `hasDerivAt_liEvenCrossActualClockPrimitive` at164–165 proves P′=F. Hence F is C∞. P is even, so differentiation at zero gives P′(0)=−P′(0), thus F(0)=0. No RH premise is used.

Define the genuine compact parameter integral

`Dens(s)=∫₀¹F(vs)dv`.

Oriented substitution u=sv gives P(s)=sDens(s) for every real s, including s<0; at s=0 both sides vanish. Thus Dens(s)=P(s)/s for s≠0, while Dens(0)=F(0)=0 equals the totalized quotient at zero.

For EVERY n≥0, parameter differentiation gives the exact formula

`Dens^(n)(s)=∫₀¹v^n F^(n)(vs)dv`.

Here is the full admission, including zero: fix any compact s interval I and choose M≥sup_I|s|. The joint maps (s,v)↦v^n F^(n)(vs) and their s derivatives v^(n+1)F^(n+1)(vs) are continuous on I×[0,1]. Continuous F^(n) and F^(n+1) have finite bounds on [−M,M]; because 0≤v≤1, these bounds are uniform integrable constant majorants on the finite interval [0,1]. Every individual integrand and derivative is genuinely L1. Dominated compact parameter differentiation applies on a neighborhood of every s, including0. Induct on n; no moving-domain majorant or unproved global L1 is needed.

Consequently Dens is C∞, the literal D(t)=∫₀ᵗDens(s)ds has D′=Dens by genuine FTC, and D is C∞ on ℝ. Its origin value remains0, and its O(t²) estimate follows from the existing primitive bound. This is an explicit clarification of the frozen355 assertion, not a new public/formal theorem or a modification of the frozen paper.

## 4. Complete compact Gamma marking: full sums, both parts and L1

For j≥1 put aj=(−1)^(j−1)M_(j−1)/(2j). Actual ℓj(p)=aj/p^(2j), with p>1. Gamma row density is p^(2j)u^(2j−1)e^(−pu)/(2j−1)! on u>0. Positive p powers allow max-scaling, so for each sign separately

`e^(pu) max(±ℓj(p),0)ρ_(p,j)(u)=max(±aj,0)u^(2j−1)/(2j−1)!`.

Degree0 has coefficient0 and therefore contributes neither density nor the row-law Dirac atom. All nonpositive-u rows are0. No atom is silently discarded.

Complete coefficient norm sums hold for p>1. Pointwise 0≤ρ_(p,j)(u)≤p follows the exponential-series bound and covers j0/u≤0 separately. Thus each sign's complete row sum is genuinely summable, bounded termwise by p|ℓj(p)|. Multiplication by a fixed finite e^(pu) preserves this summability. If an explicit comparison independent of p is wanted at a fixed u, use any one fixed p*>1 and its admitted rows; no uniform global-u estimate is asserted. Full tsum equality follows, not only finite-part cancellation.

The marked restriction to Ioc0t is finite and has genuine L1 density: e^(pu)≤e^(pt) there, and the unmarked full positive density is L1. Globally bounded extension of each compact test is available, so PUBLIC bounded-test measure identification never receives the unbounded negative-ray exponential as a bounded test. Full withDensity/set identity identifies η_(p,t)^± with the p-independent displayed densities. Therefore η_(p,t)^±=η_(q,t)^± for every p,q>1,t>0, separately. Their signed difference is P(u)/u on Ioc0t. These are coefficientwise parts, possibly overlapping; not Jordan parts. Compact equality does not claim global marked mass finite or prohibit p-dependent auxiliary proof estimates.

## 5. Actual source envelope and exact budget

Only source-admitted rate γ=1/300 (or larger) is applied to actual P:

`|P(u)|≤A_mass u²e^(γu)/2` for u≥0.

Genuine filled quotient yields |D(s)|≤(A_mass/2)∫₀ˢu e^(γu)du≤A_mass s²e^(γs)/4. At (Z), D(t)=0 gives 0≤D(s)≤E_t(s)=(A_mass/2)∫ₛᵗu e^(γu)du, for every s∈[0,t]. The terminal integral is properly oriented; no zero beyond the actual t is supplied.

All E,J,max(J,0) products are continuous on their finite domains and truly L1. Pointwise D J≤E max(J,0) gives Cout≤Nγ. Also

`0<tK(t)≤Vactual=tK(t)+(K(t)/2)∫₀^ℓD≤Vγ=K(t)[t+(A_mass/24)ℓ³e^(γℓ)]`.

The 1/24 is (1/2)*(1/4)*(1/3); no factor2 is missing. These are upper comparisons, not an estimate of signed Cout from below.

## 6. Independently checked strong K-cancelling survivor

Let γ>0,A_mass>0 be fixed. For mathematical majorants defined with the SAME actual K, assume t≥2 and ℓ≥max(1,4K(1)/b). Because ℓ<t/4≤t−1, [ℓ,t−1] is correctly oriented. Differentiate −sK(t−s) to obtain J exactly, hence

`∫_ℓ^(t−1)J=ℓK(t−ℓ)−(t−1)K(1)`.

Convexity on [t−ℓ,t] gives K(t−ℓ)≥K(t)−ℓK′(t)=3K(t)/4. Since K(t)≥bt, (t−1)K(1)≤K(t)K(1)/b. Therefore

`∫_ℓ^(t−1)max(J,0)≥∫_ℓ^(t−1)J≥[3ℓ/4−K(1)/b]K(t)≥ℓK(t)/2`.

No pointwise J≥0 claim on this whole interval is made. For every s∈[ℓ,t−1], terminal unit interval [t−1,t] is retained in [s,t], and its entire positive integrand gives E_t(s)≥A_mass t e^(γ(t−1))/4. Enlarge the nonnegative N integral only after these admissions:

`Nγ≥A_mass tℓK(t)e^(γ(t−1))/8`.

Strict K>0 and t>0 make Vγ>0. Exactly cancelling K before any growth comparison, and using ℓ≥1, ℓ<t/4, t≥2,

`t+(A_mass/24)ℓ³e^(γℓ)≤(1+A_mass/1536)t³e^(γt/4)`;

`Nγ/Vγ≥[A_mass e^(−γ)/(8(1+A_mass/1536))]e^(3γt/4)/t²`.

The constant is strictly positive. The exponential/polynomial quotient tends to∞. ℓ→∞ supplies every threshold eventually, so Nγ/Vγ→∞ on the WHOLE positive ray for every fixed γ>0,A_mass>0. Source domination remains qualified to γ≥1/300. No t-dependent DCT, K subexponential growth, ℓ/t→0 or sequence of actual first zeros is used.

## 7. Independent full terminal-lag survivor and source precision

For t≥2 and t≥2(1+K(1)/b), let r∈[1/2,1] and s=t−r. Then [t−1,t−1/2]⊆[ℓ,t] because ℓ<t/4. K′(r)≥b and K(r)≤K(1) give J(s)≥(t−1)b−K(1)≥bt/2. Terminal [t−1/2,t] is contained in [s,t]; there u≥t/2 and u≥t−1. Thus E_t(s)≥A_mass t e^(γ(t−1))/8. Integrating on a length1/2 interval yields

`Nγ≥A_mass b t²e^(γ(t−1))/32`.

Both half-length factors and the source b persist. This independently confirms majorant growth, without deleting near-terminal coordinates or reusing §6.

Two precise corpus-source clarifications preserve the correct disposition:

- C7's exact theorem has ONLY q:XiZeroCopy and states compact-recurrence-descent iff index0. It has no hclosure binder and proves neither branch. “With source closure hypotheses” in the frozen disposition means the still-missing branch needed to use the equivalence, not its exact parameter list.
- T2 includes an unconditional RH-or-nonreal-finite-stage dichotomy. Its RH implication requires all actual signed stages to have real divisors. The dichotomy does not select that branch; it is no M15 producer. Neither every T2 statement nor the entire passage is incorrectly called conditional here.

## 8. Complete independent corpus dispositions

Every record's full original fields/excerpts were read; the following are independent applicability verdicts, not compile claims. All40 C/S records are indexed/source_only, compiled_statement=null, axioms=null, compiler_metadata=null, applicability=not_checked. Stored C/S source_hash is record-local, not whole-file SHA. ALL20 P/T full provenance source hashes match live whole-file bytes; content hashes remain separate unchanged fields.

|Record|Independent disposition|
|---|---|
|C1|Generic signed weighted-moment receiver requires actual ALL-weighted PSD; no M15 producer.|
|C2|Chebyshev prime theta_zero; wrong theta observable.|
|C3|Generic nonnegative discrete weight moments; no literal D bridge.|
|C4|Finite Fisher weight definition; different law.|
|C5|Deninger Schwartz derivative-square moment; different quadratic carrier.|
|C6|Marked Mellin character/log-atom moment; different history.|
|C7|Exact q-only recurrence/index0 equivalence; proves neither branch, no D bridge.|
|C8|Generic Fisher weighted tsum moment; different carrier.|
|C9|Renewal increment at0=Theta(1)/4; not actual P(0)=0.|
|C10|Renewal drift-coordinate origin; different clock.|
|C11|Renewal loop-energy origin; different clock.|
|C12|Renewal lambda-coordinate origin; different clock.|
|C13|Finite weighted residue/history projection existence; different source.|
|C14|Positive Schwartz derivative-square mass; not signed primitive.|
|C15|ACTUAL raw weighted even moment, positive raw theta Hankel; not D-weighted history.|
|C16|Hedenmalm Hilbert-conjugacy zero identity; different source operator.|
|C17|Homogeneous vector P2 Volterra uniqueness; not positivity of inverse.|
|C18|Exact Volterra orientation/compact continuity admission; no source sign.|
|C19|Finite graded weighted-history action; different data.|
|C20|Paired-eta relative Volterra orientation; distinct symmetrized normalization.|
|S1|Actual-theta tensor prime-coordinate amplification; wrong observable.|
|S2|Gomes qubit orbit derivative; different dynamics.|
|S3|Quantum Stratonovich/Cayley theta transition; different carrier.|
|S4|Finite signed theta-stage correction operator; not complete P/D.|
|S5|Gomes qubit orbit bias; different carrier.|
|S6|Actual theta complex-source cast; analytic admission only.|
|S7|Finite eighth log-jet; no all-order signed-history bound.|
|S8|Finite sixth log-jet; no moving-history bound.|
|S9|Finite Hermite signed-stage matrix; different operator.|
|S10|Gomes SSH two-band carrier; different source.|
|S11|Canonical finite signed-stage matrix; not complete P.|
|S12|Full Fock phase moment proof; different Fock/gauge law.|
|S13|Full Fock zero-phase proof; same mismatch.|
|S14|Actual bilateral theta Laplace definition; admission only.|
|S15|EXACT full actual Borel coefficient, squared factorial; source admission only.|
|S16|Gauss-Bonnet enthalpy jump; different system.|
|S17|Actual first-theta-atom continuity; source admission only.|
|S18|Actual Schwartz source representative; admission only.|
|S19|Full ready IMS localization method, all assumptions/steps/obligations/evidence read; different Weil quadratic cost.|
|S20|Finite eighth modular curvature identity; no full moving signed cost.|
|P1|Archived actual compact theta inverse/core/tempered-jet history; different inverse.|
|P2|Prior cutoff-marking dispositions; overlapping known sign boundary, no new producer.|
|P3|Recursive compact division/localization metadata; different source mechanism.|
|P4|Compact-history certification/two-Gaussian comparison; not actual M15 counterexample.|
|P5|Schwartz compact-test/support metadata; no orientation.|
|P6|Compact inverse/core-extension metadata; no D cost.|
|P7|Finite compact reconstruction/cleanup; no actual correlation.|
|P8|Prime-Poisson character-multiplication escape; different observable.|
|P9|Endpoint/component reconciliation metadata; no M15.|
|P10|Tempered jet/core cleanup/global extension plan; no signed cost bound.|
|T1|Full Fock phase/gauge moment block; different law.|
|T2|Actual finite-stage real-divisor receiver plus unconditional dichotomy; no branch selection.|
|T3|Full Fock zero-phase/rotation block; different law.|
|T4|Full qubit transport/Gibbs rotation; wrong carrier.|
|T5|Weil IMS arithmetic localization; different quadratic defect.|
|T6|Hawking source-circle mixed derivative/smoothness admission; different observable.|
|T7|Finite weighted Clark/Hausdorff source injectivity; no sign orientation.|
|T8|Weighted-homogeneous polynomial support/mul/pow/induction; algebra, no D source.|
|T9|Weighted-homogeneous component/grading reconstruction; same mismatch.|
|T10|Hawking base-circle kinematics and mixed derivatives; different observable.|

I1: ALL two proposed steps and obligations read. Chebyshev prime theta_zero plus generic nonnegative/Fisher/Deninger moment definitions supply no actual completed-theta D-history bridge. Ingredient status not_verified, no proof ideas supplied. Reject automatic `model_suggests_sufficient_sources`. S19 is the sole nonnull generated method object: its full assumptions, steps, obligations, evidence, status/error/model/prompt/hash were read; “ready” labels another quadratic IMS identity, not M15.

Deep command was documented/direct before author source work, with author-reported owned terminal0 handle93764 and elapsed84.908215709s. Lexical handle44418 author-reported terminal0. I did not poll these historical handles or infer termination from file existence. Both complete raw captures retained. Eight round1 query traces and ALL stage/runtime/model/fingerprint/device/PID/offline/protocol metadata read; no service operated.

Deep partial=false, errors=[], unfinished=[], active_stage=finished, backendFTS5, engine deep-5-coverage, retrieval_views=all. Arrays20C/20S/1I/10P/10T; declaration/exploration/marker/proof-idea arrays empty. Original AND/prefix/per_module2/explore5/offset0/no exclusion options preserved. Inventory63818/63818,indexed63818,pending0,complete=true,error[]; Lean53527/prose10291; declarations828548,documents2395365,vectors2243801. Indexgeneration1172556; coveragegeneration1172565,current1172566,snapshot_written_at1790843993.816101. Compiler43compiled_snapshot/2error/10291NA/48129pending/2660stale/38stale_snapshot/1umbrella_source_only/2654unavailable. method_invalidation_pending=false,enrichment_counts_pending=true. Firstcandidate7.000389959081076s.

Warnings coverage_snapshot_older_generation and semantic_coverage_unavailable. Semantic complete=null,statusnot_measured,reasonreporting_budget; refreshcomplete=false,reasonbackground_indexer_running. Compiler snapshot is not a current whole-build certification; inventory completeness is not semantic completeness. Empty331-byte lexical AND report has no coverage fields and proves only no retained hit for that query, not source absence. No novelty, absence, corpus-exhaustion or global compiler applicability claim.

## 9. Primary source-block coverage and all fresh source hashes

All B01–B27 full retained blocks were independently read and byte-matched to live source, including actual EOF clipping of B19 to145. Some retained ranges include a neighboring partial declaration; no semantic claim about that partial declaration is inferred. Previously complete-audited unchanged full derivative/Gamma/primitive source bodies supply their dependencies. Additional fresh Primitive149–175 full derivative/smoothness proof read for §3. The exact source law is never replaced by a generic positive measure or synthetic clock.

|Block|Exact primary path/range|Independent admission/source disposition|
|---|---|---|
|B01|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelSource.lean:18–43`|Exact full source/normalizer, squared factorial, all nu positive and nu0=1.|
|B02|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelFlattening.lean:145–180`|Genuine all-order smoothness, full derivative positivity and K>=bt.|
|B03|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelFlattening.lean:234–277`|Exact Kprime/K limit; supplies ell→infinity.|
|B04|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelFlattening.lean:516–579`|Full logarithmic-degree proof read; this stronger degree escape is not needed in new K-cancelling envelope comparison.|
|B05|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockPrimitive.lean:177–218`|Complete-copy primitive, origin and actual gamma=1/300 full mass bound.|
|B06|`formal/GaloisForLFunctions/RHTower/PrimeArchValuationSectorCones.lean:29–59`|Full absolute mass definition, genuine summability and strict positivity.|
|B07|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockPrimitiveVolterra.lean:100–119`|Exact factor-ONE actual Volterra identity; true compact convolution.|
|B08|`formal/GaloisForLFunctions/RHTower/LiClockThetaSignedGammaJumps.lean:24–54`|Exact actual log coefficient, coefficientwise parts, full Gamma measures/densities.|
|B09|`formal/GaloisForLFunctions/RHTower/LiClockThetaSignedGammaJumps.lean:168–204`|Full coefficient part domination/summability; neither Jordan parts nor sign assumptions.|
|B10|`formal/GaloisForLFunctions/RHTower/LiClockThetaSignedGammaJumps.lean:591–674`|All-coefficient admission and exact complete exp(-pu)*P/u source identity.|
|B11|`formal/GaloisForLFunctions/RHTower/LiClockThetaSignedGammaJumps.lean:681–721`|True all-row pointwise bound0<=row<=p and complete density summability before factoring.|
|B12|`formal/GaloisForLFunctions/RHTower/LiClockThetaSignedGammaJumps.lean:977–1008`|Every bounded measurable test has genuine L1 against BOTH positive carriers and signed density.|
|B13|`formal/GaloisForLFunctions/RHTower/LiClockThetaSignedGammaJumps.lean:1202–1224`|Genuine full positive density L1/withDensity/all-row norm sums.|
|B14|`formal/GaloisForLFunctions/RHTower/LiClockThetaGammaMixture.lean:37–63`|Literal Gamma shape2j, RATEp, j0 Dirac row; degree jump weight0 kills row0.|
|B15|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaScoreMomentRecurrence.lean:92–151`|Actual full scalar303 raw score recurrence; no signed history orientation.|
|B16|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaAllOrderCumulant.lean:84–135`|Actual signed all-order Xi log recurrence; raw/log distinction.|
|B17|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaTwoAtomHankelDominance.lean:1–90`|Positive raw theta Hankel carrier distinct from signed D/Gamma history.|
|B18|`formal/GaloisForLFunctions/RHTower/CompleteHankelSignCone.lean:58–102`|Generic weighted moment/true integral domain; no actual PSD proof.|
|B19|`formal/GaloisForLFunctions/RHTower/CompleteHankelSignCone.lean:107–145`|Complete conditional sign-cone iff, continuous version and genuine assumptions; requested interval clipped at actual EOF.|
|B20|`formal/GaloisForLFunctions/RHTower/ThetaRenewalIncrement.lean:84–132`|Different renewal primitive and nonzero origin; no substitution into actual P.|
|B21|`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeCausalEquality.lean:197–232`|Homogeneous vector Volterra uniqueness; not positivity of inverse.|
|B22|`formal/GaloisForLFunctions/HTGeometry/VolterraConvolutionAlgebra.lean:18–34`|Literal convolution orientation and continuous compact commutation.|
|B23|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaRawMomentRatioVanishing.lean:102–128`|Actual raw score fence/ratio interface, no all-log/history sign.|
|B24|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaCumulantMinor.lean:439–478`|Exact M0=nu1, actual normalized moments and first cumulant relation; prior full source audit reused with unchanged hash.|
|B25|`formal/.lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean:152–165`|Fresh exact prime-Chebyshev theta_zero check; wrong theta for ingredient I1.|
|B26|`formal/GaloisForLFunctions/RHTower/IntegralCurvedTateFormationPropernessIndex.lean:178–206`|Fresh exact C7 q-only equivalence; neither branch concluded, no M15/D bridge.|
|B27|`formal/GaloisForLFunctions/RHTower/HedenmalmThetaActualFiniteDivisorRigidity.lean:29–71`|Fresh T2 implication requires all-stage real divisors; unconditional dichotomy does not select them.|

Whole-file hashes below certify byte freshness only for unrelated modules; semantic review covers their ALL returned excerpts, not every theorem in entire unrelated files. For used actual primary dependencies, the relevant source bodies were read or unchanged full prior audits reused. C/S extraction hashes are never substituted for this table.

|Key|Exact current path|SHA256|
|---|---|---|
|F01|`docs/drafts/pipeline/1-in-progress/stage-two-recursive-unconditional-formalization.md`|`33d0a5bdcba09f5e1c72b8cc6abcc402a938f6cab01fe89ecca971ce4e1faeef`|
|F02|`docs/drafts/pipeline/2-fully-proven/li-clock-cutoff-marking-boundary.md`|`aa112469013a731e72cc52a17ae6f295d2684d2d4b22a78f18d5d6485b975f48`|
|F03|`docs/drafts/pipeline/2-fully-proven/theta/theta-compact-inverse-zero-jordan-history.md`|`9c582377feed839511bfa6d9aa7f28e8e4bdb0e53f9ffe09ca76a48aeed20190`|
|F04|`docs/drafts/pipeline/3-formalized/jas-critical-singleton-prime-multiplication-escape.md`|`0ab34ce383931053706c919ff8f255f3b28bd4d1243f5a4fe0879d9dc56d2a42`|
|F05|`formal/.lake/packages/mathlib/Mathlib/NumberTheory/Chebyshev.lean`|`7660e466d974683ab0ed75ed5ee2d2e0f899d9dd7f755c419392904f711edf94`|
|F06|`formal/.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/WeightedHomogeneous.lean`|`9fa09f4ed3906b58fdbf40d804ebb74844a5876d861786ce7287002d6cf0a14c`|
|F07|`formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/MarkedMellinExchange.lean`|`3ec544d10b94a0100e3e787ac4ebbfd2daa4770beb807e795fe121ae3e506825`|
|F08|`formal/GaloisForLFunctions/HTGeometry/GaussBonnetCriticalEndpoint.lean`|`f45f151dc0cbb5a86fd89c307e3d132d3ba154f07da47ff4adfb7d1fd08c1082`|
|F09|`formal/GaloisForLFunctions/HTGeometry/GomesFockQubitGauge.lean`|`22b8d342244d03e2dd6335fc3fa1b0ba953ca7bede7446c15224fc53c477471c`|
|F10|`formal/GaloisForLFunctions/HTGeometry/GomesQubitOrbitConnection.lean`|`8d45ff0a1282e691c5166c7333e711a950cca160907c32ce743b32a2eb53d942`|
|F11|`formal/GaloisForLFunctions/HTGeometry/GomesQubitOrbitTransport.lean`|`06d2b9b044d0803b31915544d20559a1171952b4e27601767d3055b5a3026db8`|
|F12|`formal/GaloisForLFunctions/HTGeometry/GomesTwoBandAdjointMass.lean`|`0aa52e63612297ee47b0078af49aa958ca07bcba1fd540b15512996c3841a78b`|
|F13|`formal/GaloisForLFunctions/HTGeometry/NonnegativeWeightMomentHankel.lean`|`7de8284fe0d0b2d41c7b767a08e2261b27d7ef682667031ebc0993dad5c206c8`|
|F14|`formal/GaloisForLFunctions/HTGeometry/VolterraConvolutionAlgebra.lean`|`520f645d1fe538c5934c37d5c74d98c4b99a4aad1e0d5bea1799e5bb220e064a`|
|F15|`formal/GaloisForLFunctions/HTGeometry/WeightedHistoryCompletionBoundaryLaw.lean`|`ecaf0d4b5e30f07dbcf3971886c932628d226a36344cf8015979e8c7bc03c922`|
|F16|`formal/GaloisForLFunctions/RHTower/CCMThetaArithmeticLocalization.lean`|`3f8588ab3e2539f301e2e930b6f7887c01812afb4c53ed9359d9a2df11dcf2ad`|
|F17|`formal/GaloisForLFunctions/RHTower/CCMThetaPhaseLocalPotential.lean`|`f18675c620e660547d8cb49b307556ef5724cef40237a53b6f402e74d5b69109`|
|F18|`formal/GaloisForLFunctions/RHTower/CompleteHankelSignCone.lean`|`9c0e07606162a4359235f10464261ef38c8641bbfd1d5abc8e1e5b72440451fe`|
|F19|`formal/GaloisForLFunctions/RHTower/DeningerAbelMajorant.lean`|`24f1133e266465622c9ef333212cb4d9fc8e388f29297f4459339da2cce5c1b5`|
|F20|`formal/GaloisForLFunctions/RHTower/DeningerWeightedMoment.lean`|`bbd5a77dd353e31288c2fa8491c93a7ce82c4d7e0137a7ae4a049cf43c4fe700`|
|F21|`formal/GaloisForLFunctions/RHTower/EulerDeletionWeightedResidueProjection.lean`|`b255f2789c337a322a82ee9da1707276771cd67758c2a3cc084259415080dfe8`|
|F22|`formal/GaloisForLFunctions/RHTower/FisherCurvatureMoment.lean`|`0717fca8fa16883fe82a46b2e6034450da9356dc858a666a1b75d0a40b0811c6`|
|F23|`formal/GaloisForLFunctions/RHTower/GomesClarkWeightedSource.lean`|`da5f57ae16a95f4b3065e2551ade8008108753fbc2935dbbc219ac9ae577b767`|
|F24|`formal/GaloisForLFunctions/RHTower/HedenmalmThetaActualFiniteDivisorRigidity.lean`|`3fd92e46b5e63aa740e699890fe1ca3308956da445d52b618dcf714b1cd98d3c`|
|F25|`formal/GaloisForLFunctions/RHTower/HedenmalmThetaActualStageGreenBalance.lean`|`4ab0a3d7d5248fdf278a84062c28a7bd36adbe2342a7e9f032e112f21fe03831`|
|F26|`formal/GaloisForLFunctions/RHTower/HedenmalmThetaCanonicalSourceCellOddPoleCompletion.lean`|`903734d574a951919a452adb3104382989adf5137a2e82e92d7d2ee73cfc6521`|
|F27|`formal/GaloisForLFunctions/RHTower/HedenmalmThetaHermiteTraceFlag.lean`|`5618af6fb8cd45b564e2e63646d06e2b0d279f662622083adf8d67b3ee2baefd`|
|F28|`formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceDifferentialGreen.lean`|`9708ac7a8a49fa029a780db048fd33ae2b29598dcdc3f51d6a5a4e3f3c2c0756`|
|F29|`formal/GaloisForLFunctions/RHTower/IntegralCurvedTateFormationPropernessIndex.lean`|`81ce420d43650e1dd64ed6a09b29c22f619eea999a5eff623132cd6d4b7be621`|
|F30|`formal/GaloisForLFunctions/RHTower/JointAncestryCriticalSingletonPrimeMultiplicationEscape.lean`|`792a7cf225b238915cfe651b2551a62a1dbb7036dc7f23abb1ef90f24d6d49d3`|
|F31|`formal/GaloisForLFunctions/RHTower/LiClockPairedEtaPartitionRelativeVolterra.lean`|`f4c09695e01372445880b744327bb4367df98ecb5dea36319e1323e109a8e4e0`|
|F32|`formal/GaloisForLFunctions/RHTower/LiClockThetaGammaMixture.lean`|`f276f4f6b3267f00e45832ebd8a3e5b4cc0a5e9f0d560bbf4f3c74f9e1e20c85`|
|F33|`formal/GaloisForLFunctions/RHTower/LiClockThetaSignedGammaJumps.lean`|`fdda232106c1dd11b7226566691396024ce05286ed7a09f16fa261a0de0c6b9d`|
|F34|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelFlattening.lean`|`ccdf4a14032fbc30aa427f40afe611691639a696fb6d613ab4bb083521eb6445`|
|F35|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockBorelSource.lean`|`1eb4512abdbfc56ad3aa07ff3be0b10c157d58d81a92a03ccb26add83665420f`|
|F36|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockPrimitive.lean`|`19432a2d8b80329be82c8d500b1aeca07cb7f34afaf81f6a747d39275e3a8590`|
|F37|`formal/GaloisForLFunctions/RHTower/LiEvenCrossActualClockPrimitiveVolterra.lean`|`50d3f834eea44fca75ac77820a912f7d6edb9f9b57e9f359d809e1b8889a3787`|
|F38|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaAllOrderCumulant.lean`|`c4c5e670baba79e8fd8dd973c62e434cdbded47ff09a4bf7db964ad0b0b27bbf`|
|F39|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaCumulantMinor.lean`|`aa6f9e7531322c7723180d4cfde4c94c73276b91027850b74d506c1d11f62040`|
|F40|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaRawMomentRatioVanishing.lean`|`affa6c769ed9b28d3d887ddf9ea2490919299b8cacb8346c795028cf0fb20b26`|
|F41|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaScoreMomentRecurrence.lean`|`3d36927db3df83b1c9cc57db8ee1bc0da1c753440072fc12fa5fdab624f1fe1d`|
|F42|`formal/GaloisForLFunctions/RHTower/PrimeArchThetaTwoAtomHankelDominance.lean`|`3aa9597aec7e8563499cafdacea5e98ba5ce9c8df17171af81aca4a407e0dae8`|
|F43|`formal/GaloisForLFunctions/RHTower/PrimeArchValuationSectorCones.lean`|`5170f88070589bfdfb0d210f4a7c0e7c673e7e30fc6adabac4b3d955707ce487`|
|F44|`formal/GaloisForLFunctions/RHTower/ThetaCuspFullReflectionEighthGeneralModularClosure.lean`|`e11be4e54eaef3248e0cc3596d68ef9da1a228a081dc43d59cb1bbd8ec1feff6`|
|F45|`formal/GaloisForLFunctions/RHTower/ThetaCuspFullReflectionEighthLogJets.lean`|`c5e6902d38a2b3db8acaa1e88fb4e0bb02c6bab52ff4fb9e8a786e6e885c3a9f`|
|F46|`formal/GaloisForLFunctions/RHTower/ThetaCuspFullReflectionSixthLogJets.lean`|`f02d0a1bbd4a78ba0c80fed9e8e865be132b3b60f077b68cd90f2ef4cd809c91`|
|F47|`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMNativeCausalEquality.lean`|`e5ef18e925d51456213f49dbb57647023c2dea4de048043a4640d3dce525ff0a`|
|F48|`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalBaseCircleJets.lean`|`5b4b740e9ae7544c17ea4c274d05f705e05ebd32fc650633b9ab77e04c86f4a6`|
|F49|`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingQuantumStratonovichBoundaryEndpoint.lean`|`2f6b94eabe734e8b7da6bc8f978acd45109b44b58232eb06bcf8dd684b12a7b9`|
|F50|`formal/GaloisForLFunctions/RHTower/ThetaCuspKernelLogConcavity.lean`|`ee14392e0ab7cae26aab7148d64cd8f22103276f4606f489fd1b48efdb5ca41b`|
|F51|`formal/GaloisForLFunctions/RHTower/ThetaCuspSchwartz.lean`|`d58cc3761cb4628501db2bd846f393de6b495f2b7b73aa89d39fca0bd70ec76e`|
|F52|`formal/GaloisForLFunctions/RHTower/ThetaRenewalFeedbackLoop.lean`|`ef6f65b3d9228cd981e4f62764ae496fddedfe6cd0c79a49a6832a1513c3adf9`|
|F53|`formal/GaloisForLFunctions/RHTower/ThetaRenewalIncrement.lean`|`01f431568b3d368e7e84a185cb071f2fd9b1a0c26487defd473bdbadb14a7d38`|
|F54|`formal/GaloisForLFunctions/RHTower/ThetaRenewalSeamGerm.lean`|`333a7294ed6ac6a6f90136e88cfda79632c5a8b03b2e9b45ddd7b9ad2a72cea8`|
|F55|`formal/GaloisForLFunctions/RHTower/ThetaTailFirstMomentKreinTransform.lean`|`5489a69b1081328e5becd37880d0e368422b99837c3b2fe2b47a528261ed651d`|
|F56|`formal/GaloisForLFunctions/RHTower/ThetaWignerCenterMix.lean`|`4f302a6463f853cd7ee7896f7ca3e5cbcef097ca0b05456b753cc5ad8e608a3d`|

## 10. Strongest accepted survivor and exact remaining task

PAPER PASS for BOTH separate compact marked-carrier invariances, genuine guard-aware actual source envelope/budget, exact full K-cancelling majorant lower bound/explicit ratio→∞, and independent complete terminal-lag lower bound. Origin smoothness is now fully dependency-closed by §3. Every factor/multiplicity/domain/L1 admission needed by these statements is retained.

Eventually Nγ>Vγ≥Vactual at any hypothetical late (Z), so this particular sufficient absolute-envelope step Nγ≤Vactual cannot work there. Since Cout≤Nγ is only an upper estimate, it cannot be reversed. No actual first-zero existence, no Cout>Vactual, no M15 failure, no RH outcome, no finite-eta growing-window sign, and no universal failure of damping-based auxiliary proofs follow.

Precise unresolved arithmetic statement remains: for EVERY t>20 with D(t)=0 and D(s)≥0 for ALL s∈[0,t], prove the complete literal signed correlation

`∫_ℓᵗD(s)[sK′(t−s)−K(t−s)]ds ≤ tK(t)+(K(t)/2)∫₀^ℓD(s)ds`.

Equivalent marked-cost source formulation is retained with both full coefficientwise carriers, actual ψ and actual first-zero guard. Unweighted Q ceilings, raw-positive Hankel matrices, signed log recurrence, cumulative ordering, compact p-invariance and absolute-envelope domination do not prove this through any inspected mechanism. The newly audited positive survivors require future full Lean implementation/gates before no-go closure or formalized status; this certificate is independent PAPER/source/corpus acceptance only.
