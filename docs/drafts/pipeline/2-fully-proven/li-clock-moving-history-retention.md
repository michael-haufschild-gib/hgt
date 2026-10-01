# Actual theta moving-history retention and age escape

- **ID:** LI-CLOCK-MOVING-HISTORY-RETENTION
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** [active integrated-source route](../1-in-progress/li-clock-integrated-source-sign.md)
- **Statement:** For actual K=B', m=tK'/K satisfies m³/t²→0. The actual scale ell=K/(4K') obeys ell/t→0 and ell³/t→infinity, retaining the full favorable history coefficient at least K/2 on [0,ell]. The complete normalized age measure has exact factorial moments, escapes every fixed age interval, and concentrates below every fixed clock fraction.

## Goal

Control the actual full signed history in the undamped cutoff D0. These
positive conclusions expose a growing favorable interval and the complete
age distribution. The remaining D/J correlation is OPEN. The later
[correlation boundary](../3-formalized/li-clock-history-correlation-boundary.md) proves strict
continuation conditional on original nonstrict M15; no unconditional D0/RH sign.

## Gates

- [x] 0 → 1: literal single-Xi source, normalization and complete admissions.
- [x] 1 → 2: [PROVED HERE], ALL381 root/independent review plus mandatory domain addendum.
- [ ] 2 → 3: exact new retention, probability, moment and escape conclusions in Lean.
- [ ] 3 → 4: publication and external novelty audit.

## Approach and exact boundary

The full positive odd-degree posterior converts the installed arithmetic
Ward bound tK'''/K→0 into cubic degree control, retaining its degree1 term.
Convexity then yields the growing retention window. Actual age density
K(t-s)/(B(t)-1) has a complete Beta mixture and exact two-factorial moments.
Fixed-age and fractional-age limits keep every source row and their stated
order of limits. No concentration claim at the moving ell scale follows.

The sign attempt stops at paper M15 (or a sharper proof of M13). The later
dual-reviewed683 paper proves a quantitative strict crossing argument from
nonstrict M15 and rules out concentration below ell by an optimal7/16 ceiling.
Actual M15/D sign remains open; no RH route is retired. New positive survivors
M3–M12 and the later exact rigidity/crossing results require Lean formalization.

## Evidence and mandatory clarification

- Frozen381 author SHA256 `6c3efaf5fb66d01173ca4a0c906e2cefd88f898c60d4ddff115f803cf9e37996`, preserved verbatim below.
- Root ALL381 review: `/tmp/li_root_theta_moving_history_review.md`.
- Independent ALL208 certificate: `/tmp/li_producer_theta_moving_history_audit.md`, SHA256 `1cf240c640d8e679828b73a03a9418ab63b7fc12767d591b20936a139725daa9`; read entirely by root.
- Mandatory13-line addendum SHA256 `017dedc518a15c26b241bc26d0d0c217e247cfa159611e471b954e6b714af616`, preserved below the original paper. The auxiliary cumulative-J inequality requires 0<=x<=t; numbered claims remain unchanged.
- Both reviewers checked actual primary source. The replaced deep JSON is unavailable: raw retrieval metadata and original excerpt-reading completeness are author-reported. All listed dispositions were audited; no exhaustive-corpus or worldwide-novelty claim.
- 2026-10-01 — dependency-closed positive paper survivor recorded; new Lean work and RH remain OPEN.

---

# Actual theta moving-history attack: arithmetic-generated retention window

Mode: PAPER / read-only source investigation. One objective: literal
D_0(T)>=0 from the complete actual theta source. No compiler, numerical
experiment, new agent, Lean/tree/card edit or RH conclusion in this task.
Verdict: attempted full-history comparison FAILED to orient D_0. The
source-adapted growing retention window and the exact normalized age law
below are nontrivial positive paper survivors, pending independent audit.
No route is retired. All statements concern the literal single-Xi source.

## 1. Source, constants, domains and unchanged prior claims

Write nu_j=thetaCuspNormalizedEvenMoment j=R_j/R_0, with literal complete
raw theta integral R_j, R_0>0. Then nu_0=1 and nu_j>0 for every j. Set

 B(t)=sum_(j>=0) nu_j t^(2j)/((2j)!)^2,
 K(t)=B'(t), A(t)=B(t)-1,
 P(t)=liEvenCrossActualClockPrimitive t,
 D(t)=integral_0^t P(s)/s ds, with the origin value filled by continuity.

The factorial score envelope and complete ordinary derivative ladder
admit all these full series on every compact real interval. For t>0,
A(t)>0, K(t)>0, K'(t)>=b>0, K''(t)>=0, where
b=K'(0)=nu_1/2=normalizedPrimeArchMoment 0/2. K(0)=P(0)=D(0)=0;
P(t)=b t^2+O(t^4), D(t)=b t^2/2+O(t^4). No half multiplicity,
eta partition normalizer, factor TWO or alternative theta density enters.

The actual factor-ONE Volterra law and its admitted compact IBP are

 P(t)+integral_0^t P(s)K(t-s)ds=tK(t),                 (M1)
 tD'(t)=tK(t)+integral_0^t D(s)[K(t-s)-sK'(t-s)]ds.    (M2)

For M2, P(s)=sD'(s), and the boundary product sD(s)K(t-s)
vanishes at BOTH ends. All integrands are genuinely continuous on the
compact interval; P(s)/s extends continuously at zero. The earlier
complete causal-history608 paper proves these identities and admissions.
This investigation does not replace its infinite causal series by a prefix.

Fresh source inputs, all under formal/GaloisForLFunctions/RHTower:

|Input|Exact symbol/range and use|
|---|---|
|Literal B|LiEvenCrossActualClockBorelSource.lean:18,22,26; nu positivity33, zero37, factorial envelope42, coefficient positivity64. All normalized nu, both factorials retained.|
|Complete first derivative|LiEvenCrossActualClockBorelCorrection.lean:177 liEvenCrossActualClockBorel_deriv_series; exact origin389 liEvenCrossActualClockBorelCorrection_origin. Its full quartet was read; K'(0)=nu_1/2.|
|Ordinary derivatives|LiEvenCrossActualClockBorelFlattening.lean:126 tf_iteratedDeriv, :137 tf_hasDerivAt_iterated, :147 contDiff_liEvenCrossActualClockBorelKernel, :163 tf_nonneg. Previously exhaustive589 audit reused after exact hash verification; applicable126–218 freshly read.|
|Arithmetic cubic control|Same Flattening:206 tendsto_liEvenCrossActualClockBorel_clock_fourth_div_deriv_zero: t B''''(t)/B'(t)->0. This is tK'''/K->0, with actual correction ratio source proof and genuine positive denominator. Full body read.|
|Derivative degree escape|Same Flattening:558 tendsto_liEvenCrossActualClockBorel_deriv_logarithmicDegree_atTop: tB''/B'->infinity. Full K-prefix, weighted-series and escape proofs465–587 read.|
|Fixed-age ratios|Same Flattening:356 tendstoUniformlyOn_liEvenCrossActualClockBorel_deriv_shift_ratio, full public caller read; :423 tendsto_liEvenCrossActualClockBorel_deriv_div_kernel_zero, full body read. These are K(t+s)/K(t)->1 uniformly on each FIXED compact shift set, and K/B->0.|
|Full prefix escape|LiEvenCrossActualClockBorelGrowth.lean:42 liEvenCrossActualClockBorelPrefix_div_kernel_tendsto; ALL144 source read. Every fixed polynomial prefix is negligible, full remaining positive sum retained.|
|Literal P and law|LiEvenCrossActualClockPrimitive.lean:23 definition, :163 derivative, :168 smoothness, :178 origin; unchanged235 previously whole audited. PrimitiveVolterra.lean:106 liEvenCrossActualClockPrimitive_volterra, ALL119 freshly read; literal factor ONE and compact admissions.|
|M0 normalization|PrimeArchThetaCumulantMinor.lean:449 normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment; full439–462 read.|

Source hashes verified in this task:
- BorelSource276: 1eb4512abdbfc56ad3aa07ff3be0b10c157d58d81a92a03ccb26add83665420f.
- BorelGrowth144: e3cf9930d0d0871ba12fcad631492910ad7df20e798734840b31067be824ffdb.
- Flattening589: ccdf4a14032fbc30aa427f40afe611691639a696fb6d613ab4bb083521eb6445.
- Correction501: 0da5eeaa9ef72d2545fe3f3a543acce9c88acb17bec734b9c052c4fa13c0e646.
- Primitive235: 19432a2d8b80329be82c8d500b1aeca07cb7f34afaf81f6a747d39275e3a8590.
- PrimitiveVolterra119: 50d3f834eea44fca75ac77820a912f7d6edb9f9b57e9f359d809e1b8889a3787.
- Frozen608: 815457a785a910206e21ad479fad5c09c1834506f6e11ac2e77967dea374c9fc.
- Frozen609: f0a69b3cd1729e7ad9a8eb3620904c5b91078b122e1e5d72d178a9bdff6b30fa.

Both earlier papers remain untouched and already fully independently
audited. Only their applicable admitted identities are reused here.

## 2. Attempt: retain a genuinely growing favorable source window

Expand the actual positive odd derivative profile, with ALL degrees:

 K(t)=sum_(r>=0) k_r t^(d_r),
 d_r=2r+1, k_r=2(r+1)nu_(r+1)/((2r+2)!)^2>0.

For each t>0, p_t(r)=k_r t^(d_r)/K(t) is a probability on Nat. Its
first, second and third degree moments are finite. For example their
unnormalized sums are tK', t^2K''+tK', and
 t^3K'''+3t^2K''+tK', respectively. These identities follow from the
admitted complete differentiated series; no termwise differentiation
without a compact majorant or partial-degree law is being assumed.

Let m(t)=sum_r d_r p_t(r)=tK'(t)/K(t). Then m(t)>=1, and the installed
derivative-degree escape gives m(t)->infinity. Crucially, the literal
arithmetic Ward correction supplies tK'''(t)/K(t)->0. This controls the
cubic falling factorial, not immediately d_r^3. The lowest odd degree
must be retained:

 d^3 <= (9/2)d(d-1)(d-2)+1 for EVERY odd integer d>=1.   (M3)

For d=1 the added1 is exact. For d>=3, d-1>=2d/3 and d-2>=d/3, so
d(d-1)(d-2)>=2d^3/9. No unsupported d=2 case enters the odd source.
Also cubic Jensen can be proved without any probability black box:
 d^3-m^3-3m^2(d-m)=(d-m)^2(d+2m)>=0.
Multiply by p_t(r), sum the genuinely integrable full family, and use
sum p=1 and sum dp=m. Combining with M3 gives

 0<m(t)^3/t^2 <= (9/2)tK'''(t)/K(t)+1/t^2 ->0.         (M4)

Define the actual source scale, for every t>0,

 ell(t)=K(t)/(4K'(t))=t/(4m(t)).

There is no chosen source truncation or arbitrary expanding corridor.
Its exact consequences are

 0<ell(t)<=t/4,
 ell(t)/t ->0,
 ell(t)^3/t=t^2/(64m(t)^3)->infinity.                  (M5)

In particular ell->infinity and ell/t^(1/3)->infinity. These are ordinary
real-ray limits, with no uniform-in-order interchange. They are stronger
than the earlier fixed-shift source retention but assert no saddle formula.

Convexity K''>=0 gives monotonicity of K' on [0,infinity). For EVERY
0<=s<=ell(t), ordinary FTC/tangent comparison gives

 K(t-s)>=K(t)-sK'(t), K'(t-s)<=K'(t), hence
 K(t-s)-sK'(t-s)>=K(t)-2sK'(t)>=K(t)/2>0.             (M6)

This proves a favorable lower bound for the FULL first-crossing history
coefficient on a genuinely source-defined growing window. It uses no
sign of D and does not assert that this window captures all history mass.
No unique crossing or global log-concavity of K is inferred.

For any fixed integer q>=0, the admitted compact integral also satisfies

 integral_0^ell s^q K(t-s)ds >= K(t)ell^(q+1)/(2(q+1)). (M7)

For q=2 this implies integral_0^t s^2K(t-s)ds/(tK(t)) >=ell^3/(6t)
->infinity. This is a source-specific corollary confirming the known
failure of quadratic norm replacement, not a new norm-bound sign proof.
The new comparison attempt uses M6 and the actual D, not the test s^2.

## 3. Complete normalized history law: exact two-scale geometry

For t>0 define a genuine probability measure on ages s in [0,t]:

 dQ_t(s)=1_[0,t](s) K(t-s)/A(t) ds.                    (M8)

FTC gives total mass (B(t)-1)/A(t)=1. Positive density and compact
continuity prove genuine L1 for every bounded test; endpoints have zero
Lebesgue mass. The primitive equation retains the entire age history:

 P(t)=tK(t)-A(t) E_(Q_t)[P(S)].                        (M9)

This is a normalized exact source identity, not a supplied correlation
sign. Every nu and R_0 remains in K and A. In particular A is B-1,
NOT B, and Q_t is NOT the degree posterior p_t in Section2.

For every integer q>=0 there is the exact FULL moment formula

 E_(Q_t)[S^q] = q!/A(t) *
  sum_(j>=1) nu_j t^(2j+q)/[(2j)!(2j+q)!].             (M10)

To check both factorials, the K coefficient is 2j nu_j/((2j)!)^2, and
integral_0^t s^q(t-s)^(2j-1)ds=q!(2j-1)!t^(2j+q)/(2j+q)!.
Multiplication cancels only 2j(2j-1)! against ONE (2j)!. Compact uniform
convergence of K, bounded s^q and positivity admit the full exchange.
For q=0 the series is A, so M10 again gives probability mass1.

Equivalently Q_t is the COMPLETE mixture of Beta(1,2j) laws for S/t,
with weights nu_j t^(2j)/[((2j)!)^2 A(t)], j>=1. Their density in s is
(2j/t)(1-s/t)^(2j-1) on [0,t]. This descriptive mixture is derived from
the exact admitted density; no unproved Beta library API is invoked.

There are two simultaneous unconditional limits, for every fixed R>=0
and every fixed 0<epsilon<1:

 Q_t([0,R])->0,         Q_t([epsilon*t,t])->0,
 Q_t((R,epsilon*t))->1.                               (M11)

For the first, eventually t>=R, and
 Q_t([0,R])=(K(t)/A(t))*integral_0^R K(t-s)/K(t)ds.
The fixed compact ratio tends uniformly to1; its integral tends to R.
K/A=(K/B)/(1-1/B)->0, since B grows at least its strictly positive
quadratic term. R=0 is exact zero. No growing-shift convergence is used.

For the second, direct change of variable gives
 Q_t([epsilon*t,t])=A((1-epsilon)t)/A(t).
For any fixed 0<a<1 and integer J>=1, complete positivity bounds
 B(at)/B(t) <= Prefix_J(t)/B(t)+a^(2J).
Indeed the j<J contribution is bounded by Prefix_J(t), and EVERY
remaining term is bounded by a^(2J) times its original positive term.
Full fixed-prefix escape gives limsup<=a^(2J); let J->infinity only AFTER
the fixed-J full-ray limit. Thus B(at)/B(t)->0, and A(at)/A(t)->0 because
B(t)->infinity. This proof keeps the whole tail; it is not truncating Q_t.
For large t the two excluded sets are disjoint and their masses vanish,
which proves the third statement. No uniform epsilon or R quantifier.

Consequently, for EVERY fixed integer q>=1,

 E_(Q_t)[S^q]->infinity,  E_(Q_t)[(S/t)^q]->0.          (M12)

The first follows from E[S^q]>=R^q Q_t(S>R), followed by arbitrarily
large fixed R. The second uses 0<=S/t<=1 and the split at epsilon:
E[(S/t)^q]<=epsilon^q+Q_t(S>=epsilon*t), then epsilon->0. These arguments
have bounded tests at each clock, no false t-dependent DCT dominator.
The entire actual history escapes each bounded age set while occupying
ages smaller than every fixed clock fraction. Neither M11 nor M12 says
Q_t([0,ell(t)])->1; that further moving-scale admission is not proved.

## 4. Where the attempted source proof fails, exactly

At a proposed first zero D(t)=0 with D>=0 on [0,t], set
J_t(s)=sK'(t-s)-K(t-s). The necessary slope fence is

 integral_0^t D(s)J_t(s)ds <= tK(t).                   (M13)

The actual growing M6 window now yields the source-faithful lower bound

 tD'(t)>=tK(t)+(K(t)/2)integral_0^ell D(s)ds
                  - integral_ell^t D(s)J_t(s)ds.     (M14)

Thus a sufficient remaining arithmetic estimate would be

 integral_ell^t D(s)J_t(s)ds <=
     tK(t)+(K(t)/2)integral_0^ell D(s)ds.              (M15)

M15 is an explicit sufficient inequality, not asserted equivalent to
M13. The full outside history remains present and signed. J_t(t)=tb>0,
so that interval necessarily contains a positive region. D>=0 does not
bound its height or correlation there. The exact age-law escape shows
why orienting only an arbitrary fixed positive prefix cannot close this
residual; it does not itself prove a negative witness or rule out M15.
Even M13 nonstrict at every first zero would require a genuine barrier/
continuation argument to exclude higher-order crossing. None is supplied.

A second attempted step was to extract inverse orientation from monotone
posterior degree. The admitted full family does give
 m'(t)=Var_(p_t)(d)/t>=0.
But
 (K'/K)'=(Var_(p_t)(d)-m(t))/t^2.
Its sign needs a new ACTUAL variance comparison. Positive coefficients,
the arithmetic cubic bound M4 and m->infinity do not prove Var<=m.
Even that extra log-concavity would not by itself bound the actual D
correlation in M13. We therefore do not silently posit monotone K'/K,
a unique J sign change, or likelihood-ratio order for the moving history.

The exact signed coefficient also obeys
 J_t(s)=-d/ds[sK(t-s)], integral_0^x J_t=-xK(t-x)<=0,
and integral_0^t J_t=0. For any C1 test phi its admitted compact integral
is integral_0^t phi J_t=integral_0^t phi'(s)sK(t-s)ds.
At a first D zero, D need not be monotone; this elementary conservation
cannot supply M13. It is an admission check, not a renamed positive
kernel producer. Actual score-square/first-atom positivity discovered
below operates in spatial x and does not establish this clock correlation.

Outcome: no dependency-closed proof of D>=0, P>=0, or RH found. The
strongest paper survivors from this attempt are M3–M6 (full actual cubic
posterior control and expanding favorable window) plus M8–M12 (exact
complete age measure, both factorial moments and two-scale escape).
They are PAPER-ONLY pending root/peer audit and future source-faithful Lean.
No stronger claim about its moving ell-mass, rates in M11, growing-order
limits, or finite-eta clocks is made. All leading flattening limits alone
leave M13/M15 signed and unresolved.

## 5. Direct research, complete returned dispositions, freshness

The documented command was run directly, without opening research help
or implementation. Deep owned98273 TERMINALexit0:

 python3 scripts/formal_tools.py research 'actual theta Borel logarithmic derivative variance moving history convolution cumulant' --mode deep --budget-seconds 90 --module PrimeArchTheta --explore 0 --no-refresh --json

The complete186040-byte JSON capture occupied this sole authorized MD
path temporarily; its SHA was158dcddec278a5b9f51aca685c3400941eb8160db35d25f4b09f51d35e017271.
All20 candidate_lemmas, ALL20 source_arguments including their supplied
proof excerpts, ALL10 source_passages, ALL6 query_trace and full metadata
were read in bounded chunks before replacement by this paper. Zero
ingredient_sets/proof_ideas/declarations/prose/exploration were returned.
No hit was treated as compiled by virtue of research freshness metadata.

Metadata: elapsed90.054150833s, partial=true; unfinished variance-process
convolution, logarithmic-derivative moving-average, deadline and semantic
coverage. Reranking deadline expired; filter_and_judge returned incomplete/
malformed JSON. No index_warnings. Query index1170098; coverage snapshot
and current1170106, files63738/inventoried63738/pending0, inventory complete,
no inventory errors. Compiler statuses:43 compiled_snapshot,2 error,
10274 not_applicable,48066 pending,2660 stale,38 stale_snapshot,
1 umbrella_source_only,2654 unavailable. Methods ready398160/stale185802/
failed43 do not certify these consumers. Semantic coverage unreported and
unfinished. ALL6 trace queries included exact, relaxed actual-theta,
derivative-variance, convolution-cumulant and two local-model formulations.

Candidate dispositions (C indexes preserve returned order):
- C0–C6: hasDerivAt_thetaCuspBornWittenLogThirdDerivative (Popescu126),
  LogFourth derivative (SixthJet31), LogFourth definition(Popescu30),
  RadialLogDensityPotential derivative(RadialHierarchy152), LogFifth
  derivative(SixthJet76), LogEighth/EighthJet28 and LogSeventh/EighthJet21.
  Actual individual spatial derivatives; no full causal-history orientation.
- C7 thetaCusp_allOrderCumulantRecurrence(AllOrderCumulant92): exact complete
  logarithmic subtraction, no sign theorem; overlap retained.
- C8/C9 thetaCuspFirstSourceTaylorLower/Upper64 actual inequalities
  (HighOrderQuadrature802/835); C10 thetaCuspExpTaylorThree_eq_sum
  (FirstAtomFourthMomentFloor466): fixed protected quadrature/first atom.
- C11 thetaCuspReflectedEighthGeneralModularValue(ModularDifferentialClosure2308),
  C15 thetaCuspModularPositiveState975: spatial state/finite jet.
- C12 thetaCuspThirdCumulantProductIntegral(ThirdCumulantProductKernel288),
  C13 thetaCuspRawScoreGap(PolynomialScoreGap22), C14 exact raw-moment
  cubic product identity293: genuine finite score/cubic admissions, no M13.
- C16 thetaGateCurvature_exact(GateCurvatureIdentity19): indexed statement
  cut at let-v; no complete type/applicability claim is inferred from it.
- C17 thetaCuspExpTaylorFive_eq_sum(FirstAtomFourthMomentFloor461),
  C18 SixthSeamModularPolynomial_source_pos(SixthSeamChamber171),
  C19 GaussianApertureGammaRatio derivative(CurvatureFlow1395): fixed
  expansion/aperture sources, not literal K moving-history correlation.

Source_arguments S0–S19, every supplied excerpt read; all method fields null:
- S0/S1 ModularNormalizedQuasimodularDrift954/ReducedState959 definitions;
  S2 GaussianApertureGammaRatio_pos(CurvatureFlow1385), S3 inversecurvature
  score_zero_pos(Popescu378): actual spatial/aperture positivity, not M13.
- S4 two_hundred_forty_mul_firstAtomMoment_one_le_thirteen_mass(CurvatureGap283):
  genuine first-atom mean fence, not full logarithmic clock sign.
- S5 integrableOn_thetaCuspMonicQuadraticNorm(MonotoneGramRatio20),
  S6 atom_quadratic_nonneg(PolynomialScoreGap227): genuine finite L1/PSD.
- S7 self-dual scale_sq_gt_nineteen_point_one(SixthSeamChamber132),
  S8 SixthSeamModularPolynomial_pos_of_threshold150,
  S9 BornWittenPopescuNumerator_pos(Popescu301): parameter/atom positivity.
- S10 thetaCuspFullScore_gt_firstAtomSquare(FullScoreSlack141): genuine
  complete spatial fence pi*psi1(x)^2*(x-1)^2 <
  (1-303x^2)rho(x)-16x rho'(x), x>=0; does not orient a D-history test.
  S11 deriv_thetaCuspFullSource_eq_tsum_sourceTerm(FullScoreSlack29):
  useful complete-source admission only.
- S12 XiSquareNormalizedThirdJet_coeff_zero(ThirdCumulantProductKernel367),
  S13 thetaCuspFiniteScoreGap(PolynomialScoreGap27): exact finite jet/PSD.
- S14 apertureRatioCurvature_next_neg_of_boundary_deriv_neg(CurvatureFlow1519):
  conditional boundary premise in a different parameter, not a producer.
- S15 firstAtom_bornWittenAmplitude_sq_eq_exp(GaussianScoreFloorEnvelope16),
  S16/S17 firstAtomHighOrderLower/UpperPolynomial64 density bounds
  (HighOrderMomentBounds314/375), S18 firstAtom_gaussianScoreEnvelope_large97,
  S19 firstRadialQuadraticSteinScore_sq_le(QuadraticSteinRobertson132):
  genuine atom identities/bounds, insufficient for full moving M13.

All10 supplied source passage ranges and applicability:
- T0 ModularDifferentialClosure940–1046: exact normalized actual states;
  spatial profile positivity is not original clock positivity.
- T1 PolynomialScoreGap1–113: full raw factor2 and finite polynomial L1,
  exact square expansions, no causal inverse sign.
- T2 SixthSeamChamber1–118: actual mass/polynomial chamber; its explicit
  analytic seam closure gap prevents replacing actual clocks by that model.
- T3 ModularDifferentialClosure1835–1951: true spatial Lyapunov ODE states.
- T4 same2248–2354: actual modular gap decrease, completed-profile finite
  jets/reflection; not an all-order clock cumulant sign.
- T5 CumulantRatioSplit1–98: conditional actual ratio assumptions are NOT
  supplied by the theorem; no new source producer accepted.
- T6 SixthSeamChamber111–191: true self-dual scale polynomial positivity.
- T7 ScoreAffineGate1–62: exact determinant split with remaining affine
  gate, not an automatic full sign.
- T8 BornWittenPopescuCorrection327–424: genuine inverse-curvature/atom
  positivity, no source-history comparison.
- T9 ModularDifferentialClosure2045–2155: actual spatial vector field.
Entire supplied ranges were inspected; passages truncated by retrieval are
not claimed whole-module reviews. No reported ingredient-set was hidden.

Narrow lexical follow-up, owned74452 TERMINALexit0, ALL9 records read:

 python3 scripts/formal_tools.py research 'Borel' --mode lexical --module LiEvenCrossActualClockBorelGrowth --per-module 0 --explore 0 --no-refresh --json

Exactly nine eligible declarations, one module, no exploration: private
borelPrefix_le_power29; public Prefix_nonneg25, Term_le_kernel20,
Prefix17, Weighted_div_kernel_prefix_lower106, Weighted_prefix_lower75,
logarithmicDegree_tendsto_atTop137, Prefix_div_kernel_tendsto42,
Weighted_div_kernel_tendsto_atTop121. ALL144 primary body was read rather
than trusting indexed name-only records. Lexical output reports no deep
candidate/source/semantic freshness fields; none is invented.

## 6. Frontier and scope disposition

Active card docs/drafts/pipeline/1-in-progress/li-clock-integrated-source-sign.md
ALL60 read; current-frontier-map282–290 relevant causal-history/marking
entries and STATUS65–85 source-control rules read. Broader STATUS rg
locations were navigational, not an exhaustive whole-file audit claim.
The current actual Ward, fixed prefix, Gamma marking/CP and inverse sign
boundaries remain separate. This new attempt exploits full arithmetic
cubic control to enlarge the favorable history set; the complete signed
complement is exactly the unresolved source step M13/M15. No old fixed
pair, fixed prefix or norm replacement is resubmitted as its solution.

Prior overlap is bounded returned source evidence, not corpus absence or
world novelty. M1/M2, smoothness, score/derivative flattening and full
prefix escape are existing installed source results. M3–M6 and M8–M12
are explicit new paper deductions offered for independent review, not
claimed Lean exports. A successful actual arithmetic correlation estimate
and strict/continuable crossing barrier are still required. RH remains OPEN.

---

# Moving-history conservation domain

Applies to frozen381 `/tmp/li_pole_theta_moving_history_attack.md`, SHA256
`6c3efaf5fb66d01173ca4a0c906e2cefd88f898c60d4ddff115f803cf9e37996`.
In Section4's unnumbered conservation identity, the inequality
`integral_0^x J_t = -x K(t-x) <= 0` is asserted only for `0 <= x <= t`,
with the already fixed `t>0`. On this interval both x and K(t-x) are
nonnegative. The equality follows by differentiating sK(t-s); no sign
outside this interval is claimed. The full integral at x=t is zero.

This makes explicit the history-domain guard needed by that auxiliary
inequality. It changes no M1–M15 statement or positive survivor proof.
The actual D-history correlation and crossing continuation stay OPEN.
