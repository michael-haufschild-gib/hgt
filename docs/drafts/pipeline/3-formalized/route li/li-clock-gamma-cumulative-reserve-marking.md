# Actual Gamma cumulative reserve and positive exponential marking

- **ID:** LI-CLOCK-GAMMA-CUMULATIVE-RESERVE-MARKING
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [literal integrated source sign](../1-in-progress/li-clock-integrated-source-sign.md)
- **Prior:** [signed Gamma jumps and integer coupling](li-clock-signed-gamma-jump-coupling.md)
- **Statement:** Actual full signed Gamma intensity has a strict Gamma2 cumulative reserve on the exact geometric-budget domain; one admitted exponential marking yields a positive full jump measure and genuine compound-Poisson coupling at every nonnegative real time.

## Status and gates

- [x] [PROVED HERE] Complete dependency-closed paper D1–D20, preserved verbatim below.
- [x] Root ALL528/source review PASS; independent Pole ALL528/D1–D20 review PASS.
- [x] Exact prior overlap, all61 retained research-hit dispositions and freshness limits recorded.
- [x] Formalize exact new source guard, full CDF/transport/marking/probability and derivative survivors in Lean (see Lean certificate).
- [x] Final scoped compiler/axiom/import/index/lint gates (see Lean certificate).
- [ ] Original unsmoothed source sign or sufficient eventual lower bound (OPEN residual `U⁺ ≥ U⁻ ⟺ P ≥ 0`; not part of the proved theorem).

Frozen paper528 SHA256 `7bd08cc114c06b36e068b42339a4d176adfde463045ca8842de095d8f3ccbd65`. Root review `/tmp/li_root_theta_gamma_density_comparison_review.md`; independent complete82-line certificate `/tmp/li_pole_theta_gamma_density_comparison_audit.md`, SHA256 `64effc02299a798ad445ef2258c375349a6ccde0beaced03ed1ee8eedda7cfd3`. Root read both whole paper and complete independent certificate, and checked actual full-copy/strip/moment source bodies. Author-paper status line is preserved as historical frozen text; dual review is now complete. Lean certificate below.

## Exact boundary

Positive reserve requires p>0 and150p²>1+A/(2M0). This is the exact domain of the stated geometric budget; p≥1/9 is an explicit sufficient condition. Marking uses r>0 with p−r in that domain. The marked law differs from the original Gamma mixture. Pointwise U+/U− ratio is damping-independent, and original P≥0 remains OPEN.

## No-go connection

[First-row pointwise domination](../5-failed/li-clock-first-row-gamma-density-domination.md) fails on actual source; this complete positive survivor is formalized in Lean (certificate below), which completes that subroute's closure. Parent RH route remains OPEN.

## Frozen complete paper

# Actual Gamma density comparison: cumulative reserve and exponential marking

Status: dependency-closed PAPER proof below, awaiting independent review.
Literal unsmoothed N17 remains OPEN. No RH premise, numerical work, Lean/compiler,
source/card/tree edit, free coefficient sequence or new agent. All new measure
statements here are paper results, not installed Lean APIs. Frozen signed-Gamma
plan43 contracts remain unchanged; wider damping domains below are fresh paper
claims with their own complete convergence proofs.

## 1. Mechanism and exact source

Chosen mechanism: use integer-shape Gamma CDF order plus the ACTUAL first-row
mass and complete absolute tail. Test its density upgrade on the SAME source;
retain all higher positive rows. Successful salvage is cumulative reserve,
unequal-mass quantile transport, and a positive exponentially marked jump law.

Set nu_j=thetaCuspNormalizedEvenMoment j, M_n=normalizedPrimeArchMoment n,
A=xiShiftAbsoluteMass 0. All analytic multiplicity copies are retained. Define

    Phi(z)=XiC(-I*z)/XiC(0)=sum_j nu_j z^(2j)/(2j)!,
    H(p)=log Phi(1/p), p>0,
    P(t)=liEvenCrossActualClockPrimitive t=integral_0^t F(s)ds.

Here nu0=1, every nu_j>0, and the normalized source is SINGLE completed Xi,
not a squared partition. Audited author475 N6/N11 gives the local log and
complete primitive coefficients

    log Phi(x)=sum_(j>=1) (-1)^(j-1) M_(j-1) x^(2j)/(2j),
    P(t)=sum_(j>=1) (-1)^(j-1) M_(j-1) t^(2j)/(2j)!.

The second equality follows by compact absolutely admitted integration of the
installed full F series and holds at every real t. Only M0>0 and M1>0 signs
are used here. No all-order M_n sign or alternating full log-sign is assumed.

For p>0, j>=1, define

    ell_j(p)=(-1)^(j-1) M_(j-1)/(2j*p^(2j)), ell0=0,
    f_(j,p)(t)=1_(t>0) p^(2j) t^(2j-1) exp(-pt)/(2j-1)!.

Let Gamma_(2j,p) be this genuine probability law (shape2j, RATE p).
The j0 degree law is delta0, not a shape-zero density. Define positive finite
intensities, when admitted,

    tau_p^±(dt)=sum_(j>=1) max(±ell_j(p),0) f_(j,p)(t)dt,
    Lambda_p^±=sum_(j>=1) max(±ell_j(p),0),
    sigma_p=tau_p^+−tau_p^-.

These are positive/negative parts of the DISCRETE coefficients before overlapping
Gamma smoothing. They need not be Jordan parts of the continuous signed measure.

## 2. Literal mass guard and full damping domain

D1. Installed all-copy source bounds are A>0, A<infinity and
|M_n|<=A*150^(-n). The already installed sector fence gives M0>=(167/168)A.
A stronger exact geometric consequence used here is

    M0 > (299/300) A.                                  (D1)

Proof: for any q:XiZeroCopy put alpha=xiSpectralPoint q, w=alpha^-1,
a=|w|^2=|w^2|. Alpha is nonzero, |Im alpha|<1/2 and 0<a<1/150.
The elementary inverse identity gives |Im w|=|Im alpha|a<a/2. Therefore

    Re(w^2)=a−2(Im w)^2 > a−a^2/2 > (299/300)a.

The strict first inequality also holds when Im alpha=0 because a>0.
The source identities M0=sum_q Re(w_q^2), A=sum_q|w_q|^2 are genuine full-copy
absolutely convergent sums, with NO half-factor. Sum the weak inequalities;
the nonempty copy fiber supplies one strictly positive summand of the difference,
so the inequality is strict. No RH or real-zero premise is used.

D2. Write q_p=1/(150p^2), rho=1/sqrt150. For EVERY p>rho,

    |ell_j(p)| <= A/(2j*p^2) q_p^(j-1),
    sum_(j>=J)|ell_j(p)| <= A/(2J*p^2) q_p^(J-1)/(1−q_p).
                                                               (D2)

Consequently both full positive intensities are finite, the signed row series is
L1, and sum of row L1 norms=sum|ell_j|. Every polynomially weighted row sum is
L1: Gamma's n-th moment is p^(-n)(2j)...(2j+n-1), a polynomial in j absorbed by
q_p^(j-1). These are before every later exchange. Positive Tonelli constructs
all measures; signed L1 allows bounded measurable tests and Fubini.

The density identity is pointwise on t>0:

    sigma_p(t)=exp(-pt) P(t)/t.                        (D3)

For each compact t interval, cancellation of p^(2j) leaves a full factorial
majorant A*150^(-(j-1))*|t|^(2j-1)/(2j)!, so compact uniform convergence
identifies the L1 version with a continuous density. At t<=0 use density0;
P(t)/t at0 is defined by its removable value0. There is NO residual factor1/2.

D3. The wider p>rho domain also has

    Lambda_p^+−Lambda_p^-=sum_j ell_j(p)=H(p)>0.        (D4)

Indeed L(x)=sum_j(-1)^(j-1)M_(j-1)x^(2j)/(2j) is holomorphic on |x|<sqrt150.
By the audited exact local Ward/jet log identity exp L=Phi near0. The analytic
identity theorem on this connected disk gives exp L=Phi throughout it; this
proves its zero-free admission rather than assuming one. For x=1/p>0 in the
disk L is real, hence log Phi(x)=L(x). Also Phi(x)>1 from its actual positive
nu1 term. This is the same proof as author475 N8/N9 with its full radius retained.
Both Lambda±>0: ell1=M0/(2p²)>0, ell2=−M1/(4p^4)<0.

Define complete tail budget and reserve

    Tbar(p)=A/[4p^2(150p^2−1)],
    delta(p)=M0/(2p^2)−Tbar(p).                        (D5)

The full j>=2 sum is <=Tbar: use 1/(2j)<=1/4 in D2 and sum the COMPLETE
geometric series. No cutoff source or sampled rows replace the source.
Its exact positive-reserve domain is

    p>0 and 150p^2 > 1+A/(2M0).                      (D6)

Call this set D. It implies p>rho and delta>0. It is the exact domain of THIS
geometric reserve, not an asserted maximal CDF/density positivity domain.
D1 gives explicit sufficient p²>=449/44850 (including equality), since
150p²−1>=150/299 and M0/A>299/300. In particular every p>=1/9 lies in D.
For the original p>1 scope, delta(p)>19A/(40p²)>0: q_p<1/150 and
299/300−1/298>19/20. This proves reserve positivity from literal source,
not merely separate M0>0 and finiteness of A.

## 3. Complete CDF comparison

D4. For T>=0 the integer-shape Gamma CDF is

    F_(j,p)(T)=1−exp(-pT)sum_(k=0..2j−1)(pT)^k/k!,
    F_(1,p)(T)=1−(1+pT)exp(-pT).                      (D7)

Repeated integration by parts, or differentiating the displayed expression
and its zero initial value, proves this exact finite polynomial expression.
Polynomial times exp(-pt) is genuinely integrable, so it is the measure CDF;
no Xi truncation occurs. For T>0 all F_j>0, and F_j<=F_1 with strict inequality
for j>1. The difference is a nonempty sum of positive terms times exp(-pT).

D5. For p in D and T>0 set

    D_p(T)=tau_p^+((0,T])−tau_p^-((0,T])
          =integral_0^T exp(-pu)P(u)/u du.

The last identity uses D3 and genuine signed L1. Bounded indicator integration
permits the complete series sum D_p(T)=sum_j ell_j F_(j,p)(T). For each j>=2,
ell_j F_j>=−|ell_j|F_1. Thus

    D_p(T) >= delta(p) F_(1,p)(T) >0.                 (D8)

This is an ALL-cutoff strict signed cumulative-mass theorem for actual tau±,
with every Gamma row retained. It does not differentiate to a density sign.

Retaining the KNOWN negative j2 row improves the bound:

    D_p(T) >= delta(p)F_1(T)
      + M1/(4p^4) exp(-pT)[(pT)^2/2+(pT)^3/6].       (D9)

For j2, ell2 F2=−|ell2|F1+|ell2|(F1−F2); the remaining complete rows obey the
same bound. The strictly positive last term proves D_p(T)>delta F1(T) at EVERY
finite positive T, independent of all other signs.

D6. There is also strict excess total mass

    H(p)>delta(p).                                   (D10)

The tail budget at j3 uses A/(4p²)q_p², but its actual absolute upper bound is
A/(6p²)q_p². Therefore the complete sum of tail absolute values is at most
Tbar−A q_p²/(12p²); the full other rows remain in the geometric sum. Hence
H>=ell1−sum_tailabs>=delta+A q_p²/(12p²)>delta. This is strictness of a complete
upper bound, not a moment sign or a finite cutoff approximation.

## 4. Strong unequal-mass transport survivor

D7. Remove the positive probability-row reserve as a genuine measure:

    rho_p=tau_p^+−delta(p) Gamma_(2,p).

This is positive: its density is at least (ell1−delta)f_(1,p)=Tbar f_(1,p)>0
on t>0. Its mass is Lambda+−delta>Lambda−>0 by D10. Its CDF R(T) satisfies
R(T)>tau_p^-((0,T]) for all T>0 by D9. Both laws have continuous strictly
increasing CDFs on (0,infinity), limits0 at0 and their finite masses at infinity:
rho>=Tbar Gamma2, tau−>=|ell2|Gamma4, with genuine full L1 admissions.

There is a unique finite a_p>0 with R(a_p)=Lambda−. Set

    chi_p=rho_p restricted (0,a_p],
    zeta_p=rho_p restricted (a_p,infinity).

Their masses are Lambda− and H−delta>0, respectively. For every T>=0,
chi_p((0,T])=min(R(T),Lambda−)>=tau−((0,T]). Construct U uniform on
(0,Lambda−); continuous strictly increasing CDF inverses give

    X=R^(-1)(U), Y=(CDF tau−)^(-1)(U), X<Y a.s.,
    Law(X)=chi_p/Lambda−, Law(Y)=tau_p^-/Lambda−,
    tau_p^+=delta Gamma2+Lambda− Law(X)+zeta_p,
    tau_p^-=Lambda− Law(Y).                           (D11)

Strict X<Y follows R(Y)>CDFtau−(Y)=U, with U inside the open mass interval.
The inverse maps are monotone measurable and the uniform change-of-CDF gives
the displayed marginals. This is a DEPENDENT quantile coupling. It is not an
independent-product coupling and does not normalize original tau+ by Lambda+.
The original intensity masses are unequal. No stochastic order of
original tau+/Lambda+ vs tau−/Lambda− is asserted.

For every bounded measurable nonnegative NONINCREASING h,

    integral h d(tau+−tau−) >= delta integral h dGamma2 >=0. (D12)

Use D11, h(X)>=h(Y), h zeta>=0. Strictness holds when integral h dGamma2>0.
Nonnegativity of h is essential because of unequal total masses. This extends
Laplace tests to the whole decreasing-test cone; it does not cover arbitrary
nonnegative tests, which would be equivalent to the missing measure sign.

## 5. One exponential marking gives a positive complete source law

D8. Fix p>0 and r>0 with a=p−r in D; in particular p in D, since D is an upper
ray. Exp_r is probability density r exp(-rt) on t>0. Define complete marked
positive measures barTau±=tau_p± * Exp_r and signed kappa=barTau+−barTau−.
All intensities are finite by D2. The product integral of |sigma_p(u)| times
Exp_r(v) equals its finite L1 norm, so full signed Fubini and the shear u+v=t
are justified. Compact continuous densities also give the following pointwise
convolution version, not only an AE identity:

    kappa(t)=r exp(-rt) integral_0^t exp(-(p−r)u)P(u)/u du
            =r exp(-rt) D_a(t), t>0; kappa(t)=0,t<=0. (D13)

D8 gives the actual pointwise STRICT positivity and explicit lower bound

    kappa(t)>=r exp(-rt) delta(a)[1−(1+at)exp(-at)]>0. (D14)

D9 supplies an additional strictly positive lower term. This retains ALL original
Gamma rows and full signed density before marking. It is not an inverse-positive
claim or recovery of an unsmoothed sign. Kappa is now a genuine positive finite
jump measure with mass H(p), since Exp_r has mass1 and D4 applies. Every
polynomial moment is finite by positive product expansion and the D2 moments.
The lower bound itself has mass delta(a)a²/p²: integrate Exp_r times the Gamma2,a
CDF, or exchange its positive integral and use Gamma2,a Laplace at r.

D9. For s>=0 the genuine signed Laplace exchange gives

    Laplace(kappa)(s)=r/(r+s) H(p+s).                 (D15)

Indeed Gamma row Laplace=(p/(p+s))^(2j) gives Laplace(sigma_p)=sum ell_j(p+s)
=H(p+s), absolutely; the exponential factor is r/(r+s). Both factors are
finite, with no transform below the D2 domain assumed. The ordinary actual
Gamma-mixture probability mu_p still has Laplace Phi(1/(p+s))/Phi(1/p),
i.e. logLaplace(mu_p)=H(p+s)−H(p) in the real logarithm convention.

For any finite positive intensity eta, define the genuine ordinary probability
CP(eta)=exp(-eta(univ))sum_(m>=0)eta^{*m}/m!, including delta0 at m0.
Positive Tonelli gives total mass1; full positive double convolution sums and
binomial Cauchy establish CP(eta+xi)=CP(eta)*CP(xi). Therefore for EVERY
REAL v>=0, not merely integer times,

    CP(v barTau+) = CP(v barTau−) * CP(v kappa).      (D16)

This is a genuine independent-product probability coupling: take independent
X~CP(v barTau−), Y~CP(v kappa), then Y>=0 and X+Y has the left law.
Hence all bounded increasing tests give real-time stochastic domination.
All measures depend on the same actual source. This extends integer-time
comparison only AFTER exponential marking. It neither makes original mu_p
infinitely divisible nor identifies it with the new CP(kappa) law.

The new complete positive law has exact transform

    Laplace(CP(v kappa))(s)
      =exp(v*[r/(r+s) H(p+s)−H(p)]).                 (D17)

At s0 it equals1. Its exponent equals
v*[r/(r+s) logLaplace(mu_p)(s)−s/(r+s)H(p)] with the preceding real-log
convention; this is the exact relation to the actual law, not a law equality.
(Installed HTGeometry.logLaplace uses NEGATIVE log, so its sign must be reversed
when translating this displayed real log of the Laplace transform.)

D10. Genuine moment L1 makes h_(p,r)(s)=r H(p+s)/(r+s) STRICTLY completely
monotone for s>=0, ALL derivative orders n>=0:

    (-1)^n h_(p,r)^(n)(s)=integral t^n exp(-st) dkappa(t)>0.

At s0 the same derivatives follow from an explicit exponential-L1 neighborhood.
Choose epsilon>0 with 2epsilon<min(r,p−rho). Positive Gamma/product Tonelli gives

    integral exp(2epsilon*t) d(barTau+ + barTau−)(t)
      = r/(r−2epsilon) * sum_j |ell_j(p−2epsilon)| < infinity.

Since |kappa|<=barTau+ + barTau− and each t^n exp(epsilon*t) is bounded
by a constant times exp(2epsilon*t), all derivative integrands in
|s|<=epsilon have genuine L1 majorants, for EVERY fixed n. Dominated
differentiation therefore includes the ordinary derivative at s0, not just
a one-sided s>0 assertion. Strict positivity uses kappa(t)>0 for all t>0.
Leibniz gives the concrete
uniform-in-order source inequality

    sum_(k=0..n) (r+s)^k (-1)^k H^(k)(p+s)/k! >0,     (D18)

since the positive multiplier is r*n!/(r+s)^(n+1). This is a COMPENSATED
finite derivative combination at every order; it is NOT an individual sign
of H^(n) or a proof of the requested unsmoothed all-order sign/RH.

## 6. Exact failure of the first-row density upgrade

D11. On the SAME actual source tau−(t)>=|ell2|f_(2,p)(t), whereas the first
positive row is ell1 f_(1,p)(t). For t>0 their ratio obeys

    tau−(t)/(ell1 f_(1,p)(t)) >= M1 t²/(12 M0).        (D19)

Compute f2/f1=p²t²/6 and |ell2|/ell1=M1/(2M0p²); rate p cancels.
The lower bound is unbounded with t. Thus an all-t comparison of the entire
negative density against ONLY the positive first row is FALSE for the actual
source at every admitted p. This falsifies that mechanism, not N17: higher
positive rows have never been discarded from tau+ and can supply compensation.
It is not an actual P counterexample or an RH-falsification claim.

The rate cancellation is stronger:

    tau_p±(t)=exp(-pt) U±(t),
    U±(t)=sum_(j>=1) max(±(-1)^(j-1)M_(j-1),0)t^(2j-1)/(2j)!. (D20)

The full factorial bound admits both entire odd series and their compact
uniform convergence. For each t>0 both U±>0 by j1/j2. Thus the actual
pointwise tau+/tau− ratio is independent of p; damping cannot improve that
ratio at a fixed t. The density sign remains the complete cancellation

    U+(t)>=U−(t), equivalently P(t)>=0 on t>0.         (OPEN)

CDF comparison cannot be differentiated to prove it. Exponential marking loses
pointwise information and no positive inverse is supplied. Integer-time CP
comparison is not extrapolated to fractional divisibility of original mu_p.
The new D16/D18 laws concern the explicitly marked law only. No arithmetic
comparison of the remaining higher positive/negative rows closes OPEN here.

## 7. Exact source/dependency and status ledger

Every new claim above uses literal source or explicit analytic proofs. No fresh
compiler/import/axiom evidence is claimed. These primary bodies were read:

- PrimeArchValuationSectorCones.lean:33–87 defines A, proves full absolute
  summability/nonempty strict mass, and the existing 167/168 M0 fence.
- XiGuinandWeilRectangleExhaustion.lean:24–44 gives xiSpectralPoint_im_eq,
  xiSpectralPoint_im_mem_openHalf from unconditional actual divisor strip.
- XiReciprocalSquareSecondMomentRadius.lean:30–62 gives
  norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty and its actual
  Schwarz-copy/second-moment proof;115–139 gives
  abs_normalizedPrimeArchMoment_add_le_secondMomentRadius.
- XiRelativeResolventTrace.lean:197–210 defines lambda=w²;311–357 gives full
  multiplicity summability and tsum_xiZeroCopyReciprocalSquare_pow.
- PrimeArchScaledHausdorffDivisorValueRelation.lean:109–114 gives
  normalizedPrimeArchMoment_eq_re_xiCentralReciprocalMoment. These identities
  jointly give M0=sum Re(w²), with no half-copy loss. D1 is a new combination
  of these existing inputs; scoped rg found no literal299/300 fence in RHTower.
- XiThermalSourceRelativeGapBound.lean:417–429 gives
  normalizedPrimeArchMoment_one_pos from actual thermal normalization.
- PrimeArchThetaCumulantMinor.lean:201–225/439–480 and
  PrimeArchThetaAllOrderCumulant.lean:33–47/92–144 give the normalized actual
  local log/jet recurrence. This is the author475 N6 source, not supplied signs.
- LiEvenCrossActualClockVolterra.lean:78–122 and full151-line SineSource
  provide full response series/all-copy complex reality. Primitive full235
  gives literal oriented FTC, full cosine representation, sharp quadratic
  bound and CONDITIONAL RH nonnegativity. PrimitiveVolterra full119 supplies
  P+P*K=tK and unconditional unbounded-above escape; neither proves P>=0.
- PrimitiveNegative.lean:191–271 all public receiver bodies retain not-RH
  conditional escape and the all/eventual/bounded-below RH equivalences.
- BorelSource.lean:18–45 exact actual nu/B definitions; BorelFlattening
  source admissions reused from previously audited full589, no inverse sign.
- Mathlib/Probability/Distributions/Gamma.lean:74–169 gives actual gammaPDF
  positivity/measurability, gammaMeasure probability, cdf_gammaMeasure_eq_integral.
  D7's exact integer-polynomial CDF/order is proved here, not claimed existing API.
- HTGeometry/ConvolutionAtomBounds.lean:266–317 provides ordinary Poisson
  positive-mixture/Cauchy/semigroup machinery. LaplaceTransformConvolution.lean:
  196–241 has its finite-transform formula and NEGATIVE-log convention.
  CompoundPoissonWitnesses' broader arbitrary convolution mixture predicate
  is neither negated nor used to obtain original mu_p infinite divisibility.
- Audited author475 N1–N15 supplies all actual raw/Gamma/probability admissions;
  root review and final prospective768/43-contract plan stay frozen. D2–D4
  explicitly re-prove wider-domain admissions; no old public signature changed.

Full CDF/quantile/exponential-marking implementation would require genuine
Gamma finite-CDF, measure reserve/restriction, quantile coupling, signed Fubini
and positive CP probability/equality proofs. Their proofs are written above;
these bridges remain Lean OPEN, not replaced by coefficient identities.

## 8. Corpus-first coverage and all-hit applicability

Exact original direct query, before this mechanism:

    python3 scripts/formal_tools.py research 'actual theta signed Gamma jump density positive primitive logarithmic source smoothing total positivity' --mode deep --budget-seconds 300 --no-refresh --json

Session46517 terminal0,112.245582s,partialfalse/errorsnone; initial lexicalAND0.
Inventory63679allindexed, retrieval1168203, coverage1168214/current1168217,
semantic UNMEASURED/reporting_budget, oldercoverage warning. Compiler43snapshot/
2error/48018pending/2660stale/38stalesnapshot/1umbrellasource_only/2654unavailable/
10263not_applicable. Tool display truncated full hit payload, so NOT an all-hit
certificate. Follow-up18725 same theme150s terminal0/83.227842167s also displayed
a truncated payload and is not relied upon for an exhaustive hit conclusion.

Final fully retained direct repeat9810:

    python3 scripts/formal_tools.py research 'Gamma smoothing theta primitive density comparison total positivity' --mode deep --budget-seconds 150 --no-refresh --json

Its stdout was piped through a JSON filter removing only redundant dependency,
provenance, score/runtime/compiler and duplicate source-statement fields. It
retained EVERY candidate statement; EVERY source-argument statement/full returned
proof_excerpt/method; EVERY prose/source passage text; EVERY ingredient step and
all coverage fields. Full valid retained object154020chars. No standalone log
written outside this sole allowed MD; tool result/store gamma_density_compact
holds it. Session9810 terminal0/95.672370458s,partialfalse,errors0,unfinished0.
ALL61 records below read, no sampling:20candidate+20sourceargument+10prose+
10sourcepassage+1ingredient. Declarations/exploration/markers/proofideas all0.
Returned excerpts can be shorter than a full theorem body (e.g.S12); no unreturned
body or all-corpus exhaustion claim follows. Candidate applicability source-only,
not_checked, axiomsnull. Inventory63683/63683indexed, Lean53420/prose10263;
retrieval1168337,coverage1168350/current1168351. Compiler43snapshot/2error/
48022pending/2660stale/38stalesnapshot/1umbrellasource_only/2654unavailable/
10263not_applicable. Semantic UNMEASURED/reporting_budget; oldercoverage warning,
enrichment countspending, no inventory errors. Model 'sufficient sources' judgment
is rejected for this target: exact observable/normalization mismatches below.

All candidate contracts C0–C19, in returned order:

- C0 D4BMOriginalOrbitCurrent.density_smooth; C1 EinsteinCyclicVariation.density_smooth:
  private metric/current smoothness, no actual Gamma intensity or order.
- C2 IsPrimitiveRoot.isPrimitiveRoot_iff'; C3 card_primitiveRoots;
  C4 toInteger_isPrimitiveRoot; C7 rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot;
  C8 embeddingsEquivPrimitiveRoots; C9 padicCompletedPrimitiveRoot_isRoot;
  C12 rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot;
  C16 padicMultiplicativePrimitiveRoot_isPrimitiveRoot: algebraic roots,
  unrelated primitive clock; each literal contract inspected/rejected.
- C5 ExtendedSelbergClass.theta; C13 Zeta23.ThmD.theta; C15 Bottcher.thetaFour;
  C17 thetaChar_four; C18 criticalThetaCoefficient: different theta functions/
  coefficients, no literal Phi/Gamma law identity or source comparison.
- C6 density_estimate_never_forces_vanishing: zero-count envelope existence
  no-go, not Gamma density order. C10 smoothRapidExponentialFockLaplacianDensity;
  C11 smoothConvexRapidExponentialFockLaplacianDensity;
  C14 smoothRapidExponentialFockHeadLaplacianDensity; C19 ReversibleChain.density:
  different Fock/finite-chain density definitions, no applicable law.

All source arguments S0–S19, including each full returned proof/method:

- S0 routePPrimitiveGammaSewnCriticalLinearGreenFlux; S6 summable_...QuadraticGreenPairing:
  positive prime-power Green source, different log-depth Gamma; no tau identity.
- S1 cglSmoothedNonprincipalRegularizedMellinIntegrand_analyticOnGammaSafe;
  S2 cglPrimitiveClassI_leftLine_argument_eq_criticalLine;
  S3 coeffLaplaceProfile_cglDetectorTailSlice_eq_sum;
  S7 gamma_mul_LSeries_cglFull_verticalIntegrable_two;
  S8 cglPrimitiveClassI_mellinInv_eq_safeLineIntegral;
  S11 exists_uniform_norm_cglPrimitiveClassI_leftLineIntegrand_polynomialExponential_le:
  each CGL integrand/character/contour statement and returned proof read;
  gamma completion/complex detector norms do not order actual Gamma jumps.
- S4 integral_Ioi_rpow_gaussianPower: genuine Gamma integral applicable as
  elementary normalization input only; no all-order/source density sign.
- S5 Sieve.mellinInv_two_gamma_mul_LSeries_eq_coeffLaplaceProfile_of_bound:
  bounded Dirichlet coefficient Mellin inversion, not log intensities.
- S9 zeta_W_eq_integral_mu_add_PX_bilinear: compact Weil-test explicit formula
  with pole-cancellation tests; no identification with full P/t density.
- S10 Sieve.exists_inghamSmoothedDivisorWeightedMass_le: positive smoothed
  divisor mass bound, different source. S12 sharpCount_at_level: supplied
  finite-aperture count hypotheses and truncated returned proof excerpt,
  no source law admission; no beyond-excerpt claim made.
- S13 completedLFunctionPrimitiveDivisorZeroDensityBoxCount;
  S14 cglPrimitiveClassIAnalyticNaturalWellSpacedZero;
  S16 cglPrimitiveNonprincipalFamilyZeroDensityVerticalWindowCount;
  S17 completedLFunctionPrimitiveFamilyZeroDensityVerticalWindowCount:
  primitive-character zero-count definitions; no Gamma jump comparison.
- S15 primitiveFibreGammaAtom; S19 primitiveFibreModularTilt_mul_reflection:
  discrete valuation geometric atom/modular tilt, not shape2j ratep law.
- S18 thetaCuspPrimitiveRayMoment=u(1−u): angular coordinate for a density
  product, no positivity/summability/infinite log identity.

All prose P0–P9 and source passages T0–T9:

- P0 constraints-snapshot4909–4965: smoothing/order alone not a producer;
  source-specific completion still needed. P1 RoutePPrimitiveGammaSewnGreen
  threshold1–138: sharp double-Green prime smoothing, not actual tau.
  P2 fzz-p-subtracted-external-gamma64–85: different Gamma subtraction;
  P3 hypertranscendental-conservativity-spectrum119–238: reporter/gauge model;
  P4 burnol-sonin-off-axis-aperture-type-rigidity282–392: Mellin/Gaussian
  completion; P5 rh-route-literature-exchange2128–2206: spectral occupancy/
  Suzuki exterior; all observable mismatches explicitly inspected.
- P6 li-clock-signed-gamma-jump-coupling172–269: exact PRIOR overlap N9–N15,
  full signed L1, pointwise P/t, genuine integer CP coupling; reused, not new.
- P7 deninger-arithmetic-lefschetz-determinant-comparison111–179:
  prospective source cohomology, no closed density comparison.
  P8 route-e-squarefree-exponential-gibbs-parity1021–1147: different Möbius
  prime-Gamma seam; P9 suzuki-gamma-wall-block-hardy651–733: different physical
  carrier/support gate; neither identifies actual reciprocal Gamma law.
- T0 RoutePPrimitiveGammaSewnCriticalGreenThreshold1–112 matches S0/S6;
  T1 ArchimedeanMellinFourier1–120 supplies actual Gamma integral/Gaussian
  Fourier normalization, no intensity order; T2 ChenGuptaLiSmoothedNonprincipalContour1–87;
  T3 ChenGuptaLiClassIMellinNormalization1–62;
  T4 ChenGuptaLiInfiniteMellinDetector105–153 each retains CGL different law.
- T5 XiCTaylorThetaTailPrimitiveRayPolarization1–112: exact five-mode radial
  polynomial source, explicitly asserts NO sign/convergence/gcd/limit theorem.
  It cannot orient logarithmic coefficients; no substitute identity supplied.
- T6 BondarenkoHeapLemmaTenConductorExpansion1–32;
  T7 ChenGuptaLiPositiveWindowZeroDensity1–50;
  T8 DirichletLZeroDensityPrimitive1–93: all primitive-character count transports;
  T9 PrimitiveFibreModularRenormalizationLaw1–114: exact valuation Gamma
  promotion/tilt factors. All returned source text read, wrong laws rejected.
- Ingredient I0 'Gamma smoothing and density comparison' proposes combining
  metric density smoothness with an algebraic primitive root, then a zero-count
  no-go with Gaussian integral. Those exact contracts cannot establish either
  target; generated ingredient set NOT_VERIFIED, rejected in full.

Current frontier Li section was read; it already records N17 OPEN and signed
Gamma coupling. Task-relevant STATUS patterns supplied no additional matching
source law; no full STATUS or corpus absence is asserted. Primary scoped rg
299/300 and mass fences yielded no direct exact bound; D1 is a checked source
combination, no world/corpus-wide novelty claim. Gamma CDF order, quantile
transport and CP marking are classical mechanisms; claimed survivor here is
only their exact source-specific conjunction with D1–D6, including all rows.

## 9. Exhaustive self-audit and disposition

D1–D20 proofs preserve literal Phi/M, ALL copies, SINGLE Xi normalization,
rate not scale, and distinct finite masses. Every infinite exchange has a
positive Tonelli or D2 full signed/polynomial L1 admission. GammaCDF has its
exact finite polynomial proof; transport uses continuous strictly positive
densities and equal matched masses; CP probabilities/equalities use full
positive infinite Poisson sums. Complex log branches are not inserted.
Extended-domain proof uses analytic identity, not an assumed zero-free disk.
No normalized-original-law order, fractional original divisibility, omitted
higher positive row, positive inverse or RH premise enters.

Outcome: attempted FIRST-ROW POINTWISE mechanism FALSE by D19; literal total
N17 still OPEN. Strongest proved positive salvage: D11 unequal-mass strict
quantile reserve + D14 positive exponentially marked density + D16 genuine
ALL-real-time CP coupling + D18 compensated ALL-order source derivative sign.
All are PAPER-only until independent audit/formal release. No route retirement,
RH proof/falsification, broad absence or novelty claim. Exact missing inequality
remains the unsmoothed full higher-row cancellation U+>=U−; current estimates
control cumulative/marked source only and do not decide it.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.LiClockThetaGammaCumulativeReserve`, `GaloisForLFunctions.RHTower.LiClockThetaGammaQuantileReserve`, `GaloisForLFunctions.RHTower.LiClockThetaGammaExponentialMarking`, `GaloisForLFunctions.HTGeometry.HalfLineQuantileTransport`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules (all `lake env lean` clean, `lake build --old` clean, every public constant audited to `[propext, Classical.choice, Quot.sound]`, wired into the umbrellas):
`GaloisForLFunctions.RHTower.LiClockThetaGammaCumulativeReserve` (D1–D10, D19, D20), `GaloisForLFunctions.RHTower.LiClockThetaGammaQuantileReserve` (paragraph-D7 reserve measure, D11, D12), `GaloisForLFunctions.RHTower.LiClockThetaGammaExponentialMarking` (D3 continuity, D13–D18), `GaloisForLFunctions.HTGeometry.HalfLineQuantileTransport` (quantile push-forward). The wide-domain (`p > 1/√150`) admissions of `LiClockThetaSignedGammaJumps` / `LiClockThetaCompactGammaMarking` are the `_wide` theorems (the `p > 1` statements are wrappers).

| Claim | Declaration |
|-|-|
| (D1) `M₀ > (299/300)A` | `normalizedPrimeArchMoment_zero_gt_mass` |
| (D2) `\|ℓ_j\| ≤ A q^{j-1}/(2jp²)`, tails, finite intensities, signed L¹, row L¹ = Σ\|ℓ_j\|, polynomial moments | `abs_liClockThetaLogJumpCoefficient_succ_le`, `liClockThetaLogJumpCoefficient_admission_wide`, `liClockThetaJumpMeasure_admission_wide`, `liClockThetaGammaJumpDensity_admission_wide`, `liClockThetaSignedGammaMeasure_admission_wide`, `liClockThetaSignedGammaDensity_moment_wide` |
| (D3) `σ_p(t) = e^{-pt}P(t)/t`, continuous | `liClockThetaSignedGammaDensity_eq_primitive_wide`, `continuous_liClockThetaSignedGammaDensity` |
| (D4) `Λ⁺ - Λ⁻ = Σℓ_j = H(p) > 0`, `Λ^± > 0` | `liClockThetaJumpMeasure_admission_wide`, `liClockThetaReciprocalLog_pos` |
| (D5), (D6) `Σ_{j≥2}\|ℓ_j\| ≤ T̄`, `δ > 0 ⟺ p ∈ D`, `p² ≥ 449/44850`, `p ≥ 1/9`, `δ > 19A/(40p²)` for `p > 1` | `tsum_abs_liClockThetaLogJumpCoefficient_tail_le`, `liClockThetaGammaReserve_pos_iff`, `LiClockThetaGammaReserveDomain.of_sq_ge`, `.of_one_ninth_le`, `liClockThetaGammaReserve_gt_of_one_lt` |
| (D7) Gamma CDF formula, `F_j > 0`, `F_j ≤ F_1`, strict for `j > 1` | `integral_liClockThetaGammaRowDensity`, `liClockThetaGammaRowCDF_one`, `liClockThetaGammaRowCDF_pos`, `liClockThetaGammaRowCDF_antitone_index`, `liClockThetaGammaRowCDF_lt_one_index`, `liClockThetaGammaRowLaw_Ioc` |
| (D8), (D9) `D_p(T) = τ⁺(0,T] - τ⁻(0,T] = Σℓ_jF_j ≥ δF_1 + (M₁/4p⁴)e^{-pT}(…) > δF_1 > 0` | `liEvenCrossActualClockDampedCutoff_eq_gammaJump`, `_eq_tsum_gammaCDF`, `_ge_gammaReserve`, `_gt_gammaReserve` |
| (D10) `H - δ ≥ Aq²/(12p²) > 0` | `liClockThetaGammaReserve_add_le_reciprocalLog` |
| (D11) `ρ = τ⁺ - δΓ₂` positive, `ρ ≥ T̄Γ₂`, `τ⁻ ≥ \|ℓ₂\|Γ₄`, mass `Λ⁺-δ > Λ⁻`, CDFs continuous/strictly increasing/limits, `R > G⁻`, unique `a_p`, `τ⁺ = δΓ₂ + χ + ζ`, masses `Λ⁻`, `H-δ`, quantile laws, `X < Y` | `liClockThetaGammaJumpMeasure_true_eq_reserve_add`, `liClockThetaGammaReserveRemovedDensity_ge`, `liClockThetaGammaRowLaw_one_smul_le_reserveRemoved`, `liClockThetaGammaRowLaw_two_smul_le_jump_false`, `liClockThetaGammaReserveRemovedMeasure_univ`, `liClockThetaJumpMass_false_lt_reserveRemoved`, `continuous_/strictMonoOn_/tendsto_liClockThetaGamma{JumpCDF,ReserveRemovedCDF}`, `liClockThetaGammaJumpCDF_false_lt_reserveRemoved`, `liClockThetaGammaQuantileSplit_spec`, `liClockThetaGammaJumpMeasure_true_eq_quantile`, `liClockThetaGammaQuantileHead_univ`, `liClockThetaGammaQuantileTail_univ`, `liClockThetaGammaJumpMeasure_false_Iic_le_head`, `map_liClockThetaGammaQuantileUpper`, `map_liClockThetaGammaQuantileLower`, `map_liClockThetaGammaQuantileUniform`, `liClockThetaGammaQuantile_lt`, `map_halfLineQuantile_eq` |
| (D12) bounded nonnegative tests nonincreasing on `(0,∞)`: `∫h d(τ⁺-τ⁻) ≥ δ∫h dΓ₂ ≥ 0`, strict when `∫h dΓ₂ > 0` | `liClockThetaGammaJump_integral_sub_ge_of_antitoneOn` |
| (D13) `τ̄^± = τ^± ∗ Exp_r` have continuous densities `g^±`, `g⁺ - g⁻ = κ` pointwise, `τ̄⁺ = τ̄⁻ + κ`, masses `Λ^±` | `liClockThetaMarkedGammaJumpMeasure_eq_withDensity`, `continuous_liClockThetaMarkedGammaJumpDensity`, `liClockThetaMarkedGammaJumpDensity_sub`, `liClockThetaMarkedGammaJumpMeasure_true_eq`, `liClockThetaMarkedGammaJumpMeasure_univ` |
| (D14) `κ > re^{-rt}δ(a)F_{1,a} > 0` (plus the D9 term), mass `H(p)`, all moments, lower-bound mass `δ(a)a²/p²` | `liClockMarkedDensity_gt_gammaReserve`, `liClockThetaMarkedSourceMeasure_univ`, `integrable_pow_liClockThetaMarkedSourceMeasure`, `integral_liClockMarked_gammaReserve` |
| (D15) `Lκ(s) = rH(p+s)/(r+s)`, `L Exp_r = r/(r+s)`, `Lτ̄ = Lτ·r/(r+s)`, `∫e^{-st}σ_p = H(p+s)`, `log Lμ_p = H(p+s) - H(p)` | `laplace_liClockThetaMarkedSourceMeasure`, `laplace_expMeasure`, `laplace_liClockThetaMarkedGammaJumpMeasure`, `liClockThetaGammaExponentialMarking_laplace` |
| (D16) `CP(η+ξ) = CP(η) ∗ CP(ξ)`; `CP(vτ̄⁺) = CP(vτ̄⁻) ∗ CP(vκ)` for every real `v ≥ 0`; product coupling; increasing tests | `compoundPoisson_intensity_add`, `liClockThetaMarkedCompoundPoisson_coupling`, `liClockThetaMarkedCompoundPoisson_product_coupling`, `liClockThetaMarkedCompoundPoisson_monotone_integral` |
| (D17) `L CP(vκ)(s) = exp(v(rH(p+s)/(r+s) - H(p)))`, `=1` at `s=0`, exponent via `log Lμ_p` | `laplace_liClockThetaMarkedSourcePoisson`, `laplace_liClockThetaMarkedSourcePoisson_zero` |
| (D18) `(-1)^n h^{(n)}(s) = ∫t^ne^{-st}dκ > 0` on `s > -r`; compensated sums `> 0`; `κ ≤ τ̄⁺+τ̄⁻`; `∫e^{2εt}d(τ̄⁺+τ̄⁻) = r/(r-2ε)Σ\|ℓ_j(p-2ε)\|`; tilting `∫e^{ct}dτ^± = Λ^±_{p-c}` | `iteratedDeriv_liClockThetaMarkedTransform`, `compensated_liClockThetaReciprocalLog_pos`, `liClockThetaMarkedSourceMeasure_le`, `laplace_neg_liClockThetaMarkedGammaJumpMeasure_add`, `laplace_neg_liClockThetaGammaJumpMeasure` |
| (D19) `τ⁻/(ℓ₁f₁) ≥ M₁t²/(12M₀)`; first row does not dominate | `liClockThetaGammaJumpDensity_false_div_first_row_ge`, `not_forall_liClockThetaGammaJumpDensity_false_le_first_row` |
| (D20) `τ^± = e^{-pt}U^±`, `U^± > 0`, ratio independent of `p`, `U⁺ ≥ U⁻ ⟺ P ≥ 0` | `liClockThetaGammaJumpDensity_eq_exp_mul_undamped`, `liClockThetaMarkedJumpDensity_pos`, `liClockThetaGammaJumpDensity_ratio_eq`, `forall_undamped_le_iff_primitive_nonneg` |

The (OPEN) row `U⁺ ≥ U⁻ ⟺ P ≥ 0` is recorded as the open residual (its equivalence is proved; the sign itself is not claimed). Laplace uniqueness (`finite_halfLine_laplace_ext`) proves the real-time CP identity; the pointwise D13 density identity is proved directly from `conv_withDensity_eq_lconvolution`.

## Log

- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
