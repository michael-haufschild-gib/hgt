# Reciprocal-Xi raw degree transport and completed pole cancellation

- **ID:** LI-CLOCK-RECIPROCAL-RAW-DEGREE-POLE-BOUNDARY
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / exact same-source boundary
- **Parent:** [single-damping source sign](../1-in-progress/li-clock-single-damping-strip-sign.md)
- **Statement:** Every fixed actual tilt has positive-degree means increasing to infinity but sublinear in order; all successive raw ratios from n>=1 exceed their limit. For1<p<2 the complete prime/completion pole terms cancel exactly at all orders, while each component has alternating eventual signs.

## Gates

- [x] Complete441-line corrected source proof and all-order admissions.
- [x] Independent root ALL441/A1–A17 review and exact source checks.
- [ ] Exact Lean formalization with full compiler/source/integration gates.

The signed logarithmic recurrence remains OPEN. These source laws do not prove RH or all-order signs at unbounded dampings. The row ratio retains z²; the tail threshold depends on fixed z. No raw ratio assertion includes a1/a0. No route retirement.

Complete report follows verbatim: `/tmp/li_producer_single_damping_source_attack.md`, SHA256 `000c0fb60fcbc930b490505898f65fb361fed83a67353aef2c2da74bf4fcef9a`. Independent review: `/tmp/li_root_single_damping_source_review.md`.

# Literal reciprocal-Xi logarithm beyond unit damping: source attack

Scope: read-only paper/source. No Lean, compiler, numerical jobs, source/card edits,
or new agents. Verdict: OPEN for the requested all-order logarithmic signs at an
unbounded set of p>1. Two dependency-closed same-source survivors are established
below: exact all-order raw-degree transport, and complete prime/completion pole
cancellation for 1<p<2. Neither is promoted to a logarithmic sign theorem.

## 1. Literal source, normalization and objective

Let k=thetaCuspFullSource, R_j=2 integral_(0,infinity) x^(2j) k(x) dx,
nu_j=R_j/R_0. Every nu_j>0 and nu_0=1. The SINGLE normalized entire source is

  Phi(z)=XiC(-I*z)/XiC(0)=xi(1/2+z)/xi(1/2)
        =sum_(j>=0) nu_j*z^(2j)/(2j)!.

No symmetrized-square partition replaces this source. Fix p>0, z=1/p. On the
real axis Phi(z)>0. Define H(p)=log Phi(1/p), and the genuine local logarithm

  Q_z(u)=Phi(z/(1-z*u))/Phi(z),
  log Q_z(u)=H(p-u)-H(p)=sum_(n>=1) b_n(z) u^n.

Thus b_n=(-1)^n H^(n)(p)/n!, and the parent card's expression with denominator
(n-1)! is n*b_n. Its sign is exactly the sign of b_n, for n>=1. Constants,
R_0, xi(1/2) and the local branch normalized to log Q_z(0)=0 are retained.

The parent/Current exact full-copy strip classification is a separate task.
This report does not redo that receiver or claim that raw positivity proves it.
The RH-bearing request here is an independent source estimate giving ALL b_n>=0
at an unbounded set of p>1. No such estimate closes below.

Source anchors actually read:
- XiEntireReal.lean22/39: XiC coordinate and entire function.
- PrimeArchThetaCumulantMinor.lean151/267 and439-446: literal R_j/nu_j,
  exact even XiC derivatives.
- PrimeArchThetaAllOrderCumulant.lean33-47: ALL parity-coded central jets.
- XiCTaylorThetaTailMomentLogConvex.lean16-40: every R_j>0, with genuine L1
  and open positive support. LiEvenCrossActualClockBorelSource.lean33-38:
  every normalized nu_j>0 and nu_0=1.
- Frozen /tmp/li_producer_integrated_clock_cumulant_attack.md349 C7-C17:
  whole-complex source/MGF admissions, complete germ and signed recurrence.

## 2. Complete all-order raw-degree transport, n>=1

Put c_j=nu_j*z^(2j)/(2j)!. The complete negative-binomial expansion gives

  a_0=1,
  a_n=z^n/Phi(z) * A_n,
  A_n=sum_(j>=1) w_(n,j),
  w_(n,j)=c_j*choose(2j+n-1,n)>0,  n>=1.                 (A1)

The index restriction is essential. j=0 contributes to a_0, and contributes
ZERO at every n>=1. None of the ratio statements below concerns a_1/a_0.

Admission for all exchanges: for |u|<=r<1/z, the sum of absolute double-series
terms is exactly bounded by Phi(z/(1-z*r))/Phi(z). For fixed n, every j-power
weighted row is summable: choose(2j+n-1,n) is a polynomial of degree n in j,
and moving the actual entire tilt from z to 2z absorbs every fixed j-power
with geometric slack 4^j. This covers all first/second degree moments, every
normalization, and each sum below. It is a complete j sum, not a truncation.
An alternative explicit source envelope is nu_j<=(32/303)^j*j! from
LiEvenCrossActualClockBorelSource.lean41-61; (2j)!>=(j!)^2 yields the required
factorial domination. The actual Taylor identity itself uses the Xi jets.

Let P_n(j)=w_(n,j)/A_n on j>=1 and mu_n=E_n[2j-1]. Exact binomial algebra is

  w_(n+1,j)/w_(n,j)=(2j+n)/(n+1)
                  =1+(2j-1)/(n+1).

Consequently the SAME raw germ satisfies

  a_(n+1)/(z*a_n)=1+mu_n/(n+1), n>=1;                  (A2)
  mu_(n+1)-mu_n=Var_n(2j-1)/(n+1+mu_n)>0.             (A3)

For (A3), the new law is the normalized affine degree tilt of the old law;
subtract E_n[2j-1] after computing its second moment. Strict variance uses
actual j=1 and j=2 positive masses, not an auxiliary distribution assumption.
All denominators are positive.

Every fixed degree head escapes. For j fixed,
choose(2j+n-1,n)=choose(2j+n-1,2j-1) is a polynomial in n of degree2j-1 with
positive leading coefficient. Given J>=1, the sum of rows j<=J divided by
row J+1 tends0, hence their P_n mass tends0. It follows that

  mu_n>=(2J+1)*P_n(j>J),  and mu_n tends +infinity.     (A4)

This uses the whole denominator A_n>=w_(n,J+1), so it remains valid despite
arbitrarily high positive degrees. No claimed typical-degree asymptotic is used.

### 2a. Actual score bound closes mu_n/n ->0

The installed source Ward recurrence, retaining every atom and the SAME R_0, is

  303*nu_(j+1)<=(32j+17)*nu_j, all j>=0.              (A5)

PrimeArchThetaScoreMomentRecurrence.lean124-150 proves exactly this inequality.
For j>=1 it implies nu_(j+1)/nu_j<=j. The exact row ratio is therefore

  w_(n,j+1)/w_(n,j)
    =z^2*(nu_(j+1)/nu_j)*(2j+n)*(2j+n+1)
       /[(2j)*(2j+1)^2*(2j+2)]
    <=z^2*(2j+n+1)^2/(16*j^3), j>=1.                    (A6)

Both consecutive factorial factors are present. The denominator lower bound
is16*j^4 before cancelling the source factor j. The factor z^2
is retained at arbitrary fixed z>0; it may be bounded by1 only for p>=1.

Fix epsilon>0 and let J_n=max(1,ceil(epsilon*n)). For j>=J_n,

  (2j+n+1)/j<=3+1/epsilon,
  w_(n,j+1)/w_(n,j)<=z^2*(3+1/epsilon)^2/(16*epsilon*n).

Thus this ratio is <=1/2 for ALL j>=J_n and all sufficiently large n. The
constant is fixed once epsilon AND z are fixed, and the range is the full infinite
row tail. Iteration gives w_(n,J_n+k)<=2^(-k)*w_(n,J_n). Consequently

  sum_(j>J_n) (j-J_n)*w_(n,j)
    <=w_(n,J_n)*sum_(k>=1) k*2^(-k)=2*w_(n,J_n)<=2*A_n.

The head contributes at most J_n*A_n. Hence

  E_n[j]<=J_n+2,
  mu_n<=2*J_n+3,
  limsup mu_n/(n+1)<=2*epsilon.

Since epsilon is arbitrary and mu_n>=1, the full conclusion is

  mu_n/(n+1)->0.                                     (A7)

Combining (A2),(A4),(A7), for every fixed ACTUAL z>0,

  a_(n+1)/a_n>z for n>=1;
  a_(n+1)/a_n->z;
  (n+1)*(a_(n+1)/(z*a_n)-1)=mu_n->+infinity.         (A8)

This strengthens the previously audited exact raw radius and failure of
EVENTUAL raw log-convexity. In particular the ratios cannot eventually be
nondecreasing: each is >z and their limit is z. No statement about a_1/a_0
is made. The full raw law applies also at arbitrarily large p; its transfer
to logarithmic coefficients remains the hard step.

### 2b. Attempted logarithmic propagation: exact unresolved subtraction

The complete genuine local identity Q_z'=Q_z*(log Q_z)' gives

  n*a_n=sum_(k=1..n) k*b_k*a_(n-k),
  b_n=a_n-(1/n)*sum_(k=1..n-1) k*b_k*a_(n-k).         (A9)

Equivalently, b_n is the finite alternating composition sum

  sum_(m=1..n) (-1)^(m+1)/m *
    sum_(k_1+...+k_m=n, all k_i>=1) a_(k_1)...a_(k_m).

I tested the exact degree-tilt law (A2)-(A7) against (A9). It supplies full
positive raw ratios and degree moments, but no bound on the signed history
sum in (A9). Even strict increase of mu_n does not give monotonic raw ratios:
the ratio comparison would require

  Var_n(2j-1)>=mu_n*(n+1+mu_n)/(n+1),

which was not derived from the actual Ward recurrence; eventual raw
log-convexity in fact fails. No sufficient logarithmic propagation inequality
is proved here. This is an explicit unsuccessful attempt, not a claim that
all conceivable uses of the Ward identities are excluded. Stating b_n>=0
or (A9)'s desired inequality as a premise would merely restate the target.

## 3. Euler-side attempt: exact all-order pole cancellation for1<p<2

This interval permits an independently convergent prime source at the tilt,
but does not contain an unbounded set of dampings. Fix1<p<2, d=2-p>0,
s(u)=1/2+1/(p-u), s_0=s(0)>1. Literal factorization and Gamma recurrence give

  xi(s)=(s-1)*pi^(-s/2)*Gamma(1+s/2)*zeta(s).         (A10)

XiLogDerivFactorization.lean77-94 proves the four-factor identity on Re s>1;
its exact shift to(A10) is Gamma(v+1)=v Gamma(v), v=s/2. Define local logs
of positive real factors at u0, subtract their values there. No principal
complex logarithm is used across an unverified branch cut.

Let alpha_n be the Taylor coefficients of the completion log, and zeta_n
the coefficients of log zeta(s(u))-log zeta(s_0). The elementary factor obeys

  log[(s(u)-1)/(s_0-1)]=log(1+u/d)-log(1-u/p).         (A11)

The remaining completion log
log[pi^(-s(u)/2)*Gamma(1+s(u)/2)] is holomorphic on |u|<p: Re(p-u)>0 implies
Re s(u)>1/2, and its Gamma argument has real part>5/4. The exponential factor
and Gamma are analytic and nonzero there; a holomorphic logarithm exists on
this simply connected disk. Thus for any d<r<p, Cauchy estimates give

  alpha_n=(-1)^(n+1)/(n*d^n)+O_r(r^(-n)),
  n*d^n*alpha_n-(-1)^(n+1)->0.                       (A12)

The 1/(n*p^n) term from(A11) is included in the analytic remainder. Therefore
this LITERAL completion component has negative even coefficients and positive
odd coefficients for every sufficiently large order. It cannot be treated as
an independently nonnegative contribution to the desired all-order sum.

### 3a. Complete Euler coefficients and genuine interchange

On Re s>1,

  log zeta(s)=sum_(ell prime) sum_(k>=1) ell^(-k*s)/k.

This is the local real-normalized holomorphic log. Exact Mathlib source:
NumberTheory/EulerProduct/DirichletLSeries.lean57-70,137-162 gives genuine
norm-summability and riemannZeta_eulerProduct_exp_log; ExpLog.lean39-46 gives
the exponential of the full prime logarithm sum. Expanding -log(1-ell^-s)
uses its absolutely convergent disk series, since |ell^-s|<1.

For any rho<d, the complete circle/disk |u|<=rho has
Re s(u)>=1/2+1/(p+rho)>1. Prime-power sums converge locally uniformly there.
For each FIXED n their exact coefficient is

  zeta_n=p^(-n)*sum_(ell prime)sum_(k>=1)
             ell^(-k*s_0)/k * P_n(k*log ell/p),
  P_n(x)=sum_(m=1..n) choose(n-1,m-1)*(-x)^m/m!.      (A13)

Indeed exp[-a/(p-u)]=exp(-a/p)*exp[-(a/p)*(u/p)/(1-u/p)] and
[u^n](u/(1-u))^m=choose(n-1,m-1). The polynomial is signed; retaining it
is essential. Fixed-n absolute summability follows from integer sums of
m^(-s_0)*(log m)^n, s_0>1, and unique prime-power representation.
No growing-n interchange with a fixed prime tail is used.

### 3b. Pole fill, domain check and exact cancellation

Let U(s)=zetaResidueUnit(s), the entire filling of(s-1)zeta(s), with U(1)=1.
ZetaLogDerivResidue.lean61-99 proves the filling and its entire analyticity;
113-131 proves logDeriv zeta=logDeriv U-1/(s-1), with explicit nonzero guards.
HedenmalmThetaMobiusPoleUnitStrictTransverseCurvature.lean221-235 proves
xi(s)=(s/2)*GammaReal(s)*U(s) on the FULL Re s>0, including1. Equivalently,

  xi(s)=pi^(-s/2)*Gamma(1+s/2)*U(s).                 (A14)

Here no value of totalized zeta at its pole is substituted.

U(s(u)) and xi(s(u)) are nonzero on |u|<=d. To verify the complete disk,
write u=x+i*y, q=p-u. Then q!=0, and

  (p+d)*(p-x)-|q|^2=p*d+(p-d)*x-|u|^2
    >=(p-d)*(d+x)>=0.

Thus Re(1/q)>=(p+d)^(-1)=1/2 and Re s(u)>=1. The actual unconditional
xi_ne_zero_of_one_le_re (RHLadderTheory.lean123-130) excludes Xi zeros there.
The nonzero Gamma unit in(A14) then excludes U zeros, including s=1.
This uses only the known critical-strip zero exclusion, not a narrower strip
or RH. Compactness and analyticity give SOME r_U>d, r_U<p, on which both
units remain nonzero. No uniform r_U(p), or full radius p for the logarithm,
is inferred. Choose d<r<r_U. Local logs continue to this disk, so

  zeta_n=(-1)^n/(n*d^n)+O_r(r^(-n));
  b_n=alpha_n+zeta_n=O_r(r^(-n));
  n*d^n*b_n->0.                                     (A15)

The two leading pole coefficients cancel EXACTLY. Whole b_n signs are not
settled by(A15). This is a genuine all-order arithmetic cancellation survivor
and a failure of the proposed separate nonnegative-factor estimate. It is
not a negative example for the literal full logarithm or for the finite-window
sign candidate. The actual full source and every completion factor remain.

## 4. Beyond Euler convergence: actual paired eta, no black-box source

For every real s>0 let

  S=union_(n>=0) (log(2n+1),log(2n+2)],
  L(s)=integral_S exp(-s*x) dx,
  L_1(v)=integral_(0,log2] exp(-v*x) dx.

The UNION and every gap are retained. L(s) is genuinely absolutely convergent
on Re s>0, all derivatives have polynomial L1 admissions there, and L_1 is
entire. Existing literal source identities are

  eta(s)=s*L(s), d_eta(s)=(s-1)*L_1(s-1).

Consequently the filled completion gives, on a regular neighborhood of every
real s>0, including the filled point1,

  xi(s)=pi*s*GammaReal(s+2)*L(s)/L_1(s-1).            (A16)

At real s all four factors are positive and L_1(s-1)>0. The positive source
and the denominator are distinct: L is the full arithmetic union; L_1 is
only its first interval. The logarithm has the exact local decomposition

  log xi(s(u))=log pi+log s(u)+log GammaReal(s(u)+2)
                +log L(s(u))-log L_1(s(u)-1).         (A17)

Constants are removed by subtraction at u0. For arbitrary p>1, s_0>1/2;
(A17) is an independently convergent, source-preserving local representation,
not an uncontrolled continued zeta'/zeta. This representation already belongs
to the inspected paired-eta source infrastructure; no novelty is claimed.

Exact source contracts read for(A16)-(A17):
- RiemannGaussian/RiemannXiSuzukiPositiveCriticalStripEtaInfiniteLaplaceMeasure:
  35-43 support/measure;115 partition;150-192 complete L1/integral;
  195-215 eta=sL;233-239 eta-factor/zeta identity.
- RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMoments.lean68-132:
  actual MGF identification, all polynomial tilted L1 and derivative moments.
- RiemannXiSuzukiPositiveCriticalStripEta.lean138-147: eta=d_eta*zeta,
  Re s>0,s!=1, before filling.
- LiClockPairedEtaFiniteFilledDeflation.lean69-74: d_eta=(s-1)L_1(s-1),
  all complex s;33-39: entire finite partitions;77-80: shifted Gamma factor.
- (A14), GammaReal shift, and eta=sL derive(A16) off1; continuity fills1.

The attempted comparison still subtracts log L_1 from log L. Positive measures
make raw derivative moments controlled; they do not supply the required sign
of every complete logarithmic difference after rational pullback. No pointwise
limit of the alternating interval indicator, contiguous replacement, arbitrary
positive-Laplace model, or assumed cumulant sign is used. The missing signed
history is precisely(A9) for the SAME Phi, or the canceled coefficient sum in
(A17). I have no independent inequality controlling it at unbounded p.

## 5. Prior retrieval and complete disposition ledger

Direct documented deep command (no help/search-source preparation):

  python3 scripts/formal_tools.py research "actual theta Phi reciprocal logarithm all order complete monotonicity one damping beyond unit positive raw coefficient logarithmic signed convolution recurrence prime Gamma comparison" --mode deep --budget-seconds 120 --no-refresh --json

Output /tmp/li_producer_single_damping_source_research.json; session60262 exit0.
Elapsed96.523629541s; partial=true. ALL61 returned records processed:20 candidate
statements,20 source arguments including supplied method/proof excerpts,
10 prose,10 source passages,1 ingredient set. No other hit arrays had records.
Inventory63621/63621 indexed, pending0 (Lean53372/prose10249). Retrieval1166689;
coverage1166694/current1166695 snapshot. Semantic coverage unmeasured/unavailable.
Unfinished damping-factor query and reranking; local-runtime reranking deadline.
Compiler buckets43 compiled_snapshot,2 error,10249 not_applicable,47974 pending,
2660 stale,38 stale_snapshot,1 umbrella_source_only,2654 unavailable. Methods
42 failed/396991 ready/186643 stale. These are retrieval freshness, not validation
of any current Lean source. No compiler was run in this task.

Candidate order/disposition (C index is JSON array index):
- C0 EulerDeletionLogPrimeForcing logarithmic convolution: divisor algebra,
  not the present positive source or logarithm sign.
- C1 CCM logarithmic kernel convolution: generic definition only.
- C2 Hedenmalm compact recurrence: supplied symmetry criterion/receiver.
- C3 integrated scaling convolution: generic transformation, no source sign.
- C4 Sieve truncated Mangoldt convolution: finite arithmetic identity only.
- C5 logLaplace convolution additivity: needs an actual convolution factorization
  of this theta law, not provided.
- C6 IntegerBeurling abscissa: assumes different arithmetic sign.
- C7 thetaRenewalDenominator_eq: actual source coordinate identity; read primary
  ThetaRenewalIncrement.lean277-309, preserving TWO weighted reflected factors.
  It is not Phi's reciprocal logarithm.
- C8 thetaInc_pos: positive renewal increment, no logarithm orientation.
- C9 sumIccMangoldt convolution: finite identity, no completed phase control.
- C10/C13 Vaughan third-derivative estimates: different observable/fixed order.
- C11 Burnol logarithmic kernel: definition only.
- C12 Bottcher thetaFour: different theta source.
- C14/C16 renewal lambda coordinates: seam-coordinate definitions, not H.
- C15 renewal first-atom lower bound: wrong transform for logarithmic sign.
- C17/C18 GomesFock moment gauge invariance: unrelated source/phase.
- C19 Dirichlet convolution logarithmic product rule: algebra, not inequality.

Source-argument order/disposition (every full supplied statement inspected):
- S0 actual prime-coordinate L2 amplification: fixed packet, wrong observable.
- S1 Gomes orbit derivative; S2 quantum theta; S4 orbit bias; S9 SSH carrier;
  S11/S12 Fock gate; S15 enthalpy jump: unrelated source/target.
- S3 Hedenmalm signed stage correlation: defines a signed quantity, no sign.
- S5 actual theta complex casting and S17 Schwartz source: applicable source
  regularity only, no all-order logarithmic estimate.
- S6/S7 actual full-source logJet8/6: fixed x-derivative atom/likelihood splits,
  not reciprocal-H logarithmic orders.
- S8/S10 signed-theta finite matrices: definitions, no proved source positivity.
- S13 bilateral theta Fourier/Laplace identification: applicable coordinate weld.
- S14 literal Borel coefficient: actual nu_j/((2j)!)^2, not H Taylor coefficient.
- S16 first-atom continuity: regularity only.
- S18 CCM signed IMS localization: actual method excerpt read; different defect.
- S19 reflected eighth derivative: fixed-jet modular closure, wrong target.
The sole ingredient set combines C4 finite Mangoldt algebra with C7 renewal
identity. Its proposed coordinate matching/damping obligations are unproved;
no source-sign application accepted. Model's source-sufficiency assessment
is not evidence of the needed signed estimate.

All10 prose: P0/P1/P2/P4 are staged recursive/status/cleanup records; P3/P6
JAS singleton/prime-norm escape; P5 conditional C5D1 slope corridor; P7 coface
annihilator; P8 the already audited actual theta inverse291 boundary; P9
frontier topology. None supplies the present all-order sign beyond1.
All10 source passages:0/2 Fock gauge;1 Hedenmalm RH-conditional divisor
rigidity;3 Gomes orbit;4 CCM signed IMS;5 DampedPrimeSumAssembly complete
cos-floor source;6 Gamma-route harmonic class;7 Xi heat off-copy Turan;
8 PrimeLaplaceEvenFactorialTransport energy shift;9 Sieve conditional quadratic
mean-square. Every supplied passage was read; applicable regularity/algebra
was separated from source signs. No partial passage or mismatched phase was
promoted. Relevant new source proof here uses direct primary files above.

Broadened lexical command, after weak/partial deep results:

  python3 scripts/formal_tools.py research 'zetaResidueUnit logDeriv_zeta_eq xi_eq_four_factors' --mode lexical --any --exact --no-refresh --json

Output /tmp/li_producer_single_damping_pole_lexical.json; session68239 exit0.
ALL20 declarations,5 exploration and20 markers processed. No candidate/source
argument arrays returned. Lexical eligible40002,total110253,modules23897;
coverage/freshness/compiler/partial fields NOT REPORTED in this JSON. No inferred
refresh or completeness beyond returned arrays. OR matching expanded common
terms; the output is an inventory lead, not an exact applicability judgment.
D0 weighted argument principle;D1 endpoint pole-unit curvature;D2/D3/D5 local
pole-unit logD analyticity;D4 reflected conjugation;D6 filled right-half-plane
Xi factorization;D7/D8 left-edge bounds;D9 pole-weighted contour;D10 low-height
unit nonvanishing;D11 endpoint gamma;D12 multiplicity match;D13 exact logD pole
subtraction;D14/D15 zero transfer;D16 Xi/zeta logD identity;D17 local non-nullness;
D18/D19 four-factor identity/off-real variant. D6,D13,D18 were read at primary
proof bodies and support(A10)-(A15); no D1/D10 finite-order/low-height statement
is used as an all-order logarithmic producer. Exploration0 detector zero,
1 Wold operator identity,2 frontier-conditional logD bound,3 chi-reflection,
4 full-copy partial fraction: none orients the present source beyond1.
Markers0 Barnes residues,1 Harman multiplicity,2 sine logD reflection,
3 Estermann factors,4/7/8 Bottcher status,5 contour zeta reduction,
6 separated rays,9 Newton psums,10/11/12 Bottcher/hull topological gaps,
13 Hurwitz coefficient,14 Nyquist null,15 Suzuki missing correction,
16 Hurwitz exponential independence,17 Cassini charge,18 Xi fission,
19 nodal source gap: no marker supplies the requested sign; no exhaustion
of their modules or the wider corpus is claimed.

## 6. Final exhaustive mathematical self-audit and exact open burden

- A1: actual normalized single-source entire germ, all coefficients, genuine
  complete absolute/local-uniform exchange; n>=1 and j>=1 guards explicit.
- A2-A4: normalized degree tilt, finite second moments, positive variance,
  full fixed-head escape and diverging mu_n; no growing-order sampler.
- A5-A7: actual all-atom Ward recurrence; exact four-factor row denominator and z^2;
  fixed epsilon full-tail uniform ratio and weighted geometric summation.
- A8: all raw ratios n>=1, exact asymptotic and divergent correction;
  excludes a_1/a_0; no raw-to-log transfer assumption.
- A9: exact finite signed convolution/composition, unresolved sign clearly named.
- A10-A13: every completion factor, Gamma shift and branch guard retained;
  independent Euler convergence on proper local disk; fixed-order prime-power
  coefficient extraction admitted, no growing-order uniform tail assertion.
- A14-A15: genuine filled unit, full closed-disk inequality, known source
  nonvanishing only Re s>=1, compact extension and exact ALL-order cancellation.
  Completion sign failure is only a component-level mechanism obstruction.
- A16-A17: actual infinite interval union, two DISTINCT Laplace factors and
  normalizers; source L1 and derivatives, filled endpoint and local logs.
- All search arrays/metadata processed; exact source bodies underpin every
  applicable claim. No global novelty/absence claim, compiler-green claim,
  new Lean theorem, source interpolation, RH premise or artificial counterinput.

PAPER PASS for A1-A8 and A10-A17 with stated domains. Request remains OPEN:
no dependency-closed independent proof of b_n(p)>=0 for every n>=1 at an
unbounded set of p>1. The precise missing estimate is control of the actual
signed history in(A9), or equivalently the full canceled logarithmic source
sum(A17); none of the retrieved identities or actual score bounds closes it.
No extra theorem/module is recommended from merely restating that inequality.
