# Literal partition Borel kernels: critical quarter transition

- **ID:** li-clock-infinite-partition-critical-transition
- **Stage:** 3-formalized
- **Type:** THEOREM (complete paper, proof/API and formal gates PASS; external global lint errors recorded)
- **Source:** [complete infinite-source boundary](../3-formalized/li-clock-infinite-partition-density-tail-boundary.md), [subcritical quarter window](../3-formalized/li-clock-infinite-partition-quarter-window.md), [strict-supercritical paper](../3-formalized/li-clock-infinite-partition-supercritical-window.md)
- **Statement:** Determine the exact positive-real transition of the unchanged full actual/reference finite Borel kernels when the clock differs from log(2N)/4 by order sqrt(log(2N)).

## Goal

Classify the critical endpoint with a positive source-specific limit
law. Preserve both independent half-tilted source coordinates, both factorials,
and each source's own squared normalizer. This is an auxiliary source boundary
problem; completed-response orientation and RH remain OPEN.

## Exact paper-proved targets

Write L_N=log(2N), and let Phi be the standard normal distribution function.
For arbitrary natural nu(k)->infinity and real clocks t_k with
`(t_k-L_nu(k)/4)/sqrt(L_nu(k)) -> u`, where u is any fixed real number,
the paired full-source limits are

`exp(-2t_k) B_A,nu(k)(t_k) -> (lambda/2) Phi(-2u)`,
`exp(-2t_k) B_U,L_nu(k)(t_k) -> (1/2) Phi(-2u)`.

Consequences proved with the same quantifiers: actual/reference ratio tends
lambda; their unscaled real difference tends minus infinity; signed weighted
finite-minus-infinite errors tend `-(lambda/2)Phi(2u)` and `-(1/2)Phi(2u)`;
corresponding absolute and complex-norm errors at these real clocks have the
positive opposite limits. At t_N=L_N/4 this predicts lambda/4 and 1/4 for both
finite scaled values and weighted absolute approximation errors.

The shared strictly interior witness t_N=L_N/4-1 proves that no real sequence
tending to zero eventually bounds either weighted complex error uniformly on
the open or closed quarter disk. No assertion about arbitrary
complex phases in the transition, supercritical finite ratios, or RH is made.

## Proven mechanism

The full scalar factorial kernel F(w)=sum_j w^(2j)/((2j)!)^2 decomposes into
modified and ordinary order-zero Bessel series. This turns the leading
truncated exponential-density integral into half the distribution
of `(2*sqrt(t)+G1)^2+G2^2` plus a vanishing signed term, for independent
standard Gaussian coordinates.
That elementary quadratic representation proves the scale and constants
without numerical evidence. Every series/integral interchange, Gaussian
identity, negligible oscillatory term, boundary-loss estimate and actual
source transfer is covered by the complete paper below and independent audit.
All64 planned public declarations across three Lean leaves are formalized,
with complete root/independent proof and API audits and all-public axiom checks.
Global lint retains external reachability errors, listed below.

## Gates

- [x] Exact source-preserving question and attack mechanism recorded.
- [x] Complete prior-research and source applicability audit.
- [x] Dependency-closed paper proof of all proposed targets.
- [x] Independent complete paper and overlap audit; no publication novelty claim.
- [x] Exact Lean plan and complete independent target/dependency audit.
- [x] Complete implementation and scoped formal gates; global external lint errors recorded.
- [ ] Publication readiness.

## Log

2026-09-30 — COMPLETE CRITICAL TRANSITION / Stage3:
AngularKernel459/17, GaussianCutoff879/28 and literal Source854/19:
2192 lines,all64 planned public declarations (15 definitions,49 theorems).
Every public/private body and complete contract independently/root audited;
all named/direct/all-public axiom checks pass, no owned diagnostics/debt.
Final Source19 SHA256
`a2800d20c4ffda9458923c75439498004f6f53ecd5e2419b6a56c584e4d8a14b`;
complete11786,ALL19axes28228,named27377,direct65224,index25634 terminal0.
Unique umbrella imports and every generated API row verified. Named Source19
build replayed external dependency warnings/info; owned leaf clean.
Formal lint96627 terminal1:172 size warnings,12 external unreachable modules,
all classified, no owned finding. Global lint remains red. Full certificate
`/tmp/hgt-li-critical-source-final-certificate.md`; earlier17/28 final
certificates retained. Every paper target, full Gaussian law, exact source
normalization, all critical error limits and shared strict-interior quarter
obstructions now certified. Paper294 remains byte-exact. RH remains OPEN.

2026-09-30 — Complete Source19 proof/API audit PASS:
854 lines,2 definitions/17 public theorems/14 private theorems; frozen SHA256
`a2800d20c4ffda9458923c75439498004f6f53ecd5e2419b6a56c584e4d8a14b`.
ALL19 full contracts match plan; full core386/sequence169 mappings and every
new consequence/helper body reviewed. Complete11786 terminal0/EMPTY;
ALL19 axioms28228 terminal0, exact source-order foundations-only reports.
Independent98 `/tmp/li_pole_critical_source_complete_independent_audit.md`,
SHA256 `7c5164a8a8244962a4b076795d46de5a006c4c312299f80fa736e2e68adbcd6a`,
read ALL by root with corrected interior-clock proof spot-check. Root certificate
`/tmp/hgt-li-critical-source-complete-root-audit.md`. Exact tree copy and unique
umbrella import complete; named27377 running. Direct/index/lint pending;
whole card remains Stage2 until final gates. Initial850 composition failures
were corrected definitionally without changing targets or source support.

2026-09-30 — Qualified sequence3 scratch complete and full Source19 assembled:
Pole169 fragment SHA256
`56691d9538ad66635f311d03e3b67b91b6c4abfd21ef4f2be36f330965a245d2`,
three exact public scaled-limit/ratio/gap contracts and three private helpers.
Root read ALL169 proofs/complete API ledger and71 owner-certificate lines;
canonical386 prefix and entire fragment mechanically preserved in compiled547.
Full42290/ALL3axes42048 terminal0, empty diagnostics/foundations-only reports.
Root full audit `/tmp/hgt-li-critical-source-sequence3-root-audit.md` PASS.

Root assembled all19 planned exports in850 lines with14 private theorems;
all19 complete headers mechanically match frozen plan. Full check60762 and
Pole's independent review of all ten new consequences are in progress.
Quarter/interior theorems retain all six functions; common interior witness
retains both positive error floors and all four envelope obstructions.
No final full-module compile, tree promotion or Stage3 claim yet.

2026-09-30 — Literal source core6 complete dual proof/API PASS:
386 lines,2 clock definitions/4 public theorems/9 private theorems; frozen
`/tmp/hgt-li-critical-source-core-frozen.lean`, SHA256
`a55036aa91c1e706d78f5b48e10e4fec0ebb9080038f004e786ebd6524ae8f6f`.
Full raw176 and density121 bodies mechanically unchanged/private-only.
Exact reference scaled cutoff identity and actual scaled error constant proved
with genuine compact integrability and separate own normalizers. Fresh complete
source+ALL6axioms44152 terminal0, no warning/other diagnostic, foundations only.
Independent ALL386 certificate51 `/tmp/li_pole_critical_source_core_independent_audit.md`,
SHA256 `b3b6d6c971f91ca4b7bdf79124a6f68dc9358aa604f6d0415f330df9b859dc71`,
root read all and verified hash/API/support mappings. Canonical prefix released
for Pole's three qualified-sequence theorems. Root owns remaining ten
consequences and complete Source19 integration; no Source19 tree yet.

2026-09-30 — Gaussian28 full proof and API PASS:
879 lines,9 definitions/19 public theorems/36 private declarations; SHA256
`348ef9127c4e0b9f4db442d42f822abb66116ceb2379438bf7d5611c289b92bf`.
Root and independent reviewer covered ALL source: audited588-line byte-identical
prefix plus every new589–879 line; ALL28 full contracts match frozen plan.
Root `/tmp/hgt-li-critical-gaussian-complete-root-audit.md`; independent151
`/tmp/li_producer_critical_gaussian_independent_audit.md`, SHA256
`1db9988de56602601fe9291ae3f6e1f8f810c87c3e653503affb3b9c8e8962f2`,
read completely by root including hash-verified unchanged106-line prefix.
Full97070/ALL28axes90118/named90429/direct79928/index30282 terminal0;
exact tree copy, unique umbrella import and all28 generated API rows verified.
Lint26159 terminal1:172 size warnings and10 external unreachable modules;
all diagnostics/differences classified, no owned error/debt. Global lint red.
All axiom reports source-ordered and foundations-only. Gaussian28 FINAL_READY:
`/tmp/hgt-li-critical-gaussian-final-certificate.md`; Source19 imports released.

Root density121 support SHA256
`7acd5eeea4d556a17fbb9310c5e78b8908019132be7a6267f90aedca04fdb97a`
passed complete dual proof/source review, complete35381 and ALL3axes78163
terminal0. Independent64 `/tmp/li_pole_critical_source_density_independent_audit.md`,
SHA256 `e31ad0f4a15ac468cbd3d2a6ee7f0c8eee25b7aaad8fb5e07b2a63f3434294d7`,
root read all. Exact private integration released for closed reference density,
full actual raw error and genuinely admitted integrated error bound.
Root retains Source19 assembly/final gates; Pole assigned disjoint scratch
three qualified-sequence scaled-limit/ratio/gap proofs after root scaled4
support and Gaussian FINAL dependency release. All19 targets remain in scope.

2026-09-30 — Gaussian partial20 and literal raw2 complete proof audits:
Gaussian590 frozen SHA256
`a62e4f72300aac6cbedcadc0693f5f7b31194389f8f6418fe6885c68a93449c6`,
20 exports/29 private declarations; root and independent ALL-body/API PASS.
Independent106 `/tmp/li_producer_critical_gaussian_independent_audit.md`, SHA256
`6a909c8122a655686505182c1cf354f12a28689d0a324d1775fdd33667b15e52`,
read completely by root. Remaining eight callers are explicitly outside that
partial certificate; complete28 assembly is under owner compiler review.
G11 finite-measure cutoff-loss support71 passed complete dual review, clean
compile22679 and foundations-only axiom19837 checks; exact private integration
released. Its closed-band bound permits atoms and assumes only mass<=1.

Raw-source176 frozen SHA256
`a6d781f247d348c856c20f0c8549f94c6a1bd0199e3d333aaad01a2d242f4011`:
ALL2 public/5 private declarations read by root and independent reviewer;
complete10201/ALL2axes65724 terminal0, genuine compact L1 before full series
interchange, fold2 and separate own Z² verified. Independent40 certificate
`/tmp/li_producer_critical_source_raw_independent_audit.md`, SHA256
`4fdfe239b01f9e7e06c01c8e7beb13e878b4ca233fd1b255b8073f38916dcf7d`;
root read all and checked exact callers. This is support-only; Source19 tree
and Gaussian-dependent consumers remain gated. Root now implements approved
S02–S03 closed-interval reference density and actual raw-error integral bounds.
No full critical transition or RH completion claimed.

2026-09-30 — Angular17 FINAL_READY:
`LiClockCriticalAngularKernel.lean`,459 lines, SHA256
`4a72a69ecaac5f01c736f7fff434a4027cda22787a688928db8cf1a556157f1a`.
Complete root and independent ALL-body/API audits PASS; independent85 certificate
SHA256 `53bb3bd02070d87ba327d014f97023570aabb31c6d8b100280d9e46817dbd85a`.
Named53404/direct81417/ALL17axes15833 terminal0; own compiler logs clean,
all reports foundations-only. Unique umbrella import and all17 generated API
rows verified after index44522 exit0. Formal lint1026 exit1:172 size warnings
and12 external unreachable modules, zero Angular diagnostics; global lint
remains red. Complete certificate `/tmp/hgt-li-critical-angular-final-certificate.md`.
Dependent Gaussian and scalar asymptotic work may import this exact leaf.
Gaussian28 and literal Source19 remain unfinished; this card stays Stage2.
Source19 now root-owned, with its first two raw-source adapters prepared;
all Gaussian-dependent consumers remain held until Gaussian FINAL_READY.

2026-09-30 16:32 UTC — Complete angular17 scratch compiles with EMPTY log,
root17249 exit0. Frozen459 `/tmp/hgt-li-critical-angular-complete-frozen.lean`,
SHA256 `4a72a69ecaac5f01c736f7fff434a4027cda22787a688928db8cf1a556157f1a`:
four definitions, thirteen public theorems and nineteen private proofs.
All17 literal contracts match frozen plan after whitespace normalization;
root complete-body audit PASS. Producer independently reviews full leaf;
named/direct/all17 axiom gates remain pending. Exact Gamma support received
complete owner/root/independent review before private integration.
Translated Gaussian product/PDF support also passed complete two-proof review
and foundation-only axiom checks; released for exact private Gaussian integration.
Pole canonical CDF/kinematics/moving-threshold support303 compiles cleanly,
root read all bodies; full Gaussian28 and literal Source19 still unfinished.
No critical leaf is FINAL_READY; whole card stays Stage2 and RH remains OPEN.

2026-09-30 16:15 UTC — Root angular foundation scratch now compiles cleanly:
`/tmp/hgt-li-critical-angular-core-frozen.lean`,374 lines,16 of17 planned public
declarations. Full complex/real angular identities, complete parity/summability,
continuity, oscillatory bound and genuine exponential-majorant integrability
proved; compiler96250 exit0/empty. Exact Laplace-F formula remains the last
angular target. Current owns disjoint two-lemma Gamma support scratch; Pole
continues canonical Gaussian/CDF/kinematics support. No critical module is
FINAL_READY or promoted, and whole-card formal targets remain open.

2026-09-30 15:55 UTC — Complete independent formal-plan PASS:
`/tmp/li_current_critical_formal_plan_independent_audit.md`,209 lines/SHA256
`2e324c7b3541dee62dfa424c1c3b9cf21a7a1ba990a42d35d6e37eb95ccfd61f`.
Root read ALL and verified the source namespace correction: radial-power
substitution APIs are `MeasureTheory.integral_comp_rpow_Ioi` and
`MeasureTheory.integrableOn_Ioi_comp_rpow_iff`; frozen plan remains unchanged.
All64 contracts,5 groups,17 equations and genuine admissions retained.
Root owns Angular17, Pole Gaussian28, Current literal Source19 after its
separate supercritical gates. Only angular and independent Gaussian scratch
work released now; consumers import only exact FINAL_READY dependencies.
No critical source-tree promotion or theorem certification yet.

2026-09-30 15:40 UTC — Full three-leaf formal plan frozen:
`/tmp/hgt-li-critical-transition-formal-plan.md`,862 lines/SHA256
`c469de7a5e0aec95832eada2ee5e8d304a8468985b084d9c9bc932731c20e8f2`.
Root read ALL lines and checked all64 unique proposed contracts:15 complete
definitions and49 theorem headers. Complete root certificate:
`/tmp/hgt-li-critical-formal-plan-root-audit.md`. Every paper equation1–17,
all5 target groups, genuine admissions, both own squared normalizers and all
complex norm limits remain. Updated prior/source certificate is140 lines,
SHA256 `148fb86d8a89885521d2ed19089c9b67bfc45dd741632e31a9fb3e13c1aba506`;
root read ALL. Current is independently reviewing the full plan. No critical
Lean/compiler work released yet; source APIs still require toolchain probes.

2026-09-30 14:16 UTC — Root opened this separate paper-only card. Current
continues the approved strict-supercritical module; no critical-transition
Lean or compiler work is released. Frontier/STATUS explicitly leave the
critical endpoint open. Direct documented search
`scripts/formal_tools.py research 'critical quarter partition Borel transition' --json`
finished44475 exit0/15.427s, output `/tmp/hgt-li-critical-quarter-research.json`.
All20 candidates, all20 source arguments and all10 prose hits require review;
no declarations/exploration/source passages/proof ideas/ingredient sets.
Report partial=false, errors/unfinished empty; inventory63348 complete,
index/current generation1157425. Semantic coverage unmeasured; background
refresh incomplete. No absence, applicability or novelty conclusion yet.

2026-09-30 14:25 UTC — Root complete mathematical draft frozen in
`/tmp/hgt-li-critical-transition-paper-frozen.md`, 283 lines/SHA256
`aa1ad9ca2937151559254a3fb77259c655162bbbf442637aaec2687955e1b982`.
All five target groups receive explicit derivations: complete angular series,
translated planar Gaussian law, moving-threshold dominated convergence,
fixed-width split controlling the finite cutoff loss, actual-source transfer
with its own squared mass, all signed/absolute/complex-norm limits, and shared
strictly interior witnesses for both quarter-disk obstructions. Classical
Bessel series/integrals were cross-checked against NIST DLMF 10.2.2, 10.9.1,
10.25.2 and 10.32.1; the needed angular identities are also derived directly
in the draft. Complete prior-hit/source audit and independent all-proof
review remain required. Card stays CONJECTURE/Stage1; no Lean release.

2026-09-30 14:37 UTC — Complete prior/source audit PASS:
`/tmp/hgt-li-critical-quarter-prior-audit.md`,102 lines/SHA256
`41a1a14facfb5da9521311bdd350b29e02d701c35de265c405919a9511fb1880`.
Root read all50 dispositions and the full coverage/source ledger; independently
checked the exact public raw-deficit headers and unchanged Measure source hash.
The two-coordinate actual deficit is already publicly bounded by the exact
reference deficit, including the endpoint. Author paper v2 updates only the
audit metadata and this source citation: `/tmp/hgt-li-critical-transition-paper-v2.md`,
294 lines/SHA256 `677885f5528092893651f77cb3beb5ada9ff05b7a4557868ae903d9e5039f525`.
Old283-line freeze retained. Author verdict PASS on paper; producer is auditing
EVERY proof and target independently. Stage1 and no critical Lean release persist.

2026-09-30 14:44 UTC — Final independent full-paper PASS: `/tmp/hgt-li-critical-transition-independent-audit.md`,97 lines/SHA256 `e683214d786aad74318ec81371509d6c9c9be820415b69639cedc6c3214084ac`. Root READ ALL; every one of the17 equations and all5 target groups audited, with all source identities and exact normalizers. Card promoted Stage2. Complete immutable author v2 follows; its historical pending-independent sentence records the snapshot state, superseded by this certification. No critical Lean implementation released.

## Complete frozen paper proof

2026-09-30 14:58 UTC — Gaussian mechanism prerequisite audit complete:
`/tmp/hgt-li-critical-gaussian-prior-audit.md`,135 lines/SHA256
`27092cb196906213465625d2d50942a47cc6503307dbcf2450674a153a2dba78`.
Producer inspected ALL61 deep-search records, including every available
method/excerpt; root read the complete certificate and checked primary API
claims. No inspected record supplies the full transition theorem. Search
session92160 exited0,partial=false,57.690690375s; index generation1157769 is
older than coverage/current1157777, semantic coverage unmeasured, background
refresh incomplete, all40 ranked Lean records source-only/not-checked.
Installed polar/Jacobian, cosine recurrence, Gaussian probability/density,
CDF and dominated-convergence interfaces are source-read, unprobed. Exact
full-scope formal plan is being prepared; no critical Lean released.

<!-- BEGIN FROZEN CRITICAL PAPER -->
# The critical quarter transition of the literal partition Borel kernels

Root paper proof, 2026-09-30. Author verdict: PASS on paper. Complete prior-
research/source-applicability audit PASS; independent whole-proof audit remains
pending. No Lean implementation is claimed. All sources below are the unchanged
complete finite/infinite sources from the five FINAL partition modules.

## 1. Exact statement and source conventions

Put L_N=log(2N) for N>0. Let A be the literal infinite union of logarithmic
odd/even intervals and A_N=A intersect (0,L_N]. Let U_L=(0,L]. Each source has
two independently half-tilted coordinates. Denote its OWN half-tilt mass by
Z_A,N or Z_U,L, its raw even difference density by g_A,N or g_U,L, and its
complete Borel kernel by B_A,N or B_U,L. Write g_A for the infinite raw density,
Z=Z_A,infinity, c0=log(2)/2, and lambda=4c0/Z²=2log(2)/Z².

Previously certified facts: s=2-sqrt(2)>0; Z_A,N,Z_U,L_N>=s; Z_A,N->Z>0;
Z_U,L_N->2; 0<lambda<1. The infinite real kernels satisfy
exp(-2t)B_A,infinity(t)->lambda/2 and exp(-2t)B_U,infinity(t)->1/2 as t->infinity.
Their real restrictions agree with their complete complex kernels.

Let nu:Nat->Nat tend to infinity and let t_k be arbitrary real clocks. Fix
u in R and suppose

    (t_k-L_nu(k)/4)/sqrt(L_nu(k)) -> u.                         (T)

All expressions involving a positive prefix are used only eventually, when
nu(k)>0. There is no monotonicity assumption and no separate clock cap. Let
Phi(v)=(2pi)^(-1/2) integral_{-infinity}^v exp(-x²/2) dx.

The proposed theorem is the complete collection:

1. exp(-2t_k)B_A,nu(k)(t_k)->(lambda/2)Phi(-2u), and
   exp(-2t_k)B_U,L_nu(k)(t_k)->(1/2)Phi(-2u).
2. B_A,nu(k)(t_k)/B_U,L_nu(k)(t_k)->lambda, and their unscaled real
   difference tends to minus infinity.
3. The two signed weighted finite-minus-infinite errors tend respectively
   to -(lambda/2)Phi(2u) and -(1/2)Phi(2u). The two absolute errors and the
   two complex norm errors at those same real clocks tend to the positive
   opposite constants, with weight exp(-2t_k).
4. At t_N=L_N/4 the finite scaled values and weighted absolute/norm errors
   have limits lambda/4 and 1/4. At t_N=L_N/4-1 the same limits hold, and
   z_N=t_N is eventually a shared witness strictly inside |z|<L_N/4 with
   actual/reference weighted complex error floors lambda/8 and 1/8.
5. Separately for each source, there is no real sequence E_N->0 which
   eventually bounds its weighted complex approximation error for EVERY
   z in either the open or closed quarter disk. No E_N>=0 premise is added.

The weight on general complex disks is exp(-2|z|). Along the real clocks in
these conclusions t_k>0 eventually, so it is exactly exp(-2t_k).

## 2. Complete scalar series and an elementary angular representation

For w>=0 define absolutely convergent series

    H(w)=sum_{m>=0} w^m/(m!)²,
    J(w)=sum_{m>=0} (-1)^m w^m/(m!)²,
    F(w)=sum_{j>=0} w^(2j)/((2j)!)² = (H(w)+J(w))/2.             (1)

They converge uniformly on bounded w-intervals by the ratio test. No finite
Taylor truncation is used. For real q,

    H(q²/4)=(1/(2pi)) integral_0^{2pi} exp(q cos(theta)) dtheta,
    J(q²/4)=(1/(2pi)) integral_0^{2pi} cos(q cos(theta)) dtheta. (2)

Here is a direct derivation. If C_m is the average of cos(theta)^m over a
full period, odd C_m vanish by a half-period shift, C_0=1, and, for m>=2,
integration of the derivative of sin(theta)cos(theta)^(m-1) gives
m C_m=(m-1)C_(m-2). Thus C_(2j)=(2j)!/[2^(2j)(j!)²]. Expanding exp and cos
and integrating termwise yields (2). The absolute series are uniformly
bounded on the compact angle interval by exp(|q|), justifying these operations.
In particular |J(w)|<=1, while H(w)>=0 and F(w)>=0.

These are the classical I0(2sqrt(w)) and J0(2sqrt(w)) representations; the
derivation above supplies precisely the identities needed here. Primary
cross-checks are [DLMF 10.32.1](https://dlmf.nist.gov/10.32#E1),
[DLMF 10.9.1](https://dlmf.nist.gov/10.9#E1), and the defining series
[10.25.2](https://dlmf.nist.gov/10.25#E2),
[10.2.2](https://dlmf.nist.gov/10.2#E2), checked 2026-09-30.

## 3. A translated Gaussian gives the exact positive radial measure

For t>=0 let G1,G2 be independent standard Gaussian coordinates on R² and set

    Q_t=(2sqrt(t)+G1)²+G2².

Its law mu_t on [0,infinity) has Lebesgue density

    (1/2)exp(-2t-r/2) H(tr).                                  (3)

Indeed the translated planar Gaussian has density
(2pi)^(-1)exp(-((x-2sqrt(t))²+y²)/2). Use x=sqrt(r)cos(theta),
y=sqrt(r)sin(theta). The area element is (1/2)dr dtheta, so angular
integration is exactly (2), yielding (3). All integrands are nonnegative;
Tonelli and the usual polar change of variables apply. Gaussian normalization
therefore proves that mu_t is a probability, without an asymptotic formula.

Define the positive finite measure nu_t and signed measure omega_t by densities

    dnu_t(r)=(1/2)exp(-2t-r/2)F(tr)dr,
    domega_t(r)=(1/2)exp(-2t-r/2)J(tr)dr,                       (4)

on r>=0. Equations (1) and (3) give

    nu_t=(mu_t+omega_t)/2,    ||omega_t||_TV<=exp(-2t).          (5)

The total-variation bound follows from |J|<=1 and
integral_0^infinity (1/2)exp(-r/2)dr=1. In particular nu_t has total mass
at most (1+exp(-2t))/2<=1. These are full measures and full series; parity is
retained by the factor 1/2 in (5), not discarded in an approximation.

## 4. Moving thresholds and the Gaussian transition

Assumption (T) and L=L_nu(k)->infinity imply t_k/L->1/4 and hence t_k->infinity,
t_k>0 eventually, and sqrt(t_k)/sqrt(L)->1/2. Consequently

    (L-4t_k)/(4sqrt(t_k)) -> -2u.                              (6)

The exact identity

    (Q_t-4t)/(4sqrt(t)) = G1+(G1²+G2²)/(4sqrt(t))              (7)

holds for t>0. For each fixed Gaussian pair with G1!=-2u, (6) and (7) imply
that the indicator of Q_tk<=L eventually equals the indicator of G1<-2u.
The exceptional vertical line has Gaussian measure zero, since the joint
law has a Lebesgue density. Dominated convergence, with bound 1, gives

    mu_tk([0,L]) -> Phi(-2u).

Combining with (5) proves

    nu_tk([0,L]) -> (1/2)Phi(-2u).                             (8)

For every FIXED K>0 the same reasoning works with L-K, since the extra
threshold term -K/(4sqrt(t_k)) tends to zero. Both measures have Lebesgue
densities, so endpoints have zero mass and

    nu_tk([L-K,L]) -> 0.                                      (9)

No central limit theorem, Bessel large-argument expansion, clock monotonicity,
or change in the finite source is needed for (8)-(9).

## 5. The finite cutoff loss tends to zero

Define, for L>0 and t>=0,

    R(t,L)=integral_[0,L] exp(-(L-r)) dnu_t(r).

For fixed K>0 and eventually L>K, split at L-K. Using positivity and mass<=1,

    0<=R(t_k,L)<=exp(-K)+nu_tk([L-K,L]).                       (10)

Given epsilon>0 first choose K with exp(-K)<epsilon/2, then apply (9).
Therefore R(t_k,L)->0. In raw-kernel notation the exact relation is

    exp(-2t) integral_0^L exp(-L+r/2)F(tr)dr = 2R(t,L).        (11)

This controls the whole boundary loss. No unjustified pointwise density
estimate or assumption of uniform convergence at r=L is used.

## 6. Complete source integrals and the reference limit

For either finite source X, the already-certified raw moment identity is
integral_R r^(2j)g_X(r)dr=Z_X² d_X,j. Density is even, nonnegative and supported
in [-L,L]. Therefore Tonelli applied to nonnegative terms, with both
factorials intact, gives for t>=0

    B_X(t)=(2/Z_X²) integral_0^L g_X(r)F(tr)dr.                (12)

Continuity/uniform convergence of F on [0,tL] and integrable compact density
also give finite integrability, so no totalized divergent integral is involved.
These are the original complete Borel series with coefficients d_X,j/((2j)!)².

The exact reference density on 0<=r<=L is
g_U,L(r)=exp(-r/2)-exp(-L+r/2). Substituting (4) and (11) into (12) gives

    exp(-2t)B_U,L(t)=(4/Z_U,L²)[nu_t([0,L])-R(t,L)].           (13)

Because Z_U,L=2(1-exp(-L/2))->2, (8), (10) and (13) prove the reference limit
(1/2)Phi(-2u). Its OWN squared mass is used throughout.

## 7. Literal actual-source transfer

For r>=0 the actual infinite raw density has the direct representation

    g_A(r)=integral_0^infinity 1_A(y)1_A(y+r)exp(-y-r/2)dy.

The exact set identity A_N=A intersect (0,L] implies, for 0<=r<=L,

    0<=g_A(r)-g_A,N(r)<=integral_(L-r)^infinity exp(-y-r/2)dy
                         =exp(-L+r/2).                       (14)

Both source coordinates remain: the cutoff y+r<=L is the tighter of the two
cutoffs when r>=0. Endpoints affect at most Lebesgue-null sets. For r>=L the
finite density is zero. This proves (14) from the exact source definition,
rather than replacing actual density by contiguous density.

The certified infinite density-tail theorem gives, for r>=0,

    |g_A(r)-c0 exp(-r/2)|<=C exp(-3r/2),  C=pi²/16.           (15)

Together (14)-(15) give on [0,L]
|g_A,N(r)-c0 exp(-r/2)|<=exp(-L+r/2)+C exp(-3r/2).
The remaining kernel majorant is integrable, with exact identity

    integral_0^infinity exp(-3r/2)F(tr)dr=(2/3)cosh(2t/3).     (16)

To verify (16), apply Tonelli to the nonnegative defining series of F and
integrate each even power using integral_0^infinity exp(-ar)r^m dr=m!/a^(m+1).
The latter follows by rescaling the exponential integral and m integrations
by parts; exponential decay kills all boundary terms. The resulting full
series is exactly (1/a)cosh(t/a), with a=3/2.

Equations (11)-(12), (15)-(16) prove the explicit finite estimate

    |exp(-2t)B_A,N(t)-(4c0/Z_A,N²)nu_t([0,L])|
      <=(4/Z_A,N²)R(t,L)+(4C/(3Z_A,N²))exp(-2t)cosh(2t/3).    (17)

Both terms tend to zero along (T): the denominator is at least s², R tends
to zero, and exp(-2t)cosh(2t/3) tends to zero as t->infinity.
Since 4c0/Z_A,N²->lambda, (8) and (17) prove the actual limit
(lambda/2)Phi(-2u), with its independent OWN normalizer retained.

## 8. All ratio, gap, error and exact-quarter consequences

For finite real u, 0<Phi(-2u)<1: the Gaussian density is strictly positive
on every finite interval and has unit mass. Thus the reference limit in (13)
is positive. Dividing the two weighted limits proves the ratio limit lambda.
Their weighted difference tends to (lambda-1)Phi(-2u)/2<0. Since t_k->infinity,
this implies the unscaled difference tends to minus infinity: eventually
the weighted difference is at most half its negative limit, while exp(2t_k)
exceeds every fixed bound.

Compose the certified infinite real scaling limits with t_k->infinity and
subtract them from the two finite limits. Symmetry of the standard Gaussian,
Phi(v)+Phi(-v)=1, gives the signed limits in item3. Absolute-value continuity
and exp(-2t_k)>0 give both absolute limits. The four finite/infinite ofReal
identities and the norm of a real complex number identify those functions
with the two complex norm errors on the eventual positive-prefix set. This
proves the complex norm LIMITS, not just their positive eventual floors.

For nu(k)=k and t_N=L_N/4, condition (T) holds with u=0 and Phi(0)=1/2,
yielding all lambda/4 and 1/4 limits. For t_N=L_N/4-1 the normalized deviation
is -1/sqrt(L_N)->0. Eventually L_N>4, so 0<t_N<L_N/4 and the SAME complex
witness z_N=t_N lies strictly inside the quarter disk for both sources.
Their positive norm-error limits imply eventual floors lambda/8 and 1/8.

If a real E_N->0 eventually bounded every weighted actual error on the open
quarter disk, intersect that eventual set with the witness set and
E_N<lambda/8. At z_N it would give lambda/8<=E_N<lambda/8, contradiction.
The reference proof uses 1/8. The same witnesses belong to the closed disk,
so the closed-disk statements follow by the identical contradiction. No
positivity premise on E_N or supremum construction is used.

## 9. Source ledger, overlap and exact limits of this claim

All source facts have previously been fully audited in the FINAL modules;
the following anchors identify their reuse, not newly compiler-verified APIs:

- InfinitePartitionMeasure:622/629/645 exact finite inclusion/intersection/
  restriction;667/675 both normalizer floors;1034/1041 both mass limits;
  raw density definitions, evenness, positivity and actual half-line domination.
- Its PUBLIC903/935 additionally give the exact two-coordinate raw deficit
  domination and reference piecewise deficit. Root checked both full headers
  and the unchanged source hash against the independent applicability report;
  together they directly imply (14), including the matching endpoint r=L.
- PartitionDensityRatio:281 reference raw density formula;357/367 compact
  supports;970/987 both raw moment identities; all own normalized densities.
- InfinitePartitionDensityTail:1340 full raw tail error bound;1480/1495
  0<lambda<1. Equation (14) is proved directly above from the exact source.
- InfinitePartitionBorel:1198/1203 infinite ofReal bridges and its certified
  infinite real scaling; finite ofReal bridges remain in the existing finite
  source modules. No private theorem is claimed as a public interface.

Prior-research report `/tmp/hgt-li-critical-quarter-research.json` received a
complete independent ALL50-hit/source applicability PASS in
`/tmp/hgt-li-critical-quarter-prior-audit.md`, 102 lines/SHA256
`41a1a14facfb5da9521311bdd350b29e02d701c35de265c405919a9511fb1880`.
Root read the whole certificate and independently checked the precise raw-loss
source interfaces and hash. All20 candidates,20 arguments and10 prose records,
including all8 generated methods, were processed; source-only applicability,
unmeasured semantic coverage and incomplete background refresh were retained.
No searched-corpus absence or full compiler coverage is inferred.
The angular Bessel formulas, translated Gaussian radial law and elementary
Gaussian limit are classical. No publication novelty is asserted. The proposed
source-specific content is the exact lambda factor for the unchanged actual
partition, its own normalization, the sqrt(log(2N)) transition scale and the
strictly interior obstruction at the quarter coefficient itself.

No arbitrary-complex-phase critical asymptotic, uniform-in-u error rate,
supercritical finite ratio, inverse-clock sign, completed-response orientation,
or RH conclusion is established by this draft. No route is retired; the
positive transition law, if fully certified, refines the auxiliary source
boundary while the original RH-producing inequality stays OPEN.

<!-- END FROZEN CRITICAL PAPER -->
