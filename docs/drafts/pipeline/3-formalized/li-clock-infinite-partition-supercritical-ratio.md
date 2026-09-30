# Literal supercritical partition ratio and endpoint profile

- **ID:** LI-CLOCK-INFINITE-PARTITION-SUPERCRITICAL-RATIO
- **Stage:** 3-formalized
- **Type:** THEOREM (complete paper and Lean; all37 public declarations fully audited)
- **Source:** [supercritical exterior decay](../3-formalized/li-clock-infinite-partition-supercritical-window.md), [critical transition](../3-formalized/li-clock-infinite-partition-critical-transition.md), [infinite source boundary](../3-formalized/li-clock-infinite-partition-density-tail-boundary.md).
- **Statement:** Exact positive prefactors and full finite actual/reference Borel ratio for every qualified real clock with t/log(2N)->c>1/4, retaining both source normalizers and the rapidly alternating upper endpoint.

## Goal

Both existing weighted kernels vanish beyond the quarter window. That proves
no ratio limit. The audited proof resolves the surviving source comparison by its literal
endpoint profile. No completed-clock compensation, inverse sign, or RH claim.

## Audited statements

Write A=union over n>=1 of (log(2n-1),log(2n)], Z=integral_A exp(-v/2)dv,
L_N=log(2N). Keep the actual finite union A_N=A intersect (0,L_N] and the
reference interval (0,L_N]. Let B_A,N and B_U,L_N be the established FULL
normalized Borel kernels, each retaining its own squared normalizer.

For c>1/4 put a=sqrt(c)-1/2>0 and

    E(s) = s * integral_A exp(-s*v)dv,  s>0.

For s>1, E(s) is the absolutely convergent alternating Dirichlet series
sum_(n>=1) (-1)^(n-1)n^(-s). Any use of this equality needs its exact source
derivation; a new source cannot be substituted by notation.

For arbitrary natural nu_k->infinity and real t_k with
t_k/L_(nu_k)->c:

    B_A,nu_k(t_k) / B_U,L_(nu_k)(t_k) -> 2*E(sqrt(c)+1/2)/Z^2.      (R)

Positive individual prefactors: with L=L_(nu_k), the limits

    sqrt(L)*exp(L/2-2*sqrt(t_k*L))*B_U,L(t_k)
      -> 1/[8*sqrt(pi)*c^(1/4)*a*(a+1)],                           (U)

    sqrt(L)*exp(L/2-2*sqrt(t_k*L))*B_A,nu_k(t_k)
      -> E(a+1)/[4*Z^2*sqrt(pi)*c^(1/4)*a*(a+1)].                 (A)

Complete255-line proof and independent audit establish these constants and
factors. The quotient follows by dividing positive prefactor limits; neither
simultaneous weighted decay nor earlier fixed-N/bulk limits supply it.

## Proof mechanism

For fixed y>=0 and N large, r=L_N-y gives the exact source identity

    exp(r/2)*g_A,N(r)
      = integral_[0,y] exp(-v)*1_A(v)*1_A(v+L_N-y)dv.              (E1)

The installed raw-density definition gives this orientation with boundary
changes confined to null sets. The upper indicator converges weakly against
the displayed lower-source weight to1/2; no pointwise convergence is used.
The proved profile is

    exp((L_N-y)/2)*g_A,N(L_N-y)
      -> (1/2)*integral_[0,y] exp(-v)*1_A(v)dv.                   (E2)

Reference profile is exactly1-exp(-y). A bounded periodic primitive proves
(E2) after x=exp(v), M=2N*exp(-y): integration by parts controls every
lower-source interval, including each partial final cell.

Full factorial kernel F(w)=sum_j w^(2j)/[(2j)!]^2 has positive real asymptotic
exp(2sqrt(w))/(4sqrt(pi)*w^(1/4)). The critical paper supplies complete angular
H/J identities; angular rescaling and Gaussian dominated convergence prove
the asymptotic and its global bound explicitly. No numerical evidence.

For t/L->c, the endpoint exponential tends exp(-a*y). Separate bounds handle
r<=L/2 and r>=L/2: the first contribution is exponentially negligible, while
the second has one integrable exponential majorant. Dominated convergence
and nonnegative Tonelli then give

    integral_0^infinity exp(-a*y)*(1-exp(-y))dy = 1/[a*(a+1)],
    (1/2)*integral_0^infinity exp(-a*y)
      *integral_[0,y] exp(-v)*1_A(v)dv dy
      = E(a+1)/[2*a*(a+1)].

Combine with Z_U,L->2 and Z_A,N->Z, keeping both normalizers until the final
limit. The factor1/2 in (E2) is distinct from the radial/even Borel factor2.

## Additional audited consequences

For exact t=cL, each weighted kernel is asymptotic to
K_X(c)*L^(-1/2)*exp(-beta(c)*L), beta(c)=2*(sqrt(c)-1/2)^2.
For every qualified sequence above its weighted logarithm divided by L
converges to-beta(c). The ratio R(c) tends lambda as c decreases to1/4,
and tends2/Z² as c tends infinity AFTER the coupled source limit. The latter
is half the existing opposite fixed-N-first limit4/Z². No simultaneous
c_N->infinity regime or sign crossover is asserted. All equations(1)–(23),
including these exposed stronger targets, passed complete independent audit.

## Final formalization

Three leaves,2502 lines,37 public declarations (8 definitions,29 theorems):

| Lean leaf | Lines / public declarations | Frozen SHA256 |
| --- | --- | --- |
| `LiClockCriticalAngularAsymptotic.lean` |336 /7 | `eb42f918bb93454030cb26cf204742d3acdc3c662f7e9054b37ffa6b983f6fc6` |
| `LiClockPairedEtaPartitionEndpointProfile.lean` |856 /16 | `0ac17b65237ac8236f5e76660945dcba68a9a346ec794f37f6ad6b41f4b7e1ac` |
| `LiClockPairedEtaInfinitePartitionSupercriticalRatio.lean` |1310 /14 | `68c8d693dbab9310c89c2099713bb9efa36a3408dd978fda9717323e4f847ce4` |

Every complete proof and public contract passed root and independent review.
Ratio14 retains all66 definitions/proofs, including52 private support declarations;
all14 public contracts mechanically match frozen589-line V2 plan. Full46451,
ALL14axes65905, named58182 and direct42229 checks passed. Named build completed
13005 jobs with no owned diagnostic;88 replayed warnings belong to33 external
dependencies. Every public axiom report uses only propext, Classical.choice and
Quot.sound. Exact tree/freeze, unique umbrella import, index and lint dispositions
recorded in `/tmp/hgt-li-supercritical-ratio-final-certificate.md`.

Own finite normalizers survive both source integrals and split limits; endpoint
upper-source averaging contributes exactly1/2, distinct from radial factor2.
No extra all-index positivity, monotonicity, bounded clock deviation, true-source
identity or Gaussian premise. Qualified prefactors/ratio, exact-clock equivalents,
qualified log-rates and both outer parameter boundaries are formalized.

Global lint remains separately classified in the final certificate; no claim that
unrelated concurrent repository errors are repaired. Relative central-clock forcing,
completed-response compensation, inverse sign and RH remain OPEN.

## Gates and historical log

2026-09-30 — Complete Ratio14 scratch assembly underway:
All source-split, scalar, moving-cutoff DCT, nearzero, regime and profile-Laplace
supports passed full root/independent mathematical/API review and clean owned
compiler/all-export foundational-axiom checks. Constants112 retains exact five
definitions/four consequences; full67521/ALL9axes18289 terminal0, independent
Pole ALL112/95 PASS. Generic transfer128 has two exports/four private helpers;
full72689/ALL6axes15589 terminal0, independent Pole ALL128 PASS. First root12
assembly75973 exited1 on three elaboration-only errors (notation spacing,
explicit profile function, denominator cancellation); all three corrected.
Full14 assembly now includes literal source consumers and both final transfer
wrappers. No final Ratio14 compilation, integration or Stage3 claim yet.

2026-09-30 — Ratio14 assembly support now compiled:
Root source split381 retains exact full actual/reference integrals and each
2/Z_X,N²; full37979/ALL7axes77167 terminal0/foundations-only. Moving-cutoff
DCT61 and nearzero70 passed complete dual proof/API audits and all-public
axiom checks; genuine L1 precedes each interchange. Qualified-regime38 and
scaled-profile Laplace273 compile cleanly with ALL3/ALL5 foundational reports.
Pole scalar236 full54256/ALL4axes40553 terminal0; root read every proof and
complete API/owner certificate, independent review ongoing. It supplies the
full-domain exponent bound, integrable endpoint majorant and exact fixed-y
constant1/(4sqrt(pi)c^(1/4)), without bounded clock deviations.
All final root prefactor/ratio/equivalent/log-rate caller proofs are drafted;
complete assembly waits remaining independent support and Constants9/Transfer2
packets. These individual support passes do not certify final Ratio14.

2026-09-30 — EndpointProfile16 FINAL_READY scoped integration:
Exact856 tree/freeze and ALL16 API rows/source order, unique umbrella verified.
Complete21444/ALL16axes45046/named62696/direct46824/index31574 terminal0;
whole source/API independently/root audited, every axiom foundational-only.
Owner52 certificate SHA256
`d41aad58ad6fc0920acea488ac36a32e51c74fc915c72a77b56df1ff978004b2`
read ALL by root; own named/direct diagnostics empty (external replay retained).
Lint62858 terminal1:172 size warnings,11 external unreachable modules and
external proof debt SelbergPrimeRangeCascade.lean:201 sorry; complete diff
classified, no owned finding. Global lint remains red. Root final certificate
`/tmp/hgt-li-endpoint-profile-final-certificate.md`. Exact source imports released
for approved Ratio14; that final14-declaration leaf remains unfinished.

2026-09-30 18:18 UTC — Endpoint16 complete source review PASS:
856 lines,3 definitions/13 public theorems/38 private declarations; SHA256
`0ac17b65237ac8236f5e76660945dcba68a9a346ec794f37f6ad6b41f4b7e1ac`.
Root covered all source via exact prior254/574/227 mappings and every new
Jacobian/profile/caller body. ALL16 complete V2 contracts retained; final fixed-y
proof preserves both sources, fixed cutoff and exact upper multiplier.
Independent245 `/tmp/li_producer_endpoint_profile_independent_audit.md`,
SHA256 `0523f20a91221f8faf18baedcde274c3a557bba681fb91a6e16c5cb99eb0cdad`,
root read ALL and verified unchanged182 prefix/new63 certificate and source.
Complete21444 and ALL16axes45046 terminal0, empty/foundations-only diagnostics.
Exact tree copy/unique umbrella import complete; named/direct gates assigned
Current, root index/lint pending. This leaf is not yet FINAL_READY.

Root approved R01–R03/R14 integral support232 compiles (31364, then cleaned
full+ALL4axes94285 terminal0/foundations-only); independent full review ongoing.
Pole owns R05/R07/R08 scalar endpoint estimates in disjoint scratch; Producer
owns R11/R12 scalar weighted-equivalent/log-rate transfer. Root retains literal
source/DCT/final Ratio14 assembly. No Gaussian/critical-source import is used
for this ratio formalization. Whole card remains Stage2; no RH sign claimed.

2026-09-30 — AngularAsymptotic7 complete implementation and dual proof audit:
336 lines, seven public theorems,23 private declarations; SHA256
`eb42f918bb93454030cb26cf204742d3acdc3c662f7e9054b37ffa6b983f6fc6`.
ALL seven full headers match authoritative v2. Root complete certificate
`/tmp/hgt-li-critical-angular-asymptotic-root-audit.md`; independent ALL336
certificate `/tmp/li_current_critical_angular_asymptotic_independent_audit.md`,
57 lines/SHA256 `52f4de07a94360dca2cedeb95c2dda36af21d3990bd6e0093dea09d176ba0b04`.
Complete scratch33051 and root ALL7 axiom65639 gates terminal0; every report
contains only `propext`, `Classical.choice`, `Quot.sound`. Exact-byte leaf and
unique umbrella import installed. Named16991/direct72065/index65802 terminal0;
ALL7 API rows match source order. Lint21040 terminal1:172 size warnings plus14
external unreachable modules, no owned error/debt; global lint remains red.
Full186-line log and complete prior/new difference classified. Exact leaf is
FINAL_READY; `/tmp/hgt-li-critical-angular-asymptotic-final-certificate.md`.
EndpointProfile16 and SupercriticalRatio14 remain unfinished; card stays Stage2.

2026-09-30 — Complete formal-plan root and independent PASS on v2:
`/tmp/hgt-li-supercritical-ratio-formal-plan-v2.md`,589 lines/SHA256
`14f7be3d2f15d9903a36bb9874796b627c9d1dad882646fc139bb7e4f556d025`.
Sole change from v1 clarifies raw Gaussian majorant mass versus its1/pi angular
normalization; all37 contracts and remaining588 lines unchanged. Independent
ALL37/23/source audit185 `/tmp/li_current_supercritical_ratio_formal_plan_independent_audit.md`,
SHA256 `b1498f6f62eeb8ed46a1ceea267d2f132ef157517f280328e57b9af657a59c3b`,
root read ALL and verified exact correction/source applicability.
AngularKernel17 is now FINAL_READY. Disjoint implementation released:
Producer AngularAsymptotic7, Current EndpointProfile16, root SupercriticalRatio14
after those two new dependencies are FINAL_READY. No ratio theorem is yet
formalized; all37 targets retained and this card stays Stage2.

2026-09-30 16:32 UTC — Exact formal plan frozen at589 lines:
`/tmp/hgt-li-supercritical-ratio-formal-plan.md`, SHA256
`91de9aca608319b5667f2fbb3399ea004465b170e0a2fa3c1bbffefb3d1ce714`.
Root read ALL589 and audited all23 paper targets and37 prospective exports
(eight definitions,29 theorems) across AngularAsymptotic7, EndpointProfile16
and SupercriticalRatio14. Complete root certificate
`/tmp/hgt-li-supercritical-ratio-formal-plan-root-audit.md` PASS.
Independent full source/contract audit assigned to Current; no ratio Lean
released. Only unfinished dependency is AngularKernel, explicitly gated;
Gaussian and critical literal-source consumers are not dependencies.

- [x] Prior search before starting this topic; all returned records inspected.
- [x] Well-posed source-pure conjecture and explicit attack mechanism.
- [x] Exact source identity (E1) and complete averaged endpoint proof (E2).
- [x] Full factorial-kernel asymptotic and sequence-uniform domination.
- [x] Complete dependency-closed proof of (U),(A),(R), all constants audited.
- [x] Independent full proof/source/overlap audit; no novelty claim.
- [x] Exact formal plan and complete independent source/target audit.
- [ ] Complete Lean implementation and all formal gates.

No extension to c=1/4, c->infinity jointly with N, arbitrary complex phase,
monotonicity/crossover of the proposed ratio, or inverse-clock sign is proved.
Any stronger statement exposed by the proof returns through paper/audit gates.

## Prior research, all returned records

Direct documented deep search, root session22886 exit0,46.07654025s:
`scripts/formal_tools.py research 'finite partition supercritical Borel ratio eta endpoint Laplace' --mode deep --budget-seconds 300 --json`.
Artifact `/tmp/hgt-li-supercritical-ratio-prior-research.json`.

Read ALL20 candidate statements,20 source arguments with every available
proof excerpt/method,10 prose passages,10 source passages,1 ingredient set.
No declarations/exploration/proof ideas. Partial=false; errors/unfinished
empty. Inventory63362/63362 complete,pending0; index1158111 older than coverage
snapshot1158116/current1158117. Semantic coverage unmeasured; background
refresh incomplete. All40 ranked Lean records source-only/not-checked.
Compiler43 compiled_snapshot,2 error,10194 not_applicable,47770 pending,
2660 stale,38 stale_snapshot,1 umbrella_source_only,2654 unavailable.

Candidate1–6,9–11,13,18 concern different Laplace sources/operators;7/12 are
Lie-algebra Borel spaces;8 a different dispersive supercritical ratio;
14/15/20 finite-lattice phase selection;16 Nevanlinna growth;17 measurable
Borel structure;19 a finite thermal constant. None supplies (E2) or (R).

Argument1–6,8,10/11,13–18,20 concern finite partitions, variation, graph
coloring or partitions of unity;7/9/19 concern bounded-variation Sturm cells;
12 is finite GKS spin modal-width obstruction. Every proof excerpt/method was
read. Definition-only records6/13/20 are not existence proofs despite their
generated method wording. No proposed source identity follows from them.

Prose1/4 finite KMS identities;2 existing actual finite Volterra source;
3 prolate variation;5 Deninger partitions;6/7 existing infinite-source paper
and certificate;8 existing LI frontier and kills;9 temporal-factorization
boundary;10 finite spectral dressing. Useful overlaps2/6/7/8 preserve the
same source but do not provide the new endpoint profile or ratio.

Source1 graph partition;2 finite GKS modal width;3 spectral dressing;
4 Deninger finite-stage sum;5 finite graded-partition convexity;6 FINAL
InfinitePartitionBoundary642–703;7 Peierls scalar-contact obstruction;
8 FINAL PartitionEndpointComparison834–933;9 measurable Borel intervals;
10 Nevanlinna growth. ALL passages read. Sources6/8 certify earlier fixed-N
and iterated limits and ceiling only; their quantifiers do not imply (R).
The sole unverified ingredient set combines wrong-source principal Laplace
profiles and odd symmetry, so is rejected for this mechanism.

No corpus absence, compiled applicability, publication novelty or route
retirement claim. Existing FINAL source leaves remain unchanged.

## Log

- 2026-09-30 15:03 UTC — Created before hard proof work; all displayed new
  limits remain conjectural. Supercritical exterior formalization and critical
  transition formal planning continue independently.
- 2026-09-30 15:09 UTC — Complete author paper255 lines frozen:
  `/tmp/hgt-li-supercritical-ratio-paper-frozen.md`, SHA256
  `ce0a7381e4cc8f62e8924e5b2304af34f6de4a01b8f4c5c7995a53dda478e707`.
  Author verdict PASS; Pole independently audits ALL23 equations and every
  source/normalizer/limit step. Exact periodic-primitive integration by parts
  gives the upper-factor average, while the lower actual indicator remains.
  Gaussian angular dominated convergence supplies the full factorial-kernel
  asymptotic; separate near-zero and endpoint bounds justify every qualified
  sequence. New exposed targets also undergo this audit: exact L^(-1/2)
  weighted prefactor/sharp logarithmic rate, ratio matching lambda as c
  decreases to1/4, and ratio limit2/Z² as c tends infinity AFTER the coupled
  source limit (distinct from fixed-N-first4/Z²). Primary DLMF10.32.1/10.40.1
  search/open checked classical angular representation/asymptotic; paper
  derives its required estimates explicitly. Card stays CONJECTURE/Stage1;
  no Lean release or completed-clock/RH conclusion.

2026-09-30 15:22 UTC — Independent whole-paper PASS:
`/tmp/li_pole_supercritical_ratio_paper_audit.md`,67 lines/SHA256
`9e79f1f642cb365e959460b900b0182ce66e76866cd680ff17e192df9a099c47`.
Root read ALL67, checked retained inverse-mass source and unchanged FINAL
Tail hash, and verified author/independent frozen paper identity. ALL255
proof lines and23 equations, every original and exposed positive target,
both own normalizers and all qualified-sequence quantifiers covered. Promoted
Stage2; exact paper follows. Its pending-independent metadata records the
snapshot state and is superseded by this certification. No Lean released.

<!-- BEGIN FROZEN SUPERCRITICAL RATIO PAPER -->
# Literal supercritical Borel ratio: endpoint averaging and exact prefactors

Status: author paper proof; independent complete source/proof audit pending.
No new Lean or numerical evidence. Date: 2026-09-30.
Card: docs/drafts/pipeline/1-in-progress/li-clock-infinite-partition-supercritical-ratio.md.

## 1. Exact sources and targets

Let A be the union of (log(2n-1),log(2n)] for n>=1, A_N its first N intervals,
L_N=log(2N), and Z=integral_A exp(-v/2)dv. Let Z_A,N and Z_U,L denote the
literal actual and contiguous half-tilt masses. The installed source results
give A_N=A intersect (0,L_N], Z_A,N->Z>0 and Z_U,L_N->2. All finite positive
N normalizers have the already-proved lower bound s=2-sqrt(2)>0.

Write g_A,N and g_U,L for their UNNORMALIZED even difference densities, and
B_A,N and B_U,L for the full normalized real Borel kernels. Define

    F(w)=sum_(j>=0) w^(2j)/[(2j)!]^2,
    E(b)=b*integral_A exp(-b*v)dv,  b>0.                          (1)

For w>=0 all terms of F are nonnegative. The exact public raw even moments,
full Borel sums and Tonelli give, for t>=0 and X=A or U,

    B_X(t) = (2/Z_X^2)*integral_0^L g_X(r)*F(t*r)dr.              (2)

Both normalizers are distinct throughout this argument. The factor2 is
evenness of the difference density, not a replacement for one half-tilt.
The already-audited critical-transition paper derives (2) from the complete
public source, including genuine integrability/full-series interchanges.

Fix c>1/4 and arbitrary natural nu_k->infinity and real t_k with
t_k/L_(nu_k)->c. Put L_k=L_(nu_k), a=sqrt(c)-1/2>0, and

    T_k = sqrt(L_k)*exp(L_k/2-2*sqrt(t_k*L_k)).

Every expression below is used on the eventual set L_k>0,t_k>0. Then

    T_k*B_U,L_k(t_k) -> K_U(c)
       =1/[8*sqrt(pi)*c^(1/4)*a*(a+1)],                          (3)
    T_k*B_A,nu_k(t_k) -> K_A(c)
       =E(a+1)/[4*Z^2*sqrt(pi)*c^(1/4)*a*(a+1)],                (4)
    B_A,nu_k(t_k)/B_U,L_k(t_k) -> R(c)
       =2*E(sqrt(c)+1/2)/Z^2.                                  (5)

All constants are strictly positive. These are qualified real-sequence
statements, with no monotonicity requirement on nu or t.

## 2. Complete factorial kernel and its angular asymptotic

The critical paper proves by the exact cosine-moment recurrence and absolute
Taylor integration that, for q>=0 and w=q^2/4,

    H(w)=sum_(m>=0) w^m/(m!)^2
        =(1/pi)*integral_0^pi exp(q*cos(theta))dtheta,
    J(w)=sum_(m>=0) (-1)^m*w^m/(m!)^2,
    |J(w)|<=1,     F(w)=(H(w)+J(w))/2,     0<=F(w)<=H(w).        (6)

These identities keep every even and odd coefficient; no finite-order
approximation is used. The integral is the classical I_0(q) representation
([NIST DLMF 10.32.1](https://dlmf.nist.gov/10.32.E1)); below is an independent
elementary derivation of the only asymptotic required here.

For 0<=theta<=pi, concavity of sin on [0,pi/2] gives
sin(theta/2)>=theta/pi, hence 1-cos(theta)>=2*theta^2/pi^2.
For q>0, substitution u=sqrt(q)*theta gives

    sqrt(q)*exp(-q)*H(q^2/4)
      =(1/pi)*integral_0^(pi*sqrt(q))
          exp(-q*(1-cos(u/sqrt(q))))du.                         (7)

Extend the integrand by zero on the remaining positive half-line. For each
fixed u>=0 it tends exp(-u^2/2), using (1-cos x)/x^2->1/2 at0; at u=0 the
statement is immediate. It is bounded by exp(-2u^2/pi^2), an integrable
Gaussian. Dominated convergence and the standard Gaussian normalization give

    sqrt(q)*exp(-q)*H(q^2/4) -> 1/sqrt(2*pi).                    (8)

The same bound, without taking a limit, proves for every q>0

    H(q^2/4) <= C*exp(q)/sqrt(q), C=sqrt(pi)/(2*sqrt(2)).         (9)

Also H(q^2/4)<=exp(q) for all q>=0 directly from (6). Since |J|<=1, (6),(8)
give the exact positive real asymptotic

    w^(1/4)*exp(-2sqrt(w))*F(w) -> 1/(4sqrt(pi))  as w->infinity.
                                                                    (10)

This agrees with the independently checked leading term of
[NIST DLMF 10.40.1](https://dlmf.nist.gov/10.40.E1). We use the proved
dominating bounds (9) and H<=exp(q), rather than an unquantified asymptotic
as a global integrability premise.

## 3. Literal endpoint profile: averaging only the upper factor

For 0<=y<=L=L_N put r=L-y. The exact density definition, using the two
independent half-tilts before normalization, gives

    h_A,N(y):=exp((L-y)/2)*g_A,N(L-y)
      =integral_0^y exp(-v)*1_A(v)*1_A(v+L-y)dv.                 (11)

Indeed both finite indicators require 0<=v<=y and 0<=v+r<=L; their infinite
indicators agree with the finite ones there. Boundary differences are finite
sets of Lebesgue measure zero. For the contiguous source the same calculation
gives h_U(y)=1-exp(-y). In particular 0<=h_A,N(y)<=h_U(y)<=1.

For every FIXED y>=0,

    h_A,N(y) -> h_A(y):=(1/2)*integral_0^y exp(-v)*1_A(v)dv.     (12)

Here is a complete averaging proof. Let S=union_(n>=1)(2n-1,2n], p=1_S on
the positive half-line, and M=2N*exp(-y). Substitution x=exp(v) turns (11)
into integral_1^(exp(y)) x^(-2)*1_S(x)*p(M*x)dx. For N large L>=y,
Mx<=2N throughout, so no indicator beyond the true finite upper endpoint is
introduced. Define P(u)=integral_0^u (p(w)-1/2)dw for u>=0. On each full
period [2m,2m+2], p is0 then1 on unit cells. Consequently P is continuous,
piecewise linear, two-periodic, and |P(u)|<=1/2. It is absolutely continuous
on compact intervals, with derivative p-1/2 almost everywhere.

For any 1<=b<=d, integration by parts for this absolutely continuous
primitive gives

    integral_b^d x^(-2)*(p(M*x)-1/2)dx
      =[x^(-2)*P(M*x)/M]_b^d
        +(2/M)*integral_b^d x^(-3)*P(M*x)dx.

Its absolute value is at most

    (1/(2M))*(b^(-2)+d^(-2)+2*integral_b^d x^(-3)dx)
       =1/(M*b^2) <=1/M.                                     (13)

The intersection S intersect [1,exp(y)] is a finite disjoint union of K_y
intervals, including any partial final interval. Applying (13) to every
interval bounds the total averaging error by K_y/M->0. Degenerate intervals
contribute zero; y=0 is immediate. This proves (12) with the lower indicator
1_A retained exactly. Pointwise convergence of the upper indicator is neither
assumed nor asserted. No uniform-in-y error estimate is needed below.

## 4. Uniform domination for arbitrary qualified sequences

Fix c_- with 1/4<c_-<c. Eventually t_k/L_k>=c_-; put
a_-=sqrt(c_-)-1/2>0. For 0<=y<=L, concavity of sqrt gives

    y/2+2sqrt(t*(L-y))-2sqrt(t*L)
       <=-(sqrt(t/L)-1/2)*y <=-a_-*y.                          (14)

Split the full integral (2) into r<=L/2 and r>=L/2. On the first region,
g_X(r)<=exp(-r/2) and F(tr)<=exp(2sqrt(tr)). Thus its contribution AFTER
multiplication by T_k is bounded by

    (2/s^2)*sqrt(L)*(L/2)*exp(-a_-*L/2) ->0.                    (15)

This bound also handles r=0, where the asymptotic prefactor is singular.
The elementary exponential beats the displayed fixed polynomial.

On r>=L/2, set y=L-r and extend the resulting integrand by zero for y>L/2.
For each fixed y>=0, (10) and t/L->c give

    sqrt(L)*exp(y/2-2sqrt(t*L))*F(t*(L-y))
       -> exp(-a*y)/(4sqrt(pi)*c^(1/4)).                        (16)

To justify integration, use (9) with q=2sqrt(t*(L-y))>0. On y<=L/2,

    sqrt(L)/sqrt(q) <=2^(-1/4)*c_-^(-1/4).

Together with (14), this bounds the integrand in (16) by
C*2^(-1/4)*c_-^(-1/4)*exp(-a_-*y), independent of k on its eventual set.
Both profile factors lie in [0,1], so the same bound dominates their products.
All factors are measurable. Dominated convergence applies on [0,infinity);
arbitrary finitely many early terms do not affect limits. For the actual
profile use (12) along nu_k->infinity, not a monotone-cutoff assumption.

Combining (2),(15),(16), both genuine normalizer limits, and the profile
limits yields

    T_k*B_X(t_k) -> [1/(2*Z_X,infinity^2*sqrt(pi)*c^(1/4))]
                      *integral_0^infinity exp(-a*y)*h_X(y)dy.  (17)

## 5. Evaluate the constants and quotient

The reference integral is

    integral_0^infinity exp(-a*y)*(1-exp(-y))dy
       =1/a-1/(a+1)=1/[a*(a+1)].                              (18)

For the actual source all integrands are nonnegative; Tonelli gives

    integral_0^infinity exp(-a*y)*h_A(y)dy
       =(1/(2*a))*integral_A exp(-(a+1)*v)dv
       =E(a+1)/[2*a*(a+1)].                                   (19)

Use Z_U,infinity=2 and Z_A,infinity=Z in (17). Equations(18),(19) prove
(3),(4). Positivity of E(a+1) follows from A containing (0,log2]; a>0,Z>0.
The reference limiting constant is strictly positive, so division of the
two limits is valid. The common factor T_k is positive eventually and cancels
exactly, proving (5). This is a full-kernel quotient; it is not inferred from
the vanishing of two separately weighted kernels.

For b>1, integration over every disjoint interval of A gives
E(b)=sum_(n>=1)((2n-1)^(-b)-(2n)^(-b)). Absolute convergence of sum n^(-b)
justifies unpairing into the usual alternating Dirichlet series. The integral
definition (1) is the source identity used in the proof, so no analytic
continuation or zeta hypothesis enters.

## 6. Positive consequences exposed by the exact limits

These consequences are new paper targets and require the same independent
audit; no formal implementation is released.

First, for fixed c>1/4 and t=cL, the exact weighted equivalent is

    exp(-2cL)*B_X(cL) ~ K_X(c)*L^(-1/2)*exp(-beta(c)*L),
    beta(c)=2*(sqrt(c)-1/2)^2.                                 (20)

Thus the earlier supercritical exponential rate is sharp, although its
constant upper envelope omits the true L^(-1/2) prefactor. More generally
for the qualified sequences above, positivity of the constants in(3),(4)
and log(L)/L->0 give

    log(exp(-2*t_k)*B_X(t_k))/L_k -> -beta(c).                   (21)

Second, E(b)->E(1)=log2 as b->1 from above. This follows from (1) by
dominated convergence, using b in[1,2] and exp(-v) as the integrable majorant;
the exact E(1)=log2 is the banked full-source identity. Hence

    R(c) -> 2log2/Z^2=lambda as c->1/4 from above.               (22)

Third, the first interval and full-halfline upper bound give
1-2^(-b)<=E(b)<=1 for b>0. Therefore E(b)->1 as b->infinity and

    R(c) -> 2/Z^2 as c->infinity.                              (23)

This LAST limit is taken AFTER the fixed-finite-c source/clock limit. It is
half the already-proved opposite iterated endpoint limit4/Z^2. It does not
describe an arbitrary c_N->infinity regime. The distinction is the factor1/2
from rapidly alternating upper intervals, absent when N is fixed first.

## 7. Scope, prior work and audit obligations

The card records every one of61 prior-search records and coverage/freshness;
all were inspected before this proof. Useful prior overlaps are the exact
finite/infinite source definitions, full raw moments/Borel identities,
normalizer limits, fixed-N endpoint theorem and critical angular identities.
Their quantifiers do not supply this supercritical coupled ratio.
The angular asymptotic is classical (primary DLMF references above), and
periodic averaging plus endpoint Laplace asymptotics are classical methods.
No publication novelty or corpus-absence assertion is made.

Independent audit must check ALL(1)–(23), exact raw-density orientation,
every interval in(13), both factorials, even factor2 versus upper-average1/2,
normalizer2 versus Z, arbitrary qualified-sequence quantifiers, domination
of BOTH regions, and all additional consequences(20)–(23).

No conclusion at c=1/4, arbitrary complex phases, a simultaneous c_N->infinity
limit, monotonicity or sign crossover of R(c), the completed-response
compensation, inverse-clock sign, or RH is asserted.
<!-- END FROZEN SUPERCRITICAL RATIO PAPER -->
