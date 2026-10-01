# Literal mixed-kernel profile and stable sign boundary

- **ID:** LI-CLOCK-MIXED-KERNEL-SIGN-BOUNDARY
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean); repository-wide lint pending
- **Source:** [completed-clock sign attempt](../1-in-progress/li-clock-completed-forcing-direct-sign.md)
- **Statement:** The literal infinite mixed kernel has its exact signed hyperbolic profile, all fixed-order compact finite derivative limits, sharp logarithmic-curvature limit -1, and one stable pair witnessing negative comparison history in every eventual logarithmic window.

## Gates

- [x] Complete literal source, prior research and dependency-closed paper proof.
- [x] Author/root independent full177-line paper and source audits.
- [x] Full503-line typed formalization plan reviewed; implementation released.
- [x] Complete Lean implementation, all proofs/exports reviewed independently.
- [x] Owned named/direct builds, all-public axiom audit, umbrella/index integration.
- [ ] Repository-wide formal lint green;11 unrelated unwired modules remain.

## No-go closure

- **Exact killing mechanism:** Mixed logarithmic slope eventually decreases; a single fixed pair persists through every sufficiently large finite prefix and lies in every fixed positive logarithmic window.
- **Strongest positive survivor:** Full literal four-coordinate source admission, both own squared normalizers, all fixed derivative compact convergence, exact signed sigma/H profile with every fixed remainder derivative bound, scaled slope/curvature limits and stable source witness.
- **New insight:** Kernel positivity does not yield a positive comparison history; any valid proof must retain its signed part.
- **Status:** PAPER PASS; owned Lean/source/compiler/integration gates PASS. Repository-wide lint remains red. No route retirement or completed-clock/RH conclusion.

## Formalization scope

Root read ALL503 lines of `/tmp/li_pole_mixed_kernel_sign_boundary_formal_plan.md`, SHA256 `e6d108702f507a0ec5d4d1bd54f81f17affcdf137bcd9075965c7c190b2a21ff`, and spot-checked fresh installed infinite-moment L1, full finite binomial and actual error contracts. Two new leaves are authorized: `LiClockPairedEtaPartitionMixedLimit.lean` and `LiClockPairedEtaPartitionMixedSignBoundary.lean`. Preserve every contract in the plan; source helpers remain private. No edits to finalized dependencies. The simultaneous root/Producer work continues the missing actual signed source inequality.

### First leaf: implementation and proof checks complete

[LiClockPairedEtaPartitionMixedLimit.lean](../../../../formal/GaloisForLFunctions/RHTower/LiClockPairedEtaPartitionMixedLimit.lean)
contains all26 planned public declarations (7 definitions, 19 theorems).
Root and independent reviewer read every body of the frozen968-line source,
including all65 private declarations. The promoted1004-line source adds
only mathematical comments and whitespace fixes; SHA256
`cb551f719bbf5e791501873421d738a252793deff202a124daa8100af96bf96f`.
Full binomial/source identities retain both own squared normalizers and
genuine integrability. All fixed complex and real derivative limits follow
from holomorphic local uniform convergence, with the same approved contracts.

Named `lake build --old GaloisForLFunctions.RHTower.LiClockPairedEtaPartitionMixedLimit`
and exact direct `lake env lean GaloisForLFunctions/RHTower/LiClockPairedEtaPartitionMixedLimit.lean`
both exited0; direct log is empty and the named build emitted no own-leaf
warnings. All26 source-order axiom reports contain only `propext`,
`Classical.choice`, `Quot.sound`. Umbrella import is wired; index generation
exited0 and all26 public API rows were checked. Repository-wide
`scripts/formal_tools.py lint --check-generated` exited1: eleven unrelated
modules are unwired and all three generated catalogs were stale at check
time. No MixedLimit or proof-debt error was reported. The exact global
diagnostics are in `/tmp/li_root_mixed_limit_lint.log`; this is not a clean
repository-wide gate. A subsequent index refresh and lint after adding the
derivative leaf passed catalog freshness but still reported eleven unrelated
unwired modules (`/tmp/li_root_clock_derivative_lint.log`). The second leaf's
source is promoted and passes its final owned compiler/integration gates.
The full card stays Stage2 while the repository-wide lint gate remains red.

### Second leaf: exact reviewed source promoted; final checks in progress

`LiClockPairedEtaPartitionMixedSignBoundary.lean`1050 contains all24 approved
public declarations and76 private declarations. SHA256
`4123bebcf0291eb33d1d053aa0b9135365bc0df91f2b597532cdace22a52898b`.
Root read ALL1050 source lines and ALL306 ledger lines; complete root audit
`/tmp/li_root_mixed_sign_full_review.md`, SHA
`34e56349c40e9e76056ee26ea28d7a6f8e78ca06fea998611cbf457791db587f`.
Independent Current audit read ALL1050/306/503, including every24 public
contract and76 private body;236-line certificate
`/tmp/li_current_mixed_sign_independent_audit.md`, SHA
`da448a85519a6bfe75cabe15517122cf632ee913c921b701fa35346f872ca3db`,
read completely by root. Both semantic reviews PASS.

Corrected whole scratch87927 terminal0/empty. ALL24 scratch axioms81565
terminal0; author and root read every report, foundations only. Promotion is
byte-identical to the reviewed candidate, confirmed by root cmp and SHA.
Umbrella import wired after MixedLimit. Named92467 terminal0,13004/13004 jobs,
owned leaf warning-free; dependency warnings are recorded separately.
Exact final direct84839 terminal0/empty. Imported ALL24 axioms91132 terminal0;
root read every report, foundations only. Final certificate
`/tmp/li_pole_mixed_sign_final_certificate.md`, SHA
`402cef2fbb36b6ba774c831b44a22a4e880e5ab6b562f2c8cb4433b98d2304ef`,
read completely by root. Final index47749 terminal0; root read every24 API row
and verified exact source-order coverage. Lint74901 terminal1 with the same11
unrelated unwired modules as the ratio leaf's recorded check; catalogs fresh,
no owned reachability/proof-debt error. Repository-wide lint is not green;
both owned leaves' proof/compiler/axiom/reachability/catalog checks are complete.
The signed sigma coefficient remains unconstrained; one fixed positive pair
precedes every window constant, preserving the exact stable-witness quantifiers.

## Audited complete paper proof [PROVED HERE]

The following frozen proof is retained verbatim as historical certificate. Its references to future implementation describe its audit date; the formalization release above is current.

# Actual mixed-kernel logarithmic-slope barrier: independent paper audit

PASS for the proposed obstruction. The source-normalized infinite coefficient, factor λ/2, and passage from finite kernels all close. The proposed eventual growing-window nondecreasing q_N condition is FALSE. This rejects that sufficient-condition mechanism alone; original completed-clock sign conjecture and unknown normalized-forcing sign remain untouched.

Read-only mathematical/source audit. No Lean/compiler job, numerical computation, tree/card edit, new agent, or formalization claim.

## 1. Literal source definitions and normalization

Let L_N=log(2N), N≥1. Use precisely the installed actual/source measures:

- μ_A,N = liClockPairedEtaSymmetrizedMeasure N, the normalized independent half-tilt of the complete pairedEtaFiniteLogMeasure interval-union. Its joint normalizer is Z_A,N².
- μ_U,N = liClockPairedEtaContiguousSymmetrizedMeasure L_N, the separate normalized independent half-tilt of Ioc(0,L_N). Its joint normalizer is Z_U,N².
- μ_A,∞ = liClockPairedEtaInfiniteSymmetrizedMeasure; μ_U,∞ = liClockPairedEtaHalfLineSymmetrizedMeasure. Their own normalizers are Z_A,∞² and Z_U,∞²=4.

Mixed measures are μ_A,N × μ_U,N and μ_A,∞ × μ_U,∞. Write X=u1−u2 and Y=v1−v2. Every mixed quantity retains all four tilted coordinates. No contiguous substitution for the actual union, shared normalization, shifted/adaptive coordinate, or totalized N0 probability claim.

Write d_N,a=E_A,N[X^(2a)], u_N,b=E_U,N[Y^(2b)], d_a=E_A,∞[X^(2a)], u_b=E_U,∞[Y^(2b)]. All are genuine integrable moments, nonnegative, and normalized degree0=1. Installed exact reference formula is

(1) u_j = 4^j (2j)!.

Installed actual source data give

(2) r_j := d_j/u_j >0, r_0=1, r_j→λ,
    λ = 2 log2 / Z_A,∞² >0,
    |r_j−λ| ≤ E 9^(−j), E=π²/(12 Z_A,∞²)≥0.

These are unconditional arithmetic-source theorems. No higher source-sign assumption, zero-free disk, functional equation, or RH enters them.

## 2. Exact infinite mixed coefficient: factor checked

Both marginal difference distributions are even. Their odd moments vanish; absolute moments are integrable because |x|^n≤1+|x|^(2n) and all even moments are integrable. Independence and finite binomial expansion are therefore legitimate for each order, before any full-series interchange.

M_j := E[(X+Y)^(2j)]
     = Σ_(a=0)^j choose(2j,2a) d_a u_(j−a)
     = (2j)! 4^j Σ_(a=0)^j r_a.

The last equality uses choose(2j,2a)(2a)!(2j−2a)!=(2j)! and BOTH powers 4^a·4^(j−a)=4^j. Let A_j=Σ_(a=0)^j r_a. Thus the literal infinite mixed Borel kernel is

(3) B_∞(z) = Σ_(j≥0) A_j (2z)^(2j)/(2j)!.

This is not B_A(z)B_U(z), and is not a modified contour clock. It is the full mixed-source even factorial kernel. In particular B_∞(0)=A_0=r_0=1, B_∞(t)≥1 for real t. The original candidate coefficient and normalization are correct.

## 3. Full finite→infinite admission, both own normalizers

Set s=2−√2>0 and K=4/s². Installed ALL-order finite bounds, for every N≥1, give separately

0≤d_N,a≤K u_a,
0≤u_N,b≤K u_b.

Their proofs use the distinct lower bounds Z_A,N≥s and Z_U,N≥s, raw-product domination and each own squared normalization. Multiplying these bounds does not assert equality of either normalizer.

The exact installed finite mixed binomial identity consequently gives

(4) 0≤M_N,j≤K² (j+1)(2j)!4^j.

For every fixed j, the installed fixed-order actual and reference limits and their finite sum/product operations give M_N,j→M_j. No growing-order limit is assumed.

For |z|≤T, ALL finite mixed terms satisfy

(5) |M_N,j z^(2j)/((2j)!)²|
      ≤K²(j+1)(2T)^(2j)/(2j)!.

The complete majorant sums to K²[cosh(2T)+T sinh(2T)]<∞. Thus summable tails uniformly control every N≥1 on every fixed complex compact disk; fixed finite prefixes converge by the fixed-j limits. This proves full locally uniform B_N→B_∞ on ℂ. N0 is an irrelevant discarded initial index, not falsely normalized.

For each fixed derivative order m, differentiate only degrees2j≥m. Its exact majorant becomes K²(j+1)4^j T^(2j−m)/(2j−m)! on |z|≤T (take T≥1 if convenient). Reindexing k=2j−m bounds the resulting whole tail by a fixed polynomial times (2T)^k/k!. It is summable. Therefore all termwise derivatives are genuine, the full limit is entire, and B_N^(m)→B_∞^(m) locally uniformly for every fixed m. This is an admission proof, not an appeal to an unproved derivative exchange.

Source realization of (3) is also genuine. Under the four-coordinate infinite product, each even term is nonnegative for real t; (4)'s limit gives the summable integrated majorant. Tonelli then gives an integrable complete EvenKernel(t(X+Y)) and equality of its integral with (3). For complex z, integrate absolute even terms, using E|X+Y|^(2j)=M_j and (5)'s limit; absolute summability gives the corresponding full complex interchange. No assertion that the infinite ordinary MGF is entire is needed or made.

## 4. Leading profile and exponential rate

Since r_j→λ, A_j/(j+1)→λ by Cesaro (finite head/ε-tail split). Compare the complete positive series (3) with

(6) D(t) := Σ_(j≥0)(j+1)(2t)^(2j)/(2j)!
          = cosh(2t)+t sinh(2t).

Both coefficient families are nonnegative; denominator coefficients strictly positive; both series summable for every real t. The exact installed positive-even-series ratio theorem applies with coefficient ratio A_j/(j+1), giving B_∞(t)/D(t)→λ as t→+∞.

As D(t)/(t exp(2t))→1/2, we obtain

(7) B_∞(t)/(t exp(2t))→λ/2>0,
    exp(−2t)B_∞(t)→+∞,
    log B_∞(t)/t→2.

For the last limit, two eventual positive constant bounds on B_∞/(t exp2t) bound log B_∞−2t−log t, and log t/t→0. No logarithm of a zero or sign-indefinite quantity occurs. The candidate's exact λ/2 is correct.

## 5. Eventual logarithmic-window monotonicity is impossible

Let W_N=c log(2N+1), with ANY fixed c>0. It tends to+∞. For N≥1 define the genuine smooth q_N(t)=B_N'(t)/B_N(t); denominators are≥1. Suppose q_N is nondecreasing on the whole [0,W_N] for all sufficiently large N. The same result holds if the hypothesis is stated only on (0,W_N], by continuity at0.

Then f_N=log B_N has nondecreasing derivative and is convex on that interval. For arbitrary fixed0<t<T, once W_N≥T,

(8) log B_N(t) ≤ (t/T)log B_N(T)

because B_N(0)=1. Pointwise full-series convergence and strict positive limits pass (8) to

log B_∞(t) ≤ (t/T)log B_∞(T).

Now let T→∞ and use (7). Hence log B_∞(t)≤2t for every fixed t>0, or B_∞(t)≤exp(2t). This contradicts exp(−2t)B_∞(t)→∞. Passing an interval chord uses no convergence of q_N, and no finite/infinite order interchange.

Conclusion: no positive c admits the proposed eventually-all-N monotonicity on its whole growing logarithmic window. In particular every admissible c from the actual completed-clock window fails that auxiliary condition. This conclusion is about the mixed kernel, not the original F_N sign.

## 6. Sharp positive survivor: exact complete profile and stable signed history

The stronger installed geometric moment error yields a complete source profile, retaining every coefficient. Define the absolutely convergent signed constant

σ := Σ_(a≥0)(r_a−λ),
δ_j := Σ_(a≥j+1)(r_a−λ).

Then |σ|≤9E/8 and |δ_j|≤(E/8)9^(−j). Since A_j=λ(j+1)+σ−δ_j, exact ALL-complex identity is

(9) B_∞(z)=λ z sinh(2z)+(λ+σ)cosh(2z)−H(z),
    H(z)=Σ_(j≥0)δ_j(2z)^(2j)/(2j)!,
    |H(z)|≤(E/8)cosh(2|z|/3).

There is no missing constant at0: λ+σ−δ_0=λ+(r_0−λ)=1. No sign assumption on σ or H is made. For every fixed m≥0, differentiated full-series absolute bounds give, for t≥0,

(10) |H^(m)(t)|≤(E/8)(2/3)^m exp(2t/3).

Write p(t)=exp(−2t)B_∞(t). From (9)–(10), with a=λ/2>0 and b=(λ+σ)/2,

p(t)=a t+b+ε(t),
ε(t)=(-a t+b)exp(−4t)−exp(−2t)H(t).

Each fixed derivative of ε is polynomial times exp(−4t) plus O(exp(−4t/3)); thus ε,ε',ε'' decay faster than every negative power. For q_∞=B_∞'/B_∞=2+p'/p,

(11) q_∞→2,
     t(q_∞−2)→1,
     t² q_∞'→−1.

Indeed p/t→a, p'→a, t p''→0, and
 t²q_∞'=t p''/(p/t)−(p'/(p/t))²→−1.
All denominators are positive. Thus q_∞ eventually lies strictly ABOVE2 while strictly DECREASING to2. This gives exact negative logarithmic curvature, rather than only a failure of global convexity.

Choose fixed0<a0<b0 sufficiently large so q_∞(a0)>q_∞(b0). The genuine locally uniform C1 convergence from §3 implies q_N(a0)>q_N(b0) for EVERY sufficiently large N. Both fixed clocks lie inside W_N for every c>0 eventually. Hence the stronger classification holds: ALL sufficiently large finite prefixes violate the nondecreasing condition on each such window, with one fixed positive witness pair.

The proposed comparison-history kernel necessarily has a strictly negative actual-source witness. At fixed t=b0,s=b0−a0,

B_N(t−s)[q_N(t)−q_N(t−s)]
 =B_N(a0)[q_N(b0)−q_N(a0)]<0

for all sufficiently large N. Continuity also gives open witness neighborhoods. A replacement comparison proof must keep this signed history; positive inverse reasoning based on monotone q cannot apply. This does not establish either sign of F_N or R_N'.

Statements (9)–(11) and the stable-witness classification are paper-derived survivors from existing exact source inputs. They have no new Lean implementation here and require root/independent whole-paper gates before formalization.

## 7. The differentiated comparison identity itself

For a common regular source disk the already-proved literal completed forcing identity is J_N=2(F_N*B_N), with B_N(0)=1. Given genuine continuous derivative of B_N, compact convolution differentiation gives

R_N'=2F_N/B_N +(2/B_N)∫_0^t F_N(s)B_N(t−s)[q_N(t−s)−q_N(t)]ds,

hence the card's rearrangement

F_N=(B_N/2)R_N'+∫_0^t F_N(s)B_N(t−s)[q_N(t)−q_N(t−s)]ds.

Signs, factor2, endpoint normalization and orientation PASS. If both R_N'≥0 and the history kernel≥0 were independently proved, a continuous Volterra iteration/negative-part Gronwall argument would give F_N≥0. A non-strict first-touch shortcut would not suffice; the card correctly excludes it. The kernel-monotonicity premise is refuted above. R_N' and the original completed forcing/source sign remain OPEN.

## 8. Exact verified source/API ledger and remaining Lean burden

All paths below are under formal/GaloisForLFunctions/RHTower; exact headers and relevant bodies source-read, not fabricated API names.

- LiClockPairedEtaPartitionMixedSource.lean11–34: actual four-coordinate mixed measure, even moments, full Borel, signed forcing definitions. :288 liClockPairedEtaPartitionMixedEvenMoment_eq_sum; :583 zero=1; :594 one_le; :603 positive. Previously independently whole651 source16 audited; exact finite binomial contract reread for this derivation.
- LiClockPairedEtaInfinitePartitionMeasure.lean26–72: both literal infinite/reference definitions, own normalizers and λ formula; :178/:185 genuine even-moment integrability; :483/:488 exact raw-double/Z² moment identities; :568/:573 degree0; :578/:592 strict positive moments.
- Same :618 liClockPairedEtaInfinitePartitionNormalizer_ge_first; :667 liClockPairedEtaPartitionNormalizer_ge_first; :675 liClockPairedEtaContiguousPartitionNormalizer_ge_first. :1083 tendsto_liClockPairedEtaInfiniteSymmetrizedEvenMoment and :1102 tendsto_liClockPairedEtaHalfLineSymmetrizedEvenMoment retain BOTH squared normalizer limits. :1151/:1165 exact separate uniform all-order half-line comparison bounds, complete proofs read. These supply (4)–(5), not a supplied true-source premise.
- LiClockPairedEtaInfinitePartitionBorel.lean1102 liClockPairedEtaHalfLineSymmetrizedEvenMoment_eq gives u_j=4^j(2j)!. :1090 exact E definition; :1534 E≥0; :1547 liClockPairedEtaInfinitePartitionMomentRatio_error_le gives E9^(−j); :1579 tendsto_liClockPairedEtaInfinitePartitionMomentRatio gives exact λ. Relevant factorial/raw-moment normalization proof read.
- LiClockPairedEtaInfinitePartitionDensityTail.lean1480 liClockPairedEtaInfinitePartitionComparisonLimit_pos, full proof read: log2>0 and Z_A,∞²>0 only. This is imported by FINAL Borel; no unavailable dependency.
- LiClockPositiveEvenSeriesRatio.lean21 definition and :150 liClockPositiveEvenSeries_ratio_tendsto: actual complete exact header/body read. Required ha nonnegative, hb positive, all-real summability and coefficient ratio limit are each discharged explicitly in §§2–4. It transfers a coefficient ratio to full positive series, not an inverse clock sign.

New paper-only formal obligations, should root later release them: define canonical infinite mixed source/kernel; prove its finite binomial identity and source integral admission; prove fixed compact finite/kernel derivative convergence via (5); instantiate positive-series ratio after Cesaro or use exact geometric profile; derive log-convex chord and impossible-window theorem; derive exact σ/H complete profile and sharp curvature/witness survivor. None of those is asserted already installed. No Mathlib theorem name guessed or current-toolchain probe claimed; future implementation must probe actual names and obey complete proof/axiom gates.

## 9. Prior research/freshness and limited status

Used root's already-completed direct prior research; did not rerun the same searches or inspect search implementation/help. Independently checked JSON metadata, not claiming an independent all-hit method-excerpt audit:

- /tmp/hgt-li-compensation-next-research.json: query `relative Volterra signed forcing positive inverse completed clock compensation growing window`, deep, partial=false, errors=[], unfinished=[], 20 candidates/20 arguments/1 ingredient/10 prose/10 passages; root terminal95988, elapsed85.63567795899999s. Coverage63509/63509 inventoried/indexed, snapshot generation1163886/current1163887; semanticunmeasured; compiler43 compiled_snapshot,2error,47892pending,2660stale,38stale_snapshot,1umbrella_source_only,2654unavailable. Root's prior hit applicability scope, not exhaustive absence proof.
- /tmp/hgt-li-compensation-source-research.json: query `liClockPairedEtaFiniteClockResponse nonnegative compensation`, deep, partial=false, errors=[], unfinished=[], 11 declarations/20 candidates/20 arguments/1 ingredient/10 passages, no prose; root focused8913, elapsed44.302050291s. Coverage63509/63509 indexed, snapshot1163896/current1163905, semanticunmeasured, same compilercoverage counters. Card's focused-query-pending sentence is stale relative to this completed artifact; no card edit made.

Mathematical/source judgment: PASS exact mixed-profile obstruction and positive survivor. Mechanism status: NO-GO for eventual q_N nondecreasing as positive-kernel comparison premise. Original completed-clock growing-window sign remains OPEN, no route retirement, RH proof/refutation or global novelty claim. Existing positivity, aggregate area and source-normalized limits remain compatible with this signed-history obstruction.

## Implementation log

- 2026-10-01 — Root approved the complete mathematical/typed contract and released the two disjoint new leaves to Pole. One foreground compiler, verified API probes, no options/proof debt, full proof and axiom gates required. Original compensation remains OPEN.
