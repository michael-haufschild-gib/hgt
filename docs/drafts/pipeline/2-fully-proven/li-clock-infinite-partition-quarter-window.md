# Infinite partition: weighted complex quarter-window

- **ID:** LI-CLOCK-INFINITE-PARTITION-QUARTER-WINDOW
- **Stage:** 2-fully-proven
- **Type:** THEOREM; complete author/root and independent paper/source/overlap audit PASS; Lean pending
- **Source:** [complete infinite-partition boundary](../2-fully-proven/li-clock-infinite-partition-density-tail-boundary.md)
- **Owner:** root, paper only; no new Lean released

## Exact target

Use the same literal finite/infinite actual and half-line sources and normalized
full Borel kernels as the parent. Write L=log(2N), s=2−sqrt(2),
lambda=2log(2)/Z². For 0<=c<1/4 put

    delta(c)=1/2−sqrt(c)>0,
    eta(c)=(1−2sqrt(c))²/2>0,
    Q_N(c)=(2/s²)(L+1/delta(c))exp(−eta(c)L)
              +(32/s⁴)exp(−L/2).

For every N>0 and every complex z with |z|<=cL, conjecture

    exp(−2|z|)|B_A,N(z)−B_A,infinity(z)| <= Q_N(c),
    exp(−2|z|)|B_U,N(z)−cosh(2z)| <= Q_N(c).

Q_N(c)->0. Thus the parent qualified real joint limits, ratio->lambda<1,
opposite kernel-gap escape, and uniform negative gap extend to every
0<c<1/4. This is a weighted complex estimate; the parent's unweighted complex
disk estimate remains its separate 0<=c<1/16 theorem. No assertion at c=1/4,
no optimality assertion, and no inverse-clock or RH conclusion.

## Prior research and applicability

Direct documented query `Borel partition relative error growing window saddle`,
`/tmp/hgt-li-quarter-window-research.json`, terminal49971 exit0,8.949s.
All20 candidate statements, all20 source-argument statements/proof excerpts and
available methods, and all10 prose records inspected. Zero declarations,
exploration hits, proof ideas, ingredient sets or source passages. Results
overlap the existing fixed-N endpoint error theorem, complete positive-series
ratio transfer, parent infinite-source proof, and other unrelated window bounds.
The fixed-N endpoint bound has N-dependent constants and does not supply the
new joint estimate. The directly relevant source/kernel ingredients have already
been read in full and checked in the parent implementation; no search-only API
is used as a verified Lean dependency here.

Search partial=false, errors=[], unfinished=[]; inventory63296/63296 complete,
pendingfiles0. Coverage generation1155433 older than index/current1155436;
compiler43 compiled snapshots,2errors,10186notapplicable,47712pending,2660stale,
38stale snapshots,1umbrella source-only,2654unavailable. Semantic coverage
unmeasured; background refresh incomplete. No corpus-absence or publication
novelty claim. Two initial display batches truncated; every missing record was
then read in bounded batches. Indexed typed-let statements truncate early;
their exact previously audited source headers, not that index text, govern reuse.

## Complete paper proof

The complete factorial kernel is

    E(w)=sum_(j>=0) w^(2j)/((2j)!)²,  |E(w)|<=exp(2sqrt(|w|)).

All raw integrals and exchanges are genuinely integrable as in the parent.
For either source, complete raw truncation loss h_N is nonnegative and bounded
by the same full reference deficit

    h_L(x)=exp(|x|/2−L)       if |x|<L,
           exp(−|x|/2)       if |x|>=L.

Fix tau=|z| in[0,cL]. Since N>0, L>0. For 0<=r<=L,

    r/2−L+2sqrt(tau*r)−2tau
        <= −L/2+2sqrt(tau*L)−2tau
         = −(sqrt(L)−2sqrt(tau))²/2
        <= −eta(c)L.

The last step uses sqrt(tau)<=sqrt(c)sqrt(L) and 2sqrt(c)<1.
For r>=L, the elementary identity

    sqrt(r)−sqrt(L)=(r−L)/(sqrt(r)+sqrt(L))

gives

    2sqrt(tau)(sqrt(r)−sqrt(L)) <= sqrt(c)(r−L).

Consequently

    −r/2+2sqrt(tau*r)−2tau <= −eta(c)L−delta(c)(r−L).

At r=L either deficit branch agrees. Integrating both signs of x yields the
complete scaled raw loss bound

    exp(−2|z|)|R_N(z)−R_infinity(z)|
        <= 2(L+1/delta(c))exp(−eta(c)L).

No asymptotic expansion of E and no saddle approximation is used. The inner
interval contributes2L exp(−eta L), the two outer rays contribute
2 exp(−eta L)/delta. This retains both removed coordinates via the parent's
exact full product-loss inequality.

For either source let a be its finite normalizer and b its infinite normalizer.
The parent gives s<=a<=b<=2, b−a<=2exp(−L/2), and

    0<=a^(-2)−b^(-2)<=8exp(−L/2)/s⁴.

It also gives |R_infinity(z)|<=4cosh(2|z|)<=4exp(2|z|).
Apply the exact identity

    R_N/a²−R_infinity/b²
      =(R_N−R_infinity)/a²+R_infinity(a^(-2)−b^(-2)).

After multiplying by exp(−2|z|), the two bounds are precisely Q_N(c).
Since delta,eta>0 and L->infinity, Q_N(c)->0.

For real t>=0, denote scaled finite kernels by a_N=exp(−2t)B_A,N(t),
b_N=exp(−2t)B_U,N(t), and scaled infinite kernels by a,b. The bounds above
give |a_N−a|,|b_N−b|<=Q_N(c) uniformly for0<=t<=cL.
The parent supplies a->lambda/2, b->1/2 as t->infinity; hence every qualified
N_m->infinity,t_m->infinity gives those same scaled limits, finite ratio->lambda,
and B_A,N_m(t_m)−B_U,N_m(t_m)->minus infinity. The ratio step uses the positive
nonzero limiting denominator1/2; the escape multiplies a strictly negative
scaled limiting gap by exp(2t_m)->infinity.

The uniform negative gap follows quantitatively. The parent entire remainder
gives |a−lambda*b|<=C exp(−4t/3), C=pi²/(12Z²), while b>=1/2 and lambda<1.
Thus, throughout the window,

    a_N−b_N <= −(1−lambda)/2+C exp(−4t/3)+2Q_N(c).

Choose T>0 with C exp(−4T/3)<=(1−lambda)/8 and
exp(2T)(1−lambda)/4>=1/2; then choose N large enough that
Q_N(c)<=(1−lambda)/16. For all T<=t<=cL, the scaled gap is at most
−(1−lambda)/4, so the unscaled gap is at most−1/2. Empty windows are harmless.

## Outstanding gates

- [x] Independent complete paper/source/overlap audit PASS; no endpoint or optimality claim.
- [ ] Exact Lean plan and complete formalization after parent dependencies are FINAL.
- [ ] Every proof and public interface audited; named/direct/all-public foundational checks; integration.
- [ ] Publication novelty audit.

2026-09-30 12:05 UTC — Created before proof formalization. Parent's full four-leaf
formalization continues without altered statements. This new paper target is
unverified by Lean and does not settle the actual compensation sign or RH.

2026-09-30 12:12 UTC — Producer independent READ ALL141 original card and every source/overlap record PASS. Certificate `/tmp/hgt-li-quarter-window-independent-audit.md`135 lines, SHA256 `a0f2607cc6c1f74c6ca33c9df0479b0545293d7321f8b99981b10ffd49be089c`; root READ ALL135 and source prerequisites already fully reviewed. Frozen original paper SHA256 `f3c251b7fb964e0b4c7b07ea75d7da999d6820edc7dca9edf9bb5cf268ccbe3e`. Moved Stage2; formal plan/release pending parent FINAL dependencies. All weighted complex and real joint/uniform conclusions retained. RH unresolved.

2026-09-30 12:29 UTC — Formalization plan `/tmp/hgt-li-quarter-window-formal-plan.md`42 lines preserves all Q1–Q6: exact weighted whole-complex-disk bounds for both sources, vanishing explicit Q_N, all qualified real scaled/ratio/gap limits and uniform negative gap. Root full plan/proof route PASS; independent plan review pending. Minimal Borel reuse plan `/tmp/hgt-li-infinite-borel-quarter-reuse-plan.md`90 lines proposes only literal raw-loss envelope, genuine integrability and two normalized unrestricted-complex caps; root READ ALL90/PASS, independent review pending. Parent1680/48 Borel core now full author/root/independent proof PASS; no parent tree promotion or quarter implementation yet.

2026-09-30 12:34 UTC — Root READ ALL independent `/tmp/li_pole_quarter_formal_plan_audit.md` PASS; all42 formal-plan and90 reusable-interface lines plus complete Stage2 paper audited. Released producer exactly4 append-only Borel wrappers (literal raw-loss envelope/integrability/two unrestricted-complex normalized caps), retaining1680/48 baseline; full52 gates pending. Released root sole `/tmp/hgt-li-quarter-algebra-*` Q2 scratch helper and pole sole planned `LiClockPairedEtaInfinitePartitionQuarterWindow.lean` for Q1/Q3–Q6/assembly. Actual consumers import only certified FINAL Borel. All six paper targets, both lost coordinates/Z² normalizers, c=0 complex cases and0<c<1/4 real consequences retained. No critical endpoint or RH claim.

2026-09-30 12:37 UTC — Root Q2 pure helper complete: `/tmp/hgt-li-quarter-algebra-frozen.lean`60 lines/3theorems, SHA256 `aae289f37296020c1f14b8e713c25da4b6b3b8a2bb78579a1ec7b469931de0ff`. Toolchain name/type probe88267 exit0/empty; full compiler68997 exit0/empty; ALL3 axiom check77454 exit0, only foundational axioms. Every complete header/report mechanically source-matched. Exact edge/inner/outer square-root exponent estimates retain c=0,tau=0 and shared r=L boundary. Pole independent ALL60 proof review pending before exact private reuse; actual Q1/Q3–Q6 implementation remains ongoing. No tree promotion.

2026-09-30 12:38 UTC — Pole independent READ ALL60 Q2 proof audit PASS; root complete certificate read and source claims checked. Exact helper now approved for private reuse, with all3 foundational axiom checks complete. Remaining actual weighted kernel bounds/qualified/uniform consequences retain full Q1–Q6 scope.

2026-09-30 12:52 UTC — Pure Q5/Q6 helper ownership split confirmed with Pole: root sole `/tmp/hgt-li-quarter-limit-*`, Pole retains Q1/Q3/Q4, all actual source callers and sole final leaf. Root115-line scratch preserves exact prior ratio/negativegap private bodies; weighted-absolute-error perturbation transfers all4 sequence limits. Uniform lemma uses the already-proved negative scaled source-gap limit to choose one fixedT before eventualN, preserving exact Q6 conclusion. Nameprobe57713 exit0/empty; full compiler61448 active, no proof success claimed yet. Full independent proof/axiom checks required before private reuse. All original paper targets remain unchanged.

2026-09-30 12:54 UTC — Root Q5/Q6 helper compiled/frozen116 lines,2public/3private, SHA256 `e4e1277ffc431c15ef409e64b475ac3080281ea42a8384ec04ffca8bd01ac89e`: `/tmp/hgt-li-quarter-limit-frozen.lean`. Full compiler8738 exit0/empty; ALL2 axiom check29393 exit0/foundations only. Exact public headers/reports and both reused private bodies mechanically verified. Initial61448 only missing reflexive inequality discharge, fixed with le_rfl. Current independent READ ALL116 review pending; actual source callers remain Pole-owned and await FINAL Borel.

2026-09-30 12:56 UTC — Current independent READ ALL116 Q5/Q6 proof audit PASS; root complete certificate read/source claims checked, Pole full mathematical applicability review also PASS. Exact private reuse released after all2 foundational checks. All root Q2/Q5/Q6 scratch helper certificates consolidated in `/tmp/hgt-li-quarter-root-helpers-final-certificate.md`; actual Q1–Q6 source callers and full final leaf remain ongoing. Borel named52487 exit0/success13000jobs/own157s; exact direct57678 active, ALL52 axiom gate pending.

2026-09-30 13:08 UTC — Pure Quarter316-line scratch39981 exit0/empty, SHA256 `6346501a715b66a587081d39388c8213d8dbe90a21c8ab432fbb72cded9a5161`,9public/14private; full root/producer proof audits PASS. Root matched every complete API block and exact original Q2 private body mapping. Genuine whole-axis envelope integration/factor2, vanishing Q_N and weighted normalization cancellation preserved. Earlier315-line metadata was off by one; file has316 newline-terminated lines, source unchanged. Full actual582 source callers remain in toolchain work; no final quarter claim.
