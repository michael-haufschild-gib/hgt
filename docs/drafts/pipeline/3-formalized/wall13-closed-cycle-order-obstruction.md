# Wall 13: finite-order obstruction and complete closed-cycle recovery

- **ID:** BSU-W13-CYCLE-ORDER
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scope:** BiScaleUncertainty, Wall 13; no RH work.
- **Statement:** no fixed order of closed products and Gram determinants determines polar balance; all closed products together determine the entire signed correlation and polar moment.

## Plan

1. Audit current corpus and exact installed APIs.
2. Formalize concrete separated-copy packet labels, product-sign classification and charge bound.
3. Derive all bounded-order closed products and Gram determinants; construct smooth polar-distinct witnesses.
4. Prove the positive replacement: the entire hierarchy of closed products determines any compact source's signed correlation and polar moment.
5. Direct serial leaf checks, axiom/signature audits, wiring, index, lint, no-go closure and next conjecture.

`update_plan` unavailable; this card persists the plan. Previous goal turn made verified progress through three formalized square-transfer leaves. Full goal remains walls 2–15.

## Frontier audit

Parent package: [square transfer and signed reconstruction](../3-formalized/wall13-schur-square-orientation.md).
Current corpus searches: `/tmp/bsu-wall13-cycles-frontier.json` and `/tmp/bsu-wall13-cycles-copy-search.json`.
The first deep search completed without errors, but returned mostly unrelated orientation/cycle results; its proposed ingredient set does not prove this claim. All 20 candidate and 20 source statements inspected. Coverage snapshot inventories all files, but semantic coverage is unmeasured and most compiler statuses are pending/source-only/stale. No exhaustive novelty claim. The exact existing subtraction/correlation/polar identities are reused.

## Dependency-closed paper proof

Let f be an actual compact continuous real source, h its autocorrelation, and D>0 an autocorrelation support radius. For m in N choose T=(m+2)D+1. Then T>2D and T>mD. Set g_a(u)=f(u)-a f(u-T). Its correlation is

    h_a(x)=(1+a²)h(x)-a[h(x-T)+h(x+T)].

Define the integer packet label c(x) by 0 if |x|<=D, 1 if |x-T|<=D and the first condition fails, and -1 otherwise. Central and outer packets are disjoint. Hence, at every lag, including zero factors,

    h_(-a)(x)=(-1)^c(x) h_a(x).

If h_a(x) is nonzero, at least one packet is active and |x-c(x)T|<=D. For a finite list L of lags let Q(L)=sum c(x) and P_a(L)=product h_a(x). Multiplication gives the exact positive classification

    P_(-a)(L)=(-1)^Q(L) P_a(L),
    P_(-a)(L)=P_a(L) iff P_a(L)=0 or Q(L) is even.

For nonzero product, summing errors gives

    |sum L-Q(L)T| <= length(L) D.

If sum L=0 and length(L)<=m, then |Q(L)|T<T, so the integer Q(L) is zero. Thus every closed product of order at most m agrees for the two sources. The empty list gives 1 and is covered.

For any n<=m, translated sample points t_i, and permutation sigma, the lags t_(sigma i)-t_i sum to zero and number n. Each permutation product therefore agrees. The determinant expansion implies equality of all n-by-n autocorrelation Gram determinants, uniformly over all translated samples. This includes all principal minors of larger samples of those orders.

Take the existing smooth compact seed of strictly positive mass and polar moment. Choose a=exp(-T/2). Then g_a has zero normalized polar moment, whereas g_(-a) has twice the seed's strictly positive moment. Their masses agree and are positive. This proves the bounded-order obstruction with concrete smooth witnesses, not assumed correlation kernels.

## No-go closure

- **Rejected route:** any fixed order of complete closed-cycle data or Gram determinants recovers polar balance for all compact sources.
- **Exact obstruction:** arbitrarily separated smooth opposite-copy sources.
- **Strongest positive survivor:** full product-sign classification by packet-charge parity, quantitative charge/error bound for every nonzero lag product, and complete recovery from the entire closed-product hierarchy for arbitrary compact continuous sources.
- **New insight:** correlation orientation has an unbounded detection order controlled by packet separation; the previous one-anchor recovery is not replaced by a uniform finite-order closed statistic.
- **Boundary:** no sharp converse, general-source phase retrieval, blind-source coercive bound, or closure of Wall 13 is claimed.
- **Lean status:** exact obstruction and all positive survivors formalized and axiom-audited; [failed-route record](../5-failed/wall13-fixed-order-polar-recovery.md).

## Positive replacement: all closed products (proved in Lean)

The new conjecture from the bounded-order obstruction succeeds on paper. Let two actual compact continuous sources have equal closed products of every finite order. The one-edge list [0] identifies their masses R. If R=0, the autocorrelation bound |h(x)|<=R makes both profiles identically zero.

For R>0, the two-edge lists [x,-x] identify h_f(x)²=h_g(x)². By continuity and equal positive value at the origin, h_f+h_g is strictly positive on some neighborhood (-delta,delta). Equality of squares then implies h_f=h_g>0 there. For any x choose an integer n>0 with |x/n|<delta. The closed list [-x,x/n,...,x/n], with n repetitions, identifies

    h_f(x) h_f(x/n)^n = h_g(x) h_g(x/n)^n.

The small-lag factors agree and are nonzero, so cancellation recovers h_f(x)=h_g(x). The converse follows by direct substitution in every product. Thus complete closed-product data are equivalent to complete signed correlation data, including the zero source.

Polar moment depends only on correlation. Choosing any source realizing a supplied closed-data profile, and returning zero for unrealizable profiles, therefore defines a noncomputable scalar recovery functional valid on every actual compact source. Its well-definedness is proved by the preceding injectivity theorem, not assumed as an interface. This is an existence theorem, not a stable numerical reconstruction algorithm.

Corpus search `/tmp/bsu-wall13-full-cycle-search.json` completed without errors; all 20 candidate and 20 source statements inspected. It returned related packet formulas and the previous one-anchor reconstruction, but no matching all-closed-product theorem. Semantic coverage remains unmeasured; background refresh incomplete. No exhaustive absence or external novelty claim.

Lean status: `closedProduct_eq_iff_autocorr_eq`, `all_shortData_eq_iff_autocorr_eq`, and the actual functional `polarRecovery` with correctness theorem `polarRecovery_closedProduct` all pass. These prove recovery of signed correlation; they do not assert uniqueness of the original source or recovery from Gram determinants alone.

## Exported package and verification

All declarations are in `GaloisForLFunctions.BiScaleUncertainty.SeparatedCycle`.

| Leaf | Main results | Public declarations |
|---|---|---:|
| `SeparatedCopyCycleCharge` | `rawProduct_sign`, `rawProduct_eq_iff`, `packetCharge_bound`, `shortData_source_neg` | 18 |
| `SeparatedCopyCyclePolarAmbiguity` | `gramData_source_neg`, `exists_smooth_same_finite_data_distinct_polar`, `polarMoment_not_factor_through_finite_data` | 5 |
| `ClosedCorrelationCycleRecovery` | `closedProduct_eq_iff_autocorr_eq`, `all_shortData_eq_iff_autocorr_eq`, `polarRecovery_closedProduct` | 4 |

The package exports 17 theorems and ten concrete definitions. The witness theorem quantifies over every natural order and constructs actual smooth compact sources, with positive equal mass and zero versus positive normalized polar moment. The recovery theorem quantifies over arbitrary actual compact continuous sources, including zero mass. No assumed analytic estimate, factorization, positivity certificate or desired-conclusion interface is present.

- All three serial direct checks passed using `lake --old env lean -j 1 <leaf> -o <normal .olean>`, with empty logs. The final direct check `lake --old env lean -j 1 GaloisForLFunctions/BiScaleUncertainty/ClosedCorrelationCycleRecovery.lean` also passed with empty output.
- `/tmp/bsu_wall13_cycle_axioms.lean` printed all 27 axiom lists, all theorem signatures and all definition bodies. Each was inspected. Only `propext`, `Classical.choice` and `Quot.sound`; exit 0, no warnings. Log `/tmp/bsu-wall13-cycle-axioms-r2.log`.
- Installed API probes passed. No numerical experiments, added axioms, placeholders, heartbeat changes, full builds or umbrella builds.
- Exactly one umbrella import per new leaf. Compiled outputs newer than sources; source/output hashes in `/tmp/bsu-wall13-cycle-manifest.json`.
- Index refresh passed. Exact documented lexical searches discover both the finite-data obstruction and the complete recovery theorem; logs `/tmp/bsu-wall13-cycle-{counterexample,recovery}-discovery.json`.
- **Global lint failed, exit 1:** exactly two errors: `GaloisForLFunctions.BiScaleUncertainty.CoshDecayGroundPotentialAndThetaVolumeCollarProducer` unreachable from its umbrella, and `BezoutValuationIncidence.lean` a research leaf at the package root. Both are concurrent work outside these three leaves. The remaining 381 messages are large-file warnings. Log `/tmp/bsu-wall13-cycle-lint.log`.
- Read-only field README and walls ledger retain their starting hashes. Scoped whitespace checks passed. Obsolete API probes removed after verification; final axiom scratch retained.

Wall 13 remains open: no blind-source coercive lower bound or compatible positivity transfer follows. Full goal remains walls 2–15.

## Next conjecture

[Exact minimal cycle-detection order](../0-backlog/wall13-minimal-cycle-order.md): for an explicitly constructed smooth seed with correlation positive exactly on (-1,1), the least distinguishing closed-product order at copy gap T>2 should be floor(T)+1. Strict support endpoints, concrete seed construction and determinant cancellations remain unaudited. No proof is claimed.

## Gates

- [x] Concrete wall-specific paper mechanism.
- [x] Corpus and API audit complete.
- [x] Exact positive survivor, including full closed-data recovery, formalized.
- [x] Smooth bounded-order cycle and determinant witnesses formalized.
- [x] Direct checks, axioms, wiring, index and lint inspected; unrelated global failures recorded.
- [x] Failed-route record and next conjecture recorded; cross-session memory updated.

## Log

- 2026-10-18 — C3 bounded-order obstruction and C4 complete closed-product recovery formalized. C5 exact detection order remains conjectural. Goal active; no wall-closure claim.
