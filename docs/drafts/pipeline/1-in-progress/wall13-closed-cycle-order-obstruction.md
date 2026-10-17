# Wall 13: closed-cycle order and packet charge

- **ID:** BSU-W13-CYCLE-ORDER
- **Stage:** 1-in-progress
- **Type:** CONJECTURE; dependency-closed paper proof below, Lean pending
- **Scope:** BiScaleUncertainty, Wall 13; no RH work.
- **Statement:** no fixed order of closed correlation products or Gram determinants determines signed polar balance.

## Plan

1. Audit current corpus and exact installed APIs.
2. Formalize concrete separated-copy packet labels, product-sign classification and charge bound.
3. Derive all bounded-order closed products and Gram determinants; construct smooth polar-distinct witnesses.
4. Direct serial leaf checks, axiom/signature audits, wiring, index, lint, no-go closure and next conjecture.

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

## No-go closure target

- **Rejected route:** any fixed order of complete closed-cycle data or Gram determinants recovers polar balance for all compact sources.
- **Exact obstruction:** arbitrarily separated smooth opposite-copy sources.
- **Strongest positive survivor:** full product-sign classification by packet-charge parity, and the quantitative charge/error bound for every nonzero lag product.
- **New insight:** correlation orientation has an unbounded detection order controlled by packet separation; the previous one-anchor recovery is not replaced by a uniform finite-order closed statistic.
- **Boundary:** no sharp converse, general-source phase retrieval, blind-source coercive bound, or closure of Wall 13 is claimed.
- **Lean status:** pending; do not retire until the exact positive survivor is formalized.

## Next conjecture (unproved)

All finite closed-cycle products together determine the entire signed autocorrelation of a compact continuous real source. Candidate mechanism: the two-edge cycles determine squares; positive mass and continuity fix the sign near zero; a sufficiently long cycle with many small equal increments transports that sign to an arbitrary lag. Zero mass requires a separate degeneration argument. This is not yet a proved or formalized result.

## Gates

- [x] Concrete wall-specific paper mechanism.
- [ ] Corpus and API audit complete.
- [ ] Exact positive survivor formalized.
- [ ] Smooth bounded-order cycle and determinant witnesses formalized.
- [ ] Direct checks, axioms, wiring, index and lint inspected.
- [ ] Failed-route record, next conjecture and memory updated.
