# CCM-FU: initial small-subset ceiling

- **Stage:** 1-in-progress
- **Parent:** [adaptive prime ceiling](../../ccm-fu-adaptive-prime-ceiling.md)
- **Question:** Does every original processed subset of at most two primes stay below the original diagonal? What is the smallest subset size and first stored cutoff where unrestricted subset control fails?
- **Method:** Read every saved subset energy through cutoff32. Group failures by processed cardinality, retaining the exact source and original tolerance `1e-12*max(1,Q_empty)`. Regenerate neither channels nor greedy paths. Numerical output guides the next paper argument and is never a Lean premise.

The oriented initial block theorem controls any one additional prime. Arbitrary repeated smaller-prime mergers do not preserve its parity condition. This diagnostic tests whether the original energy reserve nevertheless permits two arbitrary initial mergers; it does not test or refute the existence of an adaptive complete order.

## Current evidence

All 627 two-prime states through cutoff32 satisfy the original diagonal ceiling, as do every stored state with zero, one, three or four processed primes. The first stored failure is at cutoff17 with `P={3,5,7,11,13}`: energy is approximately `0.373051588208`, exceeding original energy `0.362178444601`. The smallest failing stored cardinality is five. These are numerical statements only; neither two-prime control at every cutoff nor the cutoff17 inequality is formally certified here.

The complete grouped output, retained input hash and reproducible stored-data script are [cardinality-reanalysis.json](../../../2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/cardinality-reanalysis.json) and [cardinality_reanalysis.py](../../../2-fully-proven/computations/ccm-fu-adaptive-prime-energy-2026-09-06/cardinality_reanalysis.py). No channel or greedy path was regenerated.

The [formal quantitative defect transport](../../../3-formalized/ccm-fu-parity-defect-transport.md) gives a second-merger bound using the first merger's created sign-defect energy and the original diagonal. Its arithmetic adjacent-cutoff bound is unconditional. To establish the two-prime ceiling, a sharper source comparison must show that this cost is covered by the first merger's released energy, or directly bound the complete signed second-step gain. That comparison remains open.

The [source-local block candidate](../../ccm-fu-two-prime-local-blocks.md) isolates a sharper comparison: `K_p(N)<=2 K_1(N)` for every prime and cutoff. The [formal sharp criterion](../../../3-formalized/ccm-fu-two-prime-local-criterion.md) retains every four-coefficient block and proves an unconditional alternative: a two-prime ceiling failure at M forces a unit-channel factor-two failure for one of those same primes at `r<N<=M`. The factor two is sharp for the nonnegative local comparison class. The actual unit comparison remains open.

All 6562 stored cofactor blocks through32 pass. Extending only first-prime diagnostics to cutoffs33..1024 gives 617453 passing active source-pair factor-two comparisons and 95747 passing first-prime geometric reserve tests. The latter would suffice for all second extensions at those cutoffs, but these remain numerical checks. The saved one-dimensional source table permits further analysis without regenerating it; no computed result enters Lean.

An infinite source family now has an unconditional two-prime ceiling:
at M=12p, every sufficiently large prime p permits every available second
prime q under the original diagonal. The [formal exact-overlap proof](../../../3-formalized/ccm-fu-exact-overlap-recovery.md)
retains every four-cofactor block and is uniform in q. This includes states
whose first geometric certificate fails. The proof also supplies the global
unsigned ceiling `K_d(M)<=3sqrt(M)/5`. The unrestricted all-cutoff two-prime
comparison and complete prime orders remain open.
