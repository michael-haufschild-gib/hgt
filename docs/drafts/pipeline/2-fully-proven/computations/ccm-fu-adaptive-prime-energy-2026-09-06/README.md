# Adaptive prime-energy guidance

Frozen question PE3: at every cutoff, does some ordering of all primes below the cutoff make every literal merger nonincreasing in energy? See the [closed obstruction and positive survivor](../../../5-failed/ccm-fu-adaptive-prime-energy.md).

`screen.py` enumerates every processed-prime subset and all incoming edges for every M=1..32. Dynamic programming over this entire directed cube decides existence of a nonincreasing path, with floating-point tolerance `1e-12 max(1,Q_initial)`. Every state energy, incoming edge mask and reachability result is saved in `subset-states.csv`; terminal summaries are in `full-path-summary.json`.

The separate deterministic greedy screen chooses the prime with smallest next energy, breaking ties by smaller prime, for every M=1..1024. All steps are saved in `greedy-stages.csv`; complete orders and first increases are in `greedy-summary.json`. This screen took approximately 119 seconds. A greedy failure does not refute existence of another order.

- First full-path failure: M=7, with eight subset states and no complete nonincreasing path.
- First greedy failure: M=5. A different order succeeds there.
- Greedy has at least one increasing step at 1019 of the 1024 screened cutoffs.

`audit.py` independently evaluates the defining half-order channel sums at 80-digit precision, explicitly expands each smooth-prime subset, and checks all six complete orders at M=7. Its complete output is `direct-audit.json`. Each order increases in the final step. Initial energy is about `0.0487759959881`; final energy is about `0.0318189935442`. Thus the final increase does not violate the original diagonal budget at this cutoff.

These files supply guidance, not Lean proof inputs. The linked analytic proof derives rational channel bounds from harmonic/logarithm and square-root inequalities; proves every literal order's final increase; and proves `Q(7)-S(7)^2>1/125`. No computational result is a premise. No further run is needed without a new research question.

## Original-diagonal ceiling reanalysis

The separate frozen [PE4/PE4G questions](../../../1-in-progress/ccm-fu-adaptive-prime-ceiling.md) permit local energy increases while keeping every stage below the original diagonal. `ceiling_reanalysis.py` reads only `subset-states.csv` and `greedy-stages.csv`; it does not regenerate a channel or repeat the expensive greedy search. Its checked output is `ceiling-reanalysis.json`.

For each saved subset P it computes the exact combinatorial minimax recurrence on the stored floating-point energies: `c(empty)=Q_empty`, `c(P)=max(Q_P,min_(p in P)c(P\{p}))`. Every cutoff through32 has minimum full-path ceiling equal to its original diagonal. Every greedy stage through1024 also stays below that diagonal with the original tolerance. The largest recorded post-merge/original ratio is about `0.773063650278327` at M=17, step6, prime11; that step itself increases energy. Cutoffs with no prime below M have no recorded merger stage, and their initial energy equals their ceiling. This reanalysis took about0.12seconds and supplies guidance only. No all-cutoff PE4 or PE4G proof follows.

## Overlap-phase reanalysis

The frozen question asks whether a nonincreasing next merger always exists while two distinct remaining primes p,q satisfy `p*q<M`. `overlap_reanalysis.py` reads every saved subset state and greedy stage, using the original tolerance and regenerating neither source channels nor paths. `overlap-reanalysis.json` records the input hashes, counts and first failures.

There are 136 forced-growth states among 5720 states with possible overlap, first at M=11, P={3,7}, remaining pair {2,5}. Among 70640 greedy stages with possible overlap, 19954 increase; the first is M=16, step three, prime five, with P={2,7} and remaining overlap pair {3,5}. The greedy-specific result remains numerical guidance. These failures concern local contraction, not the frozen PE4/PE4G original-diagonal ceiling.

The [analytic M=11 certificate and exact two-coordinate minimax law](../../../5-failed/ccm-fu-overlap-phase-contraction.md) are closed in Lean independently of these values. The actual joint fibre is positive, both next steps grow by more than 1/200, and every remaining completion subset stays more than 1/100 below the original diagonal. No computational result is used as a Lean premise.

## Common-order compatibility reanalysis

Frozen PE4C asks whether one prime order can meet every smaller cutoff's original-diagonal ceiling simultaneously. `common_order_reanalysis.py` reads all saved subset energies. For each cutoff bound B, it marks a state admissible only when every restriction to M<=B meets that cutoff's ceiling, then computes reachability in this intersection graph. The original tolerance is retained. No channels or greedy paths are regenerated.

`common-order-reanalysis.json` records all bounds, graph counts, successful orders and the input hash. Every bound through 32 passes. At bound 32, all 1938 admissible states among 2048 are reachable; one complete common order is `31,29,23,19,17,13,11,2,7,3,5`. This is a finite floating-point compatibility pass, not an all-cutoff proof or Lean input. The separate arithmetic fixed-block obstruction requires any successful family of such orders to have an unbounded number of late-prime interleavings.

## Nonempty-energy reanalysis

`nonempty_reanalysis.py` tests the separate frozen assertion that every prime merger contracts `V=Q-H^2`, the energy outside the retained head; it also tests existence of a complete V-nonincreasing order. It reads every saved subset energy and reconstructs H from isolated late-prime energy differences, using the literal coefficient `C_p=-(sqrt(M)-sqrt(p))*(2 gamma-1)`. No channel table or greedy path is regenerated.

The checked output `nonempty-reanalysis.json` retains the input hash, all cutoff path witnesses and summary diagnostics. Among 41409 edges, 2472 increase V. The first is M=21, P={2}, next prime five: approximately 0.0896410813 becomes 0.0974192969. Every saved cutoff through 32 admits a V-nonincreasing complete path. All late-prime anchors are checked against each other; maximum head disagreement is about 4.2e-14. Minimum reconstructed V is about -2.0e-14, consistent with floating-point roundoff at zero-energy endpoints.

The [cutoff-21 analytic obstruction and all-cutoff steering law](../../../5-failed/ccm-fu-nonempty-energy-contraction.md) are closed in Lean without these computed values. The actual V increase exceeds 1/1000. The positive survivor identifies exact late-block removal of singleton squares and the sign-dependent affine effect of late consumption on another prime's full-energy gain. Finite V-path success does not prove PE4 or bound the final signed head.

## Initial subset-cardinality reanalysis

The frozen [small-subset ceiling question](../../../1-in-progress/ccm-fu-initial-small-subset-ceiling.md) asks whether every initial processed set of at most two primes stays below the original diagonal. `cardinality_reanalysis.py` reads every stored subset energy and groups ceiling failures by processed cardinality. It uses the original tolerance and regenerates no channels or paths. `cardinality-reanalysis.json` records every cardinality group and the input hash.

All 627 two-prime states pass; all stored states with at most four processed primes pass. The first failure is at M=17 with `P={3,5,7,11,13}`, with energy about `0.373051588208` against original `0.362178444601`. Five is the smallest failing cardinality in the saved range. These are numerical observations, not an all-cutoff theorem or a Lean premise. The formal parity-defect transport does not use these values.

## Geometric defect-reserve reanalysis

The frozen [geometric reserve questions](../../../1-in-progress/ccm-fu-geometric-defect-reserve.md) concern complete paths under the sufficient preterminal certificate `Q_P+2 sqrt(G_P D_P)<=Q_empty`, and the weaker first-prime certificate `Q_{p}+2 sqrt(Q_empty D_{p})<=Q_empty`. `defect_reserve_reanalysis.py` recovers heads from isolated late-prime edges, then recovers source coefficients by finite subset inversion and regroups them over every remaining label. Exact squarefree support is imposed by the source index bound, not by a numerical size threshold. Every reconstructed head and energy is checked against the stored data before path reachability is computed. No channel table or greedy path is regenerated.

`defect-reserve-reanalysis.json` contains every retained state's G and D, all successful path witnesses, reconstruction diagnostics and the input hash. Among 8860 states, 1478 fail the sufficient certificate, first at M=13, P={5,7,11}: upper estimate about 0.204871656029 exceeds original energy 0.195027952331 although actual energy is only 0.112242482719. Every stored cutoff through32 admits a complete path satisfying the certificate at every preterminal state. All 192 first-prime states pass the weaker certificate. Maximum reconstructed energy and head errors are about 5.82e-14 and 4.05e-14, respectively, below the original tolerance. These are numerical guidance results, not a formal failure witness or all-cutoff proof. The independent analytic square-root source bound uses no computed input.

## Two-prime cofactor-block reanalysis

The [source-local candidate](../../../1-in-progress/ccm-fu-two-prime-local-blocks.md) asks whether each original four-coefficient block contracts after both primes are processed, and whether every active source edge satisfies `K_(pd)<=2K_d`. `two_prime_blocks_reanalysis.py` reconstructs original coefficients from saved heads using finite subset inversion, retains exact squarefree support, and checks every cofactor for every prime pair through32. Reconstructed initial and two-prime energies are checked against the complete saved energies. No source channels or greedy paths are regenerated.

`two-prime-blocks-reanalysis.json` records 6562 passing blocks over 627 prime pairs and 417 passing active source-edge factor-two comparisons. Maximum aggregate reconstruction error is about 3.71e-14. The largest child/parent ratio is about 1.31933 at M=7,p=2,d=1. These are finite numerical results. The [formal sharp class and obstruction transport](../../../3-formalized/ccm-fu-two-prime-local-criterion.md) uses no such values: a two-prime ceiling failure at M forces a unit-channel factor-two failure at an active cutoff no larger than M.

## Bounded first-prime extension

`first_prime_reserve_screen.py` extends only the frozen factor-two and first-prime geometric reserve questions to M=33..1024. It computes the one-dimensional defect and unit-channel table once, saves it as `first-prime-unit-clock.csv`, and obtains all dilated channels through exact clipped interpolation. It repeats neither subset enumeration nor greedy searches. Every original diagonal agrees with the existing greedy summary.

`first-prime-reserve-screen.json` retains all 95747 first-prime states, their original energies, actual releases, defect energies and sufficient geometric costs. All pass the weaker first-prime reserve. All 617453 active squarefree source edges pass the factor-two comparison. The largest observed ratio, about 1.31933 at M=371,p=2,d=53, is a dilation of the cutoff-seven shape. These are numerical guidance results only; the actual all-cutoff unit comparison, two-prime ceiling and complete adaptive path remain open. Reuse the saved table and records before computing any further channels.
