# Full positive even series: sharp coefficient-ratio transfer

- **ID:** LI-CLOCK-POSITIVE-BOREL-RATIO-TRANSFER
- **Stage:** 2-fully-proven
- **Type:** THEOREM (dependency-closed elementary paper; root author and independent current audit PASS)
- **Source:** [actual endpoint boundary](li-clock-partition-density-ratio-endpoint-boundary.md); existing finite-partition positive Borel prefix mechanism
- **Statement:** Let `a_j>=0`, `b_j>0`, with full even series `A(t)=Σ a_j*t^(2j)`, `B(t)=Σ b_j*t^(2j)` convergent for every real clock. If `a_j/b_j→k`, then `A(t)/B(t)→k` as `t→+∞`. Under all-order `a_j<=k*b_j`, `k` is the optimal uniform coefficient and kernel ceiling; strict zeroth coefficient makes the kernel bound strict. If `k>1`, `A-B→+∞`; if also the first coefficient is strictly below its ceiling, `k*B-A→+∞`.

## Complete paper certificate

Full54-line `/tmp/hgt-li-endpoint-borel-ratio-helper-paper.md` was read completely by current. For `δ>0`, take `J>=1` with tail relative error at most `δ`. At `t>=1`, finite error prefix is at most `D*t^(2*(J-1))`, while `B(t)>=b_J*t^(2J)`. Absolute summability licenses the complete split and triangle inequality, giving `abs(A-kB)/B<=D/(b_J*t^2)+δ`. This proves the full ratio limit. Coefficient domination and strict zeroth coefficient prove the strict bound at every real clock; the first positive denominator coefficient makes `B→+∞`. The two difference limits and both optimality statements follow with exactly the listed premises. No finite-packet approximation or sign inversion.

Independent audit explicitly checked that `kB-A→+∞` needs **all-order domination plus the strict first coefficient**. Strict first coefficient alone does not suffice. All even-power bounds hold for every real clock; escape is stated at positive infinity.

## Overlap and actual-source boundary

Existing `LiClockPairedEtaFinitePartitionVolterra.lean:498` finite-prefix negligibility and :554 positive weighted-degree growth use the same higher-degree denominator mechanism; source symbols were independently checked. This is an elementary ratio-transfer extension, with no publication novelty claim. Prior documented actual relative/endpoint research coverage is recorded on the source card; every returned candidate/source argument was inspected. Actual density identification, endpoint moment ratio, and source domination remain separately audited obligations. Applying this generic theorem without them is not authorized mathematically.

## Gates and scope

- [x] Dependency-closed proof and independent complete premise/overlap audit before new Lean.
- [ ] Exact generic Lean theorem and sharp comparison/escape consumers; named/direct/all-public foundational checks.
- [ ] Wiring, scoped index/lint and full proof audit.
- [ ] Publication/novelty audit.

Root exclusively owns new `LiClockPositiveEvenSeriesRatio.lean` and own `/tmp/hgt-li-borel-ratio-*` scratch/logs. No other agent may edit it. No actual density/moment premise is introduced by definition or omitted from consumers. Existing leaves remain frozen. Root one foreground Lean at a time.

## Log

- 2026-09-30 07:06 UTC — CreatedStage2 after full author/current paper and source-overlap audits, before Lean. Actual endpoint card remainsStage1; RH residual pointwise sign remains open.
