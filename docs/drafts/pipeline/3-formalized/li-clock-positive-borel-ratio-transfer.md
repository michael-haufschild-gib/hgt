# Full positive even series: sharp coefficient-ratio transfer

- **ID:** LI-CLOCK-POSITIVE-BOREL-RATIO-TRANSFER
- **Stage:** 3-formalized
- **Type:** THEOREM (dependency-closed paper and complete formal proof; 11 public declarations FINAL)
- **Source:** [actual endpoint boundary](../3-formalized/li-clock-partition-density-ratio-endpoint-boundary.md); existing finite-partition positive Borel prefix mechanism
- **Statement:** Let `a_j>=0`, `b_j>0`, with full even series `A(t)=Σ a_j*t^(2j)`, `B(t)=Σ b_j*t^(2j)` convergent for every real clock. If `a_j/b_j→k`, then `A(t)/B(t)→k` as `t→+∞`. Under all-order `a_j<=k*b_j`, `k` is the optimal uniform coefficient and kernel ceiling; strict zeroth coefficient makes the kernel bound strict. If `k>1`, `A-B→+∞`; if also the first coefficient is strictly below its ceiling, `k*B-A→+∞`.

## Complete paper certificate

Full54-line `/tmp/hgt-li-endpoint-borel-ratio-helper-paper.md` was read completely by current. For `δ>0`, take `J>=1` with tail relative error at most `δ`. At `t>=1`, finite error prefix is at most `D*t^(2*(J-1))`, while `B(t)>=b_J*t^(2J)`. Absolute summability licenses the complete split and triangle inequality, giving `abs(A-kB)/B<=D/(b_J*t^2)+δ`. This proves the full ratio limit. Coefficient domination and strict zeroth coefficient prove the strict bound at every real clock; the first positive denominator coefficient makes `B→+∞`. The two difference limits and both optimality statements follow with exactly the listed premises. No finite-packet approximation or sign inversion.

Independent audit explicitly checked that `kB-A→+∞` needs **all-order domination plus the strict first coefficient**. Strict first coefficient alone does not suffice. All even-power bounds hold for every real clock; escape is stated at positive infinity.

## Overlap and actual-source boundary

Existing `LiClockPairedEtaFinitePartitionVolterra.lean:498` finite-prefix negligibility and :554 positive weighted-degree growth use the same higher-degree denominator mechanism; source symbols were independently checked. This is an elementary ratio-transfer extension, with no publication novelty claim. Prior documented actual relative/endpoint research coverage is recorded on the source card; every returned candidate/source argument was inspected. Actual density identification, endpoint moment ratio, and source domination remain separately audited obligations. Applying this generic theorem without them is not authorized mathematically.

## Gates and scope

- [x] Dependency-closed proof and independent complete premise/overlap audit before new Lean.
- [x] Exact generic Lean theorem and sharp comparison/escape consumers; named/direct/all-public foundational checks.
- [x] Wiring, scoped index/lint and full proof audit (global lint failures below are unrelated).
- [ ] Publication/novelty audit.

Root exclusively owns new `LiClockPositiveEvenSeriesRatio.lean` and own `/tmp/hgt-li-borel-ratio-*` scratch/logs. No other agent may edit it. No actual density/moment premise is introduced by definition or omitted from consumers. Existing leaves remain frozen. Root one foreground Lean at a time.

## Log

- 2026-09-30 07:06 UTC — CreatedStage2 after full author/current paper and source-overlap audits, before Lean. Actual endpoint card remainsStage1; RH residual pointwise sign remains open.
- 2026-09-30 08:15 UTC — Exact283-line `LiClockPositiveEvenSeriesRatio.lean` FINAL/FROZEN and wired,11 public declarations,SHA256 `9d871fe0258492a0a82bae5bd5ddead2e4efe652e2f9eb1b7ae8ebb229bded38`. Every public/private body independently read by current, full proof audit `/tmp/li_current_borel_ratio_audit.md`; quantitative complete prefix/tail estimate, coefficient-to-full ratio, both optimal ceilings for every real `K`, and both difference escapes closed. Named82240 exit0,1769jobs,own9.3s; exact direct77937 exit0 EMPTY; all11 public axioms24651 exit0,only `propext, Classical.choice, Quot.sound`. Logs `/tmp/hgt-li-borel-ratio-{named,direct,public-axioms}.log`; exact API `/tmp/hgt-li-borel-ratio-api-ledger.md`. Source applications still require their separately proved moment/summability premises; no arithmetic sign or RH conclusion. Index/lint closure pending.
- 2026-09-30 08:19 UTC — Closure index78758 exit0:1 changed,0 removed; every11 generic and53 reference definition/theorem API rows match source (reference SFinite instance separately included in the complete54 axiom audit). Global lint83316 exit1 on11 unrelated unreachable modules: `CCMApertureChainProfile`, `CCMApertureTranslationChains`, `CCMExponentialRampPrimeMoment`, `CCMExponentialRampSourceDissipation`, `CCMExponentialRampTerminalEntropy`, `CCMRetainedChainKernelLower`, `MoebiusMollifiedCriticalMoment`, `MoebiusMollifiedErrorThreeLines`, `ThetaMovingShellFirstOrderPhase`, `ThetaTranslationDensityRatio`, `ZetaZeroDensityPowerSaving`. No forbidden declaration or owned-leaf failure. Logs `/tmp/hgt-li-measure-ratio-final-{index,lint}.log`; unique umbrella imports, exact frozen hashes and scoped whitespace checks PASS. Exact generic scope complete; movedStage3. Actual endpoint/density consumers and RH residual sign remain open.

## Stronger exposed candidate

Complete proof audit found redundant numerator-nonnegativity premises in the ratio/error/coefficient-ceiling statements, and redundant source-sign premises in the ceiling-deficit escape under nonnegative full deficits. Signed extensions are candidate paper obligations, with no new public API or novelty claim; they are unnecessary for the actual positive source application. Existing positive-source theorem remains the audited scope.
