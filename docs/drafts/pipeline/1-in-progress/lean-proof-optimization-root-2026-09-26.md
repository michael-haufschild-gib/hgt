# Lean proof optimization — root

Scope: charged quadratic/source mean-square and tail-energy proof elaboration.
Mission: shorten verified iteration on the actual-source RH route; preserve all mathematical statements.

Plan: profile current leaves; freeze measurable performance hypotheses; validate replacements in scratch; apply only improvements; named-leaf builds and formal lint.

Constraints: no git; no heartbeat or recursion increases; no numerical mathematical experiments; one owned Lean process; no full builds; no edits to other agents' logs.

## Facts and no-gos

- Lean toolchain: v4.32.2. Prior optimization removed an unused compact-source import; do not count it again.
- Serena ignores formal Lean files; symbol lookup rejected. Direct file edits required.
- Baseline snapshots and sequential profiler harness: `/tmp/rh-lean-opt-root/`.
- Timing can be affected by other agents; compare proof-level profiles and deterministic heartbeat counts where needed.
- RH/source-kernel all-rank sign remains open. This task improves proof implementation only.
- Baseline `lake env lean -j1 --profile` passed all three leaves. Cold/import times vary sharply: quadratic 109s import / 116s total; source 60.3s / 68.5s; energy 7.81s / 13.16s. These cannot establish a speedup across files.
- Detailed trace isolates comparison-rate proof: 36.1M of 38.4M traced raw heartbeats are spent in `simpa only [mul_comm] using hcr`. The goal already matches `hcr` after `div_le_iff₀`.
- Performance hypothesis: direct application removes the global commutativity simplification; explicit quotient and distributivity identities remove unnecessary `convert`/`ring` in pair bounds and compact energy. Trial in scratch only.
- Instrumentation no-go: command-level `#count_heartbeats in` disables maxHeartbeats internally in this mathlib. Use tactic-level counter, which preserves limits, instead. No command-level counter was run.
- Import pruning of one full-Mathlib dependency cannot reduce this closure: 21 transitive files import all Mathlib. Do not report an unused-import edit as meaningful here.
- Verified scratch replacements preserve every declaration signature across all three modules (33 public theorems, 46 proof bodies including private lemmas). Five proof bodies improved; no theorem was weakened.
- Tactic-level measurements, raw heartbeats, same toolchain and limits:
  - Pair integral bound: 6,080,742 → 5,999,494 (1.34%).
  - Finite symmetric row bound: 2,716,233 → 1,949,278 (28.24%).
  - Compact actual source energy: 5,357,341 → 4,065,460 (24.11%).
  - Comparison-rate divergence: 37,793,986 → 1,694,898 (95.52%).
  - Weighted source energy: 8,287,724 → 7,402,603 (10.68%).
  - All 46 proof bodies: 125,582,673 → 86,464,486 (31.15%). Raw instrumentation heartbeats are 1,000 times the units used by maxHeartbeats.
- Failed trial: unrestricted `rw [mul_add, add_mul, ...]` unfolded local D at an unintended match. Explicit operands fixed it. Whole-route meaning: keep large analytic expressions outside routine normalization.
- Applied changes match passing scratch copies, modulo one trailing blank line. Proof bodies only; no new declarations, imports, limits, or assumptions.
- First full lint reported two unrelated unreachable FermiNymanBoundedWitness modules and stale generated indexes. Target leaves remain wired. Final gate status recorded below after audit.

## Review

- Correctness: unchanged signatures; all trial replacements checked by Lean without limit changes. All three named leaf builds pass; axiom result recorded below.
- Measurement limitation: warm/cold imports and concurrent work dominate wall time. Report proof-heartbeat reduction only, not total build speedup.
- Every proof body in scoped modules was measured; no sampling. Six unchanged counts drifted by fewer than 6,000 raw heartbeats; aggregate saved work exceeds 39M.
- Public API unchanged; shared finite-row proof is exercised through full quadratic-sum bound. No missing optimization prerequisite or known regression within applied changes.

## Final gates

- `lake build +GaloisForLFunctions.RHTower.ThetaCuspQuadraticMeanSquare`: pass.
- `lake build +GaloisForLFunctions.RHTower.ThetaCuspChargedSourceMeanSquare`: pass.
- `lake build +GaloisForLFunctions.RHTower.ThetaTailChargedEnergyCollapse`: pass.
- All three existing umbrella imports present exactly once. No new module or public declaration.
- Index regeneration completed. Final `lint --check-generated` has no stale-index error; it fails on exactly two unrelated unreachable modules: `FermiNymanBoundedWitnessMellin` and `FermiNymanBoundedWitnessRigidity`. These files were not edited in this task. Existing large-file warnings remain.
- Axiom audit: all 33 public theorems checked; only `propext`, `Classical.choice`, `Quot.sound`.
- Review verdict: PASS for scoped proof optimizations. Global lint remains blocked only by the two unrelated wiring errors above.
- Status: optimization complete; no owned Lean/search/build job remains. RH and the actual-source all-rank sign remain unresolved.
