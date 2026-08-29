# LI-CAB8 sublinear-tail repair no-go (2026-08-29)

Formalized `formal/GaloisForLFunctions/RHTower/LiEvenCrossCompletedAbelSublinearTailRepairNoGo.lean`, wired into `RHTower.lean`.

Result: every nonempty finite packet of genuine critical-line Xi copies has completed-Abel adjacent-current excursions of both signs with packet-dependent linear size `c(n+1)` cofinally in Li mode, for every `0<v≤1/4`. Hence any repair making packet current nonnegative in every mode must provide cofinal positive `Ω(n)` countercurrent; no correction `R` with `R(n)/(n+1)→0` can do so.

Killed proof chain: finite critical prefix + `o(n)` tail repair → LI-CAB5 all-mode nonnegativity → LI-CAB3 → RH.

Positive survivor: viable LI-CAB5 proof requires essential infinite tail cancellation at leading linear scale against every fixed nonempty critical prefix. Uniform or sublinear finite-prefix exhaustion is impossible.

Closed capstone: `not_exists_nonempty_finiteCriticalPacket_sublinearRepair_all_nonnegative`. Survivor theorem: `cofinal_linear_tail_forced_of_all_nonnegative`.

Verification: direct `lake env lean` PASS; targeted module build PASS (12,990 jobs, 70s); axiom audit only `propext`, `Classical.choice`, `Quot.sound`; global lint only unrelated pre-existing umbrella reachability errors. Stage-3 card: `docs/drafts/pipeline/3-formalized/li-even-cross-completed-abel-sublinear-tail-repair-no-go.md`. Frontier map remained untouched. Literature search found finite Li-sign tests and discretized Keiper/Li criteria but no exact completed-Abel sublinear-repair theorem; `[NOVELTY UNVERIFIED]`.