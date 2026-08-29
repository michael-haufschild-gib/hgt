# Suzuki Ward positive-channel rank escape

- **ID:** SC-WARD-RANK-ESCAPE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus searches for `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`, `SuzukiWardAtomicContinuousImbalanceBounded`, `SuzukiWardFixedTwoLightPhaseLeakage`, and `tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop`
- **Statement:** Any nonnegative channel resolution of the literal Suzuki wall mass whose individual channel masses have one uniform finite ceiling has channel rank tending to infinity; in particular no fixed finite-rank positive/light-cone completion has finite coordinatewise cofinal limits.

## Goal
Kill every fixed finite-rank positive-channel realization of the remaining Suzuki FE-reflected wall Ward assembly. Full RH chain being narrowed is:

`source-defined Robin--Gamma--holonomy assembly with controlled relative Ward displacement`
→ `SuzukiWardAtomicContinuousImbalanceBounded`
→ `riemannHypothesis_iff_suzukiWardAtomicContinuousImbalanceBounded`
→ `RiemannHypothesis`.

Corpus proves literal outgoing wall mass tends to `+∞` unconditionally and fixed two-light phase leakage also tends to `+∞`. This theorem tests the whole fixed-finite-rank positive class at once. It does not prove RH; it proves the remaining producer must use growing rank or signed relative renormalization before cofinal completion.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module `SuzukiWardPositiveChannelRankEscape`, direct check and leaf build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Represent aperture-`N` positive completion by `rank N` nonnegative real channel masses summing exactly to `unitRieszCoherentPrimeOutgoingCharge (N+2)`. If every channel is at most fixed `B`, finite-sum monotonicity gives outgoing mass at most `rank N * B`. Corpus theorem `tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop` then forces `rank N → +∞`. For constant rank, coordinatewise finite convergence makes the finite coordinate sum converge, contradicting outgoing escape.

## No-go closure
- **Exact killing theorem/mechanism:** `SuzukiWardPositiveChannelResolution.rank_tendsto_atTop_of_uniform_le`, `not_exists_uniformly_bounded_fixedRank_SuzukiWardPositiveChannelResolution`, and `not_exists_fixedRank_positiveChannelResolution_with_coordinate_limits` in `SuzukiWardPositiveChannelRankEscape.lean`.
- **Strongest positive survivor:** Growing-rank positive assembly survives. More importantly, signed relative renormalization survives because the theorem uses nonnegative channel masses and absolute per-channel ceilings; it does not touch cancellation between co-divergent atomic and continuous sectors.
- **New insight:** Fixed two-light leakage was not an accident of that polarization. Unconditional PNT-scale wall-mass escape forces every uniformly bounded positive resolution to acquire unbounded rank. Remaining RH-bearing architecture is therefore not any fixed finite positive/light-cone model; it is growing-rank coherence or signed relative Ward displacement.
- **Status:** `[PROVED HERE]`; direct Lean check and leaf build pass. Axiom dependencies are only `propext`, `Classical.choice`, `Quot.sound`. Web searches through 29 August 2026 found Suzuki canonical-system and screw-function criteria but no matching wall-mass/channel-rank theorem; label `[NOVELTY UNVERIFIED]` pending expert review.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/SuzukiWardPositiveChannelRankEscape.lean` — pass.
- `lake build GaloisForLFunctions.RHTower.SuzukiWardPositiveChannelRankEscape` — pass (`[11881/11881]`).
- `#print axioms` for all four public theorems — only standard quotient/classical axioms.
- Wired into `GaloisForLFunctions/RHTower.lean`; umbrella build intentionally not run.

## Log
- 2026-08-29 — created in 1-in-progress after corpus search and explicit RH-chain audit.
- 2026-08-29 — paper proof closed; Lean formalization, leaf build, and axiom audit passed; promoted to 3-formalized.
