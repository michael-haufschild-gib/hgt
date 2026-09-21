# PW-B literal two-emission scalar CTP seam

- **ID:** pw-b-literal-two-emission-scalar-ctp-seam
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md` · PW-B
- **Statement:** Normalized two-emission Schwarzschild recoil coherence cannot itself be the exchange-ordered CTP seam for the Parikh--Wilczek Borel recoil phase.

## Goal

Test the most literal scalar multi-event repair remaining after the single-endpoint scale split: use the exact normalized Schwarzschild two-emission entropy coherence as the complete source contact dressing the oriented PW recoil phase.

## Gates

- [x] 0 → 1 in-progress: exact normalized two-emission entropy factor coupled to the literal PW Borel recoil holonomy.
- [x] 1 → 2 fully-proven: mass, event-exchange, and off-wall zero-locus classification dependency-closed.
- [ ] 2 → 3 formalized audit: `RHTower.not_schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_ctp_skew_of_offCritical` directly kernel-checked; leaf OLean audit remains pending because its target replayed thousands of unrelated dependencies and was stopped under the no-long-build rule.
- [ ] 3 → 4 publication-ready: not applicable to retired subroute.

## Approach

The literal factor is `C(M;E,F)=exp(-4π(E-F)²)`. It is positive, independent of `M`, and invariant under `E ↔ F`. Multiply it by the actual oriented PW Borel recoil holonomy phase. Positivity preserves the exact critical-wall zero locus; exchange invariance makes a nonzero off-wall dressed phase incompatible with CTP skewness.

## No-go closure

- **Exact killing theorem/mechanism:** `not_schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_ctp_skew_of_offCritical` proves the scalar two-emission dressing cannot be its own CTP reverse at any nonreal off-critical strip mode. The proof combines exact event-swap invariance with `schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_ne_zero_of_offCritical`.
- **Strongest positive survivor:** `schwarzschildParikhWilczekTwoEmissionDressedRecoilPhase_eq_zero_iff` preserves the exact critical-wall zero locus, while `..._mass_invariant` shows the normalized factor has canceled the mass coordinate. A viable two-event source must therefore add a separately exchange-odd, channel-relative contact; scalar entropy coherence may dress it but cannot generate it.
- **New insight:** The literal Parikh--Wilczek two-emission entropy identity has no CTP orientation and no remaining mass calibration after normalization. This kills the concrete scalar multi-event repair, rather than merely restating that a generic scalar history is insufficient.
- **Status:** Paper proof is the exact entropy identity `C=exp(-4π(E-F)²)`, positivity of `exp`, exchange symmetry, and the existing PW holonomy wall classification. Lean module `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekTwoEmissionCoherenceNoGo.lean`; direct `lake env lean` and `#print axioms` passed, with only `propext`, `Classical.choice`, `Quot.sound`. The required leaf `lake build` audit was stopped before the target after it replayed thousands of unrelated dependencies.

## Log

- 2026-09-21 — literal normalized scalar two-emission PW-B CTP seam retired; exchange-odd channel contact remains required.
