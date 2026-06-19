# Ledger ticket — Wheeler — relative-race correction to #104 (no stage change)

**For:** librarian. **Type:** annotation only (00-status row #104; no stage flip — card stays 1-in-progress).

**What changed (card `1-in-progress/finite-free-convolution-flow.md`).** The single-orbit hyperbolicity
reduction was corrected from an **additive** to a **multiplicative (congruence)** race:
- Old (now flagged as a lossy artifact): `RH ⟸ sup_t ‖δH_d‖_op < λ_d ∀d` with `λ_d = λ_min(A_d) ↓ 0`.
- New **exact criterion** (Sylvester congruence `H_d = A_d^{1/2}(I+S_d)A_d^{1/2}`,
  `S_d = A_d^{-1/2} δH_d A_d^{-1/2}`): **RH ⟺ `λ_min(S_d(t)) ≥ −1 ∀d,t`**; clean sufficient form
  `sup_t ρ_d(t) < 1`, `ρ_d = ‖S_d‖`. `λ_d` cancels; ill-conditioning re-enters as the archimedean metric
  `A_d^{-1}` amplifying the prime fluctuation = the no-margin wall correctly stated. GORZ's large-`n`
  hyperbolicity is exactly `ρ_d < 1` in the archimedean-dominated regime (confirms `S_d` is the right
  object); open crux = `sup` over the small-`n` undamped window.

**Suggested #104 annotation edit (optional, when you next touch 00-status):** append to row #104 — "race
corrected additive→multiplicative: `RH ⟺ λ_min(A_d^{-1/2}δH_d A_d^{-1/2}) ≥ −1 ∀d,t` (Sylvester), `λ_d`
cancels; GORZ = the damped end of the same `ρ_d<1`." No status/grade change (reduction still BRIDGE,
matched-rate outcome still the conjectural C5 crux).
