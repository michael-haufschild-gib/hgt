# A zero-free strip gives linear heat repair

- **ID:** strip-linear-heat-repair
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (receiver: strip ⇒ rate), WP-B
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #39
- **Statement:** There are absolute `c₀, C > 0` such that if every zero with `Im ρ ≥ T₀` has
  `|Re ρ − ½| ≤ d ≤ c₀`, then `λ_t log t ≤ C d` for all large `t`. With detection
  (`λ_γ log γ ≥ depth²/200`, #1/#6) the heat pincer closes at rate `κ` iff (up to `κ ↔ κ²`) there is a
  zero-free strip.

## Plan
1. **Window transform under a shift.** For `F = paperFT (cb ℓ k)` (Littlewood windows) and `|y| ≤ d`:
   `|F(x + iy)| ≤ e^{ℓ|y|} K/(1 + |x|)²` (`norm_paperFT_le_decay`, corpus) and
   `|F(x + iy) − F(x)| ≤ |y| e^{ℓ|y|} K'/(1 + |x|)²` (complex derivative `F' = paperFT(i u cb)`,
   mean value along the vertical segment).
2. **Summand perturbation.** For a zero `ρ = ½ + η + iγ`, `x = γ − T`:
   `|Wsummand(window ℓ T k)(ρ) − m ψ_k(x)| ≤ m |η| e^{2ℓ|η|} K''/(1 + |x|)²`.
3. **Error sum.** `Σ_ρ m/(1 + |γ − T|)² ≪ log T` (corpus weighted density), so under the strip the
   explicit-formula identities (`paperInputs_zeta.EF`) give `Σ m ψ₀ ≥ S₀ − d K₃ log T` and
   `Σ m ψ₁ ≤ S₁ + d K₃ log T`.
4. **Window count under the strip.** Rerun `exists_window_count_bound` (Littlewood module) with these:
   `ℓ A² N(T − D/ℓ, T + D/ℓ) ≥ (E/2 − d K₄(ℓ)) log T − M(ℓ)`.
5. **Heat.** With `ℓ = D'/d`: windows of length `≍ d` hold `≫ d log t` zeros; the radius-`R` head with
   `R ≍ d` then has `≫ d log t` copies, and `localHeatThreshold_le_of_depth_count` gives
   `λ_t ≤ 64R²/N ≪ d/log t` at `Ξ(t) ≠ 0`; lower semicontinuity covers the ordinates.

## Status
- Step 1: corpus has the decay bound and real-argument derivatives (`hasDerivAt_paperFT_ofReal`,
  `HTGeometry.hasDerivAt_compactFourier` for complex arguments).
- Steps 2–5: open.

## Log
- 2026-10-31 — created.
