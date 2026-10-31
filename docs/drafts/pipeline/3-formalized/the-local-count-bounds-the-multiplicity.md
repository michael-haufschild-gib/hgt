# The local count bounds the multiplicity

- **ID:** local-count-multiplicity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), WP-A falsifier
- **Source:** `1-in-progress/reboot-programme-conjecture-loop-2026-10-30.md` #29
- **Statement:** (i) If a zero configuration satisfies the local count with constant `C`, every
  critical zero above height `3` has multiplicity `≤ C`. (ii) There is a zero configuration `Z'` with
  `RiemannVonMangoldt Z'`, the off-line counts `N − N₀` of `ζ` on every window, all zeros critical
  whenever those of `ζ` are, window counts within `4 log(|T₂| + 3)` of `ζ`'s, and no `C` with the
  local count. (iii) If every window `(S − 1, S + 1]` holds at most `M` off-line zeros and
  Riemann–von Mangoldt holds, then `N₀(T, 2T)/N(T, 2T) → 1`; the same if the bound fails only on a
  set of window centres of measure `o(T)`. (iv) For every configuration `Z` and
  `W`, `Z ⊕ clusters` (#26) has a window `(S − 1, S + 1]` with `Σ m (Re ρ − ½)² > W`. (v) If every
  window has depth mass `≤ W`, every zero has `(Re ρ − ½)² ≤ W`.

## Lean
Module `SquareRootThreshold/TheLocalCountBoundsTheMultiplicity.lean` (namespace
`RHTower.LocalCountFalsifier`): `mult_le_of_localCountBound`, `criticalPoint`,
`criticalClusterConfig`, `criticalClusterConfig_N_le`, `criticalClusterConfig_N0`,
`exists_zeroConfig_rvm_rh_not_localCountBound`, `offLinePart`, `N_eq_N0_add_offLinePart`,
`offLinePart_N_le`, `eventually_N_ge_of_rvm`, `tendsto_N0_div_N_of_offLineLocallyBounded`,
`AlmostOffLineLocallyBounded`, `two_mul_offLine_N_le_integral`,
`tendsto_N0_div_N_of_almostOffLineLocallyBounded`, `OffLineDepthLocallyBounded`,
`not_offLineDepthLocallyBounded_superpose`, `sq_re_sub_half_le_of_offLineDepthLocallyBounded`; `riemannVonMangoldt_superpose_of_N_le` in
`CountingInputsDoNotBoundTheLocalCount`.
Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Paper proof
(i) The disc `D(½ + δ + iγ, δ)` contains `½ + iγ` (distance `δ`) for every `δ ∈ (0, ½]`, so
`m(½ + iγ) ≤ C(δ log γ + 1)`. If `m > C`, take `δ = min(½, (m − C)/(2(|C| log γ + 1)))`: then
`C δ log γ ≤ |C| δ log γ < m − C`, a contradiction. (ii) `Z' = ζ ⊕ {½ + i exp(eᵏ)}` with multiplicity
`⌊eᵏ⌋`. The added points are critical and reflection-fixed; below `T₂` they carry
`Σ_{k ≤ log log T₂} ⌊eᵏ⌋ ≤ 2e^{n}/e ≤ 2 log T₂` zeros, so RvM survives
(`riemannVonMangoldt_superpose_of_N_le`) and `N − N₀` is unchanged. Their multiplicity `⌊eᵏ⌋` is
unbounded, so (i) rules out every `C`. (iii) `N = N₀ + N_off` with `N_off` the count of the off-line
part (a zero configuration: `Re ρ ≠ ½` is reflection-invariant); covering `(T, 2T]` by `⌈T/2⌉` windows
of length `2` gives `N_off(T, 2T) ≤ M(T/2 + 1)`, while RvM gives `N(T, 2T) ≥ (T/4π) log T` for large `T`
(`ell1 T ≥ (log T)/2 + 2`, `C log T ≤ T/8π`). So `1 − M(T/2 + 1)/((T/4π) log T) ≤ N₀/N ≤ 1`.
In density: each off-line zero of `(T, 2T]` lies in the window `(S − 1, S + 1]` for `S` in an interval
of length `2`, so `2N_off(T, 2T) ≤ ∫_{T−1}^{2T+1} N_off(S − 1, S + 1) dS ≤ M(T + 2) + 2A₀ log(2T + 4)·εT`
(windows hold `≤ 2A₀ log(2T + 4)` zeros by the unit count). Dividing by `N ≥ (T/4π) log T` leaves
`N_off/N ≤ o(1) + 16πA₀ε` for every `ε`.
(iv) The cluster at `exp(eᵏ)` alone carries depth mass `⌊eᵏ⌋/(k + 3)² ≥ (eᵏ − 1)/(k + 3)² → ∞`.
(v) The window about `Im ρ` contains `ρ`, whose term is `m (Re ρ − ½)² ≥ (Re ρ − ½)²`.

## What it changes (WP-A)
At the tangency point `½ + it` the local count of §6 A1 is a multiplicity statement: A1 implies
`m(ρ) ≤ C` for critical zeros, which is open even under RH (the RH bound is `m ≪ log γ/log log γ`).
So A1 is not a weaker substitute for RH: it does not follow from RH together with counting inputs.
The inputs that the heat and lag instruments use are the off-line lens (`Re ρ > ½`, where #26's
clusters live) and full-window counts at scale `r ∈ [δ, 1]`. A1 should be split accordingly. The
off-line part is the lag input (#26: not from counting). The full-window part at fixed scale is
consistent with RH and needs `S(t + r) − S(t − r) ≪ r log t + 1` (#8). The lag input itself, a bounded
off-line count per unit window, forces critical proportion `1`, beyond the known proportions, and
so does its version in density; under counting it fails (#26). The depth-weighted variant is the one
the Selberg moments control on average. So does the depth-weighted input `OffLineDepthLocallyBounded` of the CCM
ground-energy floor (`TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster`), which pointwise
is at least a zero-free strip `|Re ρ − ½| ≤ √W`.

Classification of the local inputs. A1: implies bounded critical multiplicity (open under RH), holds
for almost all heights (#28). Off-line count per window (lag): implies critical proportion one, also
in density (#33, #35); not known in density. Depth mass per window (CCM): implies a zero-free strip,
holds off density-`o(1)` heights (#36). None follows from counting (#26, #29, #34).

## Log
- 2026-10-31 — created; proved; formalized.
