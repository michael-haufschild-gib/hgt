# Route E growing reciprocal-marker capacity and low-breadth transport — Lean certificate

- **ID:** ROUTE-E-GROWING-RECIPROCAL-MARKER-002
- **Stage:** 3-formalized
- **Paper proof:** [route-e-growing-reciprocal-marker-low-breadth-transport.md](route-e-growing-reciprocal-marker-low-breadth-transport.md)
- **Capstone modules:** `GaloisForLFunctions.RHTower.Sieve.GrowingReciprocalMarkerCapacity`,
  `GaloisForLFunctions.RHTower.Sieve.LowBreadthMarkerTransport`
- **Umbrella:** `GaloisForLFunctions.RHTower`
- **Verification:** `lake env lean` / targeted `lake --old build` clean on every module below;
  `#print axioms` = `propext`, `Classical.choice`, `Quot.sound` for every capstone; formal lint gate
  clean for these modules. No computation.

## The card's statements

Namespace `RHTower.Sieve`.  `growingReciprocalMarkerH X = exp(log X/log log X)`,
`growingReciprocalMarkerW X = (log X)^{2/3}`, `growingReciprocalMarkerWindow X = √X·h(X)` (the
schedule `(6)`); `ReciprocalMarkerForm X σ n` says `n = a·p` with `p` prime, `√X < p`, `a < √X`,
`μ(a) = −σ`; `RHTower.woldBreadthDeviationRate c = 1 − c + c log c = I(c)`.

| Card item | Lean theorem |
|-|-|
| **(4)** + **(5)**: for `log h = o(log X)`, `√(log X)(log log X)² = o(w)`, `w = o(log h)`, an absolute `c > 0` with `#{n ∈ (X, X+H] : μ(n) = σ, n = a·p decoded} ≥ c H log h/log X` for both signs, all large `X`, `H = √X h` | `growing_reciprocal_marker_capacity` |
| **(5)** uniqueness of the decoding `n = a·p`, `p > √X > a` | `reciprocalMarker_decoding_unique` |
| the same count **uniformly** in every `h` with `(log log X)² ≤ log h ≤ (log X)/10` | `growingMarker_count_uniform` |
| **(7)** `H = X^{1/2+o(1)}` and `#T_σ(X,H) ≫ H/log log X` at the schedule `(6)` | `growing_reciprocal_marker_subpower_schedule` |
| **(32)** Shiu: `∑_{A<n≤A+y} z^{ω(n)} ≪ y (log A)^{z−1}` for `0 ≤ z ≤ 1`, uniformly in `y ≥ √A` | `shiu_omegaTilt_short_interval` |
| **(33)**–**(34)** Chernoff: `#{n ∈ (A, A+y] : μ(n) ≠ 0, ω(n) ≤ c₀ log log A} ≪ y (log A)^{−I(c₀)}`, `y ≥ √A` | `card_omega_le_le_tilt`, `card_lowBreadth_le` |
| `I(c₀) > 0` (`(31)`) | `RHTower.woldBreadthDeviationRate_pos_of_lt_one` (pre-existing) |
| **(8)**: every large `H`-cell `(X, X+H]` has disjoint opposite-sign edges of displacement `≤ H` covering `ℒ_{c₀}(X,H)`, other endpoint outside `ℒ_{c₀}(X,H)` | `lowBreadth_matching_cell` |
| the same in every cell of a dyadic shell | `lowBreadth_cell_matching`, `cell_target_count`, `eventually_card_lowBreadthCell_le` |
| **(35)**–**(36)**: across the shell `(X, 2X]` (full cells + terminal piece), for every `0 ≤ x ≤ C/X` the first-order Gibbs cost of all edges plus the terminal mass is `≤ (2C+1)H = X^{1/2+o(1)}` | `lowBreadth_transport_shell` (edge estimate `RHTower.abs_gibbsEdge_le`, pre-existing) |
| `(9)`: the composite capacity problem is confined to `ω(n) ≥ c₀ log log n` | interpretive consequence of `lowBreadth_transport_shell` (every lower-breadth vertex of every full cell is transported) |
| `(10)`–`(14)`, `(19)`–`(30)`: block count, schedule, fibres `(25)`–`(26)`, squarefree count, decoding, distinctness, aggregation | previously formalized (`MobiusReciprocalMarkerPrimeCapacity`, `Sieve/PrimeWindow`, `Sieve/ReciprocalFibre`, `Sieve/SquarefreeCount`, `Sieve/AveragedSquarefreeTail`, `GrowingReciprocalMarkerBlockCount`, `GrowingReciprocalMarkerSubpowerSchedule`, `GrowingReciprocalMarkerCapacityAggregation`); the Lean proof of `(4)` re-derives what it needs through `Sieve/MarkerLadder` |

## The analytic input `(15)`–`(18)`, replaced by what the proof uses

The card quotes Menon's 2026 mean-square rate `(15)`–`(16)` so that the Markov step `(18)` leaves
only `o(A_k/log X)` bad starts: every marker over a bad start is charged at the *maximal* fibre
multiplicity `≍ 4^k`.  The Lean proof charges the *mean-square* multiplicity instead, and then a
bounded density of bad starts suffices, so Menon's rate is not needed (`(15)`–`(17)` are not used;
Menon's theorem itself is not formalized).

| step | Lean |
|-|-|
| uniform exceptional set: `∀ ε`, eventually, for **every** window `L ∈ [(log y)⁴, √y/log y]`, `#badOuter y L ≤ 1024ε√y/ϱ² + √y/(log y)²` — a diagonal argument over window profiles from Matomäki–Radziwiłł at every length (`averagedMeanSquare_moebius_of_tendsto`) | `Sieve/BadOuterUniformWindow` (`eventually_forall_of_forall_profile`, `eventually_card_badOuter_le_uniform`) |
| markers over bad starts lose `√(#S·(#M + 2Π))/M₀` of harmonic mass, `Π` = shifted prime pairs within the fibre diameter (sharp two-dimensional sieve) | pre-existing `Sieve/MarkerLossDevice`, `Sieve/MarkerHarmonicSupply`, `GenericMarkerAnalytic.generic_pair_le'` |
| the device applied **per super-block** of `K₀+1` dyadic blocks (`multiHarmConst K₀ ≥ 1`), with block windows `H·m_k/(4Z)`: each super-block keeps half its mass | `Sieve/MarkerLadder` (`good_mass_ge_of_budget`, `ladder_card_sign_window_ge`, decoded targets `card_sign_window_decoded_ge`) |
| one physical scale: `≥ (3ϱ/256)(H·I·multiHarmConst/(2 log Z) − Z/u)` | `Sieve/GrowingMarkerCountExplicit` (`growingMarker_count_explicit`) |
| parameters `u = ⌈4Z(log Z)⁴/H⌉+2`, top start `C₂m² log Z ≤ Z`, `I ≍ log h` super-blocks | `Sieve/GrowingReciprocalMarkerCapacity` (`gmStart`, `gmTop`, `gmBlocks`, `growingMarker_count_at`) |

## Shiu's bound `(32)`, proved

`Sieve/ShiuAdaptiveCut` + `Sieve/ShiuOmegaTiltShortInterval`: `n = b·a` cut at Shiu's level
(`shiuLevel`, the least smoothness bound at which the smooth part exceeds `z ≈ A^{1/8}`); three cases
(`shiu_caseI_le`, `shiu_caseII_le`, `shiu_caseIII_le`) with fibre counts by the Selberg sieve
(`card_rough_Ioc_le_selberg`); Rankin's bound for tilted smooth sums
(`sum_smooth_rankinTilt_le`: `∑ t^{ω(b)} b^{σ−1} ≤ exp(t(log log W + C))` at `σ = 1/log W`) and its
tail (`sum_omegaTilt_div_tail_le`); the grouped estimate over the largest prime
(`sum_omegaTilt_div_log_largestPrime_le`); explicit and asymptotic forms
(`shiu_omegaTilt_explicit`, `shiu_omegaTilt_short_interval`).
