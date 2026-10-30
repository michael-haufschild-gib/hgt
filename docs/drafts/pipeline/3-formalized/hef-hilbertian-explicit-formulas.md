# Hilbertian explicit formulas: foundations

- **ID:** hef-foundations
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-3010/opus.md §7
- **Statement:** The explicit image of the same-point problem is the Weil form; holomorphic clocks carry
  no quantum; same-point carriers are quantized; resolvent Hilbertian formula; 𝔽_q calibration; effectivity.

## Goal
Programme `formal/GaloisForLFunctions/HilbertianExplicitFormulas/`. Pillars listed in its README §5.

## Gates
- [x] 0 → 1  well-posed; statements below
- [x] 1 → 2  paper proofs complete (below)
- [x] 2 → 3  Lean modules audited with `lake --old env lean`; `#print axioms`: propext, Classical.choice, Quot.sound

## Lean
- P1 `TheExplicitImageIsTheWeilForm`: `eq_weilWeight_of_calibrated`, `samePoint_sub_explicit_pair`,
  `blind_of_explicit_eq_samePoint`, `const_of_explicit_eq_samePoint_everywhere`,
  `samePointForm_sub_explicitStatistic`, `norm_sq_sub_explicit_eq_half_reflectionDefect`.
- P2 `HolomorphicClocksCarryNoQuantum`: `not_cesaroBounded_of_one_lt_norm`,
  `cesaroBounded_holomorphicClock_iff`, `cesaroBounded_holomorphicClock_real_iff`,
  `tendsto_cesaro_ordinateClock`, `tendsto_cesaro_ordinateClock_sub_diag_of_nonResonant`.
- P3 `TheSamePointQuantumOfAReflectionConfiguration`: `isCritical_tfae`, `even_collisionCharge`,
  `offLineMass_le_collisionCharge`, `one_sub_mul_total_le_lineMass`.
- P4 `TheResolventHilbertianExplicitFormula`: `pair_depth_resolvent`, `sub_mul_samePointResolvent_eq`,
  `resolventDefect_eq_zero_iff`, `sub_width_mul_samePointResolvent_le`, `integral_resolventDefect_vertical`.
- P5 `TheFiniteFieldCalibration`: `unitary_tfae`, `even_curveCollisionCharge`,
  `cesaroBounded_lefschetz_iff_curveCollisionCharge_lt_two`, `goldenDatum_curveCollisionCharge`,
  `eq_rosatiWeight_of_circleCalibrated`, `explicit_eq_rosatiPairing`.
- P6 `SamePointPositivityIsEffectivity`: `signedSamePointForm_nonneg_iff`, `exists_signedSamePointForm_neg`.

## Open
- Resolvent formula on the full Xi divisor; `D(s)` as a prime-side quantity.
- Census: `O(T) ≤ c N(T)` with `c < 1/4`.

## Paper proofs

**P1 Calibration rigidity.** `F h` entire, `h x = |F x|²` on ℝ. `G = h − F·F#`, `F#(z) = conj F(conj z)`
entire; `G(x) = 0` on ℝ; identity theorem ⇒ `G ≡ 0`. Pair identity
`|a|² + |b|² − a b̄ − b ā = |a − b|²` with `a = F z`, `b = F z̄`. Universal case: real `z` gives
calibration, so `F z = F z̄` ∀ z; then `u ↦ F(x+u) − F(x−u)` vanishes on iℝ, hence ≡ 0; derivative
at 0 gives `F'(x) = 0` on ℝ, so `F' ≡ 0`.

**P2 Clock classification.** `|e^{λ(ρ−½)}| = e^{Reλ·δ − Imλ·γ}`; the quartet realizes all sign
patterns, so the max exponent `R ≥ 0`, with `R = 0` iff every exponent vanishes. If `R > 0`, the
top fibre has positive aggregated multiplicity, so `P(n)/e^{nR}` does not tend to 0
(`not_tendsto_normalized_finitePencil_of_dominantFiber`); a bounded Cesàro mean square gives
`|P(n)|² ≤ C(n+1)`, hence `P(n)/e^{nR} → 0`. Contradiction.

**P3 Quantum law.** Off-line `ρ` has `ρ* ≠ ρ` with the same ordinate, so `H_ρ − m_ρ ≥ m_{ρ*} ≥ 1`;
summing `m_ρ ≤ m_ρ(H_ρ − m_ρ)` over off-line zeros gives `N − N₀ ≤ O`. Evenness: the ordered pair
set is swap-invariant without fixed points.

**P4 Resolvent formula.** `|s−ρ*|² − |s−ρ|² = (2σ−1)(2β−1)`; so
`(β−½)/|s−ρ|² + (½−β)/|s−ρ*|² = 2(2σ−1)(β−½)²/(|s−ρ|²|s−ρ*|²)`. Symmetrize over `ρ ↦ ρ*`.
Vertical integral: `∫ du/((a²+u²)(b²+u²)) = π/(ab(a+b))`, `a+b = 2σ−1`, giving `π d²/(u²−d²)`.

**P5 𝔽_q.** Line reflection `β ↦ 1/β̄` keeps the argument; non-unitary `β` collides with it. Lefschetz
pencil = holomorphic clock with `c = 1 > 0` on every fibre.

**P6 Effectivity.** Lagrange polynomial vanishing at all points but one.

## Log
- 2026-10-30 — created; README first draft written.
- 2026-10-30 — P1–P6 formalized; moved to 3-formalized.
