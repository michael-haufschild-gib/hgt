# Exponential off-line tail moment and exponentially rare Hadamard/monotonicity failures

- **ID:** CRIT-SCALE-EXP-TAIL
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (route LA receivers; consumer of MUST-571)
- **Parent:** `1-in-progress/rh-goal-loop-opus-2026-09-29.md`, cycle 54
- **STATUS:** MUST-581

## Theorems [L]

With `L = log U`, for all large `U` one window `T₁ ∈ (U/4, U/4+1)`, `T₂ ∈ (U/2−1, U/2)` serves every
`c ≥ 4`:

- `RHTower.exists_offLineTailMoment_window_exponential_le`:
  `Σ_{Re ρ − ½ ≥ c/L} m_ρ (Re ρ − ½) ≤ (A/2π)(1 + 4800/c) e^{−c/4800} U + (2K/π) L²`;
- `RHTower.exists_volume_hadamardFail_criticalScale_exponential_le`: the heights
  `t ∈ [T₁+1, T₂−1]` with `ξ(σ+it) = 0` or `Re(ξ'/ξ)(σ+it) < 0` on `σ = ½ + c/L` have measure
  `≤ (A/π)(1 + 4800/c) e^{−c/4800} U + (4K/π) L²`;
- `RHTower.exists_volume_monotoneFail_criticalScale_exponential_le`: the same bound for the abscissae
  where `y ↦ |Ξ(x+iy)|` fails to be nondecreasing on `y ≥ c/L`.

Axioms: `propext, Classical.choice, Quot.sound`.

## Mechanism

Dyadic shells `2^j c/(2L) ≤ Re ρ − ½ < 2^{j+1}c/(2L)` (`sum_mult_weight_le_shells` with the weight
`max(u,0)`); on each shell the MUST-571 window count at `v = 2^j c/(2L)` gives
`2^{j+1}(c/2L)·count ≤ (2/π)((U/4)A e^{−2^j c/4800} + KL)`; `Σ_j e^{−2^j x} ≤ (1 + 1/x) e^{−x}`.
The failure sets lie in the shadows `|t − Im ρ| ≤ Re ρ − ½` of zeros with `Re ρ ≥ ½ + c/L`
(the corpus shadow argument, reused verbatim).

## Relation to the frontier

Upgrades the LA entry "Hadamard sign at `σ = ½ + c/log U` and monotonicity above `c/log U` hold on
proportion `≥ 1 − O(1/c)`" (`exists_volume_hadamardFail_criticalScale_le`,
`exists_volume_monotoneFail_criticalScale_le`) to `1 − O(e^{−c/4800})`, uniformly in `c`. At fixed `c`
the failure proportion is still not `o(1)`; that is again the average-distance problem.

## Lean module

`formal/GaloisForLFunctions/RHTower/ZetaCriticalScaleExponentialTailMoment.lean`; wired after
`XiCriticalScaleDiscSeamExponentialDensity`. Clean, `lake build --old` green, no collisions.

## Log
- 2026-09-30 — created and formalized (cycle 54).
