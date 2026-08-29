# Hardy window pigeonhole: polynomial critical-line census (stage 3)

**Result (current).** Unconditional, premise-free Lean: `N₀(T) ≥ c·T^{2/7}/(1+log T)⁹` with
dyadic-difference form — history: log T → T^{1/16} (per-window cap) → T^{1/6} (CS counting)
→ T^{2/7} (resonance-graded window mean). Axioms: propext, Classical.choice, Quot.sound.

**Modules** (RHTower namespace, all umbrella-wired):
- `HardyZWindowMean.lean`: trivial window mean |∫_a^b Z| ≤ C·T^{3/4}.
- `HardyWindowCountTheorem.lean`: K-generic `exists_heavyFinset`, `window_fourth_le`,
  `exists_distinct_ordinates`, `one_add_log_pow_four_le_sixteenth` (all public),
  sixteenth-root capstones + census injection `xiPosCriticalZeroCount_add_card_le`.
- `HardySixthRootCensus.lean`: `exists_heavyFinset_sq` (CS pigeonhole, public),
  `log_sq_le_rpow` (L² ≤ 4624T^{1/32}, public), gap_of_key, sixth-root capstones.
- `HardyZWindowMeanSharp.lean` (~1300 lines): **sharp window mean**
  `exists_abs_integral_hardyZ_window_sharp_le`: |∫_a^b Z| ≤ C(T^{1/4}(1+logT)
  + (b−a)T^{-1/4} + √x + (b−a)T/x) for [a,b] ⊆ [T,2T], 1 ≤ x ≤ e^T. Graded first-derivative
  tests by log-distance to the moving resonance [√(a/2π),√(b/2π)]; harmonic telescope
  (−log(1−u) ≥ u, Σ1/k ≤ 1+log) replaces dyadic shells; rate law err ≤ 2/T from
  `gammaHardyPhaseRate_sub_log_conductor_bound`; graded twist lemma
  `norm_integral_twist_first_le_window_graded` (8‖c‖/lam via `firstDerivTestOn`).
- `HardyTwoSeventhCensus.lean`: x = T^{8/7}, K = ⌊T^{2/7}/(D·L⁵)⌋, gap_of_bound
  (512K³ME²(CF+1)L⁴ < T²), capstones `exists_many_distinct_line_zeros_dyadic_twoSeventh`,
  `exists_twoSeventhRoot_le_xiPosCriticalZeroCount[_sub]`.

**Open layers to beat 2/7** (both precisely localized): (1) oscillatory treatment of the
REFLECTED edge (dual sum) — the corpus only has the crude pointwise K(1+τ)/x bound, forcing
x ≥ T·polylog·H/target; balancing at x ≈ √T would push toward T^{1/2}. (2) windowed
second/fourth moment asymptotics (Hardy–Littlewood's route to N₀ ≫ T).

**Engineering (user directive: optimize, never raise heartbeats).** All five modules compile
with ZERO maxHeartbeats escalations. Recipe in [[lean-optimize-not-heartbeats]] auto-memory:
`linarith only`, explicit mul_le_mul/calc chains, per-block private lemmas, harmonic
reindex via `Finset.sum_Ico_eq_sum_range` + `Finset.sum_range_reflect`. Sharp module builds
in 40 s.

Card: docs/drafts/pipeline/3-formalized/hardy-window-polynomial-census.md
