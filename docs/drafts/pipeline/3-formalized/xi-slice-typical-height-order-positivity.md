# Slice positivity at orders `≥ η log t` for almost every height

- **ID:** XI-SLICE-TYPICAL-ORDER
- **Stage:** 3-formalized
- **Type:** PARTIAL PRODUCER (slice receiver, route 3 / LA)
- **Parent:** `rh-goal-loop-opus-2026-09-29.md`, cycles 44 and 46

## Target

Let `c_n(t)` be the Taylor coefficients of `g_t(x) = ξ(½+x+it)ξ(½−x+it)` at `x = 0`. The corpus proves,
for every `t`, that `c_{2k}(t) > 0` for `k ≥ max(K, (¼+ε) log t)`
(`exists_xiSliceCoeff_pos_above_quarter_log`), so RH ⟺ `c_{2k}(t) ≥ 0` below that window.

**Theorem (target).** For every `η > 0` and `ε > 0`, for all large `T`, the heights `t ∈ [T, 2T]`
at which `c_{2k}(t) ≤ 0` for some `k ≥ η log t` have measure `≤ εT`.

So at almost every height the RH content of the slice criterion sits in orders `k = o(log t)`.
The order–displacement dictionary (cycle 44) reads this as: order `k` sees zeros at displacement
`≈ 4k/log t`, and zeros at fixed displacement are `o(T)` (MUST-559).

## Mechanism

The corpus's saddle method (`xiSliceCoeff_pos_of_saddle_euler`) takes the saddle radius
`R ≈ 2k/log t ≥ ½ + 2η`, so both points `½ + w ± it` of the saddle disc lie in the Euler half-plane,
where `ζ'/ζ = O(1/η)` pointwise; the far arc uses the pointwise convexity bound, which needs
`R > ½`. For `R ∈ [η, ½ + 2η]` the discs are inside the strip. The pointwise inputs are replaced
by bounds that hold for all `t` outside a set of measure `o(T)`:

1. **Zero-free saddle discs.** No zero of `ζ` with `Re ≥ ½ + η/2` within distance `2` of height
   `t` (MUST-559/562, zero-shadow density).
2. **Typical sup.** `|ζ| ≤ t^{ε}` on `{½ ≤ Re ≤ 2, |Im − t| ≤ 2}`. Subharmonic mean over discs of
   radius `r < ε`, mean square `∫_T^{2T} |ζ(σ+it)|² ≪ T^{1+2r} log² T` for `σ ≥ ½ − r`
   (critical-line fourth moment `HardyZ…Polylog` + Cauchy–Schwarz, L² three lines
   `HTGeometry.integral_normSq_le_of_three_lines`, functional equation left of the line), Markov.
3. **Typical lower bound and log-derivative.** On the zero-free region of 1, Borel–Carathéodory
   for `log ζ` against the typical sup of 2 and the Euler value at `Re = 3` gives
   `|log ζ| ≤ Cε log t`, hence `|ζ'/ζ| ≤ C'ε log t` on the saddle discs.
4. **Deterministic strip saddle.** Copy of `xiSliceCoeff_pos_of_saddle_euler` with
   `xiEulerConstant η` replaced by `C₀ + B` (`B` the `ζ'/ζ` bound) and zero-freeness as a
   hypothesis; the Gamma part of `ξ'/ξ` is Stirling in the whole strip
   (`norm_digamma_sub_log_le_of_re_pos`).
5. **Tail.** On `θ ∈ [θ_K, π/2]`, `|g_t(Re^{iθ})|/g_t(R) ≤ t^{−R(1−cos θ)} · t^{4ε}` from the
   Gamma ratio along the arc and 2–3.

## Lean plan

- A `ZetaTypicalHeightBounds`: 2 and 3.
- B `XiSliceSaddleStrip`: 4 (base lemmas of `XiSliceCoeffQuarterArc` with `ξ(½+R+it) ≠ 0` as a
  hypothesis in place of `R > ½`).
- C `XiSliceTypicalOrderPositivity`: 5 and assembly with dyadic windows.

## Log

- 2026-09-30 — card opened; plan above. Checked: no density-one slice result below the quarter-log
  window exists; corpus tools for 2 exist (fourth moment on the line, L² three lines).
- 2026-09-30 — **A1 done [L]**: `RHTower/ZetaVerticalMeanSquare.lean`, `exists_integral_normSq_zeta_vertical_le`:
  `∫_T^{2T} |ζ(σ+it)|² ≤ C T (1+log T)³` uniformly for `σ ∈ [½, 3]` (Gaussian-windowed pole-cleared
  `ζ`, L² three lines between the critical line — fourth moment + Cauchy–Schwarz — and `Re = 3`).
  Clean, standard axioms, wired, no collisions. The other lane's `MoebiusMollifiedErrorThreeLines`
  (unwired, 10 compile errors under the current toolchain) was not touched.
- Plan for A2 (typical sup): area mean value `HTGeometry.normSq_value_mul_area_le_integral_ball`
  for `zetaEntire`, reflection of the part of the ball left of `Re = ½` by the functional equation
  (`|ζ(½−δ+iu)| ≤ 2(u/2π)^δ |ζ(½+δ+iu)|`, exact χ modulus), A1 on `σ ≥ ½`, Markov.
- 2026-09-30 — **A2 done [L]**: `RHTower/ZetaTypicalHeightSup.lean`, `eventually_volume_zetaLargeNear_le`:
  for `0 < ε ≤ 1`, `δ > 0`, eventually the `t ∈ [T,2T]` with some `z`, `½ ≤ Re z ≤ 2`,
  `|Im z − t| ≤ 2`, `|ζ(z)| > T^ε` have measure `≤ δT`. Area mean value of `(z−1)ζ(z)` on radius
  `ε/4` discs, box = iterated integral, reflection `|ζ(½−d+iy)| ≤ K y^d |ζ(½+d+iy)|`, unit cells
  with 7-fold overlap, Markov. Quantitative form `volume_zetaLargeNear_le`.
- 2026-09-30 — **A3 done [L]**: `RHTower/ZetaTypicalHeightLogDeriv.lean`. `zetaTypicalHeight η ε T t`
  (no zero `Re ≥ ½+η/4`, `|Im−t| ≤ 2`; not large). Almost every height is typical
  (`eventually_volume_not_zetaTypicalHeight_le`); at typical heights
  `|ζ'/ζ(s)| ≤ 24(ε log T + 9)/η²` on `|s−(2+it)| ≤ 3/2−η` and `|ζ(s)| ≥ e^{−12(ε log T+9)/η}/3` on
  `|s−(2+it)| ≤ 3/2−η/2` (corpus `HTGeometry.norm_logDeriv_le`, `norm_lower_bound_of_ball`).
- 2026-09-30 — **B done [L]**: `RHTower/XiSliceSaddleStrip.lean`. The Euler-region saddle with the
  Euler inputs replaced by hypotheses: slice product zero-free on open `U ⊇ {|w−R| ≤ r}` and
  `XiSliceStirling t C` (both points `½+w±it` within `C` of `½ log(s/2)`); quarter-arc formula at a
  nonvanishing radius, disc/real/slope bounds, IVT saddle radius, `xiSliceCoeff_pos_of_saddle_strip`
  for `R ≥ 2r`. Stirling from `|ζ'/ζ| ≤ B` with `C = 3 + B` (`norm_logDeriv_xi_sub_half_log_le_of_zeta`).
- 2026-09-30 — **C done [L], target proved**: `RHTower/XiSliceTypicalOrderPositivity.lean`.
  `exists_xiSliceCoeff_pos_of_typical` (typical for `(η, η⁴/10⁸)`, `2η log t ≤ k ≤ ½ log t`,
  `U = ball(3/2, 3/2−η/4)`, `R ∈ [2η, 5/4]`, tail by the corpus circle-decay law with the typical
  upper and lower `ζ` bounds) and `eventually_volume_xiSliceCoeff_nonpos_le` (target theorem; orders
  `≥ ½ log t` from `exists_xiSliceCoeff_pos_above_quarter_log`). Clean, standard axioms, wired after
  `ZetaTypicalHeightLogDeriv`, no collisions; lint errors are other lanes' unreachable modules only.
  STATUS MUST-567.
- **Boundary.** The method stops at orders `k ≍ log t`: at displacement `O(1/log t)` nearby zeros
  give `|ζ'/ζ| ≍ log t`, the size of the main term. Bounded orders need a different mechanism.
