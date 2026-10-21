# BAG: Pechersky prime-sum lemma at the natural rate; Bagchi criterion on every half-scale disc (2026-10-21)

- New module `formal/GaloisForLFunctions/RHTower/ExponentialTypeNotSummableOnPrimeLogsNaturalRate.lean`:
  `exists_primeLogWeightedSum_gt_of_lt_one_sub` (Φ entire of exponential type ρ, Φ ≠ 0, 0 ≤ σ, ρ < 1 − σ, 2ρ < 5/12 ⟹ Σ_{p<N} p^{−σ}‖Φ(log p)‖ unbounded).
  Old lemma `exists_primeLogWeightedSum_gt` needed 3ρ < 1 − σ.
- Key tool: `eq_zero_of_two_ray_window_integral_decay` (window two-ray Paley–Wiener theorem) via the unit-window average `unitWindowAverage` and `hasDerivAt_unitWindowAverage`.
- Downstream chain hypotheses weakened in place: `(hρσ₂ : ρ < 1 - z₀.re) (hρ5 : 2 * ρ < 5 / 12)` in PecherskyDensityPrimeVectorsHardyDisc, PhasedEulerProductsApproximateExponentialsOfHardyFunctions, FiniteEulerProductUniversalityOnDiscs, UniformEulerTargetDensityOnZeroFreeDiscs, ZetaDiscRecurrenceOnZeroFreeDiscs.
- New module `RHTower/ZetaDiscRecurrenceOnHalfScaleDiscs.lean`: `IsHalfScaleStripDisc`, `zetaDiscStronglyRecurrentOn_of_zeroFree_halfScale`, `zetaDiscStronglyRecurrentOn_of_riemannHypothesis`, `riemannHypothesis_iff_forall_halfScale_zetaDiscStronglyRecurrentOn`, `riemannHypothesis_iff_forall_halfScale_headTargetUniformlyDense`.
- Open: radius cap 5/24 (Hoheisel 7/12; needs Remez/Cartan small-value theorem for exponential type), doubled-closure margin of the Euler tail law. RH-selective obstacle untouched.
- Card: `docs/drafts/pipeline/3-formalized/bag-pechersky-natural-rate-half-scale-bagchi-2026-10-21.md`.
- Lean lesson: long tactic proofs exhaust the per-declaration heartbeat budget cumulatively; split into lemmas, use `obtain ⟨c, hc⟩ : ∃ c, c = … := ⟨_, rfl⟩` for constants, clear integral hypotheses before `gcongr`/`field_simp`.
