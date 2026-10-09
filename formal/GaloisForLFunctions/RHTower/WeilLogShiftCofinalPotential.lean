import GaloisForLFunctions.RHTower.WeilLogShiftFiniteExcessCriterion

/-!
# Cofinal samples characterize the whole potential domain

For arbitrary signed weights, convergence at shifts unbounded above is
equivalent to convergence at every real shift. With finite excess, this domain
is exactly detected by eventual lower bounds on any cofinal integer-log probes.
The prescribed exponential probes provide a convergence guard for the
potential-inequality receiver.
-/

open Filter Topology Zeta23

noncomputable section

namespace RHTower

open WeilExcess

/-- The cutoff-uniform inward-shift gain passes to the full kernel. -/
theorem exists_riemannAutocorr_tail_shift_gain {c : ℝ} (hc : 4 ≤ c) (A : ℝ) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → A * riemannAutocorr y ≤ riemannAutocorr (y - c) := by
  obtain ⟨Y, hY⟩ := exists_truncatedRiemannAutocorr_tail_shift_gain hc A
  refine ⟨Y, fun y hy => ?_⟩
  exact le_of_tendsto_of_tendsto ((tendsto_truncatedRiemannAutocorr y).const_mul A)
    (tendsto_truncatedRiemannAutocorr (y - c)) (Eventually.of_forall (hY y hy))

private theorem exists_paired_kernel_tail_domination {y c : ℝ} (hc : |y| + 4 ≤ c) :
    ∃ Y : ℝ, ∀ x : ℝ, Y ≤ x →
      riemannAutocorr (y + x) + riemannAutocorr (y - x) ≤
        2 * (riemannAutocorr (c + x) + riemannAutocorr (c - x)) := by
  obtain ⟨Y₁, h₁⟩ := exists_riemannAutocorr_tail_shift_gain
    (c := c + y) (by linarith only [hc, neg_le_abs y]) 1
  obtain ⟨Y₂, h₂⟩ := exists_riemannAutocorr_tail_shift_gain
    (c := c - y) (by linarith only [hc, le_abs_self y]) 1
  refine ⟨max (Y₁ - y) (Y₂ + y), fun x hx => ?_⟩
  have hx₁ : Y₁ ≤ x + y := by
    have h := (le_max_left (Y₁ - y) (Y₂ + y)).trans hx
    linarith only [h]
  have hx₂ : Y₂ ≤ x - y := by
    have h := (le_max_right (Y₁ - y) (Y₂ + y)).trans hx
    linarith only [h]
  have hplus := h₁ (x + y) hx₁
  have hminus := h₂ (x - y) hx₂
  rw [one_mul, show x + y - (c + y) = x - c by ring] at hplus
  rw [one_mul, show x - y - (c - y) = x - c by ring] at hminus
  rw [add_comm y x, show y - x = -(x - y) by ring, riemannAutocorr_neg,
    show c - x = -(x - c) by ring, riemannAutocorr_neg]
  linarith only [hplus, hminus, riemannAutocorr_nonneg (c + x)]

/-- Convergence at a sufficiently outer sample controls every inner potential,
for arbitrary signed weights. Only the tail requires comparison. -/
theorem summable_kernelPotential_of_outer_sample {v : ℕ → ℝ} {c y : ℝ}
    (hc : |y| + 4 ≤ c)
    (hs : Summable fun n => v n *
      (riemannAutocorr (c + Real.log n) + riemannAutocorr (c - Real.log n))) :
    Summable fun n => v n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n)) := by
  obtain ⟨Y, hY⟩ := exists_paired_kernel_tail_domination hc
  refine (hs.norm.mul_left 2).of_norm_bounded_eventually_nat ?_
  refine eventually_atTop.mpr ⟨⌊Real.exp Y⌋₊ + 1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnR : (⌊Real.exp Y⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hlog : Y ≤ Real.log n := ((Real.lt_log_iff_exp_lt hnpos).mpr
    ((Nat.lt_floor_add_one _).trans_le hnR)).le
  have h := mul_le_mul_of_nonneg_left (hY (Real.log n) hlog) (abs_nonneg (v n))
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg (y + Real.log n))
      (riemannAutocorr_nonneg (y - Real.log n))),
    abs_of_nonneg (add_nonneg (riemannAutocorr_nonneg (c + Real.log n))
      (riemannAutocorr_nonneg (c - Real.log n)))]
  nlinarith only [h]

/-- Whole-line potential convergence is exactly convergence on any sample
sequence unbounded above. No sign, growth, or finite-excess premise is needed. -/
theorem summable_kernelPotential_iff_cofinal_samples (v : ℕ → ℝ) (c : ℕ → ℝ)
    (hcofinal : ∀ R : ℝ, ∃ j : ℕ, R ≤ c j) :
    (∀ y : ℝ, Summable fun n => v n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) ↔
    ∀ j : ℕ, Summable fun n => v n *
      (riemannAutocorr (c j + Real.log n) + riemannAutocorr (c j - Real.log n)) := by
  constructor
  · exact fun hs j => hs (c j)
  · intro hs y
    obtain ⟨j, hj⟩ := hcofinal (|y| + 4)
    exact summable_kernelPotential_of_outer_sample hj (hs j)

/-- With finite excess, lower bounds on any cofinal family of actual probes
characterize the entire real-shift potential domain. Bounds and cutoffs may
depend on the probe; no common spacing or monotonicity is assumed. -/
theorem summable_potential_iff_cofinal_probe_lower_bounds {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) (m : ℕ → ℕ)
    (hcofinal : ∀ R : ℝ, ∃ j : ℕ, R ≤ Real.log (m j)) :
    (∀ y : ℝ, Summable fun n => weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) ↔
    ∀ j : ℕ, ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (Real.log (m j)))
        (logShiftRiemannDifference k (Real.log (m j))))).re := by
  constructor
  · intro hs j
    let d := 2 * (deviationPotential lam (Real.log (m j)) - deviationPotential lam 0)
    have ht := (tendsto_logShift_probe_of_summable_potential (m j)
      (hs 0) (hs (Real.log (m j)))).comp (tendsto_natCast_atTop_atTop (R := ℝ))
    have hev := (tendsto_order.mp ht).1 (d - 1) (by change d - 1 < d; linarith)
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    exact ⟨d - 1, N, fun k hk => (hN k hk).le⟩
  · intro hbounded
    obtain ⟨j₀, hj₀⟩ := hcofinal 4
    have horigin := summable_deficit_origin_of_probe_bounded_below hexc hj₀ (hbounded j₀)
    apply (summable_kernelPotential_iff_cofinal_samples (weilDeviation lam)
      (fun j => Real.log (m j)) hcofinal).mpr
    intro j
    exact summable_potential_of_probe_bounded_below hexc horigin (m j) (hbounded j)

private theorem exp_probe_cofinal (R : ℝ) :
    ∃ j : ℕ, R ≤ Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ) := by
  refine ⟨⌈R⌉₊, (Nat.le_ceil R).trans ?_⟩
  exact (integer_log_probe_bounds ⌈R⌉₊).2.1

/-- The prescribed exponential probes provide an exact whole-line convergence
test using only their individual eventual lower bounds. -/
theorem summable_potential_iff_exp_probe_lower_bounds {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) :
    (∀ y : ℝ, Summable fun n => weilDeviation lam n *
      (riemannAutocorr (y + Real.log n) + riemannAutocorr (y - Real.log n))) ↔
    ∀ j : ℕ, ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      b ≤ (weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference k (Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ)))
        (logShiftRiemannDifference k (Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ))))).re :=
  summable_potential_iff_cofinal_probe_lower_bounds hexc
    (fun j => ⌊Real.exp (j : ℝ)⌋₊ + 1) exp_probe_cofinal

/-- Sparse actual-probe lower bounds replace explicit convergence in the
potential-inequality receiver. The inequalities still range over every
integer-log sample. -/
theorem weilLogShiftAsymptoticPositive_iff_guarded_potential {lam : ℕ → ℝ}
    (hexc : Summable (deviationExcess lam)) :
    WeilLogShiftAsymptoticPositive lam ↔
      (∀ j : ℕ, ∃ b : ℝ, ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        b ≤ (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ)))
          (logShiftRiemannDifference k (Real.log (⌊Real.exp (j : ℝ)⌋₊ + 1 : ℕ))))).re) ∧
      ∀ m : ℕ, 2 ≤ m → deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := by
  constructor
  · intro hpos
    exact ⟨(summable_potential_iff_exp_probe_lower_bounds hexc).mp
      (summable_potential_of_logShiftAsymptoticPositive hpos hexc),
      logShiftAsymptotic_potential_le_of_summable_excess hpos hexc⟩
  · rintro ⟨hbounded, hpotential⟩
    have hs := (summable_potential_iff_exp_probe_lower_bounds hexc).mpr hbounded
    exact (weilLogShiftAsymptoticPositive_iff_sampled_potential hexc).mpr
      (fun m hm => ⟨hs (Real.log m), hpotential m hm⟩)

end RHTower
