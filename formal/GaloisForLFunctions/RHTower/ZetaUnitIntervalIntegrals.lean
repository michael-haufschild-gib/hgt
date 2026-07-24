import GaloisForLFunctions.RHTower.ZetaSawtoothTail

/-!
# Unit-interval integrals of complex powers

The integration core of the truncated ζ-representation: the exact
interval integral of `u ↦ u^r` (complex exponent, positive real base),
the telescoping-value principle for series whose partial sums are read
off a vanishing sequence, the tail integrability of `u^r` on `[c, ∞)`
for `Re r < -1`, the unit-interval `HasSum` decomposition of the tail
integral, and its exact value `-c^{r+1}/(r+1)`.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter

/-- Exact interval integral of a complex power over `Ioc`. -/
theorem integral_Ioc_ofReal_cpow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {r : ℂ} (hr : r ≠ -1) :
    ∫ u in Set.Ioc a b, (u : ℂ) ^ r
      = ((b : ℂ) ^ (r + 1) - (a : ℂ) ^ (r + 1)) / (r + 1) := by
  have hFTC : ∫ x in a..b, (x : ℂ) ^ r
      = (b : ℂ) ^ (r + 1) / (r + 1) - (a : ℂ) ^ (r + 1) / (r + 1) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => (y : ℂ) ^ (r + 1) / (r + 1))
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact hasDerivAt_ofReal_cpow_const'
        (by nlinarith [hx.1] : x ≠ 0) hr
    · apply ContinuousOn.intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hx0 : (0 : ℝ) < x := lt_of_lt_of_le ha hx.1
      have h2 : Continuous fun v : ℝ => (v, (r : ℂ)) := by fun_prop
      exact ((Complex.continuousAt_ofReal_cpow x r
        (Or.inr (ne_of_gt hx0))).comp
          (f := fun v : ℝ => (v, (r : ℂ))) h2.continuousAt).continuousWithinAt
  rw [← intervalIntegral.integral_of_le hab, hFTC]
  ring

/-- **Telescoping value**: if the telescope of a null sequence has a sum,
that sum is the initial value. -/
theorem eq_head_of_hasSum_telescope {f : ℕ → ℂ} {a : ℂ}
    (h : HasSum (fun k => f k - f (k + 1)) a)
    (h0 : Tendsto f atTop (nhds 0)) : a = f 0 := by
  have h1 := h.tendsto_sum_nat
  have h2 : (fun n => ∑ i ∈ Finset.range n, (f i - f (i + 1)))
      = fun n => f 0 - f n := by
    funext n
    exact Finset.sum_range_sub' f n
  rw [h2] at h1
  have h3 : Tendsto (fun n : ℕ => f 0 - f n) atTop (nhds (f 0 - 0)) :=
    tendsto_const_nhds.sub h0
  rw [sub_zero] at h3
  exact tendsto_nhds_unique h1 h3

/-- Tail integrability of `u^r` on `[c, ∞)` for `Re r < -1`. -/
theorem integrableOn_Ici_ofReal_cpow {c : ℝ} (hc : 0 < c) {r : ℂ}
    (hr : r.re < -1) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ r) (Set.Ici c) := by
  have hg : IntegrableOn (fun u : ℝ => u ^ r.re) (Set.Ici c) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt hr hc
  have hmeas : AEStronglyMeasurable (fun u : ℝ => (u : ℂ) ^ r)
      (volume.restrict (Set.Ici c)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ici
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hc hu
    have h2 : Continuous fun v : ℝ => (v, (r : ℂ)) := by fun_prop
    exact ((Complex.continuousAt_ofReal_cpow u r
      (Or.inr (ne_of_gt hu0))).comp
        (f := fun v : ℝ => (v, (r : ℂ))) h2.continuousAt).continuousWithinAt
  apply Integrable.mono hg hmeas
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards with u hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hc hu
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hu0.le _)]

/-- The unit-interval cover of the closed ray. -/
theorem iUnion_Ico_unit (c : ℝ) :
    (⋃ k : ℕ, Set.Ico (c + k) (c + k + 1)) = Set.Ici c := by
  ext u
  simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_Ici]
  constructor
  · rintro ⟨k, hk1, _⟩
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  · intro hu
    refine ⟨⌊u - c⌋₊, ?_, ?_⟩
    · have h1 : (⌊u - c⌋₊ : ℝ) ≤ u - c := Nat.floor_le (by linarith)
      linarith
    · have h2 : u - c < ⌊u - c⌋₊ + 1 := Nat.lt_floor_add_one _
      linarith

/-- Unit-interval `HasSum` decomposition of a tail integral. -/
theorem hasSum_integral_Ico_unit {c : ℝ} {f : ℝ → ℂ}
    (hf : IntegrableOn f (Set.Ici c)) :
    HasSum (fun k : ℕ => ∫ u in Set.Ico (c + k) (c + k + 1), f u)
      (∫ u in Set.Ici c, f u) := by
  have hd : Pairwise (Function.onFun Disjoint
      fun k : ℕ => Set.Ico (c + k) (c + k + 1)) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro u hui huj
    rw [Set.mem_Ico] at hui huj
    have h1 : (i : ℝ) < (j : ℝ) + 1 := by linarith
    have h2 : (j : ℝ) < (i : ℝ) + 1 := by linarith
    have h3 : i < j + 1 := by exact_mod_cast h1
    have h4 : j < i + 1 := by exact_mod_cast h2
    exact hij (by omega)
  have h1 := hasSum_integral_iUnion
    (fun k : ℕ => measurableSet_Ico) hd
    (by rw [iUnion_Ico_unit c]; exact hf)
  rwa [iUnion_Ico_unit c] at h1


set_option maxHeartbeats 800000 in
/-- **Exact tail integral**: `∫_c^∞ u^r = -c^{r+1}/(r+1)` for
`Re r < -1`. -/
theorem integral_Ici_ofReal_cpow {c : ℝ} (hc : 0 < c) {r : ℂ}
    (hr : r.re < -1) :
    ∫ u in Set.Ici c, (u : ℂ) ^ r = -(c : ℂ) ^ (r + 1) / (r + 1) := by
  have hre1 : (r + 1).re < 0 := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hr10 : r + 1 ≠ 0 := fun h => by
    rw [h] at hre1
    simp at hre1
  have hr1 : r ≠ -1 := fun h => hr10 (by rw [h]; ring)
  have hsum := hasSum_integral_Ico_unit
    (integrableOn_Ici_ofReal_cpow hc hr)
  have hpiece : (fun k : ℕ => ∫ u in Set.Ico (c + k) (c + k + 1),
      (u : ℂ) ^ r)
      = fun k : ℕ => -((((c + k : ℝ)) : ℂ) ^ (r + 1) / (r + 1)
          - (((c + (k + 1 : ℕ) : ℝ)) : ℂ) ^ (r + 1) / (r + 1)) := by
    funext k
    have hck : (0 : ℝ) < c + k := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    rw [integral_Ico_eq_integral_Ioc,
      integral_Ioc_ofReal_cpow hck (by linarith) hr1,
      show ((c + (k + 1 : ℕ) : ℝ) : ℂ) = ((c + k + 1 : ℝ) : ℂ) by
        push_cast; ring]
    ring
  rw [hpiece] at hsum
  have hneg := hsum.neg
  simp only [neg_neg] at hneg
  -- the telescope sequence vanishes at infinity
  have hF0 : Tendsto (fun k : ℕ =>
      (((c + k : ℝ)) : ℂ) ^ (r + 1) / (r + 1)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ k : ℕ, ‖(((c + k : ℝ)) : ℂ) ^ (r + 1) / (r + 1)‖
        = (c + k) ^ ((r + 1).re) / ‖r + 1‖ := by
      intro k
      have hck : (0 : ℝ) < c + k := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hck]
    simp only [hnorm]
    have h1 : Tendsto (fun k : ℕ => (c + k : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ c tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun x : ℝ => x ^ ((r + 1).re)) atTop (nhds 0) := by
      have h3 := tendsto_rpow_neg_atTop
        (show (0 : ℝ) < -((r + 1).re) by linarith)
      simpa using h3
    have h4 := (h2.comp h1).div_const ‖r + 1‖
    simpa using h4
  have hval := eq_head_of_hasSum_telescope
    (f := fun k : ℕ => (((c + k : ℝ)) : ℂ) ^ (r + 1) / (r + 1)) hneg hF0
  -- `-(∫) = F 0 = c^{r+1}/(r+1)`
  have h5 : -∫ u in Set.Ici c, (u : ℂ) ^ r
      = (((c + (0 : ℕ) : ℝ)) : ℂ) ^ (r + 1) / (r + 1) := hval
  rw [show ((c + (0 : ℕ) : ℝ) : ℂ) = (c : ℂ) by push_cast; ring] at h5
  linear_combination -h5

end RHTower
