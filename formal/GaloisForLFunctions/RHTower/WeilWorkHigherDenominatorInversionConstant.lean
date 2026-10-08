import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionSpatial

/-!
# The constant term of the actual inverted boundary trace

Both constant-term coefficients are retained at positive height. Compact domination
then removes the inverse-log correction and leaves the reciprocal test integral.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open RHTower.MaassBesselSeries

namespace RHTower.WeilHigherDenominator

private theorem tendsto_compactKernelPairing {F : ℝ × ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b ×ˢ univ)) :
    Tendsto (fun y : ℝ => ∫ x in a..b, F (x, y)) (𝓝[>] 0)
      (𝓝 (∫ x in a..b, F (x, 0))) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    (hF.mono (by intro p hp; exact ⟨hp.1, mem_univ _⟩))
  have hslice (y : ℝ) : ContinuousOn (fun x => F (x, y)) (uIcc a b) :=
    hF.comp (by fun_prop) (fun x hx => ⟨uIcc_of_le hab ▸ hx, mem_univ _⟩)
  have hm : ∀ᶠ y : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (fun x => F (x, y)) (volume.restrict (uIoc a b)) :=
    Eventually.of_forall fun y => (hslice y).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  have hb : ∀ᶠ y : ℝ in 𝓝[>] 0, ∀ᵐ x : ℝ, x ∈ uIoc a b → ‖F (x, y)‖ ≤ C := by
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 from
        nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))] with y hy hy1
    filter_upwards [] with x hx
    exact hC (x, y) ⟨uIcc_of_le hab ▸ uIoc_subset_uIcc hx, hy.le, hy1.le⟩
  have hl : ∀ᵐ x : ℝ, x ∈ uIoc a b →
      Tendsto (fun y : ℝ => F (x, y)) (𝓝[>] 0) (𝓝 (F (x, 0))) := by
    filter_upwards [] with x hx
    have hc : Continuous (fun y : ℝ => F (x, y)) :=
      hF.comp_continuous (by fun_prop)
        (fun y => ⟨uIcc_of_le hab ▸ uIoc_subset_uIcc hx, mem_univ _⟩)
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => C) hm hb intervalIntegrable_const hl

private theorem continuousOn_inversionWeightedTest {φ : ℝ → ℂ}
    (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × ℝ => φ p.1 * (inversionBoundaryWeight p.2 p.1 : ℂ))
      (Icc a b ×ˢ univ) := by
  have hd : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
      (Icc a b ×ˢ (univ : Set ℝ)) := by fun_prop
  have hw := hd.rpow_const (p := -(1 / 2 : ℝ)) fun p hp =>
    Or.inl (inversionBoundaryDenom_pos (ha.trans_le hp.1.1) p.2).ne'
  exact (hφ.comp continuous_fst).continuousOn.mul
    (Complex.continuous_ofReal.comp_continuousOn hw)

private theorem continuousOn_inversionWeightedLogTest {φ : ℝ → ℂ}
    (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × ℝ => φ p.1 * (inversionBoundaryWeight p.2 p.1 : ℂ) *
      (Real.log (p.1 ^ 2 + p.2 ^ 2) : ℂ)) (Icc a b ×ˢ univ) := by
  have hd : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)
      (Icc a b ×ˢ (univ : Set ℝ)) := by fun_prop
  exact (continuousOn_inversionWeightedTest hφ ha).mul
    (Complex.continuous_ofReal.comp_continuousOn
      (hd.log fun p hp => (inversionBoundaryDenom_pos (ha.trans_le hp.1.1) p.2).ne'))

theorem tendsto_inversionWeightedTestIntegral {φ : ℝ → ℂ} (hφ : Continuous φ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun y : ℝ => ∫ x in a..b, φ x * (inversionBoundaryWeight y x : ℂ))
      (𝓝[>] 0) (𝓝 (∫ x in a..b, φ x * (x⁻¹ : ℝ))) := by
  have ht := tendsto_compactKernelPairing hab (continuousOn_inversionWeightedTest hφ ha)
  have he : (∫ x in a..b, φ x * (inversionBoundaryWeight 0 x : ℂ)) =
      ∫ x in a..b, φ x * (x⁻¹ : ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx0 : 0 < x := ha.trans_le (uIcc_of_le hab ▸ hx).1
    change φ x * (inversionBoundaryWeight 0 x : ℂ) = _
    rw [inversionBoundaryWeight, zero_pow (by decide : 2 ≠ 0), add_zero,
      Real.rpow_neg (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq hx0.le]
  simpa only [he] using ht

/-- The exact positive-height expression retains both constant-term coefficients. -/
theorem normalized_constTerm_inversion (A B : ℂ) (φ : ℝ → ℂ)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hl : Real.log y ≠ 0) :
    φ x * constTerm A B (inversionBoundaryPoint y x) /
        ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ) =
      A * (φ x * (inversionBoundaryWeight y x : ℂ)) +
        (B * (φ x * (inversionBoundaryWeight y x : ℂ)) -
          A * (φ x * (inversionBoundaryWeight y x : ℂ) *
            (Real.log (x ^ 2 + y ^ 2) : ℂ))) / (Real.log y : ℂ) := by
  have hd := inversionBoundaryDenom_pos hx y
  have hp : (y / (x ^ 2 + y ^ 2)) ^ (1 / 2 : ℝ) =
      y ^ (1 / 2 : ℝ) * inversionBoundaryWeight y x := by
    rw [Real.div_rpow hy.le hd.le, inversionBoundaryWeight, Real.rpow_neg hd.le]
    rfl
  have hpow : ((y ^ (1 / 2 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hy _).ne'
  have hlog : (Real.log y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hl
  simp only [constTerm, MaassBesselSeries.sqrtPart, MaassBesselSeries.sqrtLogPart, inversionBoundaryPoint_im, hp,
    Real.log_div hy.ne' hd.ne']
  push_cast
  field_simp [hpow, hlog]
  ring

/-- Compact domination proves the constant-term trace without a boundary premise. -/
theorem tendsto_constTerm_inversion_integral (A B : ℂ) {φ : ℝ → ℂ}
    (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun y : ℝ => ∫ x in a..b, φ x * constTerm A B (inversionBoundaryPoint y x) /
        ((y ^ (1 / 2 : ℝ) * Real.log y : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (A * (∫ x in a..b, φ x * (x⁻¹ : ℝ)))) := by
  let H := fun y : ℝ => ∫ x in a..b, φ x * (inversionBoundaryWeight y x : ℂ)
  let J := fun y : ℝ => ∫ x in a..b, φ x * (inversionBoundaryWeight y x : ℂ) *
    (Real.log (x ^ 2 + y ^ 2) : ℂ)
  have hH := tendsto_inversionWeightedTestIntegral hφ ha hab
  have hJ := tendsto_compactKernelPairing hab (continuousOn_inversionWeightedLogTest hφ ha)
  have hi : Tendsto (fun y : ℝ => (Real.log y : ℂ)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero)
    simpa only [Function.comp_def, ofReal_inv, ofReal_zero] using ht
  have ht : Tendsto (fun y => A * H y + (B * H y - A * J y) / (Real.log y : ℂ))
      (𝓝[>] 0) (𝓝 (A * (∫ x in a..b, φ x * (x⁻¹ : ℝ)))) := by
    simpa only [H, J, div_eq_mul_inv, mul_zero, add_zero] using
      (hH.const_mul A).add (((hH.const_mul B).sub (hJ.const_mul A)).mul hi)
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (show ∀ᶠ y : ℝ in 𝓝[>] 0, y < 1 from
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one))] with y hy hy1
  have hHI : IntervalIntegrable (fun x => φ x * (inversionBoundaryWeight y x : ℂ)) volume a b :=
    ((continuousOn_inversionWeightedTest hφ ha).comp (f := fun x : ℝ => (x, y)) (by fun_prop)
      (fun x hx => ⟨uIcc_of_le hab ▸ hx, mem_univ _⟩)).intervalIntegrable
  have hJI : IntervalIntegrable (fun x => φ x * (inversionBoundaryWeight y x : ℂ) *
      (Real.log (x ^ 2 + y ^ 2) : ℂ)) volume a b :=
    ((continuousOn_inversionWeightedLogTest hφ ha).comp (f := fun x : ℝ => (x, y)) (by fun_prop)
      (fun x hx => ⟨uIcc_of_le hab ▸ hx, mem_univ _⟩)).intervalIntegrable
  symm
  calc
    _ = ∫ x in a..b, A * (φ x * (inversionBoundaryWeight y x : ℂ)) +
        (B * (φ x * (inversionBoundaryWeight y x : ℂ)) -
          A * (φ x * (inversionBoundaryWeight y x : ℂ) *
            (Real.log (x ^ 2 + y ^ 2) : ℂ))) / (Real.log y : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact normalized_constTerm_inversion A B φ (ha.trans_le (uIcc_of_le hab ▸ hx).1)
        hy (Real.log_neg hy hy1).ne
    _ = _ := by
      rw [intervalIntegral.integral_add (hHI.const_mul A)
        (((hHI.const_mul B).sub (hJI.const_mul A)).div_const _),
        intervalIntegral.integral_div, intervalIntegral.integral_sub (hHI.const_mul B) (hJI.const_mul A)]
      simp only [intervalIntegral.integral_const_mul, H, J]

end RHTower.WeilHigherDenominator
