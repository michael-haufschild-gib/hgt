import GaloisForLFunctions.RHTower.HyperbolicOrbitalIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The volume of the modular horizon

The hyperbolic area of the modular fundamental domain is `π/3`:
`∫_{|x| ≤ ½} ∫_{y ≥ √(1-x²)} y⁻² dy dx = ∫_{|x| ≤ ½} (1-x²)^{-½} dx = 2 arcsin ½`.
-/

open Complex MeasureTheory Set Filter Topology ModularGroup
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

/-- The domain in the chart. -/
def fdChart : Set ℂ := {w : ℂ | 1 ≤ Complex.normSq w ∧ |w.re| ≤ 1 / 2}

theorem measurableSet_fdChart : MeasurableSet fdChart := by
  refine IsClosed.measurableSet ?_
  exact (isClosed_le continuous_const Complex.continuous_normSq).inter
    (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const)

theorem lintegral_Ici_inv_sq {b : ℝ} (hb : 0 < b) :
    ∫⁻ y in Ici b, ENNReal.ofReal ((y ^ 2)⁻¹) = ENNReal.ofReal b⁻¹ := by
  have hint := integrableOn_Ioi_rpow_of_lt (a := -2) (by norm_num) (c := b) hb
  have hval := integral_Ioi_rpow_of_lt (a := -2) (by norm_num) (c := b) hb
  have heq : EqOn (fun y : ℝ => y ^ (-2 : ℝ)) (fun y : ℝ => (y ^ 2)⁻¹) (Ioi b) := fun y hy => by
    have hy0 : (0 : ℝ) < y := lt_trans hb hy
    simp only
    rw [Real.rpow_neg hy0.le]
    norm_num
  have hint' : IntegrableOn (fun y : ℝ => (y ^ 2)⁻¹) (Ioi b) := hint.congr_fun heq measurableSet_Ioi
  have hval' : ∫ y in Ioi b, (y ^ 2)⁻¹ = b⁻¹ := by
    rw [← setIntegral_congr_fun measurableSet_Ioi heq, hval]
    have h1 : (-2 : ℝ) + 1 = -1 := by norm_num
    rw [h1, Real.rpow_neg_one]
    field_simp
  rw [← restrict_Ioi_eq_restrict_Ici, ← hval', ofReal_integral_eq_lintegral_ofReal hint'
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y _ => by positivity))]

/-- **The volume of the modular fundamental domain.** -/
theorem volume_fd_eq : (volume : Measure UpperHalfPlane) fd = ENNReal.ofReal (Real.pi / 3) := by
  have hfdm : MeasurableSet (fd : Set UpperHalfPlane) := isClosed_fd.measurableSet
  rw [← lintegral_indicator_one hfdm]
  rw [_root_.RHTower.lintegral_upperHalfPlane_eq_iterated (Gc := fdChart.indicator 1)
    (measurable_one.indicator measurableSet_fdChart) (fun z => by
      by_cases hz : z ∈ (fd : Set UpperHalfPlane)
      · have : (z : ℂ) ∈ fdChart := hz
        simp [hz, this]
      · have : (z : ℂ) ∉ fdChart := hz
        simp [hz, this])]
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal ((p.1 ^ 2)⁻¹) *
      fdChart.indicator 1 (⟨p.2, p.1⟩ : ℂ)) := by
    refine ((measurable_fst.pow_const 2).inv.ennreal_ofReal).mul ?_
    exact (measurable_one.indicator measurableSet_fdChart).comp
      (Complex.measurableEquivRealProd.symm.measurable.comp measurable_swap)
  rw [lintegral_lintegral_swap (hm.aemeasurable)]
  have hinner : ∀ x : ℝ, (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal ((y ^ 2)⁻¹) *
      fdChart.indicator (1 : ℂ → ℝ≥0∞) (⟨x, y⟩ : ℂ)) =
      (Icc (-(1 / 2) : ℝ) (1 / 2)).indicator (fun x => ENNReal.ofReal (Real.sqrt (1 - x ^ 2))⁻¹) x := by
    intro x
    by_cases hx : x ∈ Icc (-(1 / 2) : ℝ) (1 / 2)
    · have hxa : |x| ≤ 1 / 2 := abs_le.mpr hx
      have h1 : 0 < 1 - x ^ 2 := by nlinarith [abs_nonneg x, sq_abs x]
      have hb := Real.sqrt_pos.mpr h1
      rw [indicator_of_mem hx, ← lintegral_Ici_inv_sq hb, ← lintegral_indicator measurableSet_Ici,
        ← lintegral_indicator measurableSet_Ioi]
      refine lintegral_congr fun y => ?_
      by_cases hy : Real.sqrt (1 - x ^ 2) ≤ y
      · have hy0 : 0 < y := hb.trans_le hy
        have hmem : (⟨x, y⟩ : ℂ) ∈ fdChart := by
          refine ⟨?_, hxa⟩
          rw [Complex.normSq_mk]
          have := Real.sq_sqrt h1.le
          nlinarith [pow_le_pow_left₀ hb.le hy 2]
        simp [hy, hy0, hmem]
      · push Not at hy
        by_cases hy0 : 0 < y
        · have hmem : (⟨x, y⟩ : ℂ) ∉ fdChart := fun h => by
            have h2 := h.1
            rw [Complex.normSq_mk] at h2
            have h3 := Real.sq_sqrt h1.le
            nlinarith [pow_lt_pow_left₀ hy hy0.le two_ne_zero]
          simp [hy0, hmem, not_le.mpr hy]
        · simp [hy0, not_le.mpr hy]
    · rw [indicator_of_notMem hx]
      have hmem : ∀ y : ℝ, (⟨x, y⟩ : ℂ) ∉ fdChart := fun y h => hx (abs_le.mp h.2)
      simp [hmem]
  simp_rw [hinner]
  rw [lintegral_indicator measurableSet_Icc]
  have hderiv : ∀ x ∈ uIcc (-(1 / 2) : ℝ) (1 / 2), HasDerivAt Real.arcsin (Real.sqrt (1 - x ^ 2))⁻¹ x := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have h := Real.hasDerivAt_arcsin (by linarith [hx.1] : x ≠ -1) (by linarith [hx.2] : x ≠ 1)
    simpa [one_div] using h
  have hcont : ContinuousOn (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹) (Icc (-(1 / 2) : ℝ) (1 / 2)) := by
    refine ContinuousOn.inv₀ (by fun_prop) fun x hx => ?_
    have hxa : |x| ≤ 1 / 2 := abs_le.mpr hx
    exact (Real.sqrt_pos.mpr (by nlinarith [abs_nonneg x, sq_abs x])).ne'
  have hint : IntegrableOn (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹) (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
    hcont.integrableOn_compact isCompact_Icc
  have hval : ∫ x in Icc (-(1 / 2) : ℝ) (1 / 2), (Real.sqrt (1 - x ^ 2))⁻¹ = Real.pi / 3 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((hcont.mono (by rw [uIcc_of_le (by norm_num)])).intervalIntegrable), Real.arcsin_neg]
    have hs : Real.arcsin (1 / 2) = Real.pi / 6 := by
      rw [← Real.sin_pi_div_six, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]
    rw [hs]
    ring
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun x _ => by positivity))]

end GaloisForLFunctions.BlackHoleRingdown

end
