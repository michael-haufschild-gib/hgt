import GaloisForLFunctions.RHTower.ChiStationaryAmplitudeFreezing
import GaloisForLFunctions.RHTower.ZetaChiConductorOrientation

open Complex MeasureTheory
noncomputable section
namespace RHTower

private theorem zetaChi_amplitude_grade_entropy_model (k : ℕ) (hk : 0 < k)
    {a t : ℝ} (ha : 0 < a) (ht : 4 ≤ t) :
    ‖zetaChi (linePt t) ^ k * bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi))) -
      bourgainOscillation ((k : ℝ) * (Real.pi / 4) + (k : ℝ) * a) *
        bourgainOscillation (-(k : ℝ) * chiStationaryEntropy a t)‖ ≤ 26 * (k : ℝ) / t := by
  have ht0 : 0 < t := by linarith
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hb := norm_zetaChi_integerGrade_sub_explicit_model_le (k : ℤ) ht
  norm_num only [Int.cast_natCast, zpow_natCast] at hb
  rw [abs_of_pos hkR] at hb
  have hphase : (bourgainOscillation (Real.pi / 4) ^ k *
      Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)) *
        bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi))) =
      bourgainOscillation ((k : ℝ) * (Real.pi / 4) + (k : ℝ) * a) *
        bourgainOscillation (-(k : ℝ) * chiStationaryEntropy a t) := by
    unfold bourgainOscillation
    rw [← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [Real.log_div ht0.ne' (by positivity : 2 * Real.pi ≠ 0),
      Real.log_div ha.ne' (by positivity : 2 * Real.pi ≠ 0)]
    unfold chiStationaryEntropy
    push_cast
    ring
  have he : zetaChi (linePt t) ^ k *
      bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi))) -
      bourgainOscillation ((k : ℝ) * (Real.pi / 4) + (k : ℝ) * a) *
        bourgainOscillation (-(k : ℝ) * chiStationaryEntropy a t) =
      (zetaChi (linePt t) ^ k - bourgainOscillation (Real.pi / 4) ^ k *
        Complex.exp ((((k : ℝ) * (t - t * Real.log (t / (2 * Real.pi))) : ℝ) : ℂ) * I)) *
        bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi))) := by
    rw [sub_mul, hphase]
  rw [he, norm_mul, norm_bourgainOscillation, mul_one]
  exact hb

/-- Actual chi stationary phase with a height-dependent complex amplitude.
The saddle value, complete conductor error and both amplitude tails remain explicit. -/
theorem norm_integral_zetaChi_complexAmplitude_stationary_le (k : ℕ) (hk : 0 < k)
    {a h l u L U : ℝ} (ha : 8 ≤ a) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a)
    (hL : 0 ≤ L) {v v' : ℝ → ℂ}
    (hv : ∀ t ∈ Set.Icc l u, HasDerivAt v (v' t) t)
    (hvi : IntervalIntegrable v' volume l u)
    (hvL : ∀ t ∈ Set.Icc l u, ‖v' t‖ ≤ L)
    (hvU : ∀ t ∈ Set.Icc l u, ‖v t‖ ≤ U) :
    ‖(∫ t in l..u, v t * (zetaChi (linePt t) ^ k *
        bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi))))) -
      v a * ((((k : ℝ)⁻¹ * Real.sqrt (2 * Real.pi * ((k : ℝ) * a)) : ℝ) : ℂ) *
        bourgainOscillation ((k : ℝ) * a + ((k : ℝ) - 1) * (Real.pi / 4)))‖ ≤
      78 * (k : ℝ) * U + 2 * L * h ^ 2 + 40 * L * a ^ 2 / ((k : ℝ) * h) +
      ‖v a‖ * (4 * (k : ℝ) * h ^ 4 / a ^ 2 + 40 * a / ((k : ℝ) * h)) := by
  have ha0 : 0 < a := by linarith
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlu : l ≤ u := by linarith
  have haI : a ∈ Set.Icc l u := ⟨by linarith, by linarith⟩
  have hU : 0 ≤ U := (norm_nonneg _).trans (hvU a haI)
  let c : ℂ := bourgainOscillation ((k : ℝ) * (Real.pi / 4) + (k : ℝ) * a)
  let f : ℝ → ℂ := fun t => zetaChi (linePt t) ^ k *
    bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi)))
  let g : ℝ → ℂ := fun t => bourgainOscillation (-(k : ℝ) * chiStationaryEntropy a t)
  let M : ℂ := ((k : ℝ)⁻¹ : ℂ) *
    ((Real.sqrt (2 * Real.pi * ((k : ℝ) * a)) : ℂ) * bourgainOscillation (-(Real.pi / 4)))
  have hc : ‖c‖ = 1 := norm_bourgainOscillation _
  have hcχ : Continuous (fun t : ℝ => zetaChi (linePt t)) := by
    simp_rw [zetaChi_line_eq_exp_neg_two_theta]
    have hθ : Continuous gammaHardyTheta := differentiable_gammaHardyTheta.continuous
    fun_prop
  have hf : Continuous f := by
    dsimp only [f]
    apply (hcχ.pow k).mul
    unfold bourgainOscillation
    fun_prop
  have hg : Continuous g := continuous_chiStationaryEntropy_grade a (k : ℝ)
  have hvC : ContinuousOn v (Set.Icc l u) :=
    fun t ht => (hv t ht).continuousAt.continuousWithinAt
  have hif : IntervalIntegrable (fun t => v t * f t) volume l u :=
    ContinuousOn.intervalIntegrable_of_Icc hlu (hvC.mul hf.continuousOn)
  have hig : IntervalIntegrable (fun t => v t * g t) volume l u :=
    ContinuousOn.intervalIntegrable_of_Icc hlu (hvC.mul hg.continuousOn)
  have hdiff : ‖∫ t in l..u, v t * (f t - c * g t)‖ ≤ 78 * (k : ℝ) * U := by
    have hbound : ‖∫ t in l..u, v t * (f t - c * g t)‖ ≤
        (52 * (k : ℝ) * U / a) * |u - l| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hlu] at ht
      have htI : t ∈ Set.Icc l u := ⟨ht.1.le, ht.2⟩
      have ht4 : 4 ≤ t := by linarith [ht.1]
      have ht0 : 0 < t := by linarith
      have hb : ‖f t - c * g t‖ ≤ 52 * (k : ℝ) / a := by
        apply (zetaChi_amplitude_grade_entropy_model k hk ha0 ht4).trans
        rw [div_le_div_iff₀ ht0 ha0]
        nlinarith [mul_le_mul_of_nonneg_left (show a ≤ 2 * t by linarith [ht.1]) hkR.le]
      rw [norm_mul]
      calc
        _ ≤ U * (52 * (k : ℝ) / a) := mul_le_mul (hvU t htI) hb (norm_nonneg _) hU
        _ = _ := by ring
    apply hbound.trans
    rw [abs_of_nonneg (sub_nonneg.mpr hlu)]
    calc
      _ ≤ (52 * (k : ℝ) * U / a) * (3 * a / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by field_simp; ring
  have heq : (∫ t in l..u, v t * f t) - c * (∫ t in l..u, v t * g t) =
      ∫ t in l..u, v t * (f t - c * g t) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hif (hig.const_mul c)]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [← heq] at hdiff
  have hmodel := norm_integral_entropy_grade_complexAmplitude_sub_stationary_le
    ha0 hkR hh hha hl hlh hhu hu hL hv hvi hvL
  have hphase : c * bourgainOscillation (-(Real.pi / 4)) =
      bourgainOscillation ((k : ℝ) * a + ((k : ℝ) - 1) * (Real.pi / 4)) := by
    dsimp only [c, bourgainOscillation]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hmain : c * (v a * M) =
      v a * ((((k : ℝ)⁻¹ * Real.sqrt (2 * Real.pi * ((k : ℝ) * a)) : ℝ) : ℂ) *
        bourgainOscillation ((k : ℝ) * a + ((k : ℝ) - 1) * (Real.pi / 4))) := by
    dsimp only [M]
    push_cast
    calc
      _ = v a * ((k : ℂ)⁻¹ * (Real.sqrt (2 * Real.pi * ((k : ℝ) * a)) : ℂ) *
          (c * bourgainOscillation (-(Real.pi / 4)))) := by ring
      _ = _ := by rw [hphase]
  change ‖(∫ t in l..u, v t * f t) - _‖ ≤ _
  rw [← hmain]
  calc
    _ = ‖((∫ t in l..u, v t * f t) - c * (∫ t in l..u, v t * g t)) +
        c * ((∫ t in l..u, v t * g t) - v a * M)‖ := by congr 1; ring
    _ ≤ ‖(∫ t in l..u, v t * f t) - c * (∫ t in l..u, v t * g t)‖ +
        ‖c * ((∫ t in l..u, v t * g t) - v a * M)‖ := norm_add_le _ _
    _ = ‖(∫ t in l..u, v t * f t) - c * (∫ t in l..u, v t * g t)‖ +
        ‖(∫ t in l..u, v t * g t) - v a * M‖ := by rw [norm_mul, hc, one_mul]
    _ ≤ 78 * (k : ℝ) * U +
        (2 * L * h ^ 2 + 40 * L * a ^ 2 / ((k : ℝ) * h) +
          ‖v a‖ * (4 * (k : ℝ) * h ^ 4 / a ^ 2 + 40 * a / ((k : ℝ) * h))) :=
      add_le_add hdiff hmodel
    _ = _ := by ring

end RHTower
