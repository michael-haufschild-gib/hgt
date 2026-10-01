import GaloisForLFunctions.RHTower.ChiGradedStationaryEntropy
import GaloisForLFunctions.RHTower.ZetaChiConductorOrientation

open Complex MeasureTheory
noncomputable section
namespace RHTower

private theorem zetaChi_positive_grade_entropy_model (k : ℕ) (hk : 0 < k)
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

/-- Every positive integer chi grade has an explicit full stationary term.
Its grade phase and complete height-dependent remainder are retained. -/
theorem norm_integral_zetaChi_positive_grade_stationary_le (k : ℕ) (hk : 0 < k)
    {a h l u : ℝ} (ha : 8 ≤ a) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a) :
    ‖(∫ t in l..u, zetaChi (linePt t) ^ k *
        bourgainOscillation ((k : ℝ) * t * Real.log (a / (2 * Real.pi)))) -
      (((k : ℝ)⁻¹ * Real.sqrt (2 * Real.pi * ((k : ℝ) * a)) : ℝ) : ℂ) *
        bourgainOscillation ((k : ℝ) * a + ((k : ℝ) - 1) * (Real.pi / 4))‖ ≤
      78 * (k : ℝ) + 4 * (k : ℝ) * h ^ 4 / a ^ 2 + 40 * a / ((k : ℝ) * h) := by
  have ha0 : 0 < a := by linarith
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hl0 : 0 < l := by linarith
  have hlu : l ≤ u := by linarith
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
  have hif : IntervalIntegrable f volume l u := hf.intervalIntegrable l u
  have hig : IntervalIntegrable g volume l u :=
    intervalIntegrable_chiStationaryEntropy_grade a (k : ℝ) hl0 hlu
  have hdiff : ‖∫ t in l..u, f t - c * g t‖ ≤ 78 * (k : ℝ) := by
    have hbound : ‖∫ t in l..u, f t - c * g t‖ ≤ (52 * (k : ℝ) / a) * |u - l| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hlu] at ht
      have ht4 : 4 ≤ t := by linarith [ht.1]
      have ht0 : 0 < t := by linarith
      apply (zetaChi_positive_grade_entropy_model k hk ha0 ht4).trans
      rw [div_le_div_iff₀ ht0 ha0]
      nlinarith [mul_le_mul_of_nonneg_left (show a ≤ 2 * t by linarith [ht.1]) hkR.le]
    apply hbound.trans
    rw [abs_of_nonneg (sub_nonneg.mpr hlu)]
    calc
      (52 * (k : ℝ) / a) * (u - l) ≤ (52 * (k : ℝ) / a) * (3 * a / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 78 * (k : ℝ) := by field_simp; ring
  have heq : (∫ t in l..u, f t) - c * (∫ t in l..u, g t) =
      ∫ t in l..u, f t - c * g t := by
    rw [intervalIntegral.integral_sub hif (hig.const_mul c), intervalIntegral.integral_const_mul]
  rw [← heq] at hdiff
  have hmodel : ‖(∫ t in l..u, g t) - M‖ ≤
      4 * (k : ℝ) * h ^ 4 / a ^ 2 + 40 * a / ((k : ℝ) * h) :=
    norm_integral_chiStationaryEntropy_grade_sub_le ha0 hkR hh hha hl hlh hhu hu
  have hphase : c * bourgainOscillation (-(Real.pi / 4)) =
      bourgainOscillation ((k : ℝ) * a + ((k : ℝ) - 1) * (Real.pi / 4)) := by
    dsimp only [c, bourgainOscillation]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hmain : c * M =
      (((k : ℝ)⁻¹ * Real.sqrt (2 * Real.pi * ((k : ℝ) * a)) : ℝ) : ℂ) *
        bourgainOscillation ((k : ℝ) * a + ((k : ℝ) - 1) * (Real.pi / 4)) := by
    dsimp only [M]
    push_cast
    calc
      _ = (k : ℂ)⁻¹ * (Real.sqrt (2 * Real.pi * ((k : ℝ) * a)) : ℂ) *
          (c * bourgainOscillation (-(Real.pi / 4))) := by ring
      _ = _ := by rw [hphase]
  change ‖(∫ t in l..u, f t) - _‖ ≤ _
  rw [← hmain]
  calc
    _ = ‖((∫ t in l..u, f t) - c * (∫ t in l..u, g t)) +
        c * ((∫ t in l..u, g t) - M)‖ := by congr 1; ring
    _ ≤ ‖(∫ t in l..u, f t) - c * (∫ t in l..u, g t)‖ +
        ‖c * ((∫ t in l..u, g t) - M)‖ := norm_add_le _ _
    _ = ‖(∫ t in l..u, f t) - c * (∫ t in l..u, g t)‖ +
        ‖(∫ t in l..u, g t) - M‖ := by rw [norm_mul, hc, one_mul]
    _ ≤ 78 * (k : ℝ) + (4 * (k : ℝ) * h ^ 4 / a ^ 2 + 40 * a / ((k : ℝ) * h)) :=
      add_le_add hdiff hmodel
    _ = _ := by ring

end RHTower
