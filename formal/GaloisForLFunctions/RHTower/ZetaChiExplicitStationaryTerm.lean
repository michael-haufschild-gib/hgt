import GaloisForLFunctions.RHTower.ZetaChiConductorOrientation
import GaloisForLFunctions.RHTower.ChiStationaryEntropyIntegral

open Complex MeasureTheory
noncomputable section
namespace RHTower

private theorem zetaChi_explicit_entropy_model {a t : ℝ} (ha : 0 < a) (ht : 4 ≤ t) :
    ‖zetaChi (linePt t) * bourgainOscillation (t * Real.log (a / (2 * Real.pi))) -
      (bourgainOscillation (Real.pi / 4) * bourgainOscillation a) *
        bourgainOscillation (-chiStationaryEntropy a t)‖ ≤ 26 / t := by
  have ht0 : 0 < t := by linarith
  have hb := norm_zetaChi_integerGrade_sub_explicit_model_le (1 : ℤ) ht
  norm_num only [Int.cast_one, zpow_one, one_mul, abs_one, mul_one] at hb
  have hc : Complex.exp (((t - t * Real.log (t / (2 * Real.pi)) : ℝ) : ℂ) * I) =
      bourgainOscillation (t - t * Real.log (t / (2 * Real.pi))) := by
    unfold bourgainOscillation
    congr 1
    ring
  rw [hc] at hb
  have hphase : bourgainOscillation (t - t * Real.log (t / (2 * Real.pi))) *
      bourgainOscillation (t * Real.log (a / (2 * Real.pi))) =
      bourgainOscillation a * bourgainOscillation (-chiStationaryEntropy a t) := by
    unfold bourgainOscillation
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [Real.log_div ht0.ne' (by positivity : 2 * Real.pi ≠ 0),
      Real.log_div ha.ne' (by positivity : 2 * Real.pi ≠ 0)]
    unfold chiStationaryEntropy
    push_cast
    ring
  have he : zetaChi (linePt t) * bourgainOscillation (t * Real.log (a / (2 * Real.pi))) -
      (bourgainOscillation (Real.pi / 4) * bourgainOscillation a) *
        bourgainOscillation (-chiStationaryEntropy a t) =
      (zetaChi (linePt t) - bourgainOscillation (Real.pi / 4) *
        bourgainOscillation (t - t * Real.log (t / (2 * Real.pi)))) *
          bourgainOscillation (t * Real.log (a / (2 * Real.pi))) := by
    rw [sub_mul]
    simp_rw [mul_assoc]
    rw [hphase]
  rw [he, norm_mul, norm_bourgainOscillation, mul_one]
  exact hb

/-- The complete physical stationary leading term has its exact phase.
At positive integer saddles it is a positive real number. -/
theorem norm_integral_zetaChi_sub_explicit_stationary_le {a h l u : ℝ}
    (ha : 8 ≤ a) (hh : 0 < h) (hha : h ≤ a / 2)
    (hl : a / 2 ≤ l) (hlh : l ≤ a - h) (hhu : a + h ≤ u) (hu : u ≤ 2 * a) :
    ‖(∫ t in l..u, zetaChi (linePt t) *
        bourgainOscillation (t * Real.log (a / (2 * Real.pi)))) -
      bourgainOscillation a * (Real.sqrt (2 * Real.pi * a) : ℂ)‖ ≤
        78 + 4 * h ^ 4 / a ^ 2 + 40 * a / h := by
  have ha0 : 0 < a := by linarith
  have hl0 : 0 < l := by linarith
  have hlu : l ≤ u := by linarith
  let c : ℂ := bourgainOscillation (Real.pi / 4) * bourgainOscillation a
  let f : ℝ → ℂ := fun t => zetaChi (linePt t) *
    bourgainOscillation (t * Real.log (a / (2 * Real.pi)))
  let g : ℝ → ℂ := fun t => bourgainOscillation (-chiStationaryEntropy a t)
  let M : ℂ := (Real.sqrt (2 * Real.pi * a) : ℂ) * bourgainOscillation (-(Real.pi / 4))
  have hc : ‖c‖ = 1 := by simp only [c, norm_mul, norm_bourgainOscillation, mul_one]
  have hf : Continuous f := by
    convert continuous_zetaChiCriticalTwistIntegrand (Real.log (a / (2 * Real.pi))) using 1
    funext t
    dsimp only [f, bourgainOscillation]
    congr 1
    congr 1
    push_cast
    ring
  have hif : IntervalIntegrable f volume l u := hf.intervalIntegrable l u
  have hig : IntervalIntegrable g volume l u :=
    intervalIntegrable_chiStationaryEntropy_neg a hl0 hlu
  have hdiff : ‖∫ t in l..u, f t - c * g t‖ ≤ 78 := by
    have hbound : ‖∫ t in l..u, f t - c * g t‖ ≤ (52 / a) * |u - l| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro t ht
      rw [Set.uIoc_of_le hlu] at ht
      have ht4 : 4 ≤ t := by linarith [ht.1]
      have ht0 : 0 < t := by linarith
      apply (zetaChi_explicit_entropy_model ha0 ht4).trans
      rw [div_le_div_iff₀ ht0 ha0]
      linarith [ht.1]
    apply hbound.trans
    rw [abs_of_nonneg (sub_nonneg.mpr hlu)]
    calc
      (52 / a) * (u - l) ≤ (52 / a) * (3 * a / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 78 := by field_simp; ring
  have heq : (∫ t in l..u, f t) - c * (∫ t in l..u, g t) =
      ∫ t in l..u, f t - c * g t := by
    rw [intervalIntegral.integral_sub hif (hig.const_mul c), intervalIntegral.integral_const_mul]
  rw [← heq] at hdiff
  have hmodel : ‖(∫ t in l..u, g t) - M‖ ≤ 4 * h ^ 4 / a ^ 2 + 40 * a / h :=
    norm_integral_entropy_sub_stationary_value_le ha0 hh hha hl hlh hhu hu
  have hunit : bourgainOscillation (Real.pi / 4) * bourgainOscillation (-(Real.pi / 4)) = 1 := by
    unfold bourgainOscillation
    rw [← Complex.exp_add]
    have he : I * ((Real.pi / 4 : ℝ) : ℂ) + I * ((-(Real.pi / 4) : ℝ) : ℂ) = 0 := by
      push_cast
      ring
    rw [he, Complex.exp_zero]
  have hmain : c * M = bourgainOscillation a * (Real.sqrt (2 * Real.pi * a) : ℂ) := by
    dsimp only [c, M]
    calc
      _ = (bourgainOscillation (Real.pi / 4) * bourgainOscillation (-(Real.pi / 4))) *
          (bourgainOscillation a * (Real.sqrt (2 * Real.pi * a) : ℂ)) := by ring
      _ = _ := by rw [hunit, one_mul]
  change ‖(∫ t in l..u, f t) - bourgainOscillation a * (Real.sqrt (2 * Real.pi * a) : ℂ)‖ ≤ _
  rw [← hmain]
  calc
    _ = ‖((∫ t in l..u, f t) - c * (∫ t in l..u, g t)) +
        c * ((∫ t in l..u, g t) - M)‖ := by congr 1; ring
    _ ≤ ‖(∫ t in l..u, f t) - c * (∫ t in l..u, g t)‖ +
        ‖c * ((∫ t in l..u, g t) - M)‖ := norm_add_le _ _
    _ = ‖(∫ t in l..u, f t) - c * (∫ t in l..u, g t)‖ +
        ‖(∫ t in l..u, g t) - M‖ := by rw [norm_mul, hc, one_mul]
    _ ≤ 78 + (4 * h ^ 4 / a ^ 2 + 40 * a / h) := add_le_add hdiff hmodel
    _ = _ := by ring

end RHTower
