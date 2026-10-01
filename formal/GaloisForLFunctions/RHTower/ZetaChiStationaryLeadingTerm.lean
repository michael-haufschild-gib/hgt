import GaloisForLFunctions.RHTower.ZetaChiStationaryIntegralModel
import GaloisForLFunctions.RHTower.ChiStationaryEntropyIntegral

open Complex MeasureTheory Set
noncomputable section
namespace RHTower

/-- A full stationary leading term for the actual chi factor, with one
common unit and a remainder retaining both exterior segments. -/
theorem exists_zetaChi_stationary_leading_term :
    ∃ κ : ℂ, ‖κ‖ = 1 ∧ ∀ a h l u : ℝ, 8 ≤ a → 0 < h → h ≤ a / 2 →
      a / 2 ≤ l → l ≤ a - h → a + h ≤ u → u ≤ 2 * a →
      ‖(∫ t in l..u, zetaChi (linePt t) *
          bourgainOscillation (t * Real.log (a / (2 * Real.pi)))) -
        κ * bourgainOscillation a * ((Real.sqrt (2 * Real.pi * a) : ℂ) *
          bourgainOscillation (-(Real.pi / 4)))‖ ≤
        78 + 4 * h ^ 4 / a ^ 2 + 40 * a / h := by
  obtain ⟨κ, hκ, hglobal⟩ := exists_zetaChi_stationary_integral_model
  refine ⟨κ, hκ, ?_⟩
  intro a h l u ha hh hha hl hlh hhu hu
  have ha0 : 0 < a := by linarith
  have hl0 : 0 < l := by linarith
  have hlu : l ≤ u := by linarith
  let F : ℝ → ℂ := fun t => zetaChi (linePt t) *
    bourgainOscillation (t * Real.log (a / (2 * Real.pi)))
  let K : ℝ → ℂ := fun t => bourgainOscillation (-chiStationaryEntropy a t)
  let M : ℂ := (Real.sqrt (2 * Real.pi * a) : ℂ) * bourgainOscillation (-(Real.pi / 4))
  let c : ℂ := κ * bourgainOscillation a
  have hc : ‖c‖ = 1 := by rw [norm_mul, hκ, norm_bourgainOscillation, mul_one]
  have hf : Continuous F := by
    convert continuous_zetaChiCriticalTwistIntegrand (Real.log (a / (2 * Real.pi))) using 1
    funext t
    dsimp only [F, bourgainOscillation]
    congr 1
    congr 1
    push_cast
    ring
  have hiF : IntervalIntegrable F volume l u := hf.intervalIntegrable l u
  have hiK : IntervalIntegrable K volume l u := intervalIntegrable_chiStationaryEntropy_neg a hl0 hlu
  have hphase (t : ℝ) (ht : t ∈ Set.uIcc l u) :
      κ * bourgainOscillation (t - t * Real.log (t / a)) = c * K t := by
    rw [Set.uIcc_of_le hlu] at ht
    have ht0 : 0 < t := hl0.trans_le ht.1
    dsimp only [c, K]
    rw [mul_assoc]
    congr 1
    unfold bourgainOscillation chiStationaryEntropy
    rw [← Complex.exp_add, Real.log_div ht0.ne' ha0.ne']
    congr 1
    push_cast
    ring
  have he : (∫ t in l..u, zetaChi (linePt t) *
        bourgainOscillation (t * Real.log (a / (2 * Real.pi))) -
        κ * bourgainOscillation (t - t * Real.log (t / a))) =
      (∫ t in l..u, F t) - c * ∫ t in l..u, K t := by
    calc
      _ = ∫ t in l..u, F t - c * K t :=
        intervalIntegral.integral_congr (fun t ht => by rw [hphase t ht])
      _ = _ := by rw [intervalIntegral.integral_sub hiF (hiK.const_mul c), intervalIntegral.integral_const_mul]
  have herror := hglobal a l u ha hl hlu hu
  rw [he] at herror
  have hmodel := norm_integral_entropy_sub_stationary_value_le ha0 hh hha hl hlh hhu hu
  have hm : ‖c * (∫ t in l..u, K t) - c * M‖ ≤ 4 * h ^ 4 / a ^ 2 + 40 * a / h := by
    rw [← mul_sub, norm_mul, hc, one_mul]
    exact hmodel
  change ‖(∫ t in l..u, F t) - c * M‖ ≤ _
  calc
    _ = ‖((∫ t in l..u, F t) - c * ∫ t in l..u, K t) +
        (c * (∫ t in l..u, K t) - c * M)‖ := by congr 1; ring
    _ ≤ ‖(∫ t in l..u, F t) - c * ∫ t in l..u, K t‖ +
        ‖c * (∫ t in l..u, K t) - c * M‖ := norm_add_le _ _
    _ ≤ 78 + (4 * h ^ 4 / a ^ 2 + 40 * a / h) := add_le_add herror hm
    _ = _ := by ring

end RHTower
