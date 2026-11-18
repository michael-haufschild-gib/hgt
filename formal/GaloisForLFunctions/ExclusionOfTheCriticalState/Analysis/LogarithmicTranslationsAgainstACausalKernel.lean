import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Logarithmic integer translations against a causal test

Exponential confinement at the negative end makes every bounded causal test
absolutely interchangeable with an integer row of finite inverse-square mass.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Integer translates of a real profile with scalar weights. -/
def logShiftWave (b : ℕ → ℝ) (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, b n * Φ (t-Real.log n)

private theorem translate_bound {b : ℕ → ℝ} (h0 : b 0 = 0) {Φ : ℝ → ℝ} {C : ℝ}
    (hΦ : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (n : ℕ) (t : ℝ) :
    |b n * Φ (t-Real.log n)| ≤ (|b n|/(n:ℝ)^2)*(C*Real.exp (2*t)) := by
  cases n with
  | zero => simp [h0]
  | succ n =>
    rw [abs_mul]
    apply (mul_le_mul_of_nonneg_left (hΦ _) (abs_nonneg _)).trans_eq
    rw [mul_sub,Real.exp_sub,two_mul (Real.log _),Real.exp_add,Real.exp_log (by positivity : (0:ℝ)<(n.succ:ℝ))]
    ring

/-- Move the integer translations from the confined profile onto a bounded test
supported on the positive ray. Both integrals are absolutely convergent. -/
theorem integral_logShiftWave_mul_causal {b : ℕ → ℝ} (h0 : b 0 = 0)
    (hs : Summable (fun n : ℕ => |b n|/(n:ℝ)^2)) {Φ : ℝ → ℝ} (hm : Measurable Φ)
    {C : ℝ} (hC : 0 ≤ C) (hc : ∀ u, |Φ u| ≤ C*Real.exp (2*u))
    {K : ℝ → ℂ} (hK : Measurable K) (hk : ∀ v, v < 0 → K v = 0)
    {B : ℝ} (hb : ∀ v, ‖K v‖ ≤ B) (T : ℝ) :
    Integrable (fun t => (logShiftWave b Φ t : ℂ)*K (T-t)) ∧
    Integrable (fun u => (Φ u : ℂ)*(∑' n : ℕ, (b n : ℂ)*K (T-u-Real.log n))) ∧
    (∫ t, (logShiftWave b Φ t : ℂ)*K (T-t)) =
      ∫ u, (Φ u : ℂ)*(∑' n : ℕ, (b n : ℂ)*K (T-u-Real.log n)) := by
  let G := fun n : ℕ => fun t : ℝ => ((b n * Φ (t-Real.log n):ℝ):ℂ)*K (T-t)
  let H := fun t : ℝ => (Iic T).indicator (fun r : ℝ => Real.exp (2*r)) t
  let m := fun n : ℕ => |b n|/(n:ℝ)^2*(C*B)
  have hH : Integrable H := (integrable_indicator_iff measurableSet_Iic).2
    (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<2) T)
  have hmeas (n : ℕ) : Measurable (G n) := by dsimp only [G]; fun_prop
  have hbound (n : ℕ) (t : ℝ) : ‖G n t‖ ≤ m n*H t := by
    dsimp only [G]
    by_cases ht : t ≤ T
    · rw [show H t = Real.exp (2*t) from indicator_of_mem (show t ∈ Iic T from ht) _,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply (mul_le_mul (translate_bound h0 hc n t) (hb _) (norm_nonneg _) (by positivity)).trans_eq
      dsimp only [m]; ring
    · rw [hk _ (sub_neg.2 (lt_of_not_ge ht)),mul_zero,norm_zero,
        show H t = 0 from indicator_of_notMem (show t ∉ Iic T from ht) _,mul_zero]
  have hi (n : ℕ) : Integrable (G n) := (hH.const_mul (m n)).mono' (hmeas n).aestronglyMeasurable
    (Eventually.of_forall (hbound n))
  have hsG : Summable (fun n => ∫ t, ‖G n t‖) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) _ ((hs.mul_right (C*B)).mul_right (∫ t, H t))
    intro n
    rw [← integral_const_mul]
    exact integral_mono (hi n).norm (hH.const_mul _) (hbound n)
  let Q := fun n : ℕ => fun u : ℝ => G n (u+Real.log n)
  have hiQ (n : ℕ) : Integrable (Q n) := (hi n).comp_add_right _
  have he (n : ℕ) : (∫ u, Q n u) = ∫ t, G n t := integral_add_right_eq_self (G n) (Real.log n)
  have heN (n : ℕ) : (∫ u, ‖Q n u‖) = ∫ t, ‖G n t‖ := integral_add_right_eq_self (fun t => ‖G n t‖) (Real.log n)
  have hl (t : ℝ) : (logShiftWave b Φ t : ℂ)*K (T-t) = ∑' n, G n t := by
    rw [logShiftWave,Complex.ofReal_tsum,← tsum_mul_right]
  have hr (u : ℝ) : (Φ u : ℂ)*(∑' n : ℕ, (b n:ℂ)*K (T-u-Real.log n)) = ∑' n, Q n u := by
    rw [← tsum_mul_left]
    apply tsum_congr fun n => ?_
    simp only [Q,G,add_sub_cancel_right,Complex.ofReal_mul]
    rw [show T-(u+Real.log n)=T-u-Real.log n by ring]; ring
  have hsQ := hsG.congr fun n => (heN n).symm
  simp_rw [hl,hr]
  refine ⟨HTGeometry.integrable_tsum_of_summable_integral_norm hi hsG,
    HTGeometry.integrable_tsum_of_summable_integral_norm hiQ hsQ,?_⟩
  rw [← integral_tsum_of_summable_integral_norm hi hsG,
    ← integral_tsum_of_summable_integral_norm hiQ hsQ]
  exact tsum_congr fun n => (he n).symm

#print axioms integral_logShiftWave_mul_causal

end GaloisForLFunctions.ExclusionOfTheCriticalState
