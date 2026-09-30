import GaloisForLFunctions.RHTower.SteinhausEulerVerticalBarrier
import GaloisForLFunctions.RHTower.SteinhausEulerGlobalEnvelope

/-!
# The actual variance-selected global spatial barrier

BAG C20.12. Select concrete cofinal cutoffs using the proved divergence of the
actual tilted variance. The proved global envelope enforces the logarithmic-variance
barrier simultaneously over all selected cutoffs and the full unit vertical segment.
The original probability of the single exceptional event has an explicit exponential
bound. No quantitative variance clock or unproved probabilistic estimate is used.
-/

open Complex Filter MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
namespace RHTower
open SteinhausModel

private theorem exists_variance_selected_cutoff (j : ℕ) :
    ∃ N : ℕ, j + 3 ≤ N ∧ (2 : ℝ) ^ j ≤ steinhausEulerTiltVariance N := by
  have hdiv : Tendsto steinhausEulerTiltVariance atTop atTop :=
    tendsto_integral_sq_steinhausEulerTiltPrimeSum_atTop
  obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp hdiv ((2 : ℝ) ^ j)
  exact ⟨max K (j + 3), le_max_right _ _, hK _ (le_max_left _ _)⟩

/-- The least actual cutoff meeting both the cofinality and exponential-variance requirements. -/
def steinhausEulerBarrierCutoff (j : ℕ) : ℕ :=
  Nat.find (exists_variance_selected_cutoff j)

theorem steinhausEulerBarrierCutoff_spec (j : ℕ) :
    j + 3 ≤ steinhausEulerBarrierCutoff j ∧
      (2 : ℝ) ^ j ≤ steinhausEulerTiltVariance (steinhausEulerBarrierCutoff j) :=
  Nat.find_spec (exists_variance_selected_cutoff j)

theorem tendsto_steinhausEulerBarrierCutoff : Tendsto steinhausEulerBarrierCutoff atTop atTop := by
  apply tendsto_atTop_mono (f := fun j : ℕ => j) _ tendsto_id
  intro j
  have := (steinhausEulerBarrierCutoff_spec j).1
  omega

private theorem barrierCutoff_ge_three (j : ℕ) : 3 ≤ steinhausEulerBarrierCutoff j := by
  have := (steinhausEulerBarrierCutoff_spec j).1
  omega

/-- A bounded global envelope enforces the actual logarithmic-variance barrier at all spatial points. -/
theorem steinhausEulerLogField_le_of_globalEnvelope (A : ℝ) (ω : Omega)
    (hω : steinhausEulerGlobalEnvelope steinhausEulerBarrierCutoff ω ≤ ENNReal.ofReal (Real.exp (2 * A)))
    (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    Real.log ‖steinhausFiniteEulerProduct (Nat.primesBelow (steinhausEulerBarrierCutoff j))
      ((1 / 2 : ℂ) + (t : ℂ) * I) ω‖ -
        Real.log (steinhausEulerPartition (Nat.primesBelow (steinhausEulerBarrierCutoff j)) (1 / 2)) ≤
      A + 2 * Real.log (1 + steinhausEulerTiltVariance (steinhausEulerBarrierCutoff j)) := by
  let N := steinhausEulerBarrierCutoff j
  let M := steinhausEulerPartition (Nat.primesBelow N) (1 / 2)
  let V := steinhausEulerTiltVariance N
  let F := steinhausFiniteEulerProduct (Nat.primesBelow N) ((1 / 2 : ℂ) + (t : ℂ) * I) ω
  have hM : 0 < M := steinhausEulerPartition_pos _
    (fun _ hp => (Nat.mem_primesBelow.mp hp).2) (by norm_num)
  have hV : (2 : ℝ) ^ j ≤ V := (steinhausEulerBarrierCutoff_spec j).2
  have hV1 : 1 ≤ V := (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)).trans hV
  have hVp : 0 < 1 + V := by linarith
  have hqE := (norm_sq_le_steinhausEulerGlobalEnvelope steinhausEulerBarrierCutoff
    barrierCutoff_ge_three ω j ht).trans (mul_le_mul_right hω _)
  have hq : ‖F‖ ^ 2 ≤ M ^ 2 * (2 : ℝ) ^ (j + 1) * Real.exp (2 * A) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    calc
      _ ≤ ENNReal.ofReal (M ^ 2) * (2 : ℝ≥0∞) ^ (j + 1) * ENNReal.ofReal (Real.exp (2 * A)) := hqE
      _ = _ := by
        rw [ENNReal.ofReal_mul (p := M ^ 2 * (2 : ℝ) ^ (j + 1)) (by positivity),
          ENNReal.ofReal_mul (sq_nonneg M),
          ENNReal.ofReal_pow (p := 2) (by norm_num) (j + 1)]
        norm_num
  have hpow : (2 : ℝ) ^ (j + 1) ≤ (1 + V) ^ 4 := by
    have hpoly : 2 * V ≤ (1 + V) ^ 2 := by nlinarith [sq_nonneg V]
    have hpoly' : (1 + V) ^ 2 ≤ (1 + V) ^ 4 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    calc
      _ = 2 * (2 : ℝ) ^ j := by rw [pow_succ]; ring
      _ ≤ 2 * V := mul_le_mul_of_nonneg_left hV (by norm_num)
      _ ≤ _ := hpoly.trans hpoly'
  have hsq : ‖F‖ ^ 2 ≤ (M * Real.exp A * (1 + V) ^ 2) ^ 2 := by
    calc
      _ ≤ M ^ 2 * (2 : ℝ) ^ (j + 1) * Real.exp (2 * A) := hq
      _ ≤ M ^ 2 * (1 + V) ^ 4 * Real.exp (2 * A) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (sq_nonneg M)) (Real.exp_pos _).le
      _ = _ := by rw [show 2 * A = A + A by ring, Real.exp_add]; ring
  have hFpos : 0 < ‖F‖ := by
    dsimp only [F]
    rw [steinhausFiniteEulerProduct_eq_exp _ (fun _ hp => (Nat.mem_primesBelow.mp hp).2)
      (by norm_num), Complex.norm_exp]
    exact Real.exp_pos _
  have hlog := Real.log_le_log hFpos ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq)
  rw [Real.log_mul (mul_ne_zero hM.ne' (Real.exp_ne_zero _)) (pow_ne_zero 2 hVp.ne'),
    Real.log_mul hM.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_pow] at hlog
  change Real.log ‖F‖ - Real.log M ≤ A + 2 * Real.log (1 + V)
  norm_num at hlog
  linarith

/-- Every finite spatial barrier holds on the same single good event. -/
theorem mem_steinhausEulerSpatialFiniteBarrier_of_globalEnvelope (A : ℝ) (ω : Omega)
    (hω : steinhausEulerGlobalEnvelope steinhausEulerBarrierCutoff ω ≤ ENNReal.ofReal (Real.exp (2 * A)))
    (J : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ω ∈ steinhausEulerSpatialFiniteBarrier steinhausEulerBarrierCutoff A J t := by
  intro j _hj
  exact steinhausEulerLogField_le_of_globalEnvelope A ω hω j ht

/-- The exceptional-event estimate for the actual variance-selected sequence. -/
theorem measure_steinhausEulerBarrier_bad_le (A : ℝ) :
    steinhausMeasure {ω | ENNReal.ofReal (Real.exp (2 * A)) ≤
      steinhausEulerGlobalEnvelope steinhausEulerBarrierCutoff ω} ≤
      ENNReal.ofReal (steinhausEulerGlobalEnvelopeConstant * Real.exp (-(2 * A))) := by
  have h := measure_steinhausEulerGlobalEnvelope_ge_le steinhausEulerBarrierCutoff
    barrierCutoff_ge_three (Real.exp_pos (2 * A))
  simpa only [Real.exp_neg, div_eq_mul_inv] using h

end RHTower
