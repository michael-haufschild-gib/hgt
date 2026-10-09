import GaloisForLFunctions.RHTower.WeilLogShiftUniformKernelComparison
import GaloisForLFunctions.RHTower.WeilLogShiftUniformFactorialLinear

/-!
# One factorial normalization for every amplitude and every real shift

The regular locus of a finite-dimensional affine history family admits one
global factorial envelope across the entire real shift line. One fixed
normalization detects this locus at every shift and gives an absolute-sum
bound uniform in shift and controlled by the amplitude norm.
-/

open Real
open scoped BoundedContinuousFunction

noncomputable section

namespace RHTower

/-- A finite-dimensional affine sequence family has a common global
factorial envelope on its actual regular locus. -/
theorem exists_weilLogShift_uniform_affine_factorial_envelope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E →ᵃ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (A D : ℝ), 0 < A ∧ 0 ≤ D ∧
      ∀ a : E, WeilLogShiftHasFactorialMajorant (F a) → ∀ n : ℕ,
        |F a n| ≤ D * (1 + ‖a‖) * exp (A * n) * (n.factorial : ℝ) ^ m := by
  let H : (E × ℝ) →ₗ[ℝ] (ℕ → ℝ) :=
    F.linear.comp (LinearMap.fst ℝ E ℝ) + (LinearMap.snd ℝ E ℝ).smulRight (F 0)
  have heq (a : E) : H (a, 1) = F a := by
    change F.linear a + (1 : ℝ) • F 0 = F a
    simpa only [one_smul, vadd_eq_add, add_zero] using (F.map_vadd (0 : E) a).symm
  obtain ⟨m, A, D, hA, hD, hbound⟩ :=
    exists_weilLogShiftFactorialMajorant_uniform_linear_envelope H
  refine ⟨m, A, D, hA, hD, fun a ha n => ?_⟩
  have hreg : WeilLogShiftHasFactorialMajorant (H (a, 1)) := by rwa [heq]
  have h := hbound (a, 1) hreg n
  rw [heq] at h
  have hn : ‖(a, (1 : ℝ))‖ ≤ 1 + ‖a‖ := by
    rw [Prod.norm_def, norm_one]
    exact max_le (by linarith [norm_nonneg a]) (by linarith [norm_nonneg a])
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hD) (exp_pos _).le)
    (by positivity))

/-- One global factorial envelope controls every regular amplitude and
every real shift of a finite-dimensional affine bounded-history family. -/
theorem exists_weilLogShift_all_shift_uniform_history_factorial_envelope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) :
    ∃ (m : ℕ) (A D : ℝ), 0 < A ∧ 0 ≤ D ∧
      ∀ a : E, (∃ c : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment c (center + T a : ℕ →ᵇ ℝ))) →
      ∀ (y : ℝ) (n : ℕ),
        |weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ) n| ≤
          D * (1 + ‖a‖) * exp (A * n) * (n.factorial : ℝ) ^ m := by
  obtain ⟨m, A, D, hA, hD, hbound⟩ :=
    exists_weilLogShift_uniform_affine_factorial_envelope
      (weilLogShiftRecoveryAmplitudeMoment center T)
  obtain ⟨b, K, hb, hK, hcompare⟩ := exists_kernelPotential_uniform_exponential_comparison 0
  refine ⟨m, A + b, K * D, add_pos hA hb, mul_nonneg hK.le hD, fun a ha y n => ?_⟩
  have hsource : |weilLogShiftRecoveryMoment 0 (center + T a : ℕ →ᵇ ℝ) n| ≤
      D * (1 + ‖a‖) * exp (A * n) * (n.factorial : ℝ) ^ m :=
    hbound a ((weilLogShiftHasFactorialMajorant_some_shift_iff_origin (center + T a)).mp ha) n
  calc
    _ ≤ K * exp (b * n) * |weilLogShiftRecoveryMoment 0 (center + T a : ℕ →ᵇ ℝ) n| :=
      hcompare (WeilExcess.weilDeviation (weilLogShiftRecoveryInverse (center + T a : ℕ →ᵇ ℝ))) y n
    _ ≤ K * exp (b * n) *
        (D * (1 + ‖a‖) * exp (A * n) * (n.factorial : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = _ := by rw [add_mul, exp_add]; ring

/-- A single normalization detects the regular locus at each real shift,
with a common absolute-sum bound across all shifts and regular amplitudes. -/
theorem exists_weilLogShift_all_shift_uniform_history_factorial_normalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) :
    ∃ (m : ℕ) (B C : ℝ), 0 < B ∧ 0 ≤ C ∧
      (∀ (a : E) (y : ℝ), (∃ c : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment c (center + T a : ℕ →ᵇ ℝ))) ↔
        Summable (fun n : ℕ => exp (-(B * n)) *
          weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ) n / (n.factorial : ℝ) ^ m)) ∧
      ∀ a : E, (∃ c : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment c (center + T a : ℕ →ᵇ ℝ))) → ∀ y : ℝ,
        (∑' n : ℕ, |exp (-(B * n)) *
          weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ) n / (n.factorial : ℝ) ^ m|) ≤
            C * (1 + ‖a‖) := by
  obtain ⟨m, A, D, hA, hD, hbound⟩ :=
    exists_weilLogShift_all_shift_uniform_history_factorial_envelope center T
  let S : ℝ := ∑' n : ℕ, exp (-(n : ℝ))
  have hS : 0 ≤ S := tsum_nonneg (fun n => (exp_pos _).le)
  refine ⟨m, A + 1, D * S, by linarith, mul_nonneg hD hS, ?_, ?_⟩
  · intro a y
    constructor
    · intro ha
      exact (weilLogShift_factorial_normalization_summable_bound
        (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ)) m A (D * (1 + ‖a‖))
        (hbound a ha y)).1
    · intro hs
      exact ⟨y, weilLogShiftHasFactorialMajorant_of_summable_normalization
        (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ)) m (A + 1) hs⟩
  · intro a ha y
    have h := (weilLogShift_factorial_normalization_summable_bound
      (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ)) m A (D * (1 + ‖a‖))
      (hbound a ha y)).2
    simpa only [S, mul_assoc, mul_left_comm, mul_comm] using h

end RHTower
