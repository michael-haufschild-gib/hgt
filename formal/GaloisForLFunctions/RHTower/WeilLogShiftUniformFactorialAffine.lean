import GaloisForLFunctions.RHTower.WeilLogShiftUniformFactorialLinear

/-!
# A fixed factorial normalization for a whole finite affine family

Homogenization turns an affine sequence map into a linear map with one
extra real coordinate. The regular-submodule theorem then selects a single
normalization for the whole affine regular fibre, including empty fibres.
-/

noncomputable section

open Real
open scoped BoundedContinuousFunction

namespace RHTower

/-- A finite-dimensional affine family has one fixed factorial normalization
detecting exactly its regular amplitudes, with a uniform affine norm bound
on the absolute normalized sums. -/
theorem exists_weilLogShift_uniform_affine_factorial_normalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E →ᵃ[ℝ] (ℕ → ℝ)) :
    ∃ (m : ℕ) (B C : ℝ), 0 < B ∧ 0 ≤ C ∧
      (∀ a : E, WeilLogShiftHasFactorialMajorant (F a) ↔
        Summable (fun n : ℕ => exp (-(B * n)) * F a n / (n.factorial : ℝ) ^ m)) ∧
      ∀ a : E, WeilLogShiftHasFactorialMajorant (F a) →
        (∑' n : ℕ, |exp (-(B * n)) * F a n / (n.factorial : ℝ) ^ m|) ≤ C * (1 + ‖a‖) := by
  let H : (E × ℝ) →ₗ[ℝ] (ℕ → ℝ) :=
    F.linear.comp (LinearMap.fst ℝ E ℝ) + (LinearMap.snd ℝ E ℝ).smulRight (F 0)
  have heq (a : E) : H (a, 1) = F a := by
    change F.linear a + (1 : ℝ) • F 0 = F a
    simpa only [one_smul, vadd_eq_add, add_zero] using (F.map_vadd (0 : E) a).symm
  obtain ⟨m, B, C, hB, hC, hiff, hbound⟩ :=
    exists_weilLogShift_uniform_linear_factorial_normalization H
  refine ⟨m, B, C, hB, hC, ?_, ?_⟩
  · intro a
    simpa only [heq] using hiff (a, 1)
  · intro a ha
    have hreg : WeilLogShiftHasFactorialMajorant (H (a, 1)) := by rwa [heq]
    have h := hbound (a, 1) hreg
    rw [heq] at h
    have hn : ‖(a, (1 : ℝ))‖ ≤ 1 + ‖a‖ := by
      rw [Prod.norm_def, norm_one]
      exact max_le (by linarith [norm_nonneg a]) (by linarith [norm_nonneg a])
    exact h.trans (mul_le_mul_of_nonneg_left hn hC)

/-- Every finite-dimensional bounded-history family has one origin
normalization equivalent to existence of any factorial-regular shift.
The order, rate, and absolute-sum constant are fixed before every amplitude.
Finite impulse lists are obtained by taking `T = weilLogShiftFiniteImpulseMap indices`. -/
theorem exists_weilLogShift_uniform_history_factorial_normalization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (center : ℕ →ᵇ ℝ) (T : E →ₗ[ℝ] (ℕ →ᵇ ℝ)) :
    ∃ (m : ℕ) (B C : ℝ), 0 < B ∧ 0 ≤ C ∧
      (∀ a : E, (∃ y : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))) ↔
        Summable (fun n : ℕ => exp (-(B * n)) *
          weilLogShiftRecoveryMoment 0 (center + T a : ℕ →ᵇ ℝ) n / (n.factorial : ℝ) ^ m)) ∧
      ∀ a : E, (∃ y : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment y (center + T a : ℕ →ᵇ ℝ))) →
        (∑' n : ℕ, |exp (-(B * n)) *
          weilLogShiftRecoveryMoment 0 (center + T a : ℕ →ᵇ ℝ) n / (n.factorial : ℝ) ^ m|) ≤
            C * (1 + ‖a‖) := by
  obtain ⟨m, B, C, hB, hC, hiff, hbound⟩ :=
    exists_weilLogShift_uniform_affine_factorial_normalization
      (weilLogShiftRecoveryAmplitudeMoment center T)
  refine ⟨m, B, C, hB, hC, ?_, ?_⟩
  · intro a
    exact (weilLogShiftHasFactorialMajorant_some_shift_iff_origin (center + T a)).trans (hiff a)
  · intro a ha
    exact hbound a
      ((weilLogShiftHasFactorialMajorant_some_shift_iff_origin (center + T a)).mp ha)

end RHTower
