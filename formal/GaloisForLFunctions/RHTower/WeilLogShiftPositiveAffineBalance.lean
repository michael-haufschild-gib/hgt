import GaloisForLFunctions.RHTower.WeilLogShiftPositiveResponseBalance

/-!
# Positive weighted balance across every regular affine fibre

One positive parity-adjusted normal, depending only on the finite index list,
is constant on each regular amplitude fibre for every bounded center history.
At the arithmetic anchor its value is zero. Nonzero balance there certifies
failure of every finite factorial majorant and summability normalization.
-/

noncomputable section

open Real
open scoped BoundedContinuousFunction

namespace RHTower

/-- Differences of finite affine-error moments are exactly the finite
column response of the amplitude difference, with the center removed. -/
theorem weilLogShiftFiniteImpulse_moment_sub {d : ℕ} (indices : Fin d → ℕ)
    (center : ℕ →ᵇ ℝ) (a b : Fin d → ℝ) (y : ℝ) (n : ℕ) :
    weilLogShiftRecoveryMoment y (center + weilLogShiftFiniteImpulseMap indices a : ℕ →ᵇ ℝ) n -
      weilLogShiftRecoveryMoment y (center + weilLogShiftFiniteImpulseMap indices b : ℕ →ᵇ ℝ) n =
      ∑ i, (a i - b i) * weilLogShiftRecoveryMomentResponse y n (indices i) := by
  calc
    _ = weilLogShiftRecoveryMomentCLM y n
        ((center + weilLogShiftFiniteImpulseMap indices a) -
          (center + weilLogShiftFiniteImpulseMap indices b)) :=
      weilLogShiftRecoveryMoment_sub_eq y n _ _
    _ = weilLogShiftRecoveryMomentCLM y n (weilLogShiftFiniteImpulseMap indices (a - b)) := by
      congr 1
      rw [map_sub]
      abel
    _ = _ := by
      change weilLogShiftRecoveryMomentCLM y n
        (∑ i, (a i - b i) • weilLogShiftRecoveryUnitHistory (indices i)) = _
      simp only [map_sum, map_smul, smul_eq_mul, weilLogShiftRecoveryMomentResponse]

/-- Every finite all-late list has one strictly positive parity-adjusted
normal valid for every bounded center. Its value is constant on each fibre
admitting any factorial-regular shift, and is zero at the arithmetic anchor. -/
theorem exists_weilLogShiftFiniteImpulse_positive_affine_balance :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (d : ℕ) (indices : Fin d → ℕ),
      (∀ i, K ≤ indices i) → ∃ w : Fin d → ℝ, (∀ i, 0 < w i) ∧
      (∀ a : Fin d → ℝ, (∃ y : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment y
          (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a : ℕ →ᵇ ℝ))) →
        ∑ i, w i * (-1 : ℝ) ^ indices i * a i = 0) ∧
      ∀ center : ℕ →ᵇ ℝ, ∃ c : ℝ, ∀ a : Fin d → ℝ,
        (∃ y : ℝ, WeilLogShiftHasFactorialMajorant
          (weilLogShiftRecoveryMoment y
            (center + weilLogShiftFiniteImpulseMap indices a : ℕ →ᵇ ℝ))) →
        ∑ i, w i * (-1 : ℝ) ^ indices i * a i = c := by
  obtain ⟨K, hK, hbalance⟩ := exists_weilLogShiftFiniteImpulse_positive_response_balance
  refine ⟨K, hK, ?_⟩
  intro d indices hk
  obtain ⟨w, hw, hann⟩ := hbalance d indices hk
  refine ⟨w, hw, ?_, ?_⟩
  · intro a ha
    apply hann a
    have h0 := (weilLogShiftHasFactorialMajorant_some_shift_iff_origin
      (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a)).mp ha
    have heq : weilLogShiftRecoveryMoment 0
        (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a : ℕ →ᵇ ℝ) =
        (fun n => ∑ i, a i * weilLogShiftRecoveryMomentResponse 0 n (indices i)) := by
      funext n
      exact weilLogShiftFiniteImpulse_moment_arithmetic indices a 0 n
    rwa [heq] at h0
  · intro center
    by_cases hex : ∃ a : Fin d → ℝ, ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
        (weilLogShiftRecoveryMoment y
          (center + weilLogShiftFiniteImpulseMap indices a : ℕ →ᵇ ℝ))
    · obtain ⟨a₀, ha₀⟩ := hex
      refine ⟨∑ i, w i * (-1 : ℝ) ^ indices i * a₀ i, ?_⟩
      intro a ha
      have h0 := (weilLogShiftHasFactorialMajorant_some_shift_iff_origin
        (center + weilLogShiftFiniteImpulseMap indices a)).mp ha
      have h0' := (weilLogShiftHasFactorialMajorant_some_shift_iff_origin
        (center + weilLogShiftFiniteImpulseMap indices a₀)).mp ha₀
      have hdiff := weilLogShiftHasFactorialMajorant_sub h0 h0'
      have heq :
          (fun n => weilLogShiftRecoveryMoment 0
            (center + weilLogShiftFiniteImpulseMap indices a : ℕ →ᵇ ℝ) n -
            weilLogShiftRecoveryMoment 0
              (center + weilLogShiftFiniteImpulseMap indices a₀ : ℕ →ᵇ ℝ) n) =
          (fun n => ∑ i, (a i - a₀ i) *
            weilLogShiftRecoveryMomentResponse 0 n (indices i)) := by
        funext n
        exact weilLogShiftFiniteImpulse_moment_sub indices center a a₀ 0 n
      rw [heq] at hdiff
      have hz := hann (a - a₀) hdiff
      simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib] at hz
      exact sub_eq_zero.mp hz
    · refine ⟨0, ?_⟩
      intro a ha
      exact (hex ⟨a, ha⟩).elim

/-- A nonzero value of the positive balance functional certifies failure
of every factorial majorant and every factorial/exponential summability
normalization at every shift of the arithmetic-anchor finite perturbation. -/
theorem exists_weilLogShiftFiniteImpulse_positive_balance_obstruction :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (d : ℕ) (indices : Fin d → ℕ),
      (∀ i, K ≤ indices i) → ∃ w : Fin d → ℝ, (∀ i, 0 < w i) ∧
      ∀ a : Fin d → ℝ, (∑ i, w i * (-1 : ℝ) ^ indices i * a i) ≠ 0 → ∀ y : ℝ,
        (¬ WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment y
          (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a : ℕ →ᵇ ℝ))) ∧
        ∀ (m : ℕ) (A : ℝ), ¬ Summable (fun n : ℕ => exp (-(A * n)) *
          weilLogShiftRecoveryMoment y
            (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a : ℕ →ᵇ ℝ) n /
              (n.factorial : ℝ) ^ m) := by
  obtain ⟨K, hK, hbalance⟩ := exists_weilLogShiftFiniteImpulse_positive_affine_balance
  refine ⟨K, hK, ?_⟩
  intro d indices hk
  obtain ⟨w, hw, hanchor, _⟩ := hbalance d indices hk
  refine ⟨w, hw, ?_⟩
  intro a hne y
  have hno : ¬ WeilLogShiftHasFactorialMajorant (weilLogShiftRecoveryMoment y
      (weilLogShiftArithmeticHistoryBCF + weilLogShiftFiniteImpulseMap indices a : ℕ →ᵇ ℝ)) :=
    fun hreg => hne (hanchor a ⟨y, hreg⟩)
  refine ⟨hno, ?_⟩
  intro m A hs
  exact hno (weilLogShiftHasFactorialMajorant_of_summable_normalization _ m A hs)

end RHTower
