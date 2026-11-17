import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing

/-!
# Proper-power contacts in a window of fixed multiplicative width

In a window from Q/D² to Q the normalized contact weight Λ(k)/√k of
all proper powers has bounded total mass, uniformly in the top degree Q.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticFunction
open scoped ArithmeticFunction.vonMangoldt

/-- A packet may use any subset of the proper powers in the window. -/
theorem properPowerContactWindow_le (S : Finset ℕ) {Q : ℕ} {D : ℝ}
    (hD : 0 ≤ D) (hS : ∀ k ∈ S, 0 < k ∧ k ≤ Q ∧ ¬ k.Prime ∧ (Q : ℝ) ≤ D^2 * k) :
    ∑ k ∈ S, Λ k / Real.sqrt k ≤ 3 * (Real.log 4 + 4) * D := by
  have hC : 0 ≤ 3 * (Real.log 4 + 4) := by positivity
  by_cases hQ : Q = 0
  · have h : S = ∅ := eq_empty_iff_forall_notMem.mpr fun k hk =>
      (Nat.not_lt_zero k) (lt_of_lt_of_le (hS k hk).1 (by simpa [hQ] using (hS k hk).2.1))
    simpa [h] using mul_nonneg hC hD
  have hr : 0 < Real.sqrt Q := Real.sqrt_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ))
  have hsub : S ⊆ (Ioc 0 Q).filter (fun k => ¬ k.Prime) := by
    intro k hk
    obtain ⟨hk0, hkQ, hkp, _⟩ := hS k hk
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hk0, hkQ⟩, hkp⟩
  have hmass : ∑ k ∈ S, Λ k ≤ 3 * (Real.log 4 + 4) * Real.sqrt Q := by
    calc ∑ k ∈ S, Λ k ≤ ∑ k ∈ (Ioc 0 Q).filter (fun k => ¬ k.Prime), Λ k :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => vonMangoldt_nonneg
      _ = Chebyshev.psi Q - Chebyshev.theta Q := by
          rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
      _ ≤ _ := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt _
  apply (le_div_iff₀' hr).mp
  rw [Finset.mul_sum]
  calc ∑ k ∈ S, Real.sqrt Q * (Λ k / Real.sqrt k)
      ≤ ∑ k ∈ S, D * Λ k := by
        apply sum_le_sum
        intro k hk
        obtain ⟨hk0, _, _, hscale⟩ := hS k hk
        have hs := Real.sqrt_le_sqrt hscale
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hD] at hs
        have hk' : 0 < Real.sqrt k := Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hk0)
        rw [← mul_div_assoc, div_le_iff₀ hk']
        calc Real.sqrt Q * Λ k ≤ (D * Real.sqrt k) * Λ k :=
              mul_le_mul_of_nonneg_right hs vonMangoldt_nonneg
          _ = _ := by ring
    _ ≤ D * (3 * (Real.log 4 + 4) * Real.sqrt Q) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left hmass hD
    _ = _ := by ring

end GaloisForLFunctions.CountingHolography.Sections
