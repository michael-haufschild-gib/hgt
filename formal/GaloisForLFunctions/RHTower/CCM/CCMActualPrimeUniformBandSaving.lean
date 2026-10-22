import GaloisForLFunctions.RHTower.CCM.CCMActualPrimeBandMassLimit

/-!
# A uniform lower bound for actual cross-band cancellation

The mixed term between two complete terminal prime bands stays a fixed
amount below perfect alignment, uniformly over every physical vector.
The actual band masses and the actual mixed inner product are retained.

This is a bound on one arithmetic interaction. It is not the completed
prime--Gamma--pole comparison required for the native Xi heat energy.
The corpus already has a stronger global prime-operator norm bound than
one could obtain by inserting this gain in the outer-shell budget.
-/

open Filter Topology
open scoped InnerProduct
noncomputable section
namespace RHTower

/-- A nonvanishing interference deficit for the complete bands, with no
restriction on the coefficients or dimension of the physical vector. -/
theorem exists_uniform_ccmActualPrimeBands_cross_deficit :
    ∃ δ : ℝ, 0 < δ ∧ ∃ A : ℝ, 4 < A ∧
      ∀ a : SuzukiPositiveAperture, A ≤ a.1 → ∀ f : suzukiApertureHilbert a,
        δ * Real.exp (2 * a.1) * ‖f‖ ^ 2 ≤
          ccmActualPrimeBandMass a 4 3 * ccmActualPrimeBandMass a 1 0 * ‖f‖ ^ 2 -
            (inner ℂ (ccmActualPrimeBandOperator a 4 3 f)
              (ccmActualPrimeBandOperator a 1 0 f)).re := by
  let β := ccmPrimeBandsLimitingMassProduct
  have hβ : 0 < β := ccmPrimeBandsLimitingMassProduct_pos
  have hlarge := (tendsto_order.1 tendsto_ccmActualPrimeBands_scaled_mass_product).1
    (β / 2) (by dsimp only [β]; linarith [ccmPrimeBandsLimitingMassProduct_pos])
  obtain ⟨A, hA⟩ := eventually_atTop.1 hlarge
  refine ⟨β / 16, div_pos hβ (by norm_num), max A 5,
    lt_of_lt_of_le (by norm_num) (le_max_right A 5), ?_⟩
  intro a ha f
  have haA : A ≤ a.1 := (le_max_left A 5).trans ha
  have ha4 : 4 < a.1 := by have := (le_max_right A 5).trans ha; linarith
  let aa : {a : SuzukiPositiveAperture // 4 < a.1} := ⟨a, ha4⟩
  have hm := (hA a.1 haA).le
  rw [← ccmActualPrimeLowBandMass_eq_difference aa,
    ← ccmActualPrimeHighBandMass_eq_difference aa] at hm
  have hcancel : Real.exp (2 * a.1) * Real.exp (-2 * a.1) = 1 := by
    rw [← Real.exp_add, show 2 * a.1 + -2 * a.1 = 0 by ring, Real.exp_zero]
  have hscaled := mul_le_mul_of_nonneg_left hm (Real.exp_pos (2 * a.1)).le
  rw [← mul_assoc, hcancel, one_mul] at hscaled
  have hmass := mul_le_mul_of_nonneg_right hscaled (sq_nonneg ‖f‖)
  have hcross := ccmActualPrimeBands_cross_bound aa f
  change 8 * (inner ℂ (ccmActualPrimeBandOperator a 4 3 f)
    (ccmActualPrimeBandOperator a 1 0 f)).re ≤
      7 * ccmActualPrimeBandMass a 4 3 * ccmActualPrimeBandMass a 1 0 * ‖f‖ ^ 2 at hcross
  nlinarith only [hmass, hcross]

end RHTower
