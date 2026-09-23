import GaloisForLFunctions.RHTower.SuzukiPrimeFlankEulerianKernel

/-!
# Macroscopic actual-prime pressure in the SP-E Eulerian coordinate

The exact Eulerian source coordinate has a positive actual-prime component.  On every width-five
block past the symbolic Chebyshev threshold, that component is at least an explicit positive
multiple of `sqrt n`.  Consequently a bounded corrected Chebyshev current can only arise through
the signed cancellation against its exact continuum increment and the remaining prime history.
This theorem does not assert that the full signed current diverges.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Normalized positive Eulerian source carried by the actual-prime width-five block. -/
def suzukiEulerianFivePrimeBlockComponent (n : ℕ) : ℝ :=
  (∑ p ∈ suzukiMangoldtFivePrimeBlock n,
    (p : ℝ) * RiemannGaussian.suzukiPrimeWeight (p - 2)) / (5 * (n : ℝ))

/-- The actual-prime width-five block contributes explicit square-root-scale positive pressure in
the literal SP-E Eulerian coordinate. -/
theorem suzukiEulerianFivePrimeBlockComponent_lower
    {n : ℕ} (hn : Real.exp 20 ≤ (n : ℝ)) :
    Real.sqrt 2 / 20 * Real.sqrt n ≤ suzukiEulerianFivePrimeBlockComponent n := by
  have hnPos : (0 : ℝ) < n := (Real.exp_pos 20).trans_le hn
  have hmass := chebyshev_fivePrimeBlock_logMass_floor hn
  have hterm : ∀ p ∈ suzukiMangoldtFivePrimeBlock n,
      Real.sqrt (2 * (n : ℝ)) * Real.log p ≤
        (p : ℝ) * RiemannGaussian.suzukiPrimeWeight (p - 2) := by
    intro p hp
    obtain ⟨hpPrime, hpLower, _hpUpper⟩ := mem_suzukiMangoldtFivePrimeBlock.mp hp
    have hpTwo : 2 ≤ p := by omega
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    have hroot : Real.sqrt (2 * (n : ℝ)) ≤ Real.sqrt p := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast hpLower.le
    rw [suzukiPrimeWeight_pred_eq_screwPrimeWeight hpTwo]
    unfold GaloisForLFunctions.RHTower.screwPrimeWeight
    rw [ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
    have hsq : Real.sqrt (p : ℝ) * Real.sqrt p = p :=
      Real.mul_self_sqrt hpR.le
    calc
      Real.sqrt (2 * (n : ℝ)) * Real.log p ≤ Real.sqrt p * Real.log p :=
        mul_le_mul_of_nonneg_right hroot hlog
      _ = (p : ℝ) * (Real.log p / Real.sqrt p) := by
        field_simp [(Real.sqrt_pos.mpr hpR).ne']
        nlinarith
  have hsum :
      Real.sqrt (2 * (n : ℝ)) *
          (∑ p ∈ suzukiMangoldtFivePrimeBlock n, Real.log p) ≤
        ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
          (p : ℝ) * RiemannGaussian.suzukiPrimeWeight (p - 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hbase : Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / 4) ≤
      ∑ p ∈ suzukiMangoldtFivePrimeBlock n,
        (p : ℝ) * RiemannGaussian.suzukiPrimeWeight (p - 2) := by
    exact (mul_le_mul_of_nonneg_left hmass (Real.sqrt_nonneg _)).trans hsum
  unfold suzukiEulerianFivePrimeBlockComponent
  apply (le_div_iff₀ (by positivity : 0 < 5 * (n : ℝ))).2
  have hsqrt : Real.sqrt (2 * (n : ℝ)) = Real.sqrt 2 * Real.sqrt n := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Real.sqrt 2 / 20 * Real.sqrt n * (5 * (n : ℝ)) =
        Real.sqrt (2 * (n : ℝ)) * ((n : ℝ) / 4) := by rw [hsqrt]; ring
    _ ≤ _ := hbase

/-- The positive width-five contribution is unbounded on the exact SP-E Eulerian coordinate. -/
theorem suzukiEulerianFivePrimeBlockComponent_unbounded
    (B : ℝ) :
    ∃ n : ℕ, Real.exp 20 ≤ (n : ℝ) ∧ B < suzukiEulerianFivePrimeBlockComponent n := by
  let c : ℝ := Real.sqrt 2 / 20
  have hc : 0 < c := by
    dsimp [c]
    positivity
  obtain ⟨n, hn⟩ := exists_nat_gt
    (max (Real.exp 20) ((max B 0 / c) ^ (2 : ℕ)))
  have hN : Real.exp 20 ≤ (n : ℝ) :=
    (le_max_left _ _).trans hn.le
  have hsq : (max B 0 / c) ^ (2 : ℕ) < (n : ℝ) :=
    (le_max_right _ _).trans_lt hn
  have hratioNonneg : 0 ≤ max B 0 / c := div_nonneg (le_max_right _ _) hc.le
  have hratioSqrt : max B 0 / c < Real.sqrt (n : ℝ) :=
    (Real.lt_sqrt hratioNonneg).2 hsq
  have hmax : max B 0 < c * Real.sqrt (n : ℝ) := by
    calc
      max B 0 = c * (max B 0 / c) := by field_simp
      _ < c * Real.sqrt (n : ℝ) := mul_lt_mul_of_pos_left hratioSqrt hc
  have hscale : B < c * Real.sqrt (n : ℝ) := (le_max_left _ _).trans_lt hmax
  have hlower := suzukiEulerianFivePrimeBlockComponent_lower hN
  exact ⟨n, hN, hscale.trans_le hlower⟩

end

end RHTower
