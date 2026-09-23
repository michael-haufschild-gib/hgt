import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicSieveSwappedReceiver

/-!
# The sieve-swapped receiver with its parameters chosen

`integral_Icc_normSq_dyadicPrimePoly_mul_harmonicCofactor_le` carries the two-dimensional sieve's
five free parameters `δ, K, k, z, P₁`.  All but the sieve's own prime cutoff `P₁` are determined by
the frequency radius and the block: `δ = 1/(2πW)` saturates the Gallagher constraint, `K` and `k`
are the least admissible integers, and `z = h^{2k}` is the least admissible level.  This file makes
that choice and discharges every side condition, leaving only the structural inequalities
`1 ≤ W`, `h ≤ R`, `1 ≤ R`, `2 ≤ P₁ ≤ h`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The saturating Gallagher width for a frequency radius. -/
def sieveSwappedDelta (W : ℝ) : ℝ := 1 / (2 * Real.pi * W)

/-- The least admissible neighbour budget of the two-dimensional sieve. -/
def sieveSwappedBudget (R : ℕ) (W : ℝ) : ℕ := ⌈6 * (R : ℝ) * sieveSwappedDelta W⌉₊

/-- The least admissible sieve dimension. -/
def sieveSwappedDimension (P₁ h : ℕ) : ℕ :=
  ⌈Real.exp 1 * (∑ p ∈ rangePrimes P₁ h, 2 / ((p : ℝ) - 2)) + Real.log 2⌉₊

/-- The least admissible sieve level. -/
def sieveSwappedLevel (P₁ h : ℕ) : ℝ := ((h : ℝ)) ^ (2 * sieveSwappedDimension P₁ h)

/-- **The sieve-swapped receiver with every sieve parameter chosen.** -/
theorem integral_Icc_normSq_dyadicPrimePoly_mul_harmonicCofactor_le_canonical
    (P D : Finset ℕ) {R h P₁ : ℕ} {W : ℝ}
    (hW : 1 ≤ W) (hhR : h ≤ R) (hR1 : 1 ≤ R)
    (hP₁ : 2 ≤ P₁) (hP₁h : P₁ ≤ h) (hh1 : 1 ≤ h) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((1 : ℂ) / (n : ℂ))) (bigPrimeSet R (2 * R)) w
          * logPoly (harmonicRamareCofactorCoeff P) D w‖ ^ (2 : ℕ))
      ≤ harmonicPrimeMass D ^ (2 : ℕ) *
          ((5 / (4 * sieveSwappedDelta W)) * (1 / (R : ℝ) ^ (2 : ℕ))
            * (((bigPrimeSet R (2 * R)).card : ℝ)
              + 2 * (2 * Real.exp 1 * ((sieveSwappedBudget R W : ℕ) : ℝ) * (2 * (R : ℝ))
                      / (Real.exp (mertensS h - mertensS P₁)) ^ (2 : ℕ)
                    + ((sieveSwappedBudget R W : ℕ) : ℝ) *
                        ∑ e ∈ (rangePrimorial P₁ h).divisors,
                        (if ((e : ℕ) : ℝ) ≤ sieveSwappedLevel P₁ h
                          then 2 * 6 ^ e.primeFactors.card else 0)))) := by
  have hpi : (0 : ℝ) < 2 * Real.pi * W := by
    have := Real.pi_gt_three
    nlinarith
  have hδ0 : 0 < sieveSwappedDelta W := by
    rw [sieveSwappedDelta]; positivity
  have hδ1 : sieveSwappedDelta W ≤ 1 := by
    rw [sieveSwappedDelta, div_le_one hpi]
    nlinarith [Real.pi_gt_three]
  have hWδ : 2 * Real.pi * sieveSwappedDelta W * W ≤ 1 := by
    rw [sieveSwappedDelta]
    rw [show 2 * Real.pi * (1 / (2 * Real.pi * W)) * W = (2 * Real.pi * W) / (2 * Real.pi * W) by
      field_simp]
    rw [div_self (ne_of_gt hpi)]
  have hK : 6 * (R : ℝ) * sieveSwappedDelta W ≤ ((sieveSwappedBudget R W : ℕ) : ℝ) := by
    rw [sieveSwappedBudget]
    exact Nat.le_ceil _
  have hk : Real.exp 1 * (∑ p ∈ rangePrimes P₁ h, 2 / ((p : ℝ) - 2)) + Real.log 2
      ≤ ((sieveSwappedDimension P₁ h : ℕ) : ℝ) := by
    rw [sieveSwappedDimension]
    exact Nat.le_ceil _
  have hhR1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
  have hz : (1 : ℝ) ≤ sieveSwappedLevel P₁ h := by
    rw [sieveSwappedLevel]
    exact one_le_pow₀ hhR1
  have hlev : ((h : ℝ)) ^ (2 * sieveSwappedDimension P₁ h) ≤ sieveSwappedLevel P₁ h :=
    le_of_eq rfl
  exact integral_Icc_normSq_dyadicPrimePoly_mul_harmonicCofactor_le P D
    hδ0 hδ1 hWδ hK hhR hR1 hP₁ hP₁h hh1 hz hlev hk

end

end RHTower.Sieve
