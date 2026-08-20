import GaloisForLFunctions.RHTower.Sieve.RamareBlockSplitOn
import GaloisForLFunctions.RHTower.Sieve.SetIntegralBlockSplit
import GaloisForLFunctions.RHTower.Sieve.LadderBlockMeanSquare
import GaloisForLFunctions.RHTower.Sieve.BlockProductAnnulus

/-!
# The Ramaré ladder over a frequency set, with the cofactor's mean square supplied

`Sieve/RamareBlockSplitOn.setIntegral_normSq_ramareBilinear_le_ladder_assembled` leaves each block's
product integral `∫_E ‖P_j·C_j‖²` open.  On a set where the **prime** block obeys a pointwise bound
— a zero-free-region estimate, valid on an annulus — the product integral is that bound squared
times the cofactor's mean square over the same set, and the latter is exactly what an integral
Halász–Montgomery estimate delivers.  Passing the mean square in as a parameter keeps the two
inputs independent: the pointwise bound comes from arithmetic, the mean square from the measure of
the set.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **One block over a frequency set, from a prime sup and a cofactor mean square.** -/
theorem setIntegral_normSq_blockProduct_le_supMeanSquare (a : ℕ → ℂ) (B D : Finset ℕ)
    {W V I : ℝ} {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (hbound : ∀ w ∈ E, ‖primeBlockPoly B w‖ ≤ V)
    (hI : (∫ w in E, ‖logPoly a D w‖ ^ 2) ≤ I) :
    (∫ w in E, ‖primeBlockPoly B w * logPoly a D w‖ ^ 2) ≤ V ^ 2 * I := by
  have hrw : (∫ w in E, ‖primeBlockPoly B w * logPoly a D w‖ ^ 2)
      = ∫ w in E, ‖primeBlockPoly B w‖ ^ 2 * ‖logPoly a D w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun hEm fun w _ => ?_
    rw [norm_mul, mul_pow]
  rw [hrw]
  refine le_trans (setIntegral_normSq_mul_le_of_bound (continuous_primeBlockPoly B)
    (continuous_logPoly a D) hEm hEs hbound) ?_
  exact mul_le_mul_of_nonneg_left hI (by positivity)

/-- **The Ramaré ladder over a frequency set, paid by a prime sup and a cofactor mean square.**
This is the orientation the exceptional half needs when the prime range is high enough for a
zero-free-region bound: the pointwise saving lives on the prime blocks and the smallness of the set
is spent on the long polynomial. -/
theorem setIntegral_normSq_ramareBilinear_le_ladder_supMeanSquare {P : Finset ℕ} (M : ℕ)
    {Q η W : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (V I : ℕ → ℝ)
    (hbound : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j)
    (hI : ∀ j ∈ Finset.range L,
      (∫ w in E, ‖logPoly (ramareCofactorCoeff P) (geomCofactorBlock M Q η j) w‖ ^ 2) ≤ I j) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          (2 * (V j ^ 2 * I j)
            + 2 * ((geomBlock P Q (1 + η) j).card : ℝ) ^ 2
                * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
                    * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 4
                      + (((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 + 1)))) := by
  refine le_trans (setIntegral_normSq_ramareBilinear_le_ladder_assembled (P := P) M hQ hη hW hL
    hPprime hP hEm hEs) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (Nat.cast_nonneg L)
  have hblk := setIntegral_normSq_blockProduct_le_supMeanSquare (ramareCofactorCoeff P)
    (geomBlock P Q (1 + η) j) (geomCofactorBlock M Q η j) hEm hEs (hbound j hj) (hI j hj)
  linarith

/-- **The Ramaré ladder over a frequency set, paid by a prime sup and the mean value theorem.**
This is the non-exceptional orientation: on the set where every prime block is small by definition,
the cofactor needs no arithmetic at all. -/
theorem setIntegral_normSq_ramareBilinear_le_ladder_sup {P : Finset ℕ} (M : ℕ)
    {Q η W : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L)
    {E : Set ℝ} (hEm : MeasurableSet E) (hEs : E ⊆ Set.Icc (-W) W)
    (V : ℕ → ℝ) (hV0 : ∀ j, 0 ≤ V j)
    (hbound : ∀ j ∈ Finset.range L, ∀ w ∈ E,
      ‖primeBlockPoly (geomBlock P Q (1 + η) j) w‖ ≤ V j) :
    (∫ w in E, ‖ramareBilinear P M w‖ ^ 2)
      ≤ (L : ℝ) * ∑ j ∈ Finset.range L,
          (2 * (V j ^ 2 * ((5 * Real.pi / 2 * W
                  + 5 * Real.exp 1 / 2 * ((⌊(M : ℝ) / (Q * (1 + η) ^ j)⌋₊ : ℕ) : ℝ))
                * ((geomCofactorBlock M Q η j).card : ℝ)))
            + 2 * ((geomBlock P Q (1 + η) j).card : ℝ) ^ 2
                * (2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
                    * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / (Q * (1 + η) ^ j) + 4
                      + (((M : ℕ) : ℝ) / (Q * (1 + η) ^ j) ^ 2 + 1)))) := by
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  refine le_trans (setIntegral_normSq_ramareBilinear_le_ladder_assembled (P := P) M hQ hη hW hL
    hPprime hP hEm hEs) ?_
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (Nat.cast_nonneg L)
  have hbounds := geomCofactorBlockAt_bounds (A₀ := 1) (B₀ := M) (by norm_num) hQ0 hη j
  have hblk := integral_normSq_blockProduct_set_le (ramareCofactorCoeff P)
    (norm_ramareCofactorCoeff_le_one P) (geomBlock P Q (1 + η) j) (geomCofactorBlock M Q η j)
    hbounds.1 hbounds.2 hW (hV0 j) hEm hEs (hbound j hj)
  linarith

end

end RHTower.Sieve
