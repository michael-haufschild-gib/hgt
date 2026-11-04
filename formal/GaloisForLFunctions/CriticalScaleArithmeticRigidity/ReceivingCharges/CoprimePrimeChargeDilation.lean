import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.PrimeIncidenceProductEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.FixedConductorDilationRows
import GaloisForLFunctions.SignedArithmeticHodgeTheory.GrowingRamanujanFamiliesHaveAUniformGramBudget
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFlipThresholdIsSetByTheConductorsOfThePrime

/-!
# Finite dilation energy of a coprime receiving fibre

Multiplication by a fixed normalized Ramanujan mode preserves the leading
prime-incidence energy. The exact discrepancy is bounded by two vanishing
costs: the coherent coefficient square mass and the harmonic input square.
-/

noncomputable section

open Finset ArithmeticFunction
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  ArithmeticIntersectionTheory SignedArithmeticHodgeTheory

/-- A normalized conductor square has unit harmonic mean with a bounded finite-horizon error. -/
theorem abs_normalizedMode_square_harmonic_sub_le {m : ℕ} (hm : 0 < m) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, normalizedRamanujanMode m n ^ 2 / (n : ℝ)) -
      ∑ n ∈ Icc 1 N, 1 / (n : ℝ)| ≤ 2 * (m : ℝ) ^ 2 := by
  have h := ramanujanPoleProfile_gram_error_le ⟨m, hm⟩ ⟨m, hm⟩ N
  simp only [ite_true, one_mul] at h
  change |(∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile m n) -
    ∑ n ∈ Icc 1 N, 1 / (n : ℝ)| ≤ 2 * (m : ℝ) * m at h
  simp only [ramanujanPoleProfile, ← sq, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at h
  exact h.trans_eq (by ring)

/-- The exact coprime-fibre dilation energy retains its weighted prime diagonal. -/
theorem jumpEnergy_coprime_mode_incidence {m : ℕ} (hm : 0 < m) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m) (b : ℕ → ℝ) (N : ℕ) :
    jumpEnergy N (fun n => normalizedRamanujanMode m n * incidencePacket P b n) =
      (∑ p ∈ P, b p ^ 2 *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n ^ 2 / (n : ℝ))) +
      ∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
        (incidencePacket P b kn.2 ^ 2 *
          (normalizedRamanujanMode m (kn.1 * kn.2) - normalizedRamanujanMode m kn.2) ^ 2 / kn.2) :=
  jumpEnergy_incidence_product hP b (normalizedRamanujanMode m)
    (fun p hp n => normalizedRamanujanMode_coprime_mul hm (hcop p hp) n) N

/-- The fixed base conductor changes coherent dilation energy only by two explicit small costs. -/
theorem abs_jumpEnergy_coprime_mode_sub_le {m : ℕ} (hm : 0 < m) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hcop : ∀ p ∈ P, p.Coprime m) (b : ℕ → ℝ) (N : ℕ) :
    |jumpEnergy N (fun n => normalizedRamanujanMode m n * incidencePacket P b n) -
      jumpEnergy N (incidencePacket P b)| ≤
      2 * (m : ℝ) ^ 2 * (∑ p ∈ P, b p ^ 2 * (Real.log p / p)) +
      (m : ℝ) * (Real.log m + tameDifferent m) *
        ∑ n ∈ Icc 1 N, incidencePacket P b n ^ 2 / (n : ℝ) := by
  let R := ∑ kn ∈ dilationPairs N, Λ kn.1 / kn.1 *
    (incidencePacket P b kn.2 ^ 2 *
      (normalizedRamanujanMode m (kn.1 * kn.2) - normalizedRamanujanMode m kn.2) ^ 2 / kn.2)
  have hR0 : 0 ≤ R := by
    exact sum_nonneg fun kn _ => mul_nonneg
      (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg kn.1))
      (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg kn.2))
  have hR := incidence_product_remainder_le N (incidencePacket P b)
    (normalizedRamanujanMode m) ((m : ℝ) * (Real.log m + tameDifferent m))
    (normalizedMode_upward_square_le hm)
  have hdiag :
      |(∑ p ∈ P, b p ^ 2 *
          (Real.log p / p * ∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n ^ 2 / (n : ℝ))) -
        ∑ p ∈ P, b p ^ 2 * (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))| ≤
        2 * (m : ℝ) ^ 2 * ∑ p ∈ P, b p ^ 2 * (Real.log p / p) := by
    rw [← sum_sub_distrib, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
    intro p _
    have hw : 0 ≤ b p ^ 2 * (Real.log p / p) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    calc
      _ = b p ^ 2 * (Real.log p / p) *
          |(∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n ^ 2 / (n : ℝ)) -
            ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)| := by
        rw [show b p ^ 2 * (Real.log p / p *
            ∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n ^ 2 / (n : ℝ)) -
            b p ^ 2 * (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)) =
            (b p ^ 2 * (Real.log p / p)) *
              ((∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n ^ 2 / (n : ℝ)) -
                ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ)) by ring,
          abs_mul, abs_of_nonneg hw]
      _ ≤ _ := (mul_le_mul_of_nonneg_left
        (abs_normalizedMode_square_harmonic_sub_le hm (N / p)) hw).trans_eq (mul_comm _ _)
  rw [jumpEnergy_coprime_mode_incidence hm hP hcop, jumpEnergy_incidencePacket_diagonal hP]
  calc
    _ = |((∑ p ∈ P, b p ^ 2 *
        (Real.log p / p * ∑ n ∈ Icc 1 (N / p), normalizedRamanujanMode m n ^ 2 / (n : ℝ))) -
        ∑ p ∈ P, b p ^ 2 * (Real.log p / p * ∑ n ∈ Icc 1 (N / p), 1 / (n : ℝ))) + R| := by
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hdiag (by rw [abs_of_nonneg hR0]; exact hR))

#print axioms jumpEnergy_coprime_mode_incidence
#print axioms abs_jumpEnergy_coprime_mode_sub_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
