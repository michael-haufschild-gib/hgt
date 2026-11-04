import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ResidueCovariance
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ReciprocalAbel
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.KernelVariation

/-!
# Weighted covariance of prime residue classes

Abel summation transfers the exact residue period means through bounded
kernel products. The full weighted discrepancy costs one inverse lower
endpoint, uniformly in both prime moduli and residue classes.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace GaloisForLFunctions.BezoutValuationIncidence

private theorem Icc_eq_Ioc_pred {A B : ℕ} (hA : 1 ≤ A) : Icc A B = Ioc (A - 1) B := by
  ext n
  simp only [mem_Icc, mem_Ioc]
  omega

private theorem inv_nat_le_one {p : ℕ} (hp : 0 < p) : 1 / (p : ℝ) ≤ 1 := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  simpa only [one_div_one] using one_div_le_one_div_of_le (zero_lt_one : (0 : ℝ) < 1) hpR

/-- Coprime centered residues retain a uniform prefix discrepancy on inclusive intervals. -/
theorem coprime_covariance_Icc {A B p q a b : ℕ}
    (hA : 1 ≤ A) (hAB : A ≤ B) (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q) :
    |∑ n ∈ Icc A B, centeredResidue p a n * centeredResidue q b n| ≤ 3 := by
  rw [Icc_eq_Ioc_pred hA]
  have h := coprime_residue_covariance (A := A - 1) (B := B) (a := a) (b := b)
    (by omega) hp hq hpq
  exact h.trans (by linarith only [inv_nat_le_one hp, inv_nat_le_one hq])

/-- Equal-modulus covariance retains its exact period mean and a uniform prefix error. -/
theorem same_covariance_Icc {A B p a b : ℕ}
    (hA : 1 ≤ A) (hAB : A ≤ B) (hp : 0 < p) :
    |∑ n ∈ Icc A B, (centeredResidue p a n * centeredResidue p b n -
      ((if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2))| ≤ 3 := by
  rw [Icc_eq_Ioc_pred hA, sum_sub_distrib, sum_const, nsmul_eq_mul,
    Nat.card_Ioc, Nat.cast_sub (by omega : A - 1 ≤ B)]
  have h := same_residue_covariance (A := A - 1) (B := B) (a := a) (b := b) (by omega) hp
  refine h.trans ?_
  calc
    1 + 2 / (p : ℝ) = 1 + 2 * (1 / (p : ℝ)) := by ring
    _ ≤ 3 := by have hi := inv_nat_le_one hp; linarith only [hi]

/-- Coprime residue covariance against a bounded-variation kernel product costs an inverse endpoint. -/
theorem weighted_coprime_covariance {f g : ℕ → ℝ} {M K : ℝ}
    (hM : 0 ≤ M) {A B p q a b : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B)
    (hp : 0 < p) (hq : 0 < q) (hpq : p.Coprime q)
    (hf : ∀ n ∈ Icc A B, |f n| ≤ M) (hg : ∀ n ∈ Icc A B, |g n| ≤ M)
    (hfv : discreteVariation f A B ≤ K) (hgv : discreteVariation g A B ≤ K) :
    |∑ n ∈ Icc A B, (centeredResidue p a n * centeredResidue q b n) *
      (f n * g n / (n : ℝ))| ≤ 3 * (2 * M ^ 2 + 2 * M * K) / (A : ℝ) := by
  have hpref : ∀ m, A ≤ m → m ≤ B →
      |∑ n ∈ Icc A m, centeredResidue p a n * centeredResidue q b n| ≤ 3 :=
    fun m hm _ => coprime_covariance_Icc hA hm hp hq hpq
  have h := abs_weighted_sum_le_of_prefix (w := fun n => f n * g n / (n : ℝ)) hAB hpref
  have hk := pair_kernel_variation hM hA hAB hf hg hfv hgv
  exact h.trans ((mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))

/-- The same inverse-endpoint bound holds after subtracting the equal-prime period mean. -/
theorem weighted_same_covariance {f g : ℕ → ℝ} {M K : ℝ}
    (hM : 0 ≤ M) {A B p a b : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) (hp : 0 < p)
    (hf : ∀ n ∈ Icc A B, |f n| ≤ M) (hg : ∀ n ∈ Icc A B, |g n| ≤ M)
    (hfv : discreteVariation f A B ≤ K) (hgv : discreteVariation g A B ≤ K) :
    |∑ n ∈ Icc A B, (centeredResidue p a n * centeredResidue p b n -
      ((if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2)) *
        (f n * g n / (n : ℝ))| ≤ 3 * (2 * M ^ 2 + 2 * M * K) / (A : ℝ) := by
  have hpref : ∀ m, A ≤ m → m ≤ B →
      |∑ n ∈ Icc A m, (centeredResidue p a n * centeredResidue p b n -
        ((if a ≡ b [MOD p] then 1 / (p : ℝ) else 0) - 1 / (p : ℝ) ^ 2))| ≤ 3 :=
    fun m hm _ => same_covariance_Icc hA hm hp
  have h := abs_weighted_sum_le_of_prefix (w := fun n => f n * g n / (n : ℝ)) hAB hpref
  have hk := pair_kernel_variation hM hA hAB hf hg hfv hgv
  exact h.trans ((mul_le_mul_of_nonneg_left hk (by norm_num : (0 : ℝ) ≤ 3)).trans_eq (by ring))

#print axioms weighted_coprime_covariance
#print axioms weighted_same_covariance

end GaloisForLFunctions.BezoutValuationIncidence
