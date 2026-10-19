import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiOddTraceCenteringAndExtremalRestriction
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiDilatedPronicMassAndRationalBounds

/-!
# Exact physical Gram forms at horizon three

After removing coefficient one, write `a = c 2`, `b = c 3`. The complete
sieve energy is `E₂ a² + 2 E₆ ab + E₃ b²`; the selected Fermi energy is
`E₄ a² + 2 E₁₂ ab + (E₃ - E₆ + E₁₂) b²`. The odd pronic mean is
`b (E₃ - E₆)`. These identities use the actual infinite trace energies,
not a truncated or averaged surrogate.

The pairwise proof uses existing exact Fermi recovery below horizon four,
and the series proof uses the previously verified dilated pronic masses.
-/

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

set_option autoImplicit false

open BezoutValuationIncidence
open scoped BigOperators

private noncomputable def divisorPronicTerm (a d n : ℕ) : ℝ :=
  (if d ∣ n then 1 else 0) / (pronicSeq (a * n) : ℝ)

private theorem divisor_term_summable {a : ℕ} (ha : 0 < a) (d : ℕ) :
    Summable (divisorPronicTerm a d) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (fermiDilatedPronicMass_summable ha)
  · unfold divisorPronicTerm
    positivity
  · unfold divisorPronicTerm
    by_cases h : d ∣ n <;> simp [h]

private theorem divisor_term_sum (a : ℕ) {d : ℕ} (hd : 0 < d) :
    (∑' n, divisorPronicTerm a d n) = fermiDilatedPronicMass (a * d) :=
  (fermiDilatedPronicMass_eq_sampled_divisor_sum a hd).symm

private theorem divisor_term_succ_sum {a d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    (∑' n, divisorPronicTerm a d (n + 1)) = fermiDilatedPronicMass (a * d) := by
  have h := (divisor_term_summable ha d).tsum_eq_zero_add
  have h0 : divisorPronicTerm a d 0 = 0 := by simp [divisorPronicTerm, pronicSeq]
  rw [h0, zero_add, divisor_term_sum a hd] at h
  exact h.symm

private theorem dilated_mass_succ_sum {a : ℕ} (ha : 0 < a) :
    (∑' n : ℕ, (1 : ℝ) / (pronicSeq (a * (n + 1)) : ℝ)) =
      fermiDilatedPronicMass a := by
  have h := (fermiDilatedPronicMass_summable ha).tsum_eq_zero_add
  have h0 : (1 : ℝ) / (pronicSeq (a * 0) : ℝ) = 0 := by simp [pronicSeq]
  rw [h0, zero_add] at h
  exact h.symm

private theorem odd_three_mass :
    (∑' m : ℕ, divisorPronicTerm 1 3 (2 * m + 1)) =
      fermiDilatedPronicMass 3 - fermiDilatedPronicMass 6 := by
  have hs := divisor_term_summable (by norm_num : 0 < 1) 3
  have he := hs.comp_injective (i := fun m => 2 * m)
    (by intro a b h; change 2 * a = 2 * b at h; omega)
  have ho := hs.comp_injective (i := fun m => 2 * m + 1)
    (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have heq : (∑' m : ℕ, divisorPronicTerm 1 3 (2 * m)) =
      fermiDilatedPronicMass 6 := by
    calc
      _ = ∑' m : ℕ, divisorPronicTerm 2 3 m := by
        apply tsum_congr
        intro m
        have h : 3 ∣ 2 * m ↔ 3 ∣ m := by omega
        simp [divisorPronicTerm, h]
      _ = _ := divisor_term_sum 2 (by norm_num : 0 < 3)
  have hsplit := tsum_even_add_odd (f := divisorPronicTerm 1 3) he ho
  rw [heq, divisor_term_sum 1 (by norm_num : 0 < 3)] at hsplit
  norm_num at hsplit
  linarith

private theorem sieve_three (c : ℕ → ℝ) (n : ℕ) :
    sieveSeq 3 c n = c 1 + (if 2 ∣ n then c 2 else 0) + (if 3 ∣ n then c 3 else 0) := by
  have hset : Finset.Icc 1 3 = {1, 2, 3} := by decide
  simp [sieveSeq, Finset.sum_filter, hset, add_assoc]

private theorem three_pair_polynomials (c : ℕ → ℝ) (hc1 : c 1 = 0) (m : ℕ) :
    sievePairedPronicEnergy 3 c {m} =
        (c 3)^2 * divisorPronicTerm 1 3 (2 * m + 1) +
          (c 2)^2 * (1 / (pronicSeq (2 * (m + 1)) : ℝ)) +
          (2 * c 2 * c 3 + (c 3)^2) * divisorPronicTerm 2 3 (m + 1) ∧
      fermiSelectedPronicEnergy 3 c {m} =
        (c 3)^2 * divisorPronicTerm 1 3 (2 * m + 1) +
          (c 2)^2 * (1 / (pronicSeq (4 * (m + 1)) : ℝ)) +
          (2 * c 2 * c 3 + (c 3)^2) * divisorPronicTerm 4 3 (m + 1) := by
  have hrec := (fermiBoundaryJump_exact_recovery_iff 3 c).2 (by intro k hk; omega)
  have hodd : ¬2 ∣ 2 * m + 1 := by omega
  have heven : 2 ∣ 2 * m + 2 := by omega
  have hthree : 3 ∣ 2 * m + 2 ↔ 3 ∣ m + 1 := by omega
  simp only [sievePairedPronicEnergy, fermiSelectedPronicEnergy, Finset.sum_singleton,
    fermiBoundaryJump_odd, hrec, neg_sq, sieve_three, hc1, if_neg hodd, if_pos heven,
    zero_add, hthree]
  have heq2 : 2 * m + 2 = 2 * (m + 1) := by omega
  have heq4 : 4 * m + 4 = 4 * (m + 1) := by omega
  rw [heq2, heq4]
  unfold divisorPronicTerm
  by_cases h3o : 3 ∣ 2 * m + 1 <;> by_cases h3e : 3 ∣ m + 1 <;>
    simp [h3o, h3e] <;> constructor <;> ring

/-- The complete sieve-energy quadratic form at horizon three with coefficient one removed. -/
noncomputable def fermiHorizonThreeNumerator (a b : ℝ) : ℝ :=
  fermiDilatedPronicMass 2 * a^2 + 2 * fermiDilatedPronicMass 6 * a * b +
    fermiDilatedPronicMass 3 * b^2

/-- The corresponding complete selected Fermi-energy quadratic form. -/
noncomputable def fermiHorizonThreeDenominator (a b : ℝ) : ℝ :=
  fermiDilatedPronicMass 4 * a^2 + 2 * fermiDilatedPronicMass 12 * a * b +
    (fermiDilatedPronicMass 3 - fermiDilatedPronicMass 6 + fermiDilatedPronicMass 12) * b^2

/-- Exact Gram formulas for every horizon-three input with zero unit coefficient. -/
theorem fermiHorizonThree_physical_energies (c : ℕ → ℝ) (hc1 : c 1 = 0) :
    sieveTotalPronicEnergy 3 c = fermiHorizonThreeNumerator (c 2) (c 3) ∧
      fermiSelectedTotalPronicEnergy 3 c = fermiHorizonThreeDenominator (c 2) (c 3) := by
  have hOdd : Summable (fun m : ℕ => divisorPronicTerm 1 3 (2 * m + 1)) :=
    (divisor_term_summable (by norm_num : 0 < 1) 3).comp_injective
    (i := fun m => 2 * m + 1) (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have hO := hOdd.mul_left ((c 3)^2)
  have hEven (a : ℕ) (ha : 0 < a) :
      Summable (fun m : ℕ => (c 2)^2 * (1 / (pronicSeq (a * (m + 1)) : ℝ))) := by
    exact ((fermiDilatedPronicMass_summable ha).comp_injective
      (i := fun m => m + 1) (by intro p q h; change p + 1 = q + 1 at h; omega)).mul_left _
  have hDiv (a : ℕ) (ha : 0 < a) :
      Summable (fun m : ℕ => (2 * c 2 * c 3 + (c 3)^2) * divisorPronicTerm a 3 (m + 1)) := by
    exact ((divisor_term_summable ha 3).comp_injective
      (i := fun m => m + 1) (by intro p q h; change p + 1 = q + 1 at h; omega)).mul_left _
  constructor
  · unfold sieveTotalPronicEnergy
    rw [tsum_congr (fun m => (three_pair_polynomials c hc1 m).1),
      (hO.add (hEven 2 (by norm_num))).tsum_add (hDiv 2 (by norm_num)),
      hO.tsum_add (hEven 2 (by norm_num)), tsum_mul_left, tsum_mul_left, tsum_mul_left,
      odd_three_mass, dilated_mass_succ_sum (by norm_num : 0 < 2),
      divisor_term_succ_sum (by norm_num : 0 < 2) (by norm_num : 0 < 3)]
    unfold fermiHorizonThreeNumerator
    norm_num
    ring
  · unfold fermiSelectedTotalPronicEnergy
    rw [tsum_congr (fun m => (three_pair_polynomials c hc1 m).2),
      (hO.add (hEven 4 (by norm_num))).tsum_add (hDiv 4 (by norm_num)),
      hO.tsum_add (hEven 4 (by norm_num)), tsum_mul_left, tsum_mul_left, tsum_mul_left,
      odd_three_mass, dilated_mass_succ_sum (by norm_num : 0 < 4),
      divisor_term_succ_sum (by norm_num : 0 < 4) (by norm_num : 0 < 3)]
    unfold fermiHorizonThreeDenominator
    norm_num
    ring

/-- Exact odd pronic mean at horizon three after removing the unit coefficient. -/
theorem fermiHorizonThree_odd_mean (c : ℕ → ℝ) (hc1 : c 1 = 0) :
    fermiOddPronicMean 3 c =
      c 3 * (fermiDilatedPronicMass 3 - fermiDilatedPronicMass 6) := by
  have hterm (m : ℕ) : sieveSeq 3 c (2 * m + 1) / (pronicSeq (2 * m + 1) : ℝ) =
      c 3 * divisorPronicTerm 1 3 (2 * m + 1) := by
    have ho : ¬2 ∣ 2 * m + 1 := by omega
    by_cases h3 : 3 ∣ 2 * m + 1 <;>
      simp [sieve_three, hc1, ho, h3, divisorPronicTerm, div_eq_mul_inv]
  unfold fermiOddPronicMean
  rw [tsum_congr hterm, tsum_mul_left, odd_three_mass]

/-- An input supported exactly on the possible coefficient locations two and three. -/
noncomputable def fermiHorizonThreeWeight (a b : ℝ) (d : ℕ) : ℝ :=
  if d = 2 then a else if d = 3 then b else 0

/-- Nonnegative parameters give pointwise nonnegative coefficient weights. -/
theorem fermiHorizonThreeWeight_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ d, 0 ≤ fermiHorizonThreeWeight a b d := by
  intro d
  unfold fermiHorizonThreeWeight
  split_ifs <;> positivity

/-- The supported two-parameter family realizes both physical quadratic forms. -/
theorem fermiHorizonThreeWeight_physical_energies (a b : ℝ) :
    sieveTotalPronicEnergy 3 (fermiHorizonThreeWeight a b) = fermiHorizonThreeNumerator a b ∧
      fermiSelectedTotalPronicEnergy 3 (fermiHorizonThreeWeight a b) =
        fermiHorizonThreeDenominator a b := by
  simpa [fermiHorizonThreeWeight] using
    fermiHorizonThree_physical_energies (fermiHorizonThreeWeight a b)
      (by simp [fermiHorizonThreeWeight])

end GaloisForLFunctions.TransHorizonIncidenceMechanics
