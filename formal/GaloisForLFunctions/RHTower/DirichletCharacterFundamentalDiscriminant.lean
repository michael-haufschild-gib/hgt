/-
# Fundamental discriminants for the certified quadratic CRT families

This module defines the source-facing fundamental-discriminant forms attached
to the three two-adic quadratic CRT characters and proves the finite
square-free/odd arithmetic of their odd prime product.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterQuadraticJacobiIdentity

noncomputable section

namespace RHTower
namespace OddPrimeFamily

/-- Standard arithmetic characterization of a fundamental discriminant. -/
def IsFundamentalDiscriminant (D : ℤ) : Prop :=
  (Squarefree D ∧ D % 4 = 1) ∨
    ∃ d : ℤ, Squarefree d ∧ (d % 4 = 2 ∨ d % 4 = 3) ∧ D = 4 * d

/-- The certified odd prime product is square-free. -/
theorem modulus_squarefree {I : Type*} [Fintype I] (P : OddPrimeFamily I) :
    Squarefree P.modulus := by
  rw [modulus]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp (P.pairwise_coprime hij)
  · intro i hi
    exact (Nat.prime_iff.mp (P.prime i).2.1).squarefree

/-- The certified odd prime product is odd. -/
theorem modulus_odd {I : Type*} [Fintype I] (P : OddPrimeFamily I) : Odd P.modulus := by
  rw [modulus]
  exact Finset.prod_induction (fun i : I => (P.prime i).1) (fun n : ℕ => Odd n)
    (fun a b ha hb => ha.mul hb)
    (by norm_num)
    (fun i hi => (P.prime i).2.1.odd_of_ne_two (P.prime i).2.2)

/-- Fundamental discriminant represented by the conductor-four CRT character. -/
def fourOddFundamentalDiscriminant {I : Type*} [Fintype I] (P : OddPrimeFamily I) : ℤ :=
  if P.modulus % 4 = 1 then -4 * (P.modulus : ℤ) else 4 * (P.modulus : ℤ)

/-- Fundamental discriminant represented by the first conductor-eight CRT character. -/
def eightOddFundamentalDiscriminant {I : Type*} [Fintype I] (P : OddPrimeFamily I) : ℤ :=
  if P.modulus % 4 = 1 then 8 * (P.modulus : ℤ) else -8 * (P.modulus : ℤ)

/-- Fundamental discriminant represented by the second conductor-eight CRT character. -/
def eightOddPrimeFundamentalDiscriminant {I : Type*} [Fintype I]
    (P : OddPrimeFamily I) : ℤ :=
  if P.modulus % 4 = 1 then -8 * (P.modulus : ℤ) else 8 * (P.modulus : ℤ)

/-- The Kronecker symbol for an even discriminant, on positive integer denominators.
For a discriminant divisible by four, even denominators have value zero and
odd denominators use Mathlib's Jacobi symbol. -/
def evenKroneckerSymbol (D : ℤ) (n : ℕ) : ℤ :=
  if Even n then 0 else jacobiSym D n

/-- The even-discriminant symbol of `-4` is the level-four quadratic character. -/
theorem evenKroneckerSymbol_negFour_eq_chiFour (n : ℕ) :
    evenKroneckerSymbol (-4) n = ZMod.χ₄ n := by
  unfold evenKroneckerSymbol
  by_cases heven : Even n
  · rw [if_pos heven]
    rw [ZMod.χ₄_nat_eq_if_mod_four, Nat.mod_eq_zero_of_dvd heven.two_dvd]
    simp
  · rw [if_neg heven]
    have hodd : Odd n := Nat.not_even_iff_odd.mp heven
    calc
      jacobiSym (-4) n = jacobiSym ((-4 : ℤ) / 4) n :=
        (jacobiSym.div_four_left (a := -4) (b := n) (by norm_num)
          (Nat.odd_iff.mp hodd)).symm
      _ = jacobiSym (-1) n := by norm_num
      _ = ZMod.χ₄ n := jacobiSym.at_neg_one hodd

/-- The even-discriminant symbol of `8` is the first level-eight quadratic character. -/
theorem evenKroneckerSymbol_eight_eq_chiEight (n : ℕ) :
    evenKroneckerSymbol 8 n = ZMod.χ₈ n := by
  unfold evenKroneckerSymbol
  by_cases heven : Even n
  · rw [if_pos heven]
    rw [ZMod.χ₈_nat_eq_if_mod_eight, Nat.mod_eq_zero_of_dvd heven.two_dvd]
    simp
  · rw [if_neg heven]
    have hodd : Odd n := Nat.not_even_iff_odd.mp heven
    calc
      jacobiSym 8 n = jacobiSym ((8 : ℤ) / 4) n :=
        (jacobiSym.div_four_left (a := 8) (b := n) (by norm_num)
          (Nat.odd_iff.mp hodd)).symm
      _ = jacobiSym 2 n := by norm_num
      _ = ZMod.χ₈ n := jacobiSym.at_two hodd

/-- The even-discriminant symbol of `-8` is the second level-eight quadratic character. -/
theorem evenKroneckerSymbol_negEight_eq_chiEightPrime (n : ℕ) :
    evenKroneckerSymbol (-8) n = ZMod.χ₈' n := by
  unfold evenKroneckerSymbol
  by_cases heven : Even n
  · rw [if_pos heven]
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, Nat.mod_eq_zero_of_dvd heven.two_dvd]
    simp
  · rw [if_neg heven]
    have hodd : Odd n := Nat.not_even_iff_odd.mp heven
    calc
      jacobiSym (-8) n = jacobiSym ((-8 : ℤ) / 4) n :=
        (jacobiSym.div_four_left (a := -8) (b := n) (by norm_num)
          (Nat.odd_iff.mp hodd)).symm
      _ = jacobiSym (-2) n := by norm_num
      _ = ZMod.χ₈' n := jacobiSym.at_neg_two hodd

/-- The conductor-four CRT discriminant is fundamental. -/
theorem fourOddFundamentalDiscriminant_isFundamental {I : Type*} [Fintype I]
    (P : OddPrimeFamily I) :
    IsFundamentalDiscriminant (fourOddFundamentalDiscriminant P) := by
  have hsq : Squarefree P.modulus := modulus_squarefree P
  have hodd : Odd P.modulus := modulus_odd P
  simp only [fourOddFundamentalDiscriminant]
  split_ifs with hmod
  · right
    refine ⟨-(P.modulus : ℤ), ?_, Or.inr ?_, by ring⟩
    · rw [← Int.squarefree_natAbs]
      simpa using hsq
    · have hcast : ((P.modulus : ℤ) % 4) = 1 := by exact_mod_cast hmod
      omega
  · right
    have hthree : P.modulus % 4 = 3 := by
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with hone | hthree
      · exact False.elim (hmod hone)
      · exact hthree
    refine ⟨(P.modulus : ℤ), ?_, Or.inr ?_, by ring⟩
    · exact Int.squarefree_natCast.mpr hsq
    · exact_mod_cast hthree

/-- The first conductor-eight CRT discriminant is fundamental. -/
theorem eightOddFundamentalDiscriminant_isFundamental {I : Type*} [Fintype I]
    (P : OddPrimeFamily I) :
    IsFundamentalDiscriminant (eightOddFundamentalDiscriminant P) := by
  have hsq : Squarefree P.modulus := modulus_squarefree P
  have hodd : Odd P.modulus := modulus_odd P
  have hcop : (2 : ℕ).Coprime P.modulus :=
    Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat
  have htwo : Squarefree (2 * P.modulus) :=
    (Nat.squarefree_mul hcop).mpr ⟨Nat.prime_two.squarefree, hsq⟩
  have htwoMod : ((2 : ℤ) * P.modulus) % 4 = 2 := by
    obtain ⟨a, ha⟩ := hodd
    omega
  simp only [eightOddFundamentalDiscriminant]
  split_ifs
  · right
    refine ⟨2 * (P.modulus : ℤ), ?_, Or.inl htwoMod, by ring⟩
    · have htwoInt : Squarefree ((2 * P.modulus : ℕ) : ℤ) :=
        Int.squarefree_natCast.mpr htwo
      convert htwoInt using 1
      norm_num
  · right
    refine ⟨-2 * (P.modulus : ℤ), ?_, Or.inl ?_, by ring⟩
    · rw [show -2 * (P.modulus : ℤ) = -((2 * P.modulus : ℕ) : ℤ) by norm_num]
      apply Int.squarefree_natAbs.mp
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      exact htwo
    · omega

/-- The second conductor-eight CRT discriminant is fundamental. -/
theorem eightOddPrimeFundamentalDiscriminant_isFundamental {I : Type*} [Fintype I]
    (P : OddPrimeFamily I) :
    IsFundamentalDiscriminant (eightOddPrimeFundamentalDiscriminant P) := by
  have hsq : Squarefree P.modulus := modulus_squarefree P
  have hodd : Odd P.modulus := modulus_odd P
  have hcop : (2 : ℕ).Coprime P.modulus :=
    Nat.prime_two.coprime_iff_not_dvd.mpr hodd.not_two_dvd_nat
  have htwo : Squarefree (2 * P.modulus) :=
    (Nat.squarefree_mul hcop).mpr ⟨Nat.prime_two.squarefree, hsq⟩
  have htwoMod : ((2 : ℤ) * P.modulus) % 4 = 2 := by
    obtain ⟨a, ha⟩ := hodd
    omega
  simp only [eightOddPrimeFundamentalDiscriminant]
  split_ifs
  · right
    refine ⟨-2 * (P.modulus : ℤ), ?_, Or.inl ?_, by ring⟩
    · rw [show -2 * (P.modulus : ℤ) = -((2 * P.modulus : ℕ) : ℤ) by norm_num]
      apply Int.squarefree_natAbs.mp
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      exact htwo
    · omega
  · right
    refine ⟨2 * (P.modulus : ℤ), ?_, Or.inl htwoMod, by ring⟩
    · have htwoInt : Squarefree ((2 * P.modulus : ℕ) : ℤ) :=
        Int.squarefree_natCast.mpr htwo
      convert htwoInt using 1
      norm_num

end OddPrimeFamily
end RHTower
