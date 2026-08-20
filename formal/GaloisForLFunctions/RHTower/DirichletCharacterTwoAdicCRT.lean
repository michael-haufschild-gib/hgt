/-
# CRT composition of a two-adic and an odd square-free quadratic character

This module joins the explicit level-four quadratic character with a certified
odd square-free CRT quadratic character.  It constructs the composite modulus,
the CRT equivalence, and a closed complete-correlation factorization.  It does
not identify this constructed family with every fundamental discriminant.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicQuadratic
import GaloisForLFunctions.RHTower.QuadraticJacobiSum

open scoped BigOperators

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- The two CRT factors: level `4` followed by the certified odd modulus. -/
def fourOddFactors (P : OddPrimeFamily I) : Fin 2 → ℕ := ![4, P.modulus]

/-- Composite modulus of the level-four and certified odd factors. -/
def fourOddModulus (P : OddPrimeFamily I) : ℕ := ∏ i, fourOddFactors P i

/-- The composite modulus is literally four times the certified odd modulus. -/
theorem fourOddModulus_eq (P : OddPrimeFamily I) : fourOddModulus P = 4 * P.modulus := by
  simp [fourOddModulus, fourOddFactors, Fin.prod_univ_two]

/-- The odd CRT product has no factor two. -/
theorem two_not_dvd_modulus (P : OddPrimeFamily I) : ¬ 2 ∣ P.modulus := by
  rw [modulus]
  apply Nat.prime_two.prime.not_dvd_finsetProd
  intro i hi hdiv
  rcases (Nat.dvd_prime (P.prime i).2.1).mp hdiv with h | h
  · norm_num at h
  · exact P.prime i |>.2.2 h.symm

/-- The level-four local factor is coprime to the odd certified modulus. -/
theorem four_coprime_modulus (P : OddPrimeFamily I) : Nat.Coprime 4 P.modulus := by
  have h : Nat.Coprime 2 P.modulus :=
    Nat.prime_two.coprime_iff_not_dvd.mpr (two_not_dvd_modulus P)
  simpa using h.pow_left 2

/-- The two factors are pairwise coprime, supplying an internal CRT certificate. -/
theorem fourOdd_pairwise_coprime (P : OddPrimeFamily I) :
    Pairwise fun i j => Nat.Coprime (fourOddFactors P i) (fourOddFactors P j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [fourOddFactors]
  all_goals first | exact four_coprime_modulus P | exact (four_coprime_modulus P).symm

/-- CRT equivalence for the two-factor composite modulus. -/
def fourOddCrtEquiv (P : OddPrimeFamily I) :
    ZMod (fourOddModulus P) ≃+* (∀ i, ZMod (fourOddFactors P i)) :=
  ZMod.prodEquivPi (fourOddFactors P) (fourOdd_pairwise_coprime P)

/-- CRT equivalence in ordinary product coordinates. -/
def fourOddCrtProductEquiv (P : OddPrimeFamily I) :
    ZMod (fourOddModulus P) ≃+* (ZMod 4 × ZMod P.modulus) :=
  (fourOddCrtEquiv P).trans
    ((RingEquiv.piFinTwo fun i => ZMod (fourOddFactors P i)).trans
      (RingEquiv.prodCongr
        (ZMod.ringEquivCongr (by simp [fourOddFactors]))
        (ZMod.ringEquivCongr (by simp [fourOddFactors]))))

instance fourOddModulus_neZero (P : OddPrimeFamily I) : NeZero (fourOddModulus P) := ⟨by
  rw [fourOddModulus_eq]
  exact mul_ne_zero (by norm_num) P.modulus_neZero.out⟩

/-- The first CRT coordinate, viewed at the literal level-four type. -/
def fourCoordinate (P : OddPrimeFamily I) (x : ZMod (fourOddModulus P)) : ZMod 4 :=
  (fourOddCrtProductEquiv P x).1

/-- The second CRT coordinate, viewed at the certified odd modulus. -/
def oddCoordinate (P : OddPrimeFamily I) (x : ZMod (fourOddModulus P)) : ZMod P.modulus :=
  (fourOddCrtProductEquiv P x).2

/-- The level-four CRT coordinate respects addition. -/
theorem fourCoordinate_add (P : OddPrimeFamily I) (x z : ZMod (fourOddModulus P)) :
    fourCoordinate P (x + z) = fourCoordinate P x + fourCoordinate P z := by
  change (fourOddCrtProductEquiv P (x + z)).1 =
    (fourOddCrtProductEquiv P x).1 + (fourOddCrtProductEquiv P z).1
  rw [map_add]
  rfl

/-- The odd CRT coordinate respects addition. -/
theorem oddCoordinate_add (P : OddPrimeFamily I) (x z : ZMod (fourOddModulus P)) :
    oddCoordinate P (x + z) = oddCoordinate P x + oddCoordinate P z := by
  change (fourOddCrtProductEquiv P (x + z)).2 =
    (fourOddCrtProductEquiv P x).2 + (fourOddCrtProductEquiv P z).2
  rw [map_add]
  rfl

/-- Product of the level-four and odd square-free CRT quadratic characters. -/
def fourOddQuadraticCharacter (P : OddPrimeFamily I) (x : ZMod (fourOddModulus P)) : ℂ :=
  quadraticCharacterFour (fourCoordinate P x) * quadraticCharacter P (oddCoordinate P x)

/-- Exact complete-correlation factorization for the level-four/odd composite character. -/
theorem fourOdd_quadratic_shiftCorrelation (P : OddPrimeFamily I)
    (k l : ZMod (fourOddModulus P)) :
    ∑ x : ZMod (fourOddModulus P),
      fourOddQuadraticCharacter P (x + k) * fourOddQuadraticCharacter P (x + l) =
      (∑ a : ZMod 4,
        quadraticCharacterFour (a + fourCoordinate P k) *
          quadraticCharacterFour (a + fourCoordinate P l)) *
      (∑ b : ZMod P.modulus,
        quadraticCharacter P (b + oddCoordinate P k) *
          quadraticCharacter P (b + oddCoordinate P l)) := by
  calc
    _ = ∑ x : ZMod (fourOddModulus P),
        (quadraticCharacterFour (fourCoordinate P x + fourCoordinate P k) *
          quadraticCharacter P (oddCoordinate P x + oddCoordinate P k)) *
        (quadraticCharacterFour (fourCoordinate P x + fourCoordinate P l) *
          quadraticCharacter P (oddCoordinate P x + oddCoordinate P l)) := by
      simp_rw [fourOddQuadraticCharacter, fourCoordinate_add, oddCoordinate_add]
    _ = ∑ y : ZMod 4 × ZMod P.modulus,
        (quadraticCharacterFour (y.1 + fourCoordinate P k) *
          quadraticCharacter P (y.2 + oddCoordinate P k)) *
        (quadraticCharacterFour (y.1 + fourCoordinate P l) *
          quadraticCharacter P (y.2 + oddCoordinate P l)) := by
      change (∑ x : ZMod (fourOddModulus P),
          (quadraticCharacterFour (((fourOddCrtProductEquiv P).toEquiv x).1 +
            fourCoordinate P k) *
            quadraticCharacter P (((fourOddCrtProductEquiv P).toEquiv x).2 +
              oddCoordinate P k)) *
          (quadraticCharacterFour (((fourOddCrtProductEquiv P).toEquiv x).1 +
            fourCoordinate P l) *
            quadraticCharacter P (((fourOddCrtProductEquiv P).toEquiv x).2 +
              oddCoordinate P l))) = _
      exact Equiv.sum_comp (fourOddCrtProductEquiv P).toEquiv
        (fun y : ZMod 4 × ZMod P.modulus =>
          (quadraticCharacterFour (y.1 + fourCoordinate P k) *
            quadraticCharacter P (y.2 + oddCoordinate P k)) *
          (quadraticCharacterFour (y.1 + fourCoordinate P l) *
            quadraticCharacter P (y.2 + oddCoordinate P l)))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      have hreorder (a : ZMod 4) (b : ZMod P.modulus) :
          (quadraticCharacterFour (a + fourCoordinate P k) *
            quadraticCharacter P (b + oddCoordinate P k)) *
          (quadraticCharacterFour (a + fourCoordinate P l) *
            quadraticCharacter P (b + oddCoordinate P l)) =
            (quadraticCharacterFour (a + fourCoordinate P k) *
              quadraticCharacterFour (a + fourCoordinate P l)) *
            (quadraticCharacter P (b + oddCoordinate P k) *
              quadraticCharacter P (b + oddCoordinate P l)) := by
        ring
      simp_rw [hreorder]
      conv_lhs =>
        enter [2, x]
        rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- Closed coarse complete-correlation envelope at the level-four/odd composite modulus. -/
theorem fourOdd_quadratic_shiftCorrelation_norm_le_modulus [DecidableEq I]
    (P : OddPrimeFamily I) (k l : ZMod (fourOddModulus P)) :
    ‖∑ x : ZMod (fourOddModulus P),
      fourOddQuadraticCharacter P (x + k) * fourOddQuadraticCharacter P (x + l)‖ ≤
      4 * (P.modulus : ℝ) := by
  rw [fourOdd_quadratic_shiftCorrelation, Complex.norm_mul]
  exact mul_le_mul (quadraticCharacterFour_correlation_norm_le _ _)
    (quadratic_shiftCorrelation_norm_le_modulus P _ _) (norm_nonneg _) (by norm_num)

/-- Integer shifts project to their literal level-four residue coordinates. -/
theorem fourCoordinate_intCast (P : OddPrimeFamily I) (n : ℤ) :
    fourCoordinate P (n : ZMod (fourOddModulus P)) = (n : ZMod 4) := by
  have h := map_intCast (fourOddCrtProductEquiv P) n
  exact congrArg Prod.fst h

/-- Integer shifts project to their literal odd-modulus residue coordinates. -/
theorem oddCoordinate_intCast (P : OddPrimeFamily I) (n : ℤ) :
    oddCoordinate P (n : ZMod (fourOddModulus P)) = (n : ZMod P.modulus) := by
  have h := map_intCast (fourOddCrtProductEquiv P) n
  exact congrArg Prod.snd h

/-- The integer-shift composite correlation is controlled by the odd local gcd. -/
theorem fourOdd_quadratic_shiftCorrelation_norm_le_gcdOdd [DecidableEq I]
    (P : OddPrimeFamily I) (k l : ℤ) :
    ‖∑ x : ZMod (fourOddModulus P),
      fourOddQuadraticCharacter P (x + (k : ZMod (fourOddModulus P))) *
        fourOddQuadraticCharacter P (x + (l : ZMod (fourOddModulus P)))‖ ≤
      4 * P.modulus.gcd (l - k).natAbs := by
  rw [fourOdd_quadratic_shiftCorrelation, Complex.norm_mul]
  rw [fourCoordinate_intCast, fourCoordinate_intCast, oddCoordinate_intCast, oddCoordinate_intCast]
  exact mul_le_mul (quadraticCharacterFour_correlation_norm_le _ _)
    (quadratic_shiftCorrelation_norm_le_gcd P k l) (norm_nonneg _) (by norm_num)

/-- Enlarging the modulus by four can only increase the gcd kernel. -/
theorem gcdOdd_le_gcdFourOdd (P : OddPrimeFamily I) (d : ℕ) :
    P.modulus.gcd d ≤ (fourOddModulus P).gcd d := by
  rw [fourOddModulus_eq]
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left d
      (mul_ne_zero (by norm_num) P.modulus_neZero.out |> Nat.pos_of_ne_zero))
    (gcd_dvd_gcd (dvd_mul_of_dvd_right (dvd_refl P.modulus) 4) dvd_rfl)

/-- Level-four/odd complete correlations satisfy a closed integer-shift gcd majorant. -/
theorem fourOdd_quadratic_shiftCorrelation_norm_le_gcd [DecidableEq I]
    (P : OddPrimeFamily I) (k l : ℤ) :
    ‖∑ x : ZMod (fourOddModulus P),
      fourOddQuadraticCharacter P (x + (k : ZMod (fourOddModulus P))) *
        fourOddQuadraticCharacter P (x + (l : ZMod (fourOddModulus P)))‖ ≤
      4 * (fourOddModulus P).gcd (l - k).natAbs := by
  calc
    _ ≤ (4 : ℝ) * P.modulus.gcd (l - k).natAbs :=
      fourOdd_quadratic_shiftCorrelation_norm_le_gcdOdd P k l
    _ ≤ (4 : ℝ) * (fourOddModulus P).gcd (l - k).natAbs := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast gcdOdd_le_gcdFourOdd P (l - k).natAbs
      · norm_num

end OddPrimeFamily
end RHTower
