/-
# CRT composition of the conductor-eight and odd quadratic characters

This module constructs each explicit conductor-eight character times the
certified odd square-free CRT character and proves closed correlation bounds.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicQuadratic
import GaloisForLFunctions.RHTower.QuadraticJacobiSum

open scoped BigOperators

noncomputable section

namespace RHTower
namespace OddPrimeFamily

variable {I : Type*} [Fintype I]

/-- The conductor-eight and certified odd CRT factors. -/
def eightOddFactors (P : OddPrimeFamily I) : Fin 2 → ℕ := ![8, P.modulus]

/-- Composite modulus of the conductor-eight and certified odd factors. -/
def eightOddModulus (P : OddPrimeFamily I) : ℕ := ∏ i, eightOddFactors P i

/-- The composite modulus is literally eight times the certified odd modulus. -/
theorem eightOddModulus_eq (P : OddPrimeFamily I) : eightOddModulus P = 8 * P.modulus := by
  simp [eightOddModulus, eightOddFactors, Fin.prod_univ_two]

/-- The certified odd CRT product has no factor two. -/
theorem two_not_dvd_oddModulus (P : OddPrimeFamily I) : ¬ 2 ∣ P.modulus := by
  rw [modulus]
  apply Nat.prime_two.prime.not_dvd_finsetProd
  intro i hi hdiv
  rcases (Nat.dvd_prime (P.prime i).2.1).mp hdiv with h | h
  · norm_num at h
  · exact P.prime i |>.2.2 h.symm

/-- The conductor-eight local factor is coprime to the certified odd modulus. -/
theorem eight_coprime_modulus (P : OddPrimeFamily I) : Nat.Coprime 8 P.modulus := by
  have h : Nat.Coprime 2 P.modulus :=
    Nat.prime_two.coprime_iff_not_dvd.mpr (two_not_dvd_oddModulus P)
  simpa using h.pow_left 3

/-- The conductor-eight and odd factors form an internally certified CRT pair. -/
theorem eightOdd_pairwise_coprime (P : OddPrimeFamily I) :
    Pairwise fun i j => Nat.Coprime (eightOddFactors P i) (eightOddFactors P j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eightOddFactors]
  all_goals first | exact eight_coprime_modulus P | exact (eight_coprime_modulus P).symm

/-- CRT equivalence for the conductor-eight/odd composite modulus. -/
def eightOddCrtEquiv (P : OddPrimeFamily I) :
    ZMod (eightOddModulus P) ≃+* (∀ i, ZMod (eightOddFactors P i)) :=
  ZMod.prodEquivPi (eightOddFactors P) (eightOdd_pairwise_coprime P)

/-- CRT equivalence in ordinary product coordinates. -/
def eightOddCrtProductEquiv (P : OddPrimeFamily I) :
    ZMod (eightOddModulus P) ≃+* (ZMod 8 × ZMod P.modulus) :=
  (eightOddCrtEquiv P).trans
    ((RingEquiv.piFinTwo fun i => ZMod (eightOddFactors P i)).trans
      (RingEquiv.prodCongr
        (ZMod.ringEquivCongr (by simp [eightOddFactors]))
        (ZMod.ringEquivCongr (by simp [eightOddFactors]))))

instance eightOddModulus_neZero (P : OddPrimeFamily I) : NeZero (eightOddModulus P) := ⟨by
  rw [eightOddModulus_eq]
  exact mul_ne_zero (by norm_num) P.modulus_neZero.out⟩

/-- The conductor-eight CRT coordinate. -/
def eightCoordinate (P : OddPrimeFamily I) (x : ZMod (eightOddModulus P)) : ZMod 8 :=
  (eightOddCrtProductEquiv P x).1

/-- The certified odd CRT coordinate. -/
def eightOddCoordinate (P : OddPrimeFamily I) (x : ZMod (eightOddModulus P)) :
    ZMod P.modulus :=
  (eightOddCrtProductEquiv P x).2

/-- The conductor-eight CRT coordinate respects addition. -/
theorem eightCoordinate_add (P : OddPrimeFamily I) (x z : ZMod (eightOddModulus P)) :
    eightCoordinate P (x + z) = eightCoordinate P x + eightCoordinate P z := by
  change (eightOddCrtProductEquiv P (x + z)).1 =
    (eightOddCrtProductEquiv P x).1 + (eightOddCrtProductEquiv P z).1
  rw [map_add]
  rfl

/-- The certified odd CRT coordinate respects addition. -/
theorem eightOddCoordinate_add (P : OddPrimeFamily I) (x z : ZMod (eightOddModulus P)) :
    eightOddCoordinate P (x + z) = eightOddCoordinate P x + eightOddCoordinate P z := by
  change (eightOddCrtProductEquiv P (x + z)).2 =
    (eightOddCrtProductEquiv P x).2 + (eightOddCrtProductEquiv P z).2
  rw [map_add]
  rfl

/-- Product of an arbitrary level-eight complex function with the odd CRT quadratic character. -/
def eightOddQuadraticCharacter (γ : ZMod 8 → ℂ) (P : OddPrimeFamily I)
    (x : ZMod (eightOddModulus P)) : ℂ :=
  γ (eightCoordinate P x) * quadraticCharacter P (eightOddCoordinate P x)

/-- The first conductor-eight quadratic composite character. -/
def eightOddQuadraticCharacterEight (P : OddPrimeFamily I) :
    ZMod (eightOddModulus P) → ℂ :=
  eightOddQuadraticCharacter quadraticCharacterEight P

/-- The second conductor-eight quadratic composite character. -/
def eightOddQuadraticCharacterEightPrime (P : OddPrimeFamily I) :
    ZMod (eightOddModulus P) → ℂ :=
  eightOddQuadraticCharacter quadraticCharacterEightPrime P

/-- Exact complete-correlation factorization for a conductor-eight/odd composite character. -/
theorem eightOdd_shiftCorrelation (γ : ZMod 8 → ℂ) (P : OddPrimeFamily I)
    (k l : ZMod (eightOddModulus P)) :
    ∑ x : ZMod (eightOddModulus P),
      eightOddQuadraticCharacter γ P (x + k) * eightOddQuadraticCharacter γ P (x + l) =
      (∑ a : ZMod 8,
        γ (a + eightCoordinate P k) * γ (a + eightCoordinate P l)) *
      (∑ b : ZMod P.modulus,
        quadraticCharacter P (b + eightOddCoordinate P k) *
          quadraticCharacter P (b + eightOddCoordinate P l)) := by
  calc
    _ = ∑ x : ZMod (eightOddModulus P),
        (γ (eightCoordinate P x + eightCoordinate P k) *
          quadraticCharacter P (eightOddCoordinate P x + eightOddCoordinate P k)) *
        (γ (eightCoordinate P x + eightCoordinate P l) *
          quadraticCharacter P (eightOddCoordinate P x + eightOddCoordinate P l)) := by
      simp_rw [eightOddQuadraticCharacter, eightCoordinate_add, eightOddCoordinate_add]
    _ = ∑ y : ZMod 8 × ZMod P.modulus,
        (γ (y.1 + eightCoordinate P k) *
          quadraticCharacter P (y.2 + eightOddCoordinate P k)) *
        (γ (y.1 + eightCoordinate P l) *
          quadraticCharacter P (y.2 + eightOddCoordinate P l)) := by
      change (∑ x : ZMod (eightOddModulus P),
          (γ (((eightOddCrtProductEquiv P).toEquiv x).1 + eightCoordinate P k) *
            quadraticCharacter P (((eightOddCrtProductEquiv P).toEquiv x).2 +
              eightOddCoordinate P k)) *
          (γ (((eightOddCrtProductEquiv P).toEquiv x).1 + eightCoordinate P l) *
            quadraticCharacter P (((eightOddCrtProductEquiv P).toEquiv x).2 +
              eightOddCoordinate P l))) = _
      exact Equiv.sum_comp (eightOddCrtProductEquiv P).toEquiv
        (fun y : ZMod 8 × ZMod P.modulus =>
          (γ (y.1 + eightCoordinate P k) *
            quadraticCharacter P (y.2 + eightOddCoordinate P k)) *
          (γ (y.1 + eightCoordinate P l) *
            quadraticCharacter P (y.2 + eightOddCoordinate P l)))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      have hreorder (a : ZMod 8) (b : ZMod P.modulus) :
          (γ (a + eightCoordinate P k) * quadraticCharacter P (b + eightOddCoordinate P k)) *
          (γ (a + eightCoordinate P l) * quadraticCharacter P (b + eightOddCoordinate P l)) =
            (γ (a + eightCoordinate P k) * γ (a + eightCoordinate P l)) *
            (quadraticCharacter P (b + eightOddCoordinate P k) *
              quadraticCharacter P (b + eightOddCoordinate P l)) := by
        ring
      simp_rw [hreorder]
      conv_lhs =>
        enter [2, x]
        rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- Integer shifts project to their literal conductor-eight residue coordinate. -/
theorem eightCoordinate_intCast (P : OddPrimeFamily I) (n : ℤ) :
    eightCoordinate P (n : ZMod (eightOddModulus P)) = (n : ZMod 8) := by
  have h := map_intCast (eightOddCrtProductEquiv P) n
  exact congrArg Prod.fst h

/-- Integer shifts project to their literal odd-modulus residue coordinate. -/
theorem eightOddCoordinate_intCast (P : OddPrimeFamily I) (n : ℤ) :
    eightOddCoordinate P (n : ZMod (eightOddModulus P)) = (n : ZMod P.modulus) := by
  have h := map_intCast (eightOddCrtProductEquiv P) n
  exact congrArg Prod.snd h

/-- Enlarging the odd modulus by eight can only increase the gcd kernel. -/
theorem gcdOdd_le_gcdEightOdd (P : OddPrimeFamily I) (d : ℕ) :
    P.modulus.gcd d ≤ (eightOddModulus P).gcd d := by
  rw [eightOddModulus_eq]
  exact Nat.le_of_dvd (Nat.gcd_pos_of_pos_left d
      (mul_ne_zero (by norm_num) P.modulus_neZero.out |> Nat.pos_of_ne_zero))
    (gcd_dvd_gcd (dvd_mul_of_dvd_right (dvd_refl P.modulus) 8) dvd_rfl)

/-- First conductor-eight composite correlations satisfy a closed integer-shift gcd majorant. -/
theorem eightOdd_quadraticCharacterEight_shiftCorrelation_norm_le_gcd [DecidableEq I]
    (P : OddPrimeFamily I) (k l : ℤ) :
    ‖∑ x : ZMod (eightOddModulus P),
      eightOddQuadraticCharacterEight P (x + (k : ZMod (eightOddModulus P))) *
        eightOddQuadraticCharacterEight P (x + (l : ZMod (eightOddModulus P)))‖ ≤
      8 * (eightOddModulus P).gcd (l - k).natAbs := by
  rw [eightOddQuadraticCharacterEight, eightOdd_shiftCorrelation, Complex.norm_mul]
  rw [eightCoordinate_intCast, eightCoordinate_intCast,
    eightOddCoordinate_intCast, eightOddCoordinate_intCast]
  calc
    _ ≤ (8 : ℝ) * P.modulus.gcd (l - k).natAbs :=
      mul_le_mul (quadraticCharacterEight_correlation_norm_le _ _)
        (quadratic_shiftCorrelation_norm_le_gcd P k l) (norm_nonneg _) (by norm_num)
    _ ≤ (8 : ℝ) * (eightOddModulus P).gcd (l - k).natAbs := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast gcdOdd_le_gcdEightOdd P (l - k).natAbs
      · norm_num

/-- Second conductor-eight composite correlations satisfy a closed integer-shift gcd majorant. -/
theorem eightOdd_quadraticCharacterEightPrime_shiftCorrelation_norm_le_gcd [DecidableEq I]
    (P : OddPrimeFamily I) (k l : ℤ) :
    ‖∑ x : ZMod (eightOddModulus P),
      eightOddQuadraticCharacterEightPrime P (x + (k : ZMod (eightOddModulus P))) *
        eightOddQuadraticCharacterEightPrime P (x + (l : ZMod (eightOddModulus P)))‖ ≤
      8 * (eightOddModulus P).gcd (l - k).natAbs := by
  rw [eightOddQuadraticCharacterEightPrime, eightOdd_shiftCorrelation, Complex.norm_mul]
  rw [eightCoordinate_intCast, eightCoordinate_intCast,
    eightOddCoordinate_intCast, eightOddCoordinate_intCast]
  calc
    _ ≤ (8 : ℝ) * P.modulus.gcd (l - k).natAbs :=
      mul_le_mul (quadraticCharacterEightPrime_correlation_norm_le _ _)
        (quadratic_shiftCorrelation_norm_le_gcd P k l) (norm_nonneg _) (by norm_num)
    _ ≤ (8 : ℝ) * (eightOddModulus P).gcd (l - k).natAbs := by
      apply mul_le_mul_of_nonneg_left
      · exact_mod_cast gcdOdd_le_gcdEightOdd P (l - k).natAbs
      · norm_num

end OddPrimeFamily
end RHTower
