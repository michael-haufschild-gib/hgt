/-
# Fundamental-discriminant Kronecker identities for certified CRT characters

The three primitive quadratic CRT characters at levels `4q` and `8q` are
identified pointwise with the standard Kronecker convention for their signed
fundamental discriminants.  Every branch is finite: even inputs vanish, and
the odd branch uses Jacobi reciprocity and the explicit two-adic characters.
-/
import GaloisForLFunctions.RHTower.DirichletCharacterFundamentalDiscriminant
import GaloisForLFunctions.RHTower.DirichletCharacterTwoAdicCRTProduct

noncomputable section

namespace RHTower
namespace OddPrimeFamily

/-- The even-discriminant Kronecker convention is multiplicative in its numerator. -/
theorem evenKroneckerSymbol_mul (A B : ℤ) (n : ℕ) :
    evenKroneckerSymbol (A * B) n = evenKroneckerSymbol A n * evenKroneckerSymbol B n := by
  unfold evenKroneckerSymbol
  by_cases heven : Even n
  · simp [heven]
  · simp [heven, jacobiSym.mul_left]

/-- The complex level-four local character is the `-4` Kronecker value on integer lifts. -/
theorem quadraticCharacterFour_intCast_eq_evenKroneckerSymbol (n : ℕ) :
    quadraticCharacterFour ((n : ℤ) : ZMod 4) = (evenKroneckerSymbol (-4) n : ℂ) := by
  change ((ZMod.χ₄ ((n : ℤ) : ZMod 4) : ℤ) : ℂ) = _
  simpa using congrArg (fun z : ℤ => (z : ℂ))
    (evenKroneckerSymbol_negFour_eq_chiFour n).symm

/-- The first complex level-eight local character is the `8` Kronecker value on integer lifts. -/
theorem quadraticCharacterEight_intCast_eq_evenKroneckerSymbol (n : ℕ) :
    quadraticCharacterEight ((n : ℤ) : ZMod 8) = (evenKroneckerSymbol 8 n : ℂ) := by
  change ((ZMod.χ₈ ((n : ℤ) : ZMod 8) : ℤ) : ℂ) = _
  simpa using congrArg (fun z : ℤ => (z : ℂ))
    (evenKroneckerSymbol_eight_eq_chiEight n).symm

/-- The second complex level-eight local character is the `-8` Kronecker value on integer lifts. -/
theorem quadraticCharacterEightPrime_intCast_eq_evenKroneckerSymbol (n : ℕ) :
    quadraticCharacterEightPrime ((n : ℤ) : ZMod 8) = (evenKroneckerSymbol (-8) n : ℂ) := by
  change ((ZMod.χ₈' ((n : ℤ) : ZMod 8) : ℤ) : ℂ) = _
  simpa using congrArg (fun z : ℤ => (z : ℂ))
    (evenKroneckerSymbol_negEight_eq_chiEightPrime n).symm

/-- Integer lifts evaluate the level-four CRT character coordinatewise. -/
theorem fourOddQuadraticDirichletCharacter_intCast_eval {I : Type*} [Fintype I]
    (P : OddPrimeFamily I) (n : ℕ) :
    fourOddQuadraticDirichletCharacter P ((n : ℤ) : ZMod (fourOddModulus P)) =
      quadraticCharacterFour ((n : ℤ) : ZMod 4) *
        quadraticDirichletCharacter P ((n : ℤ) : ZMod P.modulus) := by
  rw [fourOddQuadraticDirichletCharacter, crtProductCharacter_apply]
  change quadraticCharacterFour (fourCoordinate P ((n : ℤ) : ZMod (fourOddModulus P))) *
      quadraticDirichletCharacter P (oddCoordinate P ((n : ℤ) : ZMod (fourOddModulus P))) = _
  rw [fourCoordinate_intCast, oddCoordinate_intCast]

/-- Integer lifts evaluate the first level-eight CRT character coordinatewise. -/
theorem eightOddQuadraticDirichletCharacterEight_intCast_eval {I : Type*} [Fintype I]
    (P : OddPrimeFamily I) (n : ℕ) :
    eightOddQuadraticDirichletCharacterEight P ((n : ℤ) : ZMod (eightOddModulus P)) =
      quadraticCharacterEight ((n : ℤ) : ZMod 8) *
        quadraticDirichletCharacter P ((n : ℤ) : ZMod P.modulus) := by
  rw [eightOddQuadraticDirichletCharacterEight, crtProductCharacter_apply]
  change quadraticCharacterEight (eightCoordinate P ((n : ℤ) : ZMod (eightOddModulus P))) *
      quadraticDirichletCharacter P (eightOddCoordinate P ((n : ℤ) : ZMod (eightOddModulus P))) = _
  rw [eightCoordinate_intCast, eightOddCoordinate_intCast]

/-- Integer lifts evaluate the second level-eight CRT character coordinatewise. -/
theorem eightOddQuadraticDirichletCharacterEightPrime_intCast_eval {I : Type*} [Fintype I]
    (P : OddPrimeFamily I) (n : ℕ) :
    eightOddQuadraticDirichletCharacterEightPrime P ((n : ℤ) : ZMod (eightOddModulus P)) =
      quadraticCharacterEightPrime ((n : ℤ) : ZMod 8) *
        quadraticDirichletCharacter P ((n : ℤ) : ZMod P.modulus) := by
  rw [eightOddQuadraticDirichletCharacterEightPrime, crtProductCharacter_apply]
  change quadraticCharacterEightPrime (eightCoordinate P ((n : ℤ) : ZMod (eightOddModulus P))) *
      quadraticDirichletCharacter P (eightOddCoordinate P ((n : ℤ) : ZMod (eightOddModulus P))) = _
  rw [eightCoordinate_intCast, eightOddCoordinate_intCast]

/-- The certified level-four CRT character is its signed fundamental-discriminant Kronecker symbol. -/
theorem fourOddQuadraticDirichletCharacter_intCast_eq_fundamentalKronecker
    {I : Type*} [Fintype I] (P : OddPrimeFamily I) (n : ℕ) :
    (evenKroneckerSymbol (fourOddFundamentalDiscriminant P) n : ℂ) =
      fourOddQuadraticDirichletCharacter P ((n : ℤ) : ZMod (fourOddModulus P)) := by
  by_cases hmod : P.modulus % 4 = 1
  · rw [fourOddFundamentalDiscriminant, if_pos hmod,
      fourOddQuadraticDirichletCharacter_intCast_eval,
      quadraticCharacterFour_intCast_eq_evenKroneckerSymbol,
      quadraticDirichletCharacter_intCast_eq_jacobi]
    rw [evenKroneckerSymbol_mul]
    by_cases heven : Even n
    · have hzero : evenKroneckerSymbol (-4) n = 0 := by
        simp [evenKroneckerSymbol, heven]
      simp [hzero]
    · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
      have hrecip : jacobiSym (P.modulus : ℤ) n = jacobiSym n P.modulus :=
        jacobiSym.quadratic_reciprocity_one_mod_four hmod hodd
      simp only [evenKroneckerSymbol, if_neg heven, Int.cast_mul]
      rw [hrecip]
  · have hthree : P.modulus % 4 = 3 := by
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (modulus_odd P)) with hone | hthree
      · exact False.elim (hmod hone)
      · exact hthree
    rw [fourOddFundamentalDiscriminant, if_neg hmod,
      fourOddQuadraticDirichletCharacter_intCast_eval,
      quadraticCharacterFour_intCast_eq_evenKroneckerSymbol,
      quadraticDirichletCharacter_intCast_eq_jacobi]
    rw [evenKroneckerSymbol_mul]
    by_cases heven : Even n
    · have hzero : evenKroneckerSymbol 4 n = 0 := by
        simp [evenKroneckerSymbol, heven]
      have hlocal : evenKroneckerSymbol (-4) n = 0 := by
        simp [evenKroneckerSymbol, heven]
      simp [hzero, hlocal]
    · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
      have hfour : jacobiSym 4 n = 1 := jacobiSym.at_four hodd
      have hlocal : jacobiSym (-4) n = ZMod.χ₄ n := by
        simpa [evenKroneckerSymbol, heven] using evenKroneckerSymbol_negFour_eq_chiFour n
      have hrecip : jacobiSym (P.modulus : ℤ) n = ZMod.χ₄ n * jacobiSym n P.modulus := by
        rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with hn1 | hn3
        · rw [jacobiSym.quadratic_reciprocity_one_mod_four'
            (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hthree)) hn1,
            ZMod.χ₄_nat_one_mod_four hn1, one_mul]
        · rw [jacobiSym.quadratic_reciprocity_three_mod_four hthree hn3,
            ZMod.χ₄_nat_three_mod_four hn3, neg_one_mul]
      simp only [evenKroneckerSymbol, if_neg heven, Int.cast_mul]
      rw [hfour]
      simp only [Int.cast_one, one_mul]
      rw [hrecip, hlocal, Int.cast_mul]

/-- The certified first level-eight CRT character is its signed fundamental-discriminant Kronecker symbol. -/
theorem eightOddQuadraticDirichletCharacterEight_intCast_eq_fundamentalKronecker
    {I : Type*} [Fintype I] (P : OddPrimeFamily I) (n : ℕ) :
    (evenKroneckerSymbol (eightOddFundamentalDiscriminant P) n : ℂ) =
      eightOddQuadraticDirichletCharacterEight P ((n : ℤ) : ZMod (eightOddModulus P)) := by
  by_cases hmod : P.modulus % 4 = 1
  · rw [eightOddFundamentalDiscriminant, if_pos hmod,
      eightOddQuadraticDirichletCharacterEight_intCast_eval,
      quadraticCharacterEight_intCast_eq_evenKroneckerSymbol,
      quadraticDirichletCharacter_intCast_eq_jacobi]
    rw [evenKroneckerSymbol_mul]
    by_cases heven : Even n
    · have hzero : evenKroneckerSymbol 8 n = 0 := by
        simp [evenKroneckerSymbol, heven]
      simp [hzero]
    · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
      have hrecip : jacobiSym (P.modulus : ℤ) n = jacobiSym n P.modulus :=
        jacobiSym.quadratic_reciprocity_one_mod_four hmod hodd
      simp only [evenKroneckerSymbol, if_neg heven, Int.cast_mul]
      rw [hrecip]
  · have hthree : P.modulus % 4 = 3 := by
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (modulus_odd P)) with hone | hthree
      · exact False.elim (hmod hone)
      · exact hthree
    rw [eightOddFundamentalDiscriminant, if_neg hmod,
      eightOddQuadraticDirichletCharacterEight_intCast_eval,
      quadraticCharacterEight_intCast_eq_evenKroneckerSymbol,
      quadraticDirichletCharacter_intCast_eq_jacobi]
    rw [evenKroneckerSymbol_mul]
    by_cases heven : Even n
    · have hzero : evenKroneckerSymbol (-8) n = 0 := by
        simp [evenKroneckerSymbol, heven]
      have hlocal : evenKroneckerSymbol 8 n = 0 := by
        simp [evenKroneckerSymbol, heven]
      simp [hzero, hlocal]
    · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
      have hnegEight : jacobiSym (-8) n = ZMod.χ₈' n := by
        simpa [evenKroneckerSymbol, heven] using evenKroneckerSymbol_negEight_eq_chiEightPrime n
      have hrecip : jacobiSym (P.modulus : ℤ) n = ZMod.χ₄ n * jacobiSym n P.modulus := by
        rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with hn1 | hn3
        · rw [jacobiSym.quadratic_reciprocity_one_mod_four'
            (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hthree)) hn1,
            ZMod.χ₄_nat_one_mod_four hn1, one_mul]
        · rw [jacobiSym.quadratic_reciprocity_three_mod_four hthree hn3,
            ZMod.χ₄_nat_three_mod_four hn3, neg_one_mul]
      have hrel : ZMod.χ₈' n = ZMod.χ₄ n * ZMod.χ₈ n := by
        simpa using ZMod.χ₈'_int_eq_χ₄_mul_χ₈ (n : ℤ)
      have hposEight : jacobiSym 8 n = ZMod.χ₈ n := by
        simpa [evenKroneckerSymbol, heven] using evenKroneckerSymbol_eight_eq_chiEight n
      have hsqC : (ZMod.χ₄ n : ℂ) * (ZMod.χ₄ n : ℂ) = 1 := by
        rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with hn1 | hn3
        · rw [ZMod.χ₄_nat_one_mod_four hn1]
          norm_num
        · rw [ZMod.χ₄_nat_three_mod_four hn3]
          norm_num
      simp only [evenKroneckerSymbol, if_neg heven, Int.cast_mul]
      rw [hnegEight, hrecip, hrel, hposEight]
      simp only [Int.cast_mul]
      calc
        (ZMod.χ₄ n : ℂ) * (ZMod.χ₈ n : ℂ) *
            ((ZMod.χ₄ n : ℂ) * (jacobiSym n P.modulus : ℂ)) =
            ((ZMod.χ₄ n : ℂ) * (ZMod.χ₄ n : ℂ)) *
              ((ZMod.χ₈ n : ℂ) * (jacobiSym n P.modulus : ℂ)) := by ring
        _ = (ZMod.χ₈ n : ℂ) * (jacobiSym n P.modulus : ℂ) := by rw [hsqC, one_mul]

/-- The certified second level-eight CRT character is its signed fundamental-discriminant Kronecker symbol. -/
theorem eightOddQuadraticDirichletCharacterEightPrime_intCast_eq_fundamentalKronecker
    {I : Type*} [Fintype I] (P : OddPrimeFamily I) (n : ℕ) :
    (evenKroneckerSymbol (eightOddPrimeFundamentalDiscriminant P) n : ℂ) =
      eightOddQuadraticDirichletCharacterEightPrime P ((n : ℤ) : ZMod (eightOddModulus P)) := by
  by_cases hmod : P.modulus % 4 = 1
  · rw [eightOddPrimeFundamentalDiscriminant, if_pos hmod,
      eightOddQuadraticDirichletCharacterEightPrime_intCast_eval,
      quadraticCharacterEightPrime_intCast_eq_evenKroneckerSymbol,
      quadraticDirichletCharacter_intCast_eq_jacobi]
    rw [evenKroneckerSymbol_mul]
    by_cases heven : Even n
    · have hzero : evenKroneckerSymbol (-8) n = 0 := by
        simp [evenKroneckerSymbol, heven]
      simp [hzero]
    · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
      have hrecip : jacobiSym (P.modulus : ℤ) n = jacobiSym n P.modulus :=
        jacobiSym.quadratic_reciprocity_one_mod_four hmod hodd
      simp only [evenKroneckerSymbol, if_neg heven, Int.cast_mul]
      rw [hrecip]
  · have hthree : P.modulus % 4 = 3 := by
      rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp (modulus_odd P)) with hone | hthree
      · exact False.elim (hmod hone)
      · exact hthree
    rw [eightOddPrimeFundamentalDiscriminant, if_neg hmod,
      eightOddQuadraticDirichletCharacterEightPrime_intCast_eval,
      quadraticCharacterEightPrime_intCast_eq_evenKroneckerSymbol,
      quadraticDirichletCharacter_intCast_eq_jacobi]
    rw [evenKroneckerSymbol_mul]
    by_cases heven : Even n
    · have hzero : evenKroneckerSymbol 8 n = 0 := by
        simp [evenKroneckerSymbol, heven]
      have hlocal : evenKroneckerSymbol (-8) n = 0 := by
        simp [evenKroneckerSymbol, heven]
      simp [hzero, hlocal]
    · have hodd : Odd n := Nat.not_even_iff_odd.mp heven
      have hposEight : jacobiSym 8 n = ZMod.χ₈ n := by
        simpa [evenKroneckerSymbol, heven] using evenKroneckerSymbol_eight_eq_chiEight n
      have hnegEight : jacobiSym (-8) n = ZMod.χ₈' n := by
        simpa [evenKroneckerSymbol, heven] using evenKroneckerSymbol_negEight_eq_chiEightPrime n
      have hrecip : jacobiSym (P.modulus : ℤ) n = ZMod.χ₄ n * jacobiSym n P.modulus := by
        rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd) with hn1 | hn3
        · rw [jacobiSym.quadratic_reciprocity_one_mod_four'
            (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_three hthree)) hn1,
            ZMod.χ₄_nat_one_mod_four hn1, one_mul]
        · rw [jacobiSym.quadratic_reciprocity_three_mod_four hthree hn3,
            ZMod.χ₄_nat_three_mod_four hn3, neg_one_mul]
      have hrel : ZMod.χ₈' n = ZMod.χ₄ n * ZMod.χ₈ n := by
        simpa using ZMod.χ₈'_int_eq_χ₄_mul_χ₈ (n : ℤ)
      simp only [evenKroneckerSymbol, if_neg heven, Int.cast_mul]
      rw [hposEight, hrecip, hnegEight, hrel]
      simp only [Int.cast_mul]
      ring

/-- Pointwise level-four CRT/Kronecker identity at every residue. -/
theorem fourOddQuadraticDirichletCharacter_eq_fundamentalKronecker
    {I : Type*} [Fintype I] (P : OddPrimeFamily I) (x : ZMod (fourOddModulus P)) :
    (evenKroneckerSymbol (fourOddFundamentalDiscriminant P) x.val : ℂ) =
      fourOddQuadraticDirichletCharacter P x := by
  simpa [ZMod.val_natCast_of_lt x.val_lt] using
    fourOddQuadraticDirichletCharacter_intCast_eq_fundamentalKronecker P x.val

/-- Pointwise first level-eight CRT/Kronecker identity at every residue. -/
theorem eightOddQuadraticDirichletCharacterEight_eq_fundamentalKronecker
    {I : Type*} [Fintype I] (P : OddPrimeFamily I) (x : ZMod (eightOddModulus P)) :
    (evenKroneckerSymbol (eightOddFundamentalDiscriminant P) x.val : ℂ) =
      eightOddQuadraticDirichletCharacterEight P x := by
  simpa [ZMod.val_natCast_of_lt x.val_lt] using
    eightOddQuadraticDirichletCharacterEight_intCast_eq_fundamentalKronecker P x.val

/-- Pointwise second level-eight CRT/Kronecker identity at every residue. -/
theorem eightOddQuadraticDirichletCharacterEightPrime_eq_fundamentalKronecker
    {I : Type*} [Fintype I] (P : OddPrimeFamily I) (x : ZMod (eightOddModulus P)) :
    (evenKroneckerSymbol (eightOddPrimeFundamentalDiscriminant P) x.val : ℂ) =
      eightOddQuadraticDirichletCharacterEightPrime P x := by
  simpa [ZMod.val_natCast_of_lt x.val_lt] using
    eightOddQuadraticDirichletCharacterEightPrime_intCast_eq_fundamentalKronecker P x.val

end OddPrimeFamily
end RHTower
