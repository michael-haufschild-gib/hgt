import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.CharacterFiberCount
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Active characters in finite-field power fibers

The complex character group of a finite field is cyclic. Inside the
characters killed by `n`, the characters also killed by `a` therefore
form a kernel of gcd cardinality. Its complement counts the nontrivial
Gauss factors in a three-point Jacobi expansion.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable (K : Type*) [Field K] [Finite K]

omit [Finite K] in
/-- The multiplicative order of a finite field divides that of every finite field extension. -/
theorem finiteField_unit_card_dvd_extension (L : Type*) [Field L] [Finite L] [Algebra K L] :
    Nat.card K - 1 ∣ Nat.card L - 1 := by
  rw [Module.natCard_eq_pow_finrank (K := K) (V := L)]
  exact Nat.sub_one_dvd_pow_sub_one (Nat.card K) (Module.finrank K L)

/-- The complex multiplicative characters of a finite field form a cyclic group. -/
theorem finiteField_mulChar_isCyclic : IsCyclic (MulChar K ℂ) := by
  obtain ⟨e⟩ := MulChar.mulEquiv_units K ℂ
  exact e.isCyclic.mpr inferInstance

/-- Characters killed by two prescribed powers are counted by the iterated gcd. -/
theorem finiteField_power_character_kernel_card (n a : ℕ) :
    Nat.card {χ : unitEndomorphismCharacters (R := ℂ) (powMonoidHom n : Kˣ →* Kˣ) |
      χ.val ^ a = 1} = Nat.gcd (Nat.gcd (Nat.card K - 1) n) a := by
  letI := finiteField_mulChar_isCyclic K
  let H := unitEndomorphismCharacters (R := ℂ) (powMonoidHom n : Kˣ →* Kˣ)
  let E : {χ : H | χ.val ^ a = 1} ≃ (powMonoidHom a : H →* H).ker :=
    { toFun χ := ⟨χ.val, Subtype.ext χ.property⟩
      invFun χ := ⟨χ.val, congrArg (fun ψ : H => ψ.val) χ.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr E, IsCyclic.card_powMonoidHom_ker]
  change Nat.gcd (Nat.card (unitEndomorphismCharacters (R := ℂ)
    (powMonoidHom n : Kˣ →* Kˣ))) a = _
  rw [powerEndomorphismCharacters_card, Nat.card_units]

/-- The characters producing a nontrivial powered character are counted by subtracting that kernel. -/
theorem finiteField_power_character_active_card (n a : ℕ) :
    Nat.card {χ : unitEndomorphismCharacters (R := ℂ) (powMonoidHom n : Kˣ →* Kˣ) |
      χ.val ^ a ≠ 1} =
      Nat.gcd (Nat.card K - 1) n - Nat.gcd (Nat.gcd (Nat.card K - 1) n) a := by
  classical
  let H := unitEndomorphismCharacters (R := ℂ) (powMonoidHom n : Kˣ →* Kˣ)
  letI : Fintype H := Fintype.ofFinite _
  have h := Fintype.card_subtype_compl (fun χ : H => χ.val ^ a = 1)
  simp only [← Nat.card_eq_fintype_card] at h
  calc
    _ = Nat.card H - Nat.card {χ : H | χ.val ^ a = 1} := h
    _ = _ := by
      change Nat.card (unitEndomorphismCharacters (R := ℂ) (powMonoidHom n : Kˣ →* Kˣ)) -
        Nat.card {χ : unitEndomorphismCharacters (R := ℂ) (powMonoidHom n : Kˣ →* Kˣ) |
          χ.val ^ a = 1} = _
      rw [powerEndomorphismCharacters_card, Nat.card_units, finiteField_power_character_kernel_card]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
