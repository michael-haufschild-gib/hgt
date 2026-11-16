import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.ReducedResidueFloorSum
import Mathlib.Data.Nat.ModEq

/-!
# Distinct pole weights from reduced residues

If `1+mR` is invertible modulo `N`, the reduced weights
`i+m(iR mod N)` represent distinct residue classes. Adding multiples of
`N` therefore preserves uniqueness of the character and polynomial degree.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

/-- A reduced weight retains its linear residue after adding any multiple of the modulus. -/
theorem reducedResidue_weighted_mod (N m R i a : ℕ) :
    (N * a + (i + m * (i * R % N))) % N = ((1 + m * R) * i) % N := by
  rw [Nat.mul_add_mod_self_left, reducedResidue_mod]

/-- Equal weighted pole orders force the same reduced character. -/
theorem reducedResidue_weighted_index_unique (N m R : ℕ)
    (hcop : Nat.Coprime (1 + m * R) N) (i j : Fin N) (a b : ℕ)
    (h : N * a + (i.val + m * (i.val * R % N)) =
      N * b + (j.val + m * (j.val * R % N))) : i = j := by
  have hm := congrArg (fun n : ℕ => n % N) h
  rw [reducedResidue_weighted_mod, reducedResidue_weighted_mod] at hm
  have hc : Nat.ModEq N i.val j.val :=
    Nat.ModEq.cancel_left_of_coprime hcop.symm hm
  exact Fin.ext (hc.eq_of_lt_of_lt i.isLt j.isLt)

/-- Every character and nonnegative polynomial degree give a different pole order. -/
theorem reducedResidue_weighted_injective (N m R : ℕ)
    (hcop : Nat.Coprime (1 + m * R) N) :
    Function.Injective (fun x : Fin N × ℕ =>
      N * x.2 + (x.1.val + m * (x.1.val * R % N))) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hij := reducedResidue_weighted_index_unique N m R hcop i j a b h
  subst j
  have hab : a = b := Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt i.isLt)
    (Nat.add_right_cancel h)
  subst b
  rfl

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
