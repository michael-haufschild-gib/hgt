import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialOrderClosedPoints
import Mathlib.FieldTheory.Finite.Extension

/-!
# Divisibility monotonicity of extension point counts

A closed prime supporting points over degree `e` also supports points over
every multiple of `e`. The degree-weighted closed-prime formula therefore
makes extension point counts monotone along divisibility.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolynomialOrderClosedPoints
open Polynomial IsDedekindDomain
variable (K B : Type*) [Field K] [Finite K] [CommRing B] [IsDedekindDomain B]
    [Infinite B] [Algebra K B] [Algebra K[X] B] [IsScalarTower K K[X] B]
    [Module.Finite K[X] B] (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Passing to a divisible extension degree retains every splitting closed prime. -/
theorem placesOver_extension_subset {e f : ℕ} [NeZero e] [NeZero f] (hef : e ∣ f) :
    placesOver K B (FiniteField.Extension K p e) ⊆
      placesOver K B (FiniteField.Extension K p f) := by
  intro v hv
  rw [mem_placesOver_iff, FiniteField.finrank_extension] at hv ⊢
  exact hv.trans hef

/-- Extension-valued algebra points are monotone under divisibility of extension degrees. -/
theorem card_algHom_extension_mono {e f : ℕ} [NeZero e] [NeZero f] (hef : e ∣ f) :
    Nat.card (B →ₐ[K] FiniteField.Extension K p e) ≤
      Nat.card (B →ₐ[K] FiniteField.Extension K p f) := by
  rw [card_algHom_eq_closed_place_sum K B (FiniteField.Extension K p e),
    card_algHom_eq_closed_place_sum K B (FiniteField.Extension K p f)]
  simp only [Finset.sum_coe_sort]
  exact Finset.sum_le_sum_of_subset (placesOver_extension_subset K B p hef)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PolynomialOrderClosedPoints
