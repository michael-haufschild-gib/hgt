import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerNormFibers

/-!
# Power fibers over an arbitrary finite field

Every nonempty nonzero power fiber is a coset of the power-map kernel
in the cyclic unit group. Its size is the gcd of the exponent with the
unit-group order. This applies without requiring a quadratic field or
a norm exponent.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open scoped Classical
variable {K : Type*} [Field K] [Finite K]

/-- Every nonempty unit power fiber has the power-map kernel's gcd cardinality. -/
theorem finiteField_unit_power_fiber_card (N : ℕ) (u : Kˣ) :
    Nat.card {z : Kˣ | z ^ N = u ^ N} = Nat.gcd (Nat.card K - 1) N := by
  have h := Nat.card_congr ((powMonoidHom N : Kˣ →* Kˣ).fiberEquivKer u)
  simp only [Set.preimage, Set.mem_singleton_iff, powMonoidHom_apply] at h
  rw [h, IsCyclic.card_powMonoidHom_ker, Nat.card_units]

/-- A soluble nonzero radical equation has exactly the corresponding gcd many roots. -/
theorem finiteField_nonzero_power_fiber_card_of_soluble
    (n : ℕ) (a : K) (ha : a ≠ 0) (hsol : ∃ z : K, z ^ (n + 1) = a) :
    Nat.card {z : K | z ^ (n + 1) = a} = Nat.gcd (Nat.card K - 1) (n + 1) := by
  obtain ⟨z, hz⟩ := hsol
  have hz0 : z ≠ 0 := by
    intro h
    exact ha (hz.symm.trans (by rw [h, zero_pow (Nat.succ_ne_zero _)]))
  have hu : (Units.mk0 z hz0) ^ (n + 1) = Units.mk0 a ha := Units.ext hz
  rw [Nat.card_congr (nonzeroPowerFiberEquivUnits n a ha), ← hu]
  exact finiteField_unit_power_fiber_card (n + 1) (Units.mk0 z hz0)

/-- Every nonzero radical fiber is either empty or has the exact gcd cardinality. -/
theorem finiteField_nonzero_power_fiber_card (n : ℕ) (a : K) (ha : a ≠ 0) :
    Nat.card {z : K | z ^ (n + 1) = a} =
      if ∃ z : K, z ^ (n + 1) = a then Nat.gcd (Nat.card K - 1) (n + 1) else 0 := by
  classical
  by_cases hsol : ∃ z : K, z ^ (n + 1) = a
  · rw [if_pos hsol]
    exact finiteField_nonzero_power_fiber_card_of_soluble n a ha hsol
  · rw [if_neg hsol]
    exact Nat.card_eq_zero.mpr (Or.inl ⟨fun z => hsol ⟨z.val, z.property⟩⟩)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
