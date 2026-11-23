import Mathlib.RingTheory.DedekindDomain.Different

/-! Membership in the trace dual is equivalent to integrality after
multiplication by the different. -/

noncomputable section

namespace GlobalTheory.PD

variable {A B F E : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDedekindDomain B] [Field F] [Field E]
  [Algebra A B] [Algebra A F] [Algebra B E] [Algebra A E] [Algebra F E]
  [IsScalarTower A F E] [IsScalarTower A B E]
  [IsFractionRing A F] [IsFractionRing B E] [IsIntegralClosure B A E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Module.IsTorsionFree A B]

/-- The trace pairing is integral against the normalization exactly when
the product with every element of the different belongs to that normalization. -/
theorem trace_mem_range_iff_mul_different (z : E) :
    (∀ b : B, Algebra.trace F E (z * algebraMap B E b) ∈ (algebraMap A F).range) ↔
      ∀ d ∈ differentIdeal A B, z * algebraMap B E d ∈ (algebraMap B E).range := by
  let I : FractionalIdeal (nonZeroDivisors B) E := 1
  let D : FractionalIdeal (nonZeroDivisors B) E := (differentIdeal A B : Ideal B)
  have hI : I ≠ 0 := one_ne_zero
  have hD : D = (FractionalIdeal.dual A F I)⁻¹ := coeIdeal_differentIdeal A F E B
  have hD0 : D ≠ 0 := by
    rw [hD]
    exact inv_ne_zero (FractionalIdeal.dual_ne_zero A F hI)
  have hOne {u : E} : u ∈ (1 : FractionalIdeal (nonZeroDivisors B) E) ↔
      u ∈ (algebraMap B E).range := FractionalIdeal.mem_one_iff (nonZeroDivisors B)
  have hTrace : (∀ b : B, Algebra.trace F E (z * algebraMap B E b) ∈ (algebraMap A F).range) ↔
        z ∈ FractionalIdeal.dual A F I := by
    rw [FractionalIdeal.mem_dual hI]
    constructor
    · intro h a ha
      obtain ⟨b, rfl⟩ := hOne.mp ha
      exact h b
    · intro h b
      exact h _ (hOne.mpr ⟨b, rfl⟩)
  rw [hTrace, ← inv_inv (FractionalIdeal.dual A F I), ← hD, FractionalIdeal.mem_inv_iff hD0]
  constructor
  · intro h d hd
    exact hOne.mp (h _ (FractionalIdeal.mem_coeIdeal_of_mem _ hd))
  · intro h y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact hOne.mpr (h d hd)

end GlobalTheory.PD
