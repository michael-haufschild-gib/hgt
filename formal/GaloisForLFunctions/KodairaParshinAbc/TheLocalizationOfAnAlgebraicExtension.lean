import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The localization of an algebraic extension of domains

Let `A ⊆ B` be domains with `B` algebraic over `A`, and let `F` be the fraction field of `B`.
Inverting the nonzero elements of `A` already produces `F`:

  `B ⊗_A Frac(A) = F`,  i.e.  `F` is the localization of `B` at the image of `A ∖ {0}`.

The point is that every nonzero `b ∈ B` divides a nonzero element of `A`
(`IsAlgebraic.exists_nonzero_dvd`): from a minimal relation `a₀ bⁿ + ⋯ + aₙ = 0` with `aₙ ≠ 0`,
`b · c = aₙ` for some `c ∈ B`.  So `b₁/b₂ = b₁ c / (b₂ c)` has denominator in `A`.  No integrality or
normality of `B` is needed, so this applies to arbitrary orders in number fields, not only to
rings of integers.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc

variable {A B F : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
  [FaithfulSMul A B] [Field F] [Algebra B F] [IsFractionRing B F]

/-- **`F` is the localization of `B` at `A ∖ {0}`** for `B` algebraic over `A`. -/
theorem isLocalization_algebraMapSubmonoid_of_isAlgebraic [Algebra.IsAlgebraic A B] :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) F where
  map_units := by
    rintro ⟨_, a, ha, rfl⟩
    refine IsUnit.mk0 _ ?_
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff]
    exact nonZeroDivisors.ne_zero ha
  surj := by
    intro z
    obtain ⟨⟨b₁, b₂⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors B) z
    obtain ⟨a, ha0, c, hc⟩ :=
      (Algebra.IsAlgebraic.isAlgebraic (R := A) (b₂ : B)).exists_nonzero_dvd b₂.2
    refine ⟨⟨b₁ * c, ⟨algebraMap A B a, a, mem_nonZeroDivisors_of_ne_zero ha0, rfl⟩⟩, ?_⟩
    simp only at hz ⊢
    rw [hc, map_mul, map_mul, ← mul_assoc, hz]
  exists_of_eq := by
    intro x y h
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    exact IsFractionRing.injective B F h

end GaloisForLFunctions.KodairaParshinAbc
