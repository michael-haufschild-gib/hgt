import GaloisForLFunctions.HTGeometry.PrimitiveFiniteRingCharactersHaveGaussTransforms

/-!
# Gauss sums detect primitive additive characters

For a primitive multiplicative character, an imprimitive additive
character has zero Gauss sum. A nonzero element annihilating its
multiplicative shifts generates a nonzero ideal; a congruence unit
detected by the multiplicative character fixes the additive one and
forces cancellation. Together with the exact primitive Gauss norm,
this classifies every coefficient by additive primitivity.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.FiniteRing

variable {R : Type*} [CommRing R] [Fintype R]

/-- A primitive multiplicative character annihilates every imprimitive additive character. -/
theorem gaussSum_eq_zero_of_not_isPrimitive {χ : MulChar R ℂ} (hχ : IsPrimitive χ)
    {ψ : AddChar R ℂ} (hψ : ¬ψ.IsPrimitive) : gaussSum χ ψ = 0 := by
  obtain ⟨a, ha, hψa⟩ : ∃ a : R, a ≠ 0 ∧ ψ.mulShift a = 1 := by
    simpa only [AddChar.IsPrimitive, not_forall, not_not, exists_prop] using hψ
  have hJ : Ideal.span ({a} : Set R) ≠ ⊥ := by
    intro h
    have haJ := Ideal.subset_span (Set.mem_singleton a)
    rw [h] at haJ
    exact ha (show a = 0 from haJ)
  obtain ⟨u, hu, hχu⟩ := (isPrimitive_iff χ).mp hχ _ hJ
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hu
  have hψu : ψ.mulShift (u : R) = ψ := by
    ext x
    have h := DFunLike.congr_fun hψa (r * x)
    change ψ (a * (r * x)) = 1 at h
    change ψ ((u : R) * x) = ψ x
    have he : (u : R) * x = a * (r * x) + x := by
      rw [← mul_assoc, ← hr]
      ring
    rw [he, ψ.map_add_eq_mul, h, one_mul]
  have h := gaussSum_mulShift χ ψ u
  rw [hψu] at h
  exact eq_zero_of_mul_eq_self_left hχu h

/-- For primitive multiplicative characters, Gauss nonvanishing detects additive primitivity. -/
theorem gaussSum_ne_zero_iff_isPrimitive {χ : MulChar R ℂ} (hχ : IsPrimitive χ)
    (ψ : AddChar R ℂ) : gaussSum χ ψ ≠ 0 ↔ ψ.IsPrimitive := by
  constructor
  · intro h
    by_contra hn
    exact h (gaussSum_eq_zero_of_not_isPrimitive hχ hn)
  · intro hψ hzero
    have h := norm_gaussSum_sq hχ hψ
    rw [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
    exact (Nat.cast_ne_zero.mpr Fintype.card_ne_zero : (Fintype.card R : ℝ) ≠ 0) h.symm

/-- Every Gauss coefficient has either zero squared norm or the full ring cardinality. -/
theorem norm_gaussSum_sq_eq_ite {χ : MulChar R ℂ} (hχ : IsPrimitive χ)
    (ψ : AddChar R ℂ) :
    ‖gaussSum χ ψ‖ ^ 2 = if ψ.IsPrimitive then (Fintype.card R : ℝ) else 0 := by
  by_cases hψ : ψ.IsPrimitive
  · rw [if_pos hψ]
    exact norm_gaussSum_sq hχ hψ
  · rw [if_neg hψ, gaussSum_eq_zero_of_not_isPrimitive hχ hψ, norm_zero]
    exact zero_pow (by decide : (2 : ℕ) ≠ 0)

end GaloisForLFunctions.FiniteRing
