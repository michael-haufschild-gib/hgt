import GaloisForLFunctions.HTGeometry.QuadraticSubextension

/-!
# A quadratic element generates a square root

In characteristic zero an element of degree two over the base can be shifted by half of its trace
so that its square lands in the base, and the shift does not change the field it generates.

So every quadratic subextension is a square-root extension, which is what lets the square-class
obstruction be applied to it.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **Completing the square.**  An element of degree two generates the same field as a square root
of a base element. -/
theorem exists_sqrt_adjoin_eq [CharZero F] {x : L} (hx : IsIntegral F x)
    (hdeg : (minpoly F x).natDegree = 2) :
    ∃ (δ : L) (c : F), δ * δ = algebraMap F L c ∧ F⟮δ⟯ = F⟮x⟯ ∧
      δ ∉ (⊥ : IntermediateField F L) := by
  set b : F := (minpoly F x).coeff 1 with hb
  set c₀ : F := (minpoly F x).coeff 0 with hc₀
  have hmonic : (minpoly F x).Monic := minpoly.monic hx
  have htop : (minpoly F x).coeff 2 = 1 := by
    have := hmonic.coeff_natDegree
    rwa [hdeg] at this
  have hroot : algebraMap F L c₀ + algebraMap F L b * x + x * x = 0 := by
    have h0 : Polynomial.aeval x (minpoly F x) = 0 := minpoly.aeval F x
    rw [Polynomial.aeval_eq_sum_range, hdeg] at h0
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, htop] at h0
    simp only [pow_zero, pow_one, zero_add, Algebra.smul_def, mul_one, map_one] at h0
    linear_combination h0
  refine ⟨x + algebraMap F L (b / 2), b / 2 * (b / 2) - c₀, ?_, ?_, ?_⟩
  · have h2 : algebraMap F L (b / 2) * 2 = algebraMap F L b := by
      rw [← map_ofNat (algebraMap F L) 2, ← map_mul]
      congr 1
      field_simp
    rw [map_sub, map_mul]
    linear_combination hroot + x * h2
  · refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact add_mem (IntermediateField.mem_adjoin_simple_self F x)
        (IntermediateField.algebraMap_mem _ _)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have hmem : (x + algebraMap F L (b / 2)) - algebraMap F L (b / 2) ∈
          F⟮x + algebraMap F L (b / 2)⟯ :=
        sub_mem (IntermediateField.mem_adjoin_simple_self F _)
          (IntermediateField.algebraMap_mem _ _)
      simpa using hmem
  · intro hcon
    obtain ⟨t, ht⟩ := IntermediateField.mem_bot.1 hcon
    have hxbot : x ∈ (⊥ : IntermediateField F L) := by
      refine IntermediateField.mem_bot.2 ⟨t - b / 2, ?_⟩
      rw [map_sub, ht]
      ring
    have hbot : F⟮x⟯ = ⊥ := by
      refine le_antisymm ?_ bot_le
      rw [IntermediateField.adjoin_simple_le_iff]
      exact hxbot
    have hrank : Module.finrank F F⟮x⟯ = (minpoly F x).natDegree :=
      IntermediateField.adjoin.finrank hx
    rw [hbot, hdeg] at hrank
    simp at hrank

end GaloisForLFunctions.HTGeometry
