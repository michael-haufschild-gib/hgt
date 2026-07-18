import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.Tactic

/-!
# Intersection with a simple transcendental extension

If `K ⊆ L` are intermediate fields and `t` is transcendental over `L`, then adjoining `t` to
`K` creates no new element of `L`.  This ordinary field-theoretic lemma is the no-cancellation
leaf used by scalar differential-order additivity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial
open scoped Polynomial

/-- A simple transcendental extension of a smaller field meets a larger coefficient field only
in the smaller field. -/
theorem adjoin_simple_restrictScalars_inf_eq_left_of_transcendental
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (K L : IntermediateField C E) (hKL : K ≤ L) (t : E)
    (ht : Transcendental L t) :
    (IntermediateField.adjoin K {t}).restrictScalars C ⊓ L = K := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨hxKt, hxL⟩
    change x ∈ IntermediateField.adjoin K {t} at hxKt
    rw [IntermediateField.mem_adjoin_simple_iff] at hxKt
    rcases hxKt with ⟨p, q, hpq⟩
    by_cases hq : aeval t q = 0
    · rw [hq, div_zero] at hpq
      rw [hpq]
      exact K.zero_mem
    · let i : K →+* L := (IntermediateField.inclusion hKL).toRingHom
      let xL : L := ⟨x, hxL⟩
      let P : L[X] := p.map i - Polynomial.C xL * q.map i
      have hP_eval : aeval t P = 0 := by
        dsimp [P]
        rw [map_sub, map_mul, aeval_C]
        rw [Polynomial.aeval_def, Polynomial.eval₂_map,
          Polynomial.aeval_def, Polynomial.eval₂_map]
        change aeval t p - x * aeval t q = 0
        exact sub_eq_zero.mpr ((eq_div_iff hq).mp hpq).symm
      have hP : P = 0 := (transcendental_iff.mp ht) P hP_eval
      have hq0 : q ≠ 0 := by
        intro h
        apply hq
        simp [h]
      have hqc : q.coeff q.natDegree ≠ 0 := by
        simpa only [coeff_natDegree] using q.leadingCoeff_ne_zero.mpr hq0
      have hic : i (q.coeff q.natDegree) ≠ 0 := by
        intro hi
        apply hqc
        apply IntermediateField.inclusion_injective hKL
        simpa using hi
      have hcoeff := congrArg (fun r : L[X] ↦ r.coeff q.natDegree) hP
      have hxL_eq : xL = i (p.coeff q.natDegree / q.coeff q.natDegree) := by
        rw [map_div₀ i]
        apply (eq_div_iff hic).mpr
        symm
        simpa [P, coeff_sub, coeff_map, coeff_C_mul, sub_eq_zero] using hcoeff
      have hx_eq : x = (p.coeff q.natDegree / q.coeff q.natDegree : K) := by
        exact congrArg Subtype.val hxL_eq
      rw [hx_eq]
      exact (p.coeff q.natDegree / q.coeff q.natDegree : K).property
  · refine le_inf ?_ hKL
    intro x hx
    change x ∈ IntermediateField.adjoin K {t}
    exact (IntermediateField.adjoin K {t}).algebraMap_mem ⟨x, hx⟩

/-- Membership form of
`adjoin_simple_restrictScalars_inf_eq_left_of_transcendental`. -/
theorem mem_left_of_mem_adjoin_simple_of_mem_of_transcendental
    {C E : Type*} [Field C] [Field E] [Algebra C E]
    (K L : IntermediateField C E) (hKL : K ≤ L) {t z : E}
    (ht : Transcendental L t)
    (hzKt : z ∈ IntermediateField.adjoin K {t}) (hzL : z ∈ L) :
    z ∈ K := by
  rw [← adjoin_simple_restrictScalars_inf_eq_left_of_transcendental K L hKL t ht]
  exact ⟨hzKt, hzL⟩

end

end GaloisForLFunctions.HTGeometry
