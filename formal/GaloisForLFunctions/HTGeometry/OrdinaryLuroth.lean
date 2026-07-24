import Mathlib.FieldTheory.RatFunc.Luroth
import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Degree-one Lüroth: a generating rational function is Möbius

A rational function `f` that generates the whole rational function field `K⟮X⟯` over `K` has
`[K⟮X⟯ : K⟮f⟯] = 1`, so by the degree formula `[K⟮X⟯ : K⟮f⟯] = max (deg num) (deg denom)` its
numerator and denominator are linear.  Hence `f` is a fractional-linear (Möbius) transform of `X`,

`f · (c X + d) = a X + b`,  `a d - b c ≠ 0`.

This is the ordinary Lüroth input to the differential clock-character classification: it upgrades a
generator of the ordinary rational subfield to an explicit `PGL₂` element.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open RatFunc Polynomial

variable {K : Type*} [Field K]

/-- A generator of `K⟮X⟯` has numerator/denominator degree bounded by the extension degree, which
is one: `max (deg num) (deg denom) = 1`. -/
theorem ratFunc_generator_max_natDegree_eq_one {f : RatFunc K}
    (hgen : IntermediateField.adjoin K {f} = ⊤) :
    max f.num.natDegree f.denom.natDegree = 1 := by
  have h1 := RatFunc.finrank_eq_max_natDegree f
  rw [hgen, IntermediateField.finrank_top] at h1
  exact h1.symm

/-- **Degree-one Lüroth.**  A rational function generating `K⟮X⟯` over `K` is a Möbius transform of
`X`: there are `a, b, c, d ∈ K` with `a d - b c ≠ 0` and `f · (c X + d) = a X + b`. -/
theorem ratFunc_generator_mobius {f : RatFunc K}
    (hgen : IntermediateField.adjoin K {f} = ⊤) :
    ∃ a b c d : K, a * d - b * c ≠ 0 ∧
      f * (RatFunc.C c * RatFunc.X + RatFunc.C d)
        = RatFunc.C a * RatFunc.X + RatFunc.C b := by
  have hmax := ratFunc_generator_max_natDegree_eq_one hgen
  have hnum1 : f.num.natDegree ≤ 1 := le_of_max_le_left hmax.le
  have hden1 : f.denom.natDegree ≤ 1 := le_of_max_le_right hmax.le
  have hnumeq : f.num
      = Polynomial.C (f.num.coeff 1) * Polynomial.X + Polynomial.C (f.num.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hnum1
  have hdeneq : f.denom
      = Polynomial.C (f.denom.coeff 1) * Polynomial.X + Polynomial.C (f.denom.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one hden1
  set a := f.num.coeff 1 with ha
  set b := f.num.coeff 0 with hb
  set c := f.denom.coeff 1 with hc
  set d := f.denom.coeff 0 with hd
  have hD0 : (algebraMap (Polynomial K) (RatFunc K)) f.denom ≠ 0 := fun h =>
    RatFunc.denom_ne_zero f
      (IsFractionRing.injective (Polynomial K) (RatFunc K) (by rw [map_zero]; exact h))
  have hrel0 : f * (algebraMap (Polynomial K) (RatFunc K)) f.denom
      = (algebraMap (Polynomial K) (RatFunc K)) f.num := by
    nth_rewrite 1 [← RatFunc.num_div_denom f]
    exact div_mul_cancel₀ _ hD0
  rw [hnumeq, hdeneq] at hrel0
  simp only [map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X] at hrel0
  set N : RatFunc K := RatFunc.C a * RatFunc.X + RatFunc.C b with hNdef
  set D : RatFunc K := RatFunc.C c * RatFunc.X + RatFunc.C d with hDdef
  -- `f` generates, so it is not a base-field constant
  have hfnb : f ∉ (⊥ : IntermediateField K (RatFunc K)) := by
    intro hmem
    have htb : (⊤ : IntermediateField K (RatFunc K)) = ⊥ := by
      rw [← hgen]; exact IntermediateField.adjoin_simple_eq_bot_iff.mpr hmem
    have hX : (RatFunc.X : RatFunc K) ∈ (⊥ : IntermediateField K (RatFunc K)) := by
      rw [← htb]; exact IntermediateField.mem_top
    rw [IntermediateField.mem_bot] at hX
    obtain ⟨e, he⟩ := hX
    have hcontra : (1 : ℤ) = 0 := by
      rw [← RatFunc.intDegree_X (K := K), ← he]
      exact RatFunc.intDegree_C e
    exact one_ne_zero hcontra
  refine ⟨a, b, c, d, ?_, hrel0⟩
  intro h0
  have hDeq : D = (algebraMap (Polynomial K) (RatFunc K)) f.denom := by
    rw [hDdef, hdeneq]
    simp only [map_add, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  have hDne : D ≠ 0 := by rw [hDeq]; exact hD0
  have key1 : RatFunc.C d * N = RatFunc.C b * D := by
    have hda : RatFunc.C d * RatFunc.C a = RatFunc.C b * RatFunc.C c := by
      rw [← map_mul, ← map_mul]; congr 1; linear_combination h0
    rw [hNdef, hDdef]; linear_combination RatFunc.X * hda
  have key2 : RatFunc.C c * N = RatFunc.C a * D := by
    have hca : RatFunc.C c * RatFunc.C b = RatFunc.C a * RatFunc.C d := by
      rw [← map_mul, ← map_mul]; congr 1; linear_combination -h0
    rw [hNdef, hDdef]; linear_combination hca
  have e1 : RatFunc.C d * f = RatFunc.C b :=
    mul_right_cancel₀ hDne (by rw [mul_assoc, hrel0]; exact key1)
  have e2 : RatFunc.C c * f = RatFunc.C a :=
    mul_right_cancel₀ hDne (by rw [mul_assoc, hrel0]; exact key2)
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨ha0, hc0⟩ := h
    have hmax0 : max f.num.natDegree f.denom.natDegree = 0 := by
      rw [hnumeq, hdeneq, ha0, hc0]
      simp
    rw [hmax] at hmax0
    exact one_ne_zero hmax0
  have hcne : c ≠ 0 := by
    rcases hac with hane | hcne
    · intro hc0
      rw [hc0, map_zero, zero_mul] at e2
      exact hane ((map_eq_zero RatFunc.C).mp e2.symm)
    · exact hcne
  have hcC : RatFunc.C c ≠ 0 := by rw [Ne, map_eq_zero]; exact hcne
  have hfC : f = RatFunc.C (a / c) := by
    rw [map_div₀, eq_div_iff hcC, mul_comm]
    exact e2
  exact hfnb (hfC ▸ IntermediateField.mem_bot.mpr ⟨a / c, rfl⟩)

end GaloisForLFunctions.HTGeometry
