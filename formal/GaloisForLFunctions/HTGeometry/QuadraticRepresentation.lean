import GaloisForLFunctions.HTGeometry.QuadraticSubextension

/-!
# Elements of a square-root extension

Adjoining a square root gives an extension in which every element is a scalar plus a scalar multiple
of the root, because a polynomial in the root reduces modulo its quadratic relation.

If such an element has its square back in the base, the scalar part must vanish, so its square
differs from the radicand by a square.  That is the computation which turns membership of the
discriminant square root in a Kummer extension into a square-class identity.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **Every element of a square-root extension is linear in the root.** -/
theorem exists_repr_of_mem_adjoin_sqrt {δ α : L} {c : F} (hsq : α * α = algebraMap F L c)
    (hδ : δ ∈ F⟮α⟯) :
    ∃ a b : F, δ = algebraMap F L a + algebraMap F L b * α := by
  have hint : IsIntegral F α := isIntegral_of_sq_mem_bot hsq
  have hadj : (F⟮α⟯ : IntermediateField F L).toSubalgebra = Algebra.adjoin F {α} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic
  have hmem : δ ∈ Algebra.adjoin F ({α} : Set L) := by
    rw [← hadj]
    exact hδ
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  have hpa : Polynomial.aeval α p = δ := hp
  have hmonic : (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F).Monic := by
    refine (Polynomial.monic_X_pow 2).sub_of_left ?_
    refine lt_of_le_of_lt Polynomial.degree_C_le ?_
    rw [Polynomial.degree_X_pow]
    exact WithBot.coe_lt_coe.2 (by norm_num)
  have hgα : Polynomial.aeval α (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, pow_two, hsq, sub_self]
  have hred : Polynomial.aeval α (p %ₘ (Polynomial.X ^ 2 - Polynomial.C c)) =
      Polynomial.aeval α p :=
    Polynomial.aeval_modByMonic_eq_self_of_root hgα
  have hdegg : (Polynomial.X ^ 2 - Polynomial.C c : Polynomial F).natDegree = 2 := by
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_X_pow]
  have hdeg : (p %ₘ (Polynomial.X ^ 2 - Polynomial.C c)).natDegree ≤ 1 := by
    have h := Polynomial.natDegree_modByMonic_lt p hmonic (by
      intro hcon
      rw [hcon, Polynomial.natDegree_one] at hdegg
      exact absurd hdegg (by norm_num))
    rw [hdegg] at h
    omega
  refine ⟨(p %ₘ (Polynomial.X ^ 2 - Polynomial.C c)).coeff 0,
    (p %ₘ (Polynomial.X ^ 2 - Polynomial.C c)).coeff 1, ?_⟩
  rw [← hpa, ← hred]
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg]
  rw [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_X]
  ring

/-- **A square root of a base element inside a square-root extension is a multiple of the root.**
Hence its square times the radicand is a square in the base. -/
theorem sq_mul_eq_sq_of_mem_adjoin_sqrt [CharZero F] {δ α : L} {c e : F}
    (hsq : α * α = algebraMap F L c) (hα : α ∉ (⊥ : IntermediateField F L))
    (hδ : δ ∈ F⟮α⟯) (hδsq : δ * δ = algebraMap F L e)
    (hδbot : δ ∉ (⊥ : IntermediateField F L)) :
    ∃ t : F, e * c = t * t := by
  obtain ⟨a, b, hab⟩ := exists_repr_of_mem_adjoin_sqrt hsq hδ
  have hinj : Function.Injective (algebraMap F L) := (algebraMap F L).injective
  have hexp : algebraMap F L e =
      algebraMap F L (a * a + b * b * c) + algebraMap F L ((2 : F) * a * b) * α := by
    rw [← hδsq, hab]
    simp only [map_add, map_mul, map_ofNat]
    rw [show (algebraMap F L a + algebraMap F L b * α) *
        (algebraMap F L a + algebraMap F L b * α) =
      algebraMap F L a * algebraMap F L a +
        algebraMap F L b * algebraMap F L b * (α * α) +
        2 * algebraMap F L a * algebraMap F L b * α from by ring, hsq]
  have hab0 : (2 : F) * a * b = 0 := by
    by_contra hcon
    refine hα ?_
    have hne : algebraMap F L ((2 : F) * a * b) ≠ 0 :=
      fun h => hcon (hinj (by rw [h, map_zero]))
    have hmul : algebraMap F L ((2 : F) * a * b) * α =
        algebraMap F L (e - (a * a + b * b * c)) := by
      rw [map_sub]
      linear_combination -hexp
    have hαeq : α = algebraMap F L (e - (a * a + b * b * c)) /
        algebraMap F L ((2 : F) * a * b) := by
      rw [eq_div_iff hne, mul_comm]
      exact hmul
    rw [hαeq]
    exact div_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.algebraMap_mem _ _)
  have hb0 : b ≠ 0 := by
    intro h
    refine hδbot ?_
    rw [hab, h, map_zero, zero_mul, add_zero]
    exact IntermediateField.algebraMap_mem _ _
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 hab0 with h | h
    · rcases mul_eq_zero.1 h with h2 | h2
      · exact absurd h2 two_ne_zero
      · exact h2
    · exact absurd h hb0
  refine ⟨b * c, ?_⟩
  refine hinj ?_
  have he : algebraMap F L e = algebraMap F L (b * b * c) := by
    rw [hexp, ha0]
    simp
  rw [map_mul, he, map_mul, map_mul, map_mul, map_mul]
  ring

end GaloisForLFunctions.HTGeometry
