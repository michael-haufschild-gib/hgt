import GaloisForLFunctions.HTGeometry.QuadraticRepresentation

/-!
# Two obstructions to a square root lying in an extension

A square root of a base element that is not itself in the base cannot lie in an extension of odd
degree, since it would generate a quadratic subextension.

Nor can it lie in a square-root extension whose radicand is in a different square class, since
inside such an extension it would have to be a multiple of the root.

Together these are the two cases of the Kummer step: the odd degree case needs no computation, and
the even one is decided by a square class.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- **Odd degree obstruction.**  A square root of a base element not lying in the base cannot lie in
an intermediate field of odd degree. -/
theorem notMem_of_not_two_dvd_finrank {M : IntermediateField F L} [FiniteDimensional F M]
    (hodd : ¬ 2 ∣ Module.finrank F M) {δ : L} {e : F}
    (hδsq : δ * δ = algebraMap F L e) (hδbot : δ ∉ (⊥ : IntermediateField F L)) :
    δ ∉ M := by
  intro hδM
  refine hodd ?_
  have hsq' : (⟨δ, hδM⟩ : M) * ⟨δ, hδM⟩ = algebraMap F M e := by
    refine Subtype.ext ?_
    show δ * δ = ((algebraMap F M e : M) : L)
    rw [hδsq]
    rfl
  have hbot' : (⟨δ, hδM⟩ : M) ∉ (⊥ : IntermediateField F M) := by
    intro hcon
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hcon
    refine hδbot ?_
    refine IntermediateField.mem_bot.2 ⟨c, ?_⟩
    have := congrArg (fun y : M => (y : L)) hc
    simpa using this
  exact two_dvd_finrank_of_sq_mem_bot hsq' hbot'

/-- **Square class obstruction.**  A square root of a base element not lying in the base cannot lie
in a square-root extension unless the two radicands differ by a square. -/
theorem notMem_adjoin_sqrt_of_not_sq [CharZero F] {δ α : L} {c e : F}
    (hsq : α * α = algebraMap F L c) (hα : α ∉ (⊥ : IntermediateField F L))
    (hδsq : δ * δ = algebraMap F L e) (hδbot : δ ∉ (⊥ : IntermediateField F L))
    (hns : ¬ ∃ t : F, e * c = t * t) : δ ∉ F⟮α⟯ := by
  intro hδ
  exact hns (sq_mul_eq_sq_of_mem_adjoin_sqrt hsq hα hδ hδsq hδbot)

end GaloisForLFunctions.HTGeometry
