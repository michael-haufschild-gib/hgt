import GaloisForLFunctions.HTGeometry.CuspedHorizonPoset

/-!
# Cusped vertices of positive depth exist

The depth-slice laws are stated for a vertex whose depth is nonzero, and only the depth-zero
retraction was ever constructed.  A positive-depth vertex is a proper line: in any space of
dimension at least two a nonzero vector spans one, which is neither zero nor everything, and whose
rank is one — exactly the condition a positive depth imposes.
-/

namespace GaloisForLFunctions.HTGeometry

namespace CuspedVertex

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The line spanned by a nonzero vector, as a cusped vertex of depth one. -/
noncomputable def line [FiniteDimensional K V] {x : V} (hx : x ≠ 0)
    (hdim : 1 < Module.finrank K V) : CuspedVertex K V where
  space := Submodule.span K {x}
  depth := 1
  ne_bot := by
    intro h
    exact hx (by simpa using (Submodule.span_eq_bot.mp h) x rfl)
  ne_top := by
    intro h
    have hrank : Module.finrank K (Submodule.span K ({x} : Set V)) = 1 :=
      finrank_span_singleton hx
    rw [h] at hrank
    simp only [finrank_top] at hrank
    omega
  finrank_of_depth _ := finrank_span_singleton hx

@[simp] theorem line_depth [FiniteDimensional K V] {x : V} (hx : x ≠ 0)
    (hdim : 1 < Module.finrank K V) : (line hx hdim).depth = 1 := rfl

/-- **A space of dimension at least two carries a cusped vertex of positive depth.** -/
theorem exists_depth_ne_zero [FiniteDimensional K V] (hdim : 1 < Module.finrank K V) :
    ∃ v : CuspedVertex K V, v.depth ≠ 0 := by
  have hnontriv : Nontrivial V := by
    refine Module.nontrivial_of_finrank_pos (R := K) ?_
    omega
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  exact ⟨line hx hdim, by simp⟩

end CuspedVertex

end GaloisForLFunctions.HTGeometry
