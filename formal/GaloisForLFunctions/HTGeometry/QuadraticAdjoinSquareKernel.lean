import GaloisForLFunctions.HTGeometry.QuadraticTowerSquareClasses
import GaloisForLFunctions.HTGeometry.QuadraticSubextension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-!
# Exact square classes and degrees in a quadratic adjunction

A chosen square root belongs to an intermediate field exactly when its scalar
is square there. Adjoining one nonsquare radical kills only its defining square
class. Two independent radicals consequently generate a field of degree four.
The square-class step uses the existing explicit quadratic span construction.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped IntermediateField
variable {F L : Type*} [Field F] [Field L] [Algebra F L]

theorem isSqIn_fieldRange_iff_isSquare (a : F) :
    IsSqIn (algebraMap F L).fieldRange (algebraMap F L a) ↔ IsSquare a := by
  constructor
  · rintro ⟨r, hr, h⟩
    change ∃ b, algebraMap F L b = r at hr
    obtain ⟨b, rfl⟩ := hr
    refine ⟨b, (algebraMap F L).injective ?_⟩
    simpa only [map_mul] using h
  · rintro ⟨r, hr⟩
    refine ⟨algebraMap F L r, RingHom.mem_fieldRange_self _ r, ?_⟩
    rw [hr, map_mul]

/-- A chosen root belongs to an intermediate field exactly when its scalar is square there. -/
theorem root_mem_iff_isSquare {a : F} {r : L} (hr : r * r = algebraMap F L a)
    (E : IntermediateField F L) : r ∈ E ↔ IsSquare (algebraMap F E a) := by
  constructor
  · intro hmem
    refine ⟨⟨r, hmem⟩, ?_⟩
    apply Subtype.ext
    exact hr.symm
  · rintro ⟨u, hu⟩
    have he : algebraMap F L a = (u : L) * u := congrArg (fun w : E => (w : L)) hu
    have hprod : (r - u) * (r + u) = 0 := by linear_combination hr + he
    rcases mul_eq_zero.mp hprod with h | h
    · rw [sub_eq_zero.mp h]
      exact u.property
    · rw [eq_neg_of_add_eq_zero_left h]
      exact E.neg_mem u.property

theorem adjoin_root_le_iff_isSquare {a : F} {r : L} (hr : r * r = algebraMap F L a)
    (E : IntermediateField F L) : F⟮r⟯ ≤ E ↔ IsSquare (algebraMap F E a) := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  exact root_mem_iff_isSquare hr E

theorem root_not_mem_bot_of_not_isSquare {a : F} {r : L}
    (hr : r * r = algebraMap F L a) (ha : ¬ IsSquare a) :
    r ∉ (⊥ : IntermediateField F L) := by
  intro hmem
  obtain ⟨b, hb⟩ := IntermediateField.mem_bot.mp hmem
  apply ha
  refine ⟨b, (algebraMap F L).injective ?_⟩
  rw [map_mul, hb, hr]

/-- One quadratic adjunction kills exactly its defining square class. -/
theorem isSquare_adjoin_root_iff {d a : F} {r : L}
    (h2 : (2 : L) ≠ 0) (hr : r * r = algebraMap F L d) (hd : ¬ IsSquare d) :
    IsSquare (algebraMap F F⟮r⟯ a) ↔ IsSquare a ∨ IsSquare (d * a) := by
  let B := (algebraMap F L).fieldRange
  have hrr : r * r ∈ B := by rw [hr]; exact RingHom.mem_fieldRange_self _ _
  have hrB : r ∉ B := root_not_mem_bot_of_not_isSquare hr hd
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := mem_closure_insert_iff hrr hrB (u : L) u.property
    have he : algebraMap F L a = (u : L) * u := congrArg (fun w : F⟮r⟯ => (w : L)) hu
    rw [hxy] at he
    rcases isSq_or_isSq_mul_of_span h2 hrr hrB (RingHom.mem_fieldRange_self _ a) hx hy he with h | h
    · exact Or.inl ((isSqIn_fieldRange_iff_isSquare a).mp h)
    · rw [hr, ← map_mul] at h
      exact Or.inr ((isSqIn_fieldRange_iff_isSquare (d * a)).mp h)
  · rintro (h | h)
    · exact h.map (algebraMap F F⟮r⟯)
    · let rE : F⟮r⟯ := ⟨r, IntermediateField.mem_adjoin_simple_self F r⟩
      have hrE : rE ^ 2 = algebraMap F F⟮r⟯ d := by
        apply Subtype.ext
        exact (pow_two r).trans hr
      have hd0 : algebraMap F F⟮r⟯ d ≠ 0 := (map_ne_zero _).mpr
        (fun hz => hd (hz ▸ IsSquare.zero))
      have hs := (h.map (algebraMap F F⟮r⟯)).div (IsSquare.sq rE)
      rw [hrE, map_mul, mul_div_cancel_left₀ _ hd0] at hs
      exact hs

/-- Two independent square classes generate an extension of degree four. -/
theorem finrank_adjoin_two_roots_eq_four {a b : F} {r s : L}
    (h2 : (2 : L) ≠ 0)
    (hr : r * r = algebraMap F L a) (hs : s * s = algebraMap F L b)
    (ha : ¬ IsSquare a) (hb : ¬ IsSquare b) (hab : ¬ IsSquare (a * b)) :
    Module.finrank F ↥(IntermediateField.adjoin F ({r, s} : Set L)) = 4 := by
  let E := F⟮r⟯
  have hE : Module.finrank F E = 2 :=
    finrank_adjoin_eq_two hr (root_not_mem_bot_of_not_isSquare hr ha)
  have hbn : ¬ IsSquare (algebraMap F E b) := by
    intro h
    rcases (isSquare_adjoin_root_iff h2 hr ha).mp h with h | h
    · exact hb h
    · exact hab h
  have hsE : s * s = algebraMap E L (algebraMap F E b) := by
    change s * s = algebraMap F L b
    exact hs
  have hlast : Module.finrank E E⟮s⟯ = 2 :=
    finrank_adjoin_eq_two hsE (root_not_mem_bot_of_not_isSquare hsE hbn)
  have heq : (E⟮s⟯).restrictScalars F = IntermediateField.adjoin F ({r, s} : Set L) := by
    dsimp [E]
    rw [IntermediateField.adjoin_adjoin_left]
    congr 1
  rw [← heq]
  change Module.finrank F E⟮s⟯ = 4
  rw [← Module.finrank_mul_finrank F E E⟮s⟯, hE, hlast]

end GaloisForLFunctions.HTGeometry
