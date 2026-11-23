import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! In the fraction field of a finite normal algebra, integrality over
the image of the coefficient ring cuts out exactly the original algebra. -/

namespace GlobalTheory.SchemeCohomology

/-- A finite integrally closed domain realizes the integral closure of the
coefficient image in its function field. -/
theorem isIntegral_range_iff_of_finite {A B E : Type*} [CommRing A] [CommRing B] [Field E]
    [Algebra B E] [IsFractionRing B E] [IsIntegrallyClosed B]
    (f : A →+* B) (hf : f.Finite) (x : E) :
    IsIntegral ((algebraMap B E).comp f).range x ↔ ∃ b : B, algebraMap B E b = x := by
  let g := algebraMap B E
  let D := (g.comp f).range
  let i : D →+* g.range := D.subtype.codRestrict g.range (by
    rintro ⟨_, a, rfl⟩
    exact ⟨f a, rfl⟩)
  let e := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b h => IsFractionRing.injective B E (congrArg Subtype.val h),
      g.rangeRestrict_surjective⟩
  have he : g.comp (e.symm.toRingHom.comp i) = D.subtype := by
    apply RingHom.ext
    intro a
    exact congrArg Subtype.val (e.apply_symm_apply (i a))
  constructor
  · intro h
    change D.subtype.IsIntegralElem x at h
    rw [← he] at h
    exact IsIntegrallyClosed.isIntegral_iff.mp h.of_comp
  · rintro ⟨b, rfl⟩
    letI := f.toAlgebra
    letI : Module.Finite A B := hf
    have h : f.IsIntegralElem b := Algebra.IsIntegral.isIntegral b
    have hm := h.map g
    change D.subtype.IsIntegralElem (g b)
    have hc : D.subtype.comp (g.comp f).rangeRestrict = g.comp f := rfl
    rw [← hc] at hm
    exact hm.of_comp

end GlobalTheory.SchemeCohomology
