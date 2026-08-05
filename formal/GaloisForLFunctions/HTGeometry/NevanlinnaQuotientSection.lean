import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierBridge

/-!
# Canonical separated nodes for the Nevanlinna quotient

Every map is injective after restricting its codomain to its image and choosing one representative
from each fibre. Applied to the analytic Nevanlinna quotient, this gives the maximal canonical
family of nodes with pairwise distinct quotient values. Finite packets used by carrier laws are
obtained by composing this section with any injective finite selection from the image.
-/

namespace GaloisForLFunctions.HTGeometry

open Function Set

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- Image of the meromorphic Nevanlinna quotient. -/
def QuotientImage : Type := Set.range F.quotient

/-- One canonical node in every nonempty quotient fibre. -/
noncomputable def quotientSection (q : F.QuotientImage) : ℂ :=
  Classical.choose q.property

/-- Chosen node lies in the fibre it represents. -/
@[simp]
theorem quotient_quotientSection (q : F.QuotientImage) :
    F.quotient (F.quotientSection q) = q.1 :=
  Classical.choose_spec q.property

/-- **Universal quotient-section law.** Quotient is injective on canonical family containing one
representative of every fibre. -/
theorem injective_quotient_quotientSection :
    Function.Injective (fun q : F.QuotientImage => F.quotient (F.quotientSection q)) := by
  intro q r h
  apply Subtype.ext
  simpa only [F.quotient_quotientSection] using h

/-- Every injectively selected subfamily of quotient image gives separated Nevanlinna nodes. -/
theorem injective_quotient_section_comp
    {ι : Type*} (e : ι → F.QuotientImage) (he : Function.Injective e) :
    Function.Injective (fun i => F.quotient (F.quotientSection (e i))) :=
  F.injective_quotient_quotientSection.comp he

/-- Quotient value, regarded as an element of quotient image. -/
def quotientImagePoint (z : ℂ) : F.QuotientImage :=
  ⟨F.quotient z, z, rfl⟩

/-- One-node packet is smallest unconditional separated packet. -/
theorem injective_quotient_singleton (z : ℂ) :
    Function.Injective (fun _ : Unit => F.quotient z) :=
  fun _ _ _ => Subsingleton.elim _ _

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
