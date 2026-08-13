import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierBridge
import GaloisForLFunctions.HTGeometry.ProjectiveLabelNullPreimage

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

/-- **Universal projective-separation anchor law.** Determinant one prevents a common zero of the
analytic denominator pair, while the source-faithful finite and infinite boundary fibres supply,
respectively, nonzero and zero values of `c`. -/
theorem projectiveSeparationAnchors :
    (∀ z, ¬ (F.c z = 0 ∧ F.d z = 0)) ∧
      (∃ p, F.c p = 0) ∧ ∃ c, F.c c ≠ 0 := by
  have hnoCommon : ∀ z, ¬ (F.c z = 0 ∧ F.d z = 0) := by
    intro z
    rintro ⟨hc, hd⟩
    have hdet := F.det_one z
    simp [hc, hd] at hdet
  obtain ⟨p, hp⟩ := F.base.toBoundaryFamily.infinityDenominatorFiber_nonempty
  have hCp : F.c (p : ℂ) = 0 := by
    rw [F.c_real]
    exact_mod_cast hp
  obtain ⟨c, hc⟩ := F.base.toBoundaryFamily.finiteDenominatorFiber_nonempty 0
  have hDc : F.base.toBoundaryFamily.matrix.d c = 0 := by
    change F.base.toBoundaryFamily.matrix.c c * 0 +
      F.base.toBoundaryFamily.matrix.d c = 0 at hc
    simpa using hc
  have hCcReal : F.base.toBoundaryFamily.matrix.c c ≠ 0 := by
    intro hC
    exact F.base.toBoundaryFamily.matrix.C_D_ne_zero c ⟨hC, hDc⟩
  have hCc : F.c (c : ℂ) ≠ 0 := by
    rw [F.c_real]
    exact_mod_cast hCcReal
  exact ⟨hnoCommon, ⟨p, hCp⟩, c, hCc⟩

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
