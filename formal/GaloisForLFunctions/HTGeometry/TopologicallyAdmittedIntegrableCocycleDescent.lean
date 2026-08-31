import GaloisForLFunctions.HTGeometry.CompactAbelianHaar
import GaloisForLFunctions.HTGeometry.ConstitutiveCompactRecurrenceCharacterDescent
import GaloisForLFunctions.HTGeometry.TopologicallyAdmittedMeasurableHahnLabel

open MeasureTheory
open GaloisForLFunctions

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {L : Type u} [AddCommGroup L]

variable {Ω : Type v} [MeasurableSpace Ω]

/-- An integrable constant-increment cocycle over any finite nonzero measure-preserving action has
zero increment. -/
theorem character_eq_zero_of_integrable_measurePreserving_increment
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hmass : μ.real Set.univ ≠ 0)
    (act : L → Ω → Ω) (hpres : ∀ l : L, MeasurePreserving (act l) μ μ)
    (chi : L →+ ℝ) (u : Ω → ℝ) (hu : Integrable u μ)
    (hcocycle : ∀ l : L, (fun x => u (act l x)) =ᵐ[μ] fun x => u x + chi l) :
    chi = 0 := by
  ext l
  change chi l = 0
  have hmap : Measure.map (act l) μ = μ := (hpres l).map_eq
  have hmeasmap : AEStronglyMeasurable u (Measure.map (act l) μ) := by
    rw [hmap]
    exact hu.aestronglyMeasurable
  have hshift : ∫ x, u (act l x) ∂μ = ∫ x, u x ∂μ := by
    calc
      ∫ x, u (act l x) ∂μ = ∫ x, u x ∂Measure.map (act l) μ := by
        simpa only [Function.comp_apply] using
          (integral_map (hpres l).measurable.aemeasurable hmeasmap).symm
      _ = ∫ x, u x ∂μ := by rw [hmap]
  have hbalance :
      ∫ x, u x ∂μ = (∫ x, u x ∂μ) + μ.real Set.univ * chi l := by
    calc
      ∫ x, u x ∂μ = ∫ x, u (act l x) ∂μ := hshift.symm
      _ = ∫ x, (u x + chi l) ∂μ := integral_congr_ae (hcocycle l)
      _ = (∫ x, u x ∂μ) + ∫ _ : Ω, chi l ∂μ :=
        integral_add hu (integrable_const (chi l))
      _ = (∫ x, u x ∂μ) + μ.real Set.univ * chi l := by
        rw [integral_const]
        simp
  have hmul : μ.real Set.univ * chi l = 0 := by linarith
  exact (mul_eq_zero.mp hmul).resolve_left hmass

variable {G : Type v} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/-- An integrable gauge potential on a compact phase quotient whose translation increment recovers
an open real formation character. -/
def IntegrableTranslationPotential (i : L →+ G) (chi : L →+ ℝ) : Prop :=
  ∃ u : G → ℝ,
    Integrable u (CompactAbelian.haarProb G) ∧
      ∀ l : L, (fun x => u (x + i l)) =ᵐ[CompactAbelian.haarProb G]
        fun x => u x + chi l

omit [T2Space G] in
/-- Haar-integrable coboundary descent selects exactly the neutral real character. -/
theorem integrableTranslationPotential_iff (i : L →+ G) (chi : L →+ ℝ) :
    IntegrableTranslationPotential i chi ↔ chi = 0 := by
  constructor
  · rintro ⟨u, hu, hcocycle⟩
    ext l
    change chi l = 0
    have hshift :
        ∫ x, u x ∂(CompactAbelian.haarProb G) =
          ∫ x, u x ∂(CompactAbelian.haarProb G) + chi l := by
      calc
        ∫ x, u x ∂(CompactAbelian.haarProb G) =
            ∫ x, u (x + i l) ∂(CompactAbelian.haarProb G) :=
          (integral_add_right_eq_self u (i l)).symm
        _ = ∫ x, (u x + chi l) ∂(CompactAbelian.haarProb G) :=
          integral_congr_ae (hcocycle l)
        _ = (∫ x, u x ∂(CompactAbelian.haarProb G)) +
            ∫ _ : G, chi l ∂(CompactAbelian.haarProb G) :=
          integral_add hu (integrable_const (chi l))
        _ = (∫ x, u x ∂(CompactAbelian.haarProb G)) + chi l := by simp
    linarith [hshift]
  · rintro rfl
    refine ⟨0, ?_, ?_⟩
    · exact integrable_const (μ := CompactAbelian.haarProb G) (0 : ℝ)
    intro l
    simp

omit [T2Space G] in
/-- A nonzero open character cannot be represented by an `L¹` gauge potential on a compact phase
quotient, even without continuity of the potential. -/
theorem not_integrableTranslationPotential_of_ne_zero
    (i : L →+ G) (chi : L →+ ℝ) (hchi : chi ≠ 0) :
    ¬ IntegrableTranslationPotential i chi := by
  rw [integrableTranslationPotential_iff]
  exact hchi

omit [T2Space G] in
/-- Hahn/Radon--Nikodym specialization: if the canonical measurable source density is an integrable
translation potential for a formation character, then that character is information-neutral. -/
theorem character_eq_zero_of_measurableHahnDensity_translationPotential
    (i : L →+ G) (chi : L →+ ℝ) (P Q : Measure G)
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hcocycle : ∀ l : L,
      (fun x => measurableHahnDensity P Q (x + i l)) =ᵐ[CompactAbelian.haarProb G]
        fun x => measurableHahnDensity P Q x + chi l)
    (hcontrol : currentControl P Q = CompactAbelian.haarProb G) :
    chi = 0 := by
  rw [← integrableTranslationPotential_iff i chi]
  refine ⟨measurableHahnDensity P Q, ?_, hcocycle⟩
  rw [← hcontrol]
  exact integrable_measurableHahnDensity P Q

end

end GaloisForLFunctions.HTGeometry
