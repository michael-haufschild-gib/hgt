import GaloisForLFunctions.HTGeometry.GomesTruncatedJetUnipotentHorizonSection
import Mathlib.Algebra.Group.Prod

/-!
# A group section for every actual gauge horizon restriction

The scalar coordinate is retained, while the full unipotent factor is lifted
by logarithm, zero extension and exponential. This splits the actual gauge
restriction at every phase and every finite horizon.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Actual horizon restriction retains every scalar gauge transformation. -/
theorem gomesTruncatedJetGaugeHorizon_scalarSection (n r : ℕ) (z : ℂ) (c : ℂˣ) :
    gomesTruncatedJetGaugeHorizon n r z (gomesTruncatedJetScalarSection (n + r) z c) =
      gomesTruncatedJetScalarSection n z c := by
  apply Subtype.ext
  apply Units.ext
  change (gomesTruncatedJetHorizonRestriction n r z
    (algebraMap ℂ (gomesTruncatedJetJointAlgebra (n + r) z) c.val)).val =
      (algebraMap ℂ (gomesTruncatedJetJointAlgebra n z) c.val).val
  rw [AlgHom.commutes]

/-- Extend every actual gauge transformation by retaining its scalar and lifting its logarithmic unipotent part. -/
def gomesTruncatedJetGaugeHorizonSection (n r : ℕ) (z : ℂ) :
    gomesTruncatedJetGaugeGroup n z →* gomesTruncatedJetGaugeGroup (n + r) z :=
  (gomesTruncatedJetGaugeSplitting (n + r) z).symm.toMonoidHom.comp
    ((MonoidHom.prodMap (MonoidHom.id ℂˣ) (gomesTruncatedJetUnipotentHorizonSection n r z)).comp
      (gomesTruncatedJetGaugeSplitting n z).toMonoidHom)

/-- The complete actual gauge section is scalar transport times the extended unipotent transformation. -/
theorem gomesTruncatedJetGaugeHorizonSection_apply (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    gomesTruncatedJetGaugeHorizonSection n r z u =
      gomesTruncatedJetScalarSection (n + r) z (gomesTruncatedJetGaugeCharacter n z u) *
        (gomesTruncatedJetUnipotentHorizonSection n r z (gomesTruncatedJetUnipotentPart n z u)).val := by
  change (gomesTruncatedJetGaugeSplitting (n + r) z).symm
    (gomesTruncatedJetGaugeCharacter n z u,
      gomesTruncatedJetUnipotentHorizonSection n r z (gomesTruncatedJetUnipotentPart n z u)) = _
  exact gomesTruncatedJetGaugeSplitting_symm (n + r) z _ _

/-- Restriction recovers every actual gauge transformation extended by the canonical group section. -/
theorem gomesTruncatedJetGaugeHorizon_section (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    gomesTruncatedJetGaugeHorizon n r z (gomesTruncatedJetGaugeHorizonSection n r z u) = u := by
  rw [gomesTruncatedJetGaugeHorizonSection_apply, map_mul, gomesTruncatedJetGaugeHorizon_scalarSection]
  have hu : gomesTruncatedJetGaugeHorizon n r z
      (gomesTruncatedJetUnipotentHorizonSection n r z (gomesTruncatedJetUnipotentPart n z u)).val =
      (gomesTruncatedJetUnipotentPart n z u).val :=
    congrArg Subtype.val (gomesTruncatedJetUnipotentHorizon_section n r z (gomesTruncatedJetUnipotentPart n z u))
  rw [hu]
  have h := (gomesTruncatedJetGaugeSplitting n z).symm_apply_apply u
  change (gomesTruncatedJetGaugeSplitting n z).symm
    (gomesTruncatedJetGaugeCharacter n z u, gomesTruncatedJetUnipotentPart n z u) = u at h
  rw [gomesTruncatedJetGaugeSplitting_symm] at h
  exact h

/-- Every actual lower-horizon gauge symmetry lifts through a group homomorphism. -/
theorem gomesTruncatedJetGaugeHorizon_surjective (n r : ℕ) (z : ℂ) :
    Function.Surjective (gomesTruncatedJetGaugeHorizon n r z) := by
  intro u
  exact ⟨gomesTruncatedJetGaugeHorizonSection n r z u, gomesTruncatedJetGaugeHorizon_section n r z u⟩

/-- The canonical group section faithfully retains every lower-horizon gauge transformation. -/
theorem gomesTruncatedJetGaugeHorizonSection_injective (n r : ℕ) (z : ℂ) :
    Function.Injective (gomesTruncatedJetGaugeHorizonSection n r z) := by
  intro u v h
  have hr := congrArg (gomesTruncatedJetGaugeHorizon n r z) h
  simpa only [gomesTruncatedJetGaugeHorizon_section] using hr

/-- The canonical group lift retains the actual scalar character. -/
theorem gomesTruncatedJetGaugeHorizonSection_character (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup n z) :
    gomesTruncatedJetGaugeCharacter (n + r) z (gomesTruncatedJetGaugeHorizonSection n r z u) =
      gomesTruncatedJetGaugeCharacter n z u := by
  rw [← gomesTruncatedJetGaugeHorizon_character n r z, gomesTruncatedJetGaugeHorizon_section]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
