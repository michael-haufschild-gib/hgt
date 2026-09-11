import GaloisForLFunctions.HTGeometry.GomesFiniteFockFormalLogCalculus
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetUnipotentLogarithm

/-!
# Actual finite joint coordinates lift to the full formal coordinate groups

Existing polynomial-symbol classification supplies every lift. The literal
scalar observation forces constant coefficient zero for nilpotent coordinates
and one for unipotent units, so no additional lift hypotheses are required.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Every nilpotent joint coordinate is the actual finite evaluation of a based formal series. -/
theorem gomesTruncatedJetNilpotentSpace_formal_lift (n : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    ∃ G : GomesBasedFormalSeries, gomesFiniteFockFormalHom (n + 1) G.val = E.val.val := by
  obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial (n + 1) E.val.val).mp
    ((gomesTruncatedJetJointAlgebra_mem_iff n z E.val.val).mp E.val.property).1
  have hc := gomesTruncatedJetNilpotentSpace_augmentation n z E
  change E.val.val 0 0 = 0 at hc
  rw [← hp, gomesFiniteFockPolynomialHom_diagonal] at hc
  let G : GomesBasedFormalSeries := ⟨(p : PowerSeries ℂ), by
    change PowerSeries.constantCoeff (p : PowerSeries ℂ) = 0
    rw [Polynomial.constantCoeff_coe]
    exact hc⟩
  refine ⟨G, ?_⟩
  change gomesFiniteFockFormalHom (n + 1) (p : PowerSeries ℂ) = E.val.val
  rw [gomesFiniteFockFormalHom_coe]
  exact hp

/-- Every actual unipotent gauge transformation lifts to an actual normalized formal unit. -/
theorem gomesTruncatedJetUnipotentGroup_formal_lift (n : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) :
    ∃ F : gomesNormalizedFormalUnitGroup, gomesFiniteFockFormalHom (n + 1) F.val.val = u.val.val.val := by
  obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial (n + 1) u.val.val.val).mp
    ((gomesTruncatedJetJointAlgebra_mem_iff n z u.val.val.val).mp u.val.property).1
  have hc : u.val.val.val 0 0 = 1 :=
    congrArg Units.val (show gomesTruncatedJetGaugeCharacter n z u.val = 1 from u.property)
  rw [← hp, gomesFiniteFockPolynomialHom_diagonal] at hc
  have hf : IsUnit (p : PowerSeries ℂ) := by
    rw [PowerSeries.isUnit_iff_constantCoeff, Polynomial.constantCoeff_coe, hc]
    exact isUnit_one
  let F : gomesNormalizedFormalUnitGroup := ⟨hf.unit, by
    rw [gomesNormalizedFormalUnitGroup_mem_iff, IsUnit.unit_spec, Polynomial.constantCoeff_coe, hc]⟩
  refine ⟨F, ?_⟩
  change gomesFiniteFockFormalHom (n + 1) hf.unit.val = u.val.val.val
  rw [IsUnit.unit_spec, gomesFiniteFockFormalHom_coe]
  exact hp

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
