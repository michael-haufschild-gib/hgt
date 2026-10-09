import GaloisForLFunctions.RHTower.PhysicalPluckerThetaLift
import GaloisForLFunctions.HTGeometry.ApertureLogTranslation

/-!
# The cone extension of the physical Plücker density (POINH §7)

For the normalized physical-overlap Plücker density `T` (positive, compact, injective on an
infinite-dimensional space) the scale histories `[ε ↦ E_ε(cT)]` generate one cone in the
boundary-history corona:

* every scale germ has quasispectrum `[0,1]`, all are fractional-linear functions of `e_1`, and
  `C*(e_c : c > 0) = C*(e_1) ≅ C_0((0,1])` isometrically;
* the differences of two scales generate the open-history (suspension) ideal, the kernel of the
  endpoint character, giving the endpoint sequence `0 → J_T → C*(e_1) → ℂ → 0`;
* its connecting map `n ↦ [exp(2πi n e_1)]` identifies `ℤ` with the winding classes of
  unitaries of `J_T`, and the closed unit goes to the class `t ↦ exp(2πit)` of winding one;
* this unit is common to every scale lift, while two lifts differ by the sub-unit contrast and
  their relative exponential is null-homotopic.
-/

open GaloisForLFunctions.HTGeometry

namespace RHTower.HedenmalmThetaSource

noncomputable section

local notation "Tn" => normalizedPhysicalPluckerOperator

private theorem hT : (Tn).IsPositive := normalizedPhysicalPluckerOperator_isPositive
private theorem hcpt : IsCompactOperator Tn := normalizedPhysicalPluckerOperator_isCompact
private theorem hinj : Function.Injective Tn := normalizedPhysicalPluckerOperator_injective
private theorem hH : ¬ FiniteDimensional ℂ GammaSewnCriticalPhysicalPluckerHilbert :=
  not_finiteDimensional_pluckerHilbert

/-- One generator and spectrum `[0,1]` for the scale germs of the physical density. -/
theorem physicalPlucker_scaleGerm_cone :
    (∀ (c : ℝ) (hc : 0 < c), quasispectrum ℂ (scaleGerm Tn hT hcpt hc) = unitIntervalC) ∧
      (∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d),
        scaleGerm Tn hT hcpt hd = cfcₙ (scaleChange (d / c)) (scaleGerm Tn hT hcpt hc)) ∧
      scaleOrbitAlgebra hT hcpt = NonUnitalStarAlgebra.elemental ℂ (scaleGerm Tn hT hcpt one_pos) ∧
      Isometry (cfcₙHom (R := ℂ) (isSelfAdjoint_scaleGerm hT hcpt one_pos).isStarNormal) :=
  ⟨fun _ hc => quasispectrum_scaleGerm hT hcpt hc hinj hH,
    fun _ _ hc hd => scaleGerm_eq_cfcₙ_scaleChange hT hcpt hc hinj hH hd,
    scaleOrbitAlgebra_eq_elemental hT hcpt hinj hH,
    (scaleGerm_cstar_iso hT hcpt hinj hH).2.1⟩

/-- **The endpoint sequence** `0 → J_T → C*(e_1) → ℂ → 0` of the physical density. -/
theorem physicalPlucker_endpoint_exact_sequence :
    let h1 := one_mem_quasispectrum_unitGerm hT hcpt hinj hH
    let hn := isStarNormal_unitGerm hT hcpt
    Isometry (cfcₙHom (R := ℂ) hn) ∧
      NonUnitalStarAlgHom.range (cfcₙHom (R := ℂ) hn) =
        NonUnitalStarAlgebra.elemental ℂ (unitGerm hT hcpt) ∧
      openHistoryIdeal hT hcpt = (endpointKernel h1).map (cfcₙHom (R := ℂ) hn) ∧
      (∀ g, g ∈ endpointKernel h1 ↔ endpointChar h1 g = 0) ∧
      Function.Surjective (endpointChar h1) ∧
      ∀ (c : ℝ) (hc : 0 < c), ∃ g, cfcₙHom (R := ℂ) hn g = scaleGerm Tn hT hcpt hc ∧
        endpointChar h1 g = 1 :=
  endpoint_exact_sequence hT hcpt hinj hH

/-- **The integral charge**: the connecting map is a bijection onto the winding classes and the
closed unit goes to the class of winding one. -/
theorem physicalPlucker_connectingMap :
    Function.Bijective (connectingMap hT hcpt hinj hH) ∧
      Function.Bijective (openK₁Winding hT hcpt hinj hH) ∧
      openK₁Winding hT hcpt hinj hH (connectingMap hT hcpt hinj hH 1) = 1 :=
  connectingMap_bijective hT hcpt hinj hH

/-- **Scale blindness**: the unit is common to every positive scale lift and cannot be bounded by
the sub-unit contrast between two lifts. -/
theorem physicalPlucker_directSubunit_noGo :
    (∀ (c : ℝ) (hc : 0 < c),
      openWinding hT hcpt hinj hH (boundaryExp (scaleGerm Tn hT hcpt hc)) = 1) ∧
    (∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d),
      JoinedIn (openHistoryUnitaries hT hcpt)
        (boundaryExp (scaleGerm Tn hT hcpt hc - scaleGerm Tn hT hcpt hd)) 1) ∧
    (∀ (c d : ℝ) (hc : 0 < c) (hd : 0 < d),
      ‖scaleGerm Tn hT hcpt hc - scaleGerm Tn hT hcpt hd‖ = |germContrast c d| ∧
        |germContrast c d| < 1 ∧ (germContrast c d = 0 ↔ c = d)) ∧
    (∀ (κ : OpenK₁ hT hcpt → ℤ) (c d : ℝ) (hc : 0 < c) (hd : 0 < d),
      κ (ZerothHomotopy.mk ⟨_, boundaryExp_sub_mem hT hcpt hinj hH hc hd⟩) =
        κ (ZerothHomotopy.mk ⟨1, one_mem_openHistoryUnitaries hT hcpt⟩)) :=
  directSubunit_noGo hT hcpt hinj hH

end

end RHTower.HedenmalmThetaSource
