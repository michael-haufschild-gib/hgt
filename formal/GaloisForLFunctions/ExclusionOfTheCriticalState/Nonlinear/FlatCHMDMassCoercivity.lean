import GaloisForLFunctions.ExclusionOfTheCriticalState.Nonlinear.FlatProbabilityCompactness
import GaloisForLFunctions.RHTower.CHMDSignedGraphPolarization
import GaloisForLFunctions.RHTower.CHMDPolarJumpForm

/-!
# Sharp flat mass control on the actual arithmetic source graph

The theta–cosh source measure has total mass one half. The reflected
flat potential therefore controls source norm by an explicit nonlinear
bound, attained by every constant profile. Its pullback to the complete
arithmetic graph is C¹ and has exactly one critical point. This positive
mass loss is distinct from the original signed Weil energy.
-/

open MeasureTheory Filter Set
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
open _root_.RHTower.CHMDDoobGraph _root_.RHTower.CHMDPolar
noncomputable section

private theorem arithmetic_mass_total : massMeasure.real univ = 1 / 2 := by
  have h := integral_mass (fun _ => (1 : ℝ))
  simpa only [integral_const, smul_eq_mul, mul_one, integral_massDensity] using h

private theorem arithmetic_mass_ne_zero : massMeasure ≠ 0 := by
  intro h
  have hm := arithmetic_mass_total
  norm_num [h] at hm

/-- The reflected flat potential integrated against the literal arithmetic source measure. -/
def flatMassEnergy (p : SourceGraph) : ℝ := evenIntegralEnergy (sourceMap p)

def flatMassFirstVariation (p : SourceGraph) : SourceGraph →L[ℝ] ℝ :=
  (innerSL ℝ (evenGradientLp (sourceMap p))).comp sourceMap

theorem flatMassEnergy_hasFDerivAt (p : SourceGraph) :
    HasFDerivAt flatMassEnergy (flatMassFirstVariation p) p :=
  (evenIntegralEnergy_hasFDerivAt (sourceMap p)).comp p sourceMap.hasFDerivAt

theorem flatMassEnergy_contDiff_one : ContDiff ℝ 1 flatMassEnergy :=
  evenIntegralEnergy_contDiff_one.comp sourceMap.contDiff

/-- The exact finite source mass fixes both constants in the nonlinear norm bound. -/
theorem flatMassEnergy_coercivity (p : SourceGraph) :
    potential (Real.sqrt (2 * ‖p.val.fst‖ ^ 2)) ≤ 2 * flatMassEnergy p := by
  letI : NeZero massMeasure := ⟨arithmetic_mass_ne_zero⟩
  have h := evenIntegralEnergy_finite_coercivity (sourceMap p)
  rw [arithmetic_mass_total] at h
  norm_num only [one_div, inv_inv] at h
  exact h

/-- The positive flat source loss has a single zero on the complete graph. -/
theorem flatMassEnergy_zero_iff (p : SourceGraph) : flatMassEnergy p = 0 ↔ p = 0 := by
  change evenIntegralEnergy (sourceMap p) = 0 ↔ p = 0
  rw [evenIntegralEnergy_zero_iff]
  constructor
  · intro h
    apply source_projection_injective
    change sourceMap p = sourceMap 0
    rwa [map_zero]
  · rintro rfl
    exact map_zero sourceMap

/-- Testing the first variation on the profile itself excludes every nonzero critical point. -/
theorem flatMassEnergy_critical_iff (p : SourceGraph) :
    fderiv ℝ flatMassEnergy p = 0 ↔ p = 0 := by
  rw [(flatMassEnergy_hasFDerivAt p).fderiv]
  constructor
  · intro h
    have hx := congrArg (fun L : SourceGraph →L[ℝ] ℝ => L p) h
    change inner ℝ (evenGradientLp (sourceMap p)) (sourceMap p) = 0 at hx
    have he : flatMassEnergy p ≤ 0 :=
      (evenIntegralEnergy_le_inner_gradient (sourceMap p)).trans_eq hx
    have hn : 0 ≤ flatMassEnergy p :=
      add_nonneg (integral_energy_bounds (sourceMap p)).1
        (integral_energy_bounds (-sourceMap p)).1
    exact (flatMassEnergy_zero_iff p).mp (le_antisymm he hn)
  · rintro rfl
    have hg : evenGradientLp (0 : Lp ℝ 2 massMeasure) = 0 :=
      (evenGradientLp_zero_iff _).mpr rfl
    simp only [flatMassFirstVariation, map_zero, hg, ContinuousLinearMap.zero_comp]

/-- Every constant graph profile has an exact nonlinear source energy. -/
theorem flatMassEnergy_constant (c : ℝ) : flatMassEnergy (constantLift c) = evenPotential c / 2 := by
  have hc : (constantLift c).val.fst =ᵐ[massMeasure] fun _ => c :=
    (memLp_const c : MemLp (fun _ : ℝ => c) 2 massMeasure).coeFn_toLp
  rw [flatMassEnergy, evenIntegralEnergy_integral]
  calc
    (∫ x, evenPotential (sourceMap (constantLift c) x) ∂massMeasure) =
        ∫ _, evenPotential c ∂massMeasure := by
      apply integral_congr_ae
      filter_upwards [hc] with x hx
      change evenPotential ((constantLift c).val.fst x) = _
      rw [hx]
    _ = evenPotential c / 2 := by
      rw [integral_const, arithmetic_mass_total, smul_eq_mul]
      ring

/-- The arithmetic norm bound is attained, with no loss in its measure normalization. -/
theorem flatMassEnergy_coercivity_attained (c : ℝ) :
    potential (Real.sqrt (2 * ‖(constantLift c).val.fst‖ ^ 2)) =
      2 * flatMassEnergy (constantLift c) := by
  rw [constantLift_mass, flatMassEnergy_constant]
  have h : 2 * (c ^ 2 / 2) = c ^ 2 := by ring
  rw [h, Real.sqrt_sq_eq_abs, evenPotential_eq_potential_abs]
  ring

#print axioms flatMassEnergy_hasFDerivAt
#print axioms flatMassEnergy_coercivity
#print axioms flatMassEnergy_zero_iff
#print axioms flatMassEnergy_critical_iff
#print axioms flatMassEnergy_coercivity_attained
end
end GaloisForLFunctions.ExclusionOfTheCriticalState.FlatConvex
