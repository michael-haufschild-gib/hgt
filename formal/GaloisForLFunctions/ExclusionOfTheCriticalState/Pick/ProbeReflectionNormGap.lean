import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeZeroPhaseSensitivity

/-!
# The sharp operator-norm gap of actual zero reflection

Reflection differs from identity by either zero or operator norm two.
A single off-line coordinate supplies a nonzero negative-sector vector and
attains the upper bound. Every orbital phase defect has the corresponding
exact scalar gap, so small reflection error already implies triviality.
-/

noncomputable section
open Classical
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23

/-- The actual reflection is the identity exactly when every zero coordinate is fixed. -/
theorem zeroReflection_eq_one_iff :
    zeroReflection = 1 ↔ ∀ z : zetaZeroConfig.carrier, (z : ℂ).re = 1 / 2 := by
  constructor
  · intro h z
    by_contra hz
    have hm := (sector_masses_zeroBasis z).2
    rw [if_neg hz] at hm
    have hn : negativePart (zeroBasis z) = 0 := by
      rw [negativePart, h]
      simp only [one_apply_eq_self, sub_self, smul_zero]
    rw [negativeMass, hn, norm_zero] at hm
    norm_num at hm
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext z
    change x (reflectCarrier zetaZeroConfig z) = x z
    rw [(zeroCarrier_reflection_fixed_iff z).mpr (h z)]

private theorem norm_reflection_sub_one_le : ‖zeroReflection - 1‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖zeroReflection x - x‖ ≤ 2 * ‖x‖
  calc
    _ ≤ ‖zeroReflection x‖ + ‖x‖ := norm_sub_le _ _
    _ = 2 * ‖x‖ := by rw [norm_zeroReflection]; ring

/-- A single off-line coordinate forces the maximal possible reflection norm gap. -/
theorem norm_zeroReflection_sub_one :
    ‖zeroReflection - 1‖ =
      if ∀ z : zetaZeroConfig.carrier, (z : ℂ).re = 1 / 2 then 0 else 2 := by
  classical
  by_cases h : ∀ z : zetaZeroConfig.carrier, (z : ℂ).re = 1 / 2
  · rw [if_pos h, zeroReflection_eq_one_iff.mpr h, sub_self, norm_zero]
  · rw [if_neg h]
    obtain ⟨z, hz⟩ := not_forall.mp h
    let x := negativePart (zeroBasis z)
    have hx : 0 < ‖x‖ := by
      have hm := (sector_masses_zeroBasis z).2
      rw [if_neg hz] at hm
      change ‖x‖ ^ 2 = 1 / 2 at hm
      have hn := norm_nonneg x
      nlinarith only [hm, hn]
    have he : (zeroReflection - 1) x = (-2 : ℂ) • x := by
      change zeroReflection (negativePart (zeroBasis z)) - x = _
      rw [zeroReflection_negativePart]
      change -x - x = _
      module
    have hl := (zeroReflection - 1).le_opNorm x
    rw [he, norm_smul] at hl
    norm_num at hl
    apply le_antisymm norm_reflection_sub_one_le
    nlinarith only [hl, hx]

/-- Approximation within operator distance two already forces exact reflection triviality. -/
theorem norm_zeroReflection_sub_one_lt_two_iff :
    ‖zeroReflection - 1‖ < 2 ↔
      ∀ z : zetaZeroConfig.carrier, (z : ℂ).re = 1 / 2 := by
  rw [norm_zeroReflection_sub_one]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => by norm_num⟩
  · exact ⟨fun hn => ((lt_irrefl 2) hn).elim, fun hh => (h hh).elim⟩

/-- Every sector phase has the exact gap determined by its scalar phase and off-line support. -/
theorem norm_phaseRotation_sub_one (u : Circle) :
    ‖(phaseRotationEquiv u).toLinearIsometry.toContinuousLinearMap - 1‖ =
      if ∀ z : zetaZeroConfig.carrier, (z : ℂ).re = 1 / 2 then 0
      else ‖1 - (u : ℂ)‖ := by
  classical
  have he : (phaseRotationEquiv u).toLinearIsometry.toContinuousLinearMap - 1 =
      ((1 - (u : ℂ)) / 2) • (zeroReflection - 1) := by
    apply ContinuousLinearMap.ext
    intro x
    change phaseRotate u x - x = ((1 - (u : ℂ)) / 2) • (zeroReflection x - x)
    unfold phaseRotate positivePart negativePart
    module
  rw [he, norm_smul, norm_zeroReflection_sub_one]
  split_ifs
  · exact mul_zero _
  · rw [norm_div]
    norm_num

#print axioms zeroReflection_eq_one_iff
#print axioms norm_phaseRotation_sub_one
#print axioms norm_zeroReflection_sub_one
#print axioms norm_zeroReflection_sub_one_lt_two_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
