import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.EnergyMesh.GaussianCover
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # A finite-size bound for the entire scalar distance profile -/

open Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
noncomputable section

/-- Chord distance associated to an interval of phases of length a,
capped when the interval covers a whole turn. -/
def clippedChord (a : ℝ) := 2*sin (min a (2*π)/4)

private theorem chord_lipschitz (a b : ℝ) :
    |2*sin (a/4)-2*sin (b/4)| ≤ |a-b|/2 := by
  rw [←mul_sub,abs_mul,abs_of_pos zero_lt_two]
  have h := Real.abs_sin_sub_sin_le (a/4) (b/4)
  rw [←sub_div,abs_div,abs_of_pos (by norm_num : (0:ℝ)<4)] at h
  linarith only [h]

theorem clippedChord_lipschitz (a b : ℝ) : |clippedChord a-clippedChord b| ≤ |a-b|/2 := by
  apply (chord_lipschitz _ _).trans
  apply div_le_div_of_nonneg_right _ zero_le_two
  rcases le_total a (2*π) with ha | ha <;> rcases le_total b (2*π) with hb | hb
  · simp only [min_eq_left ha,min_eq_left hb,le_rfl]
  · rw [min_eq_left ha,min_eq_right hb,abs_of_nonpos (sub_nonpos.mpr ha),
      abs_of_nonpos (sub_nonpos.mpr (ha.trans hb))]
    linarith only [hb]
  · rw [min_eq_right ha,min_eq_left hb,abs_of_nonneg (sub_nonneg.mpr hb),
      abs_of_nonneg (sub_nonneg.mpr (hb.trans ha))]
    linarith only [ha]
  · simp only [min_eq_right ha,min_eq_right hb,sub_self,abs_zero,abs_nonneg]

/-- Diameter gives the exact clipped profile to within t times the energy
covering radius, including dates beyond the first wrap. -/
theorem scalar_chord_error {N : ℕ} (H : EnergyOperator (Fin N→Bool)) {q t : ℝ}
    (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hc : ∀ y ∈ Icc (lower H) (upper H), ∃ i, |H.2.isHermitian.eigenvalues i-y| ≤ q) :
    |orbitCircuitDistance H 0 t-clippedChord (t*circuitHamiltonianSpectralWidth H)| ≤ t*q := by
  let b := t*circuitHamiltonianSpectralWidth H
  let A := orbitSpectralEnclosingArcLength H t
  obtain ⟨hl,hu⟩ := physical_arc_bounds H hc ht
  change min b (2*π-2*t*q) ≤ A at hl
  change A ≤ min b (2*π) at hu
  have h : min b (2*π)-2*t*q ≤ A := by
    apply le_trans _ hl
    exact le_min ((sub_le_self _ (mul_nonneg (mul_nonneg zero_le_two ht) hq)).trans (min_le_left ..))
      (sub_le_sub_right (min_le_right ..) _)
  rw [orbitCircuitDistance_zeroGate_eq_enclosingArc]
  apply (chord_lipschitz A (min b (2*π))).trans
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith only [h]

/-- After a full turn the missing squared diameter is at most the
square of t times the energy covering radius. -/
theorem saturated_scalar_deficit {N : ℕ} (H : EnergyOperator (Fin N→Bool)) {q t : ℝ}
    (hq : 0 ≤ q) (ht : 0 ≤ t) (hfull : 2*π ≤ t*circuitHamiltonianSpectralWidth H)
    (hc : ∀ y ∈ Icc (lower H) (upper H), ∃ i, |H.2.isHermitian.eigenvalues i-y| ≤ q) :
    sqrt (4-(orbitCircuitDistance H 0 t)^2) ≤ t*q := by
  let A := orbitSpectralEnclosingArcLength H t
  obtain ⟨hl,hu⟩ := physical_arc_bounds H hc ht
  rw [min_eq_right ((sub_le_self _ (mul_nonneg (mul_nonneg zero_le_two ht) hq)).trans hfull)] at hl
  have hA : 0 ≤ A := spectralEnclosingArcLength_nonneg _
  have hπ : A ≤ 2*π := hu.trans (min_le_right ..)
  have hcos : 0 ≤ cos (A/4) := cos_nonneg_of_mem_Icc ⟨by linarith only [hA,pi_pos],by linarith only [hπ]⟩
  rw [orbitCircuitDistance_zeroGate_eq_enclosingArc]
  change sqrt (4-(2*sin (A/4))^2) ≤ _
  rw [show 4-(2*sin (A/4))^2=(2*cos (A/4))^2 by nlinarith only [sin_sq_add_cos_sq (A/4)],
    sqrt_sq (mul_nonneg zero_le_two hcos)]
  have h := Real.abs_cos_sub_cos_le (A/4) (π/2)
  rw [cos_pi_div_two,sub_zero,abs_of_nonneg hcos,abs_of_nonpos (by linarith only [hπ] : A/4-π/2 ≤ 0)] at h
  change 2*π-2*t*q ≤ A at hl
  linarith only [h,hl]

#print axioms saturated_scalar_deficit
#print axioms scalar_chord_error
end
end GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
