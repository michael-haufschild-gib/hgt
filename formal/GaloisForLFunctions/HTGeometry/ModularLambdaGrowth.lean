import GaloisForLFunctions.HTGeometry.ModularThetaNormBounds
import GaloisForLFunctions.HTGeometry.ModularHeightBounds

/-!
# A global height bound for modular lambda

Theta estimates in the fundamental domain and the finite anharmonic action
give a global bound exponential in the maximum of height and reciprocal height.
-/

open Complex UpperHalfPlane
open scoped MatrixGroups

namespace Bottcher

/-- The three quantities needed to control all six anharmonic transforms. -/
theorem modularLambda_norm_bounds_of_im_ge {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    ‖modularLambda τ‖ ≤ 14641 ∧
      ‖(modularLambda τ)⁻¹‖ ≤ 625 * Real.exp (Real.pi * τ.im) ∧
      ‖(1 - modularLambda τ)⁻¹‖ ≤ 625 := by
  have hp : 0 < τ.im := by linarith
  obtain ⟨h3l, h3u⟩ := thetaThree_norm_bounds hτ
  obtain ⟨h4l, h4u⟩ := thetaFour_norm_bounds hτ
  obtain ⟨h2l, h2u⟩ := thetaTwo_norm_bounds hτ
  have h3p : 0 < ‖thetaThree τ‖ := by linarith
  have h3ne : thetaThree τ ≠ 0 := norm_pos_iff.mp h3p
  have h4p : 0 < ‖thetaFour τ‖ := by linarith
  have h2p : 0 < ‖thetaTwo τ‖ := norm_pos_iff.mpr (thetaTwo_ne_zero_of_im_pos hp)
  have hepos := Real.exp_pos (-Real.pi * τ.im / 4)
  have hele : Real.exp (-Real.pi * τ.im / 4) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_pos Real.pi_pos hp])
  have h23 : ‖thetaTwo τ‖ / ‖thetaThree τ‖ ≤ 11 := by
    rw [div_le_iff₀ h3p]
    nlinarith
  have h32 : ‖thetaThree τ‖ / ‖thetaTwo τ‖ ≤ 5 / Real.exp (-Real.pi * τ.im / 4) := by
    rw [div_le_div_iff₀ h2p hepos]
    nlinarith
  have h34 : ‖thetaThree τ‖ / ‖thetaFour τ‖ ≤ 5 := by
    rw [div_le_iff₀ h4p]
    linarith
  have hminus : 1 - modularLambda τ = (thetaFour τ / thetaThree τ) ^ (4 : ℕ) := by
    have hh := Bottcher2Cusp.quarticDefect_eq_zero hp
    dsimp [quarticDefect] at hh
    rw [modularLambda, div_pow, div_pow]
    field_simp
    linear_combination hh
  refine ⟨?_, ?_, ?_⟩
  · rw [modularLambda, norm_pow, norm_div]
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ‖thetaTwo τ‖ / ‖thetaThree τ‖) h23 4
    norm_num at hh
    exact hh
  · rw [modularLambda, ← inv_pow, inv_div, norm_pow, norm_div]
    calc
      _ ≤ (5 / Real.exp (-Real.pi * τ.im / 4)) ^ (4 : ℕ) :=
        pow_le_pow_left₀ (by positivity) h32 4
      _ = 625 * Real.exp (Real.pi * τ.im) := by
        rw [div_pow, ← Real.exp_nat_mul]
        norm_num only [Nat.cast_ofNat, pow_succ, pow_zero]
        rw [div_eq_mul_inv, ← Real.exp_neg]
        congr 1
        congr 1
        ring
  · rw [hminus, ← inv_pow, inv_div, norm_pow, norm_div]
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ ‖thetaThree τ‖ / ‖thetaFour τ‖) h34 4
    norm_num at hh
    exact hh

/-- Three basic norm bounds control the complete anharmonic orbit. -/
theorem norm_anharmonic_le {w : Punctured} {B : ℝ}
    (h0 : ‖(w : ℂ)‖ ≤ B) (h1 : ‖(w : ℂ)⁻¹‖ ≤ B)
    (h2 : ‖(1 - (w : ℂ))⁻¹‖ ≤ B)
    {φ : Equiv.Perm Punctured} (hφ : φ ∈ anharmonicGroup) :
    ‖(φ w : ℂ)‖ ≤ 1 + B := by
  have hw0 : (w : ℂ) ≠ 0 := (mem_compl01.mp w.2).1
  have hw1 : (w : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (mem_compl01.mp w.2).2
  have hw10 : 1 - (w : ℂ) ≠ 0 := sub_ne_zero.mpr (mem_compl01.mp w.2).2.symm
  have h6 := anharmonicGroup_subset_sixSet hφ
  simp only [sixSet, Set.mem_insert_iff, Set.mem_singleton_iff] at h6
  rcases h6 with rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [Equiv.Perm.coe_one, id_eq] using h0.trans (by linarith)
  · simpa only [anharmS_apply] using
      (norm_sub_le (1 : ℂ) (w : ℂ)).trans (by simpa using add_le_add_left h0 1)
  · simp only [anharmT_apply]
    have he : (w : ℂ) / ((w : ℂ) - 1) = 1 - (1 - (w : ℂ))⁻¹ := by
      simp only [inv_eq_one_div]
      field_simp [hw0, hw1, hw10]
      ring
    rw [he]
    simpa only [norm_one] using (norm_sub_le (1 : ℂ) (1 - (w : ℂ))⁻¹).trans
      (by simpa using add_le_add_left h2 1)
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply]
    have he : 1 - (w : ℂ) / ((w : ℂ) - 1) = (1 - (w : ℂ))⁻¹ := by
      simp only [inv_eq_one_div]
      field_simp [hw0, hw1, hw10]
      ring
    rw [he]
    linarith
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply]
    have he : (1 - (w : ℂ)) / ((1 - (w : ℂ)) - 1) = 1 - (w : ℂ)⁻¹ := by
      simp only [inv_eq_one_div]
      field_simp [hw0, hw1, hw10]
      ring
    rw [he]
    simpa only [norm_one] using (norm_sub_le (1 : ℂ) (w : ℂ)⁻¹).trans
      (by simpa using add_le_add_left h1 1)
  · simp only [Equiv.Perm.coe_mul, Function.comp_apply, anharmS_apply, anharmT_apply]
    have he : 1 - (1 - (w : ℂ)) / ((1 - (w : ℂ)) - 1) = (w : ℂ)⁻¹ := by
      simp only [inv_eq_one_div]
      field_simp [hw0, hw1, hw10]
      ring
    rw [he]
    linarith

/-- Modular lambda has a global exponential bound in height and reciprocal height. -/
theorem norm_modularLambda_le_exp_height (τ : ℍ) :
    ‖modularLambda (τ : ℂ)‖ ≤ 20001 * Real.exp (Real.pi * max τ.im (1 / τ.im)) := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
  let w := g • τ
  have hw : (4 : ℝ) / 5 ≤ w.im := im_ge_four_fifths_of_mem_fd hg
  obtain ⟨h0, h1, h2⟩ := modularLambda_norm_bounds_of_im_ge hw
  change ‖(modularLambda (w : ℂ))⁻¹‖ ≤ 625 * Real.exp (Real.pi * w.im) at h1
  have he : 1 ≤ Real.exp (Real.pi * w.im) := Real.one_le_exp (by positivity)
  obtain ⟨φ, hφ, hφeq⟩ := exists_anharm_eq g⁻¹
  have heq : lambdaPunct τ = φ (lambdaPunct w) := by
    have hh := hφeq w
    simpa only [w, inv_smul_smul] using hh
  have hb : ‖(φ (lambdaPunct w) : ℂ)‖ ≤ 1 + 20000 * Real.exp (Real.pi * w.im) := by
    apply norm_anharmonic_le (B := 20000 * Real.exp (Real.pi * w.im))
    · change ‖modularLambda (w : ℂ)‖ ≤ _
      nlinarith
    · change ‖(modularLambda (w : ℂ))⁻¹‖ ≤ _
      nlinarith
    · change ‖(1 - modularLambda (w : ℂ))⁻¹‖ ≤ _
      nlinarith
    · exact hφ
  calc
    ‖modularLambda (τ : ℂ)‖ = ‖(φ (lambdaPunct w) : ℂ)‖ := by
      rw [← heq]; rfl
    _ ≤ 1 + 20000 * Real.exp (Real.pi * w.im) := hb
    _ ≤ 20001 * Real.exp (Real.pi * w.im) := by linarith
    _ ≤ 20001 * Real.exp (Real.pi * max τ.im (1 / τ.im)) := by
      gcongr
      exact modular_smul_im_le_max g τ

end Bottcher
