import GaloisForLFunctions.RHTower.ThetaCuspModularEnergyBounds

/-!
# A compact tube from the global modular energy

The exact source stays in 0 ≤ u,w ≤ 1 and 17 ≤ A ≤ 20 through x=8/95.
The same argument retains w ≤ 5u/4, needed to preserve the favorable terms
in the compensation source derivative.
-/

namespace RHTower
noncomputable section
open Set
set_option maxHeartbeats 800000

private abbrev u := thetaCuspModularMassDrift
private abbrev a := thetaCuspModularGapAmplitude
private abbrev w := thetaCuspModularTransverseShear

private theorem w_zero : w 0 = 0 := by
  simp [w, thetaCuspModularTransverseShear, thetaCuspModularDrift_re_zero,
    thetaCuspModularODEState_Z_zero]

private theorem w_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ w x := by
  exact (thetaCuspModularMassDrift_nonneg hx).trans
    (thetaCuspModularMassDrift_le_shear hx)

/-- The actual shear lies below a rational linear envelope through 8/95. -/
theorem thetaCuspModularTransverseShear_le_energyTangent {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) : w x ≤ (95/8)*x := by
  apply image_le_of_deriv_right_lt_deriv_boundary
    (f := w) (f' := deriv w) (a := 0) (b := 8/95)
    (fun t _ => (hasDerivAt_thetaCuspModularTransverseShear t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_thetaCuspModularTransverseShear t).differentiableAt.hasDerivAt.hasDerivWithinAt)
    (B := fun t => (95/8)*t) (B' := fun _ => 95/8)
    (by rw [w_zero]; norm_num)
    (fun t => by simpa using (hasDerivAt_id t).const_mul (95/8 : ℝ)) ?_ hx
  intro t ht heq
  have hw0 := w_nonneg ht.1
  have hw1 : w t ≤ 1 := by rw [heq]; linarith [ht.2]
  have hs := thetaCuspModularTransverseShear_deriv_lt_quadratic ht.1
  have hw2 : w t^2 ≤ 1 := by nlinarith
  linarith

/-- A quadratic lower barrier for the complete modular gap, with its literal initial value. -/
theorem thetaCuspModularGapAmplitude_energy_lower {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    thetaCuspSelfDualModularScale^2-228*x^2 ≤ a x := by
  have hd (t : ℝ) : HasDerivAt (fun t => a t+228*t^2)
      (-2*a t*w t+456*t) t := by
    convert (hasDerivAt_thetaCuspModularGapAmplitude t).add
      ((hasDerivAt_id t).pow 2 |>.const_mul 228) using 1 <;>
      first | rfl | (dsimp only [id_eq, a, w]; ring)
  have hmono : MonotoneOn (fun t => a t+228*t^2) (Icc 0 (8/95)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (8/95))
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) (8/95) :=
      ⟨(show t ∈ Ioo (0 : ℝ) (8/95) from by simpa only [interior_Icc] using ht).1.le,
       (show t ∈ Ioo (0 : ℝ) (8/95) from by simpa only [interior_Icc] using ht).2.le⟩
    have hw := thetaCuspModularTransverseShear_le_energyTangent ht'
    have hw0 := w_nonneg ht'.1
    have he := thetaCuspModularStrongEnergy_lt ht'.1
    have ha : a t ≤ 96/5 := by nlinarith [sq_nonneg (u t)]
    have hp := (mul_le_mul_of_nonneg_right ha hw0).trans
      (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 96/5))
    linarith
  have h := hmono (by norm_num : (0 : ℝ) ∈ Icc 0 (8/95)) hx hx.1
  simp only [thetaCuspModularGapAmplitude_zero] at h
  linarith

/-- The literal orbit enters no unproved coordinate box on the enlarged interval. -/
theorem thetaCuspModularState_energy_box {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) :
    0 ≤ u x ∧ u x ≤ 1 ∧ 17 ≤ a x ∧ a x ≤ 20 ∧ 0 ≤ w x ∧ w x ≤ 1 := by
  have hu0 := thetaCuspModularMassDrift_nonneg hx.1
  have hu := thetaCuspModularMassDrift_le_tangent hx.1
  have hw0 := w_nonneg hx.1
  have hw := thetaCuspModularTransverseShear_le_energyTangent hx
  have ha := thetaCuspModularGapAmplitude_energy_lower hx
  have hinit := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have he := thetaCuspModularStrongEnergy_lt hx.1
  have hx2 : x^2 ≤ (8/95 : ℝ)^2 := by nlinarith [hx.1, hx.2]
  refine ⟨hu0, ?_, ?_, ?_, hw0, ?_⟩ <;> nlinarith [hx.2, sq_nonneg (u x)]

/-- The same compact tube retains a positive lower linear drift. -/
theorem thetaCuspModularMassDrift_energy_lower {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) : (39/4)*x ≤ u x := by
  have hd (t : ℝ) : HasDerivAt (fun t => u t-(39/4)*t)
      (-3+u t^2/3+3*a t/4-39/4) t :=
    (hasDerivAt_thetaCuspModularMassDrift t).sub
      (by simpa using (hasDerivAt_id t).const_mul (39/4 : ℝ))
  have hmono : MonotoneOn (fun t => u t-(39/4)*t) (Icc 0 (8/95)) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (8/95))
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) (8/95) := by simpa only [interior_Icc] using ht
    have hb := thetaCuspModularState_energy_box ⟨ht'.1.le, ht'.2.le⟩
    nlinarith [hb.2.2.1, sq_nonneg (u t)]
  have h := hmono (by norm_num : (0 : ℝ) ∈ Icc 0 (8/95)) hx hx.1
  simp only [thetaCuspModularMassDrift_zero] at h
  linarith

/-- Relative shear is controlled by the actual drift, not an independent coordinate sample. -/
theorem thetaCuspModularTransverseShear_le_fiveFourths_drift {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (8/95)) : w x ≤ (5/4)*u x := by
  have hw := thetaCuspModularTransverseShear_le_energyTangent hx
  have hu := thetaCuspModularMassDrift_energy_lower hx
  linarith [hx.1]

end
end RHTower
