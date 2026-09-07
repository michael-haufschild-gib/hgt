import GaloisForLFunctions.RHTower.ThetaCuspModularGlobalDriftBarrier
import GaloisForLFunctions.RHTower.ThetaCuspFullReflectionEighthProjectiveClockChamber

/-!
# Decreasing energies of the actual modular source orbit

Completeness bounds the mass drift. A shear-gap identity then makes a first
quadratic energy decrease, bounding the drift by its initial tangent. This
orders shear above drift and exposes the stronger energy A + 4 u²/3.
-/

namespace RHTower
noncomputable section
open Set
set_option maxHeartbeats 1000000

private abbrev u := thetaCuspModularMassDrift
private abbrev a := thetaCuspModularGapAmplitude
private abbrev w := thetaCuspModularTransverseShear

private theorem dw (x : ℝ) :
    HasDerivAt w (2+a x/2+2*u x^2/9+2*u x*w x/3) x := by
  convert hasDerivAt_thetaCuspModularTransverseShear x using 1
  dsimp [u, thetaCuspModularMassDrift]
  ring

private theorem w_zero : w 0 = 0 := by
  simp [w, thetaCuspModularTransverseShear, thetaCuspModularDrift_re_zero,
    thetaCuspModularODEState_Z_zero]

private theorem w_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ w x := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [w_zero]
  · exact (thetaCuspModularTransverseShear_pos_of_pos hx).le

/-- Uniform rational ceiling for the initial modular squared scale. -/
theorem thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths :
    thetaCuspSelfDualModularScale^2 < (96/5 : ℝ) := by
  have h := thetaCuspSelfDualModularScale_sq_lt_projectiveClockThreshold
  linarith

private theorem shearGap_deriv (x : ℝ) :
    HasDerivAt (fun t => w t-2*u t/3-4*t) (2*u x*w x/3) x := by
  convert ((dw x).sub ((hasDerivAt_thetaCuspModularMassDrift x).const_mul 2
    |>.div_const 3)).sub ((hasDerivAt_id x).const_mul 4) using 1 <;>
    first | rfl | (dsimp only [id_eq, u, a, w]; ring)

/-- A source-forced shear gap grows at least linearly on the entire positive half-orbit. -/
theorem thetaCuspModularTransverseShear_lower {x : ℝ} (hx : 0 ≤ x) :
    4*x+2*u x/3 ≤ w x := by
  have hmono : MonotoneOn (fun t => w t-2*u t/3-4*t) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t _ => (shearGap_deriv t).continuousAt.continuousWithinAt)
      (fun t _ => (shearGap_deriv t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (show 0 < t from by simpa only [interior_Ici, mem_Ioi] using ht).le
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (thetaCuspModularMassDrift_nonneg ht0)) (w_nonneg ht0)) (by norm_num)
  have h := hmono (by norm_num : (0 : ℝ) ∈ Ici (0 : ℝ)) (show x ∈ Ici 0 from hx) hx
  simp only [w_zero, thetaCuspModularMassDrift_zero] at h
  linarith

private theorem energy_deriv (c x : ℝ) :
    HasDerivAt (fun t => a t+c*u t^2)
      (-2*a x*w x+2*c*u x*(-3+u x^2/3+3*a x/4)) x := by
  convert (hasDerivAt_thetaCuspModularGapAmplitude x).add
    ((hasDerivAt_thetaCuspModularMassDrift x).pow 2 |>.const_mul c) using 1 <;>
    first | rfl | ring

private theorem firstEnergy_le_initial {x : ℝ} (hx : 0 ≤ x) :
    a x+(4/9 : ℝ)*u x^2 ≤ thetaCuspSelfDualModularScale^2 := by
  have hanti : AntitoneOn (fun t => a t+(4/9 : ℝ)*u t^2) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t _ => (energy_deriv (4/9) t).continuousAt.continuousWithinAt)
      (fun t _ => (energy_deriv (4/9) t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (show 0 < t from by simpa only [interior_Ici, mem_Ioi] using ht).le
    have hu0 := thetaCuspModularMassDrift_nonneg ht0
    have hu3 := thetaCuspModularMassDrift_lt_three ht0
    have hw := thetaCuspModularTransverseShear_lower ht0
    have ha := thetaCuspModularGapAmplitude_pos t
    have hp := mul_nonneg ha.le (show 0 ≤ w t-u t/3 by linarith)
    have hq := mul_nonneg hu0 (show 0 ≤ 9-u t^2 by nlinarith)
    nlinarith only [hp, hq]
  have h := hanti (by norm_num : (0 : ℝ) ∈ Ici (0 : ℝ)) (show x ∈ Ici 0 from hx) hx
  norm_num only [thetaCuspModularMassDrift_zero, thetaCuspModularGapAmplitude_zero, add_zero] at h
  exact h

/-- The full mass drift stays below its rational initial tangent. -/
theorem thetaCuspModularMassDrift_le_tangent {x : ℝ} (hx : 0 ≤ x) :
    u x ≤ (57/5)*x := by
  have hd (t : ℝ) : HasDerivAt (fun t => u t-(57/5)*t)
      (-3+u t^2/3+3*a t/4-57/5) t :=
    (hasDerivAt_thetaCuspModularMassDrift t).sub
      (by simpa using ((hasDerivAt_id t).const_mul (57/5 : ℝ)))
  have hanti : AntitoneOn (fun t => u t-(57/5)*t) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t _ => (hd t).hasDerivWithinAt)
    intro t ht
    have ht0 : 0 ≤ t := (show 0 < t from by simpa only [interior_Ici, mem_Ioi] using ht).le
    have he := firstEnergy_le_initial ht0
    have hs := thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths
    nlinarith
  have h := hanti (by norm_num : (0 : ℝ) ∈ Ici (0 : ℝ)) (show x ∈ Ici 0 from hx) hx
  simp only [thetaCuspModularMassDrift_zero] at h
  linarith

/-- Transverse shear dominates actual mass drift globally. -/
theorem thetaCuspModularMassDrift_le_shear {x : ℝ} (hx : 0 ≤ x) :
    u x ≤ w x := by
  have hgap := thetaCuspModularTransverseShear_lower hx
  have hu := thetaCuspModularMassDrift_le_tangent hx
  linarith

/-- Strong quadratic energy of the full modular source is decreasing. -/
theorem antitoneOn_thetaCuspModularStrongEnergy :
    AntitoneOn (fun t => a t+(4/3 : ℝ)*u t^2) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun t _ => (energy_deriv (4/3) t).continuousAt.continuousWithinAt)
    (fun t _ => (energy_deriv (4/3) t).hasDerivWithinAt)
  intro t ht
  have ht0 : 0 ≤ t := (show 0 < t from by simpa only [interior_Ici, mem_Ioi] using ht).le
  have hu0 := thetaCuspModularMassDrift_nonneg ht0
  have hu3 := thetaCuspModularMassDrift_lt_three ht0
  have hw := thetaCuspModularMassDrift_le_shear ht0
  have ha := thetaCuspModularGapAmplitude_pos t
  have hp := mul_nonneg ha.le (show 0 ≤ w t-u t by linarith)
  have hq := mul_nonneg hu0 (show 0 ≤ 9-u t^2 by nlinarith)
  nlinarith only [hp, hq]

/-- Unconditional global quadratic energy ceiling on the actual source orbit. -/
theorem thetaCuspModularStrongEnergy_lt {x : ℝ} (hx : 0 ≤ x) :
    a x+(4/3 : ℝ)*u x^2 < 96/5 := by
  have h := antitoneOn_thetaCuspModularStrongEnergy (by norm_num : (0 : ℝ) ∈ Ici (0 : ℝ)) (show x ∈ Ici 0 from hx) hx
  norm_num only [thetaCuspModularMassDrift_zero, thetaCuspModularGapAmplitude_zero, add_zero] at h
  exact h.trans_lt thetaCuspSelfDualModularScale_sq_lt_ninetySix_fifths

/-- The stronger energy removes the adverse mixed term in the shear equation. -/
theorem thetaCuspModularTransverseShear_deriv_lt_quadratic {x : ℝ} (hx : 0 ≤ x) :
    deriv w x < 58/5+w x^2/4 := by
  rw [(dw x).deriv]
  have he := thetaCuspModularStrongEnergy_lt hx
  nlinarith [sq_nonneg (2*u x/3-w x/2)]

end
end RHTower
