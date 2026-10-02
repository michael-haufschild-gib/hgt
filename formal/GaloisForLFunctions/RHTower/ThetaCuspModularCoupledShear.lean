import GaloisForLFunctions.RHTower.ThetaCuspModularEnergyTube

/-!
# Coupled amplitude--shear bound for the complete theta source

The source ODE preserves `(3a-12)w <= (2a+8)u`.  Its defect has a
nonpositive derivative because the actual modular orbit satisfies
`0 <= u <= w`.  This retains amplitude dependence lost by independent
coordinate bounds and gives the sharper compact ratio `w/u < 46/45`.
-/

namespace RHTower.ThetaCuspCompactProjective
open Set
noncomputable section
private abbrev u := thetaCuspModularMassDrift
private abbrev a := thetaCuspModularGapAmplitude
private abbrev w := thetaCuspModularTransverseShear

private theorem dw (x : ℝ) :
    HasDerivAt w (2+a x/2+2*u x^2/9+2*u x*w x/3) x := by
  convert! hasDerivAt_thetaCuspModularTransverseShear x using 1
  dsimp [u,thetaCuspModularMassDrift]
  ring

private theorem w_zero : w 0 = 0 := by
  simp [w,thetaCuspModularTransverseShear,thetaCuspModularDrift_re_zero,
    thetaCuspModularODEState_Z_zero]

private theorem coupled_deriv (x : ℝ) :
    HasDerivAt (fun x => (3*a x-12)*w x-(2*a x+8)*u x)
      (-6*a x*w x*(w x-u x)-8*u x*w x-16*u x^2/3) x := by
  have ha := hasDerivAt_thetaCuspModularGapAmplitude x
  convert! ((((ha.const_mul 3).sub_const 12).mul (dw x)).sub
    (((ha.const_mul 2).add_const 8).mul (hasDerivAt_thetaCuspModularMassDrift x))) using 1
  dsimp [a,w,u]
  ring

/-- Global amplitude-dependent shear bound on the actual modular orbit. -/
theorem coupled_shear_bound {x : ℝ} (hx : 0 ≤ x) :
    (3*a x-12)*w x ≤ (2*a x+8)*u x := by
  have hm : AntitoneOn (fun x => (3*a x-12)*w x-(2*a x+8)*u x) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t _; exact (coupled_deriv t).continuousAt.continuousWithinAt
    · intro t _; exact (coupled_deriv t).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := (show 0 < t by simpa only [interior_Ici,mem_Ioi] using ht).le
      rw [(coupled_deriv t).deriv]
      have hu := thetaCuspModularMassDrift_nonneg ht0
      have huw := thetaCuspModularMassDrift_le_shear ht0
      have hw : 0 ≤ w t := le_trans hu huw
      have ha := thetaCuspModularGapAmplitude_pos t
      have hprod : 0 ≤ 6*a t*w t*(w t-u t) := by positivity
      have hprod2 := mul_nonneg hu hw
      nlinarith [sq_nonneg (u t)]
  have h := hm (by simp) hx hx
  simp only [w_zero,u,thetaCuspModularMassDrift_zero,mul_zero,sub_zero] at h
  linarith

/-- A quantitative compact box for the actual source. -/
theorem compact_source_bounds {x : ℝ} (hx : x ∈ Icc (0:ℝ) (1/50)) :
    0 ≤ u x ∧ u x < 23/100 ∧ 19 < a x ∧ a x < 96/5 ∧ u x ≤ w x := by
  have hx' : x ∈ Icc (0:ℝ) (8/95) := ⟨hx.1,by linarith [hx.2]⟩
  have hu0 := thetaCuspModularMassDrift_nonneg hx.1
  have hu := thetaCuspModularMassDrift_le_tangent hx.1
  have ha := thetaCuspModularGapAmplitude_energy_lower hx'
  have hinit := thetaCuspSelfDualModularScale_sq_gt_nineteen_point_one
  have he := thetaCuspModularStrongEnergy_lt hx.1
  have hx2 : x^2 ≤ (1/50:ℝ)^2 := by nlinarith [hx.1,hx.2]
  refine ⟨hu0,?_,?_,?_,thetaCuspModularMassDrift_le_shear hx.1⟩
  · linarith [hx.2]
  · linarith
  · nlinarith [sq_nonneg (u x)]

/-- The coupled invariant improves the independent compact shear cone. -/
theorem compact_relative_shear_lt {x : ℝ} (hx0 : 0 < x) (hx : x ≤ 1/50) :
    w x < (46/45)*u x := by
  obtain ⟨_,_,ha,_,huw⟩ := compact_source_bounds ⟨hx0.le,hx⟩
  have hu : 0 < u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx0)
  have hd : 0 < (a x-19)*(3*w x-2*u x) :=
    mul_pos (by linarith) (by linarith)
  have hc := coupled_shear_bound hx0.le
  nlinarith only [hd,hc]

end
end RHTower.ThetaCuspCompactProjective
