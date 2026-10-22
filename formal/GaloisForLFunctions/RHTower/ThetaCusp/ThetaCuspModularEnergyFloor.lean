import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularEnergyBounds

/-!
# A global modular energy floor and positive theta-power sources

A subcritical energy value would force the bounded mass drift to grow at a
uniform positive rate on a complete ray. The resulting energy floor keeps the
curvature bracket positive for every theta power through four. Normalizing the
mass slopes gives an even, strictly positive cusp source for this whole family;
parameter one recovers the literal full theta-cusp source.
-/

namespace RHTower
noncomputable section
open Set

private abbrev u := thetaCuspModularMassDrift
private abbrev a := thetaCuspModularGapAmplitude
private abbrev w := thetaCuspModularTransverseShear
private abbrev e (x : ℝ) := a x + (4 / 3 : ℝ) * u x ^ (2 : ℕ)

private theorem source_reserve (x : ℝ) : 0 < 2 * u x ^ (2 : ℕ) + 3 * a x - 18 := by
  have h := thetaCuspModularSourceFactor_re_pos x
  rw [thetaCuspModularSourceFactor_re_eq_driftCone] at h
  have hq : 0 < (2 * u x ^ (2 : ℕ) + 3 * a x - 18) / 48 := by
    convert h using 1
    dsimp only [u, a, thetaCuspModularMassDrift, thetaCuspModularGapAmplitude]
    ring
  linarith only [hq]

private theorem energy_deriv (x : ℝ) :
    HasDerivAt e
      (-2 * a x * (w x - u x) - (8 * u x / 9) * (9 - u x ^ (2 : ℕ))) x := by
  convert (hasDerivAt_thetaCuspModularGapAmplitude x).add
    ((hasDerivAt_thetaCuspModularMassDrift x).pow 2 |>.const_mul (4 / 3 : ℝ)) using 1 <;>
    first | rfl | ring

/-- The actual strong modular energy decreases strictly on the nonnegative ray. -/
theorem strictAntiOn_thetaCuspModularStrongEnergy :
    StrictAntiOn (fun x => thetaCuspModularGapAmplitude x +
      (4 / 3 : ℝ) * thetaCuspModularMassDrift x ^ (2 : ℕ)) (Ici 0) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ici 0)
    (fun x _ => (energy_deriv x).continuousAt.continuousWithinAt)
    (fun x _ => (energy_deriv x).hasDerivWithinAt)
  intro x hx
  have hx0 : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
  have hu : 0 < u x := neg_pos.mpr (thetaCuspModularDrift_re_neg_of_pos hx0)
  have hu3 := thetaCuspModularMassDrift_lt_three hx0.le
  have hp := mul_nonneg (thetaCuspModularGapAmplitude_pos x).le
    (sub_nonneg.mpr (thetaCuspModularMassDrift_le_shear hx0.le))
  have hq := mul_pos hu (show 0 < 9 - u x ^ (2 : ℕ) by nlinarith only [hu, hu3])
  nlinarith only [hp, hq]

private theorem energy_lower {x : ℝ} (hx : 0 ≤ x) : 12 ≤ e x := by
  by_contra hn
  have he : e x < 12 := lt_of_not_ge hn
  let c := (12 - e x) / 8
  have hc : 0 < c := by dsimp [c]; linarith only [he]
  have hbound (t : ℝ) (ht : x ≤ t) : c ≤ deriv u t := by
    have ht0 := hx.trans ht
    have het := antitoneOn_thetaCuspModularStrongEnergy hx ht0 ht
    have ha := thetaCuspModularGapAmplitude_pos t
    have hs := source_reserve t
    rw [(hasDerivAt_thetaCuspModularMassDrift t).deriv]
    dsimp only [c, e, u, a] at *
    nlinarith only [het, ha, hs]
  have hgrowth := (convex_Ici x).mul_sub_le_image_sub_of_le_deriv (f := u) (C := c)
    (fun t _ => (hasDerivAt_thetaCuspModularMassDrift t).continuousAt.continuousWithinAt)
    (fun t _ => (hasDerivAt_thetaCuspModularMassDrift t).differentiableAt.differentiableWithinAt)
    (fun t ht => hbound t (show x ≤ t from
      (show x < t from by simpa only [interior_Ici, mem_Ioi] using ht).le))
    x (show x ∈ Ici x from le_refl x) (x + 4 / c)
    (show x + 4 / c ∈ Ici x from
      le_add_of_nonneg_right (div_nonneg (by norm_num) hc.le))
    (by have := div_pos (by norm_num : (0 : ℝ) < 4) hc; linarith)
  have hcancel : c * (x + 4 / c - x) = 4 := by field_simp [hc.ne']; ring
  rw [hcancel] at hgrowth
  have hu := thetaCuspModularMassDrift_nonneg hx
  have hu3 := thetaCuspModularMassDrift_lt_three
    (show 0 ≤ x + 4 / c by positivity)
  linarith only [hgrowth, hu, hu3]

/-- Completeness and positive source force the strong energy strictly above twelve. -/
theorem thetaCuspModularStrongEnergy_gt_twelve {x : ℝ} (hx : 0 ≤ x) :
    12 < thetaCuspModularGapAmplitude x +
      (4 / 3 : ℝ) * thetaCuspModularMassDrift x ^ (2 : ℕ) := by
  have hl := energy_lower (show 0 ≤ x + 1 by linarith)
  have hs := strictAntiOn_thetaCuspModularStrongEnergy hx
    (show 0 ≤ x + 1 by linarith) (show x < x + 1 by linarith)
  exact hl.trans_lt hs

/-- The curvature bracket of every theta power through four is strictly positive. -/
theorem thetaCuspModularPowerSourceBracket_pos {x v : ℝ}
    (hx : 0 ≤ x) (hv : v ≤ 4) :
    0 < (-3 + thetaCuspModularMassDrift x ^ (2 : ℕ) / 3 +
        3 * thetaCuspModularGapAmplitude x / 4) / 6 -
      v * (1 / 4 - thetaCuspModularMassDrift x ^ (2 : ℕ) / 36) := by
  have he := thetaCuspModularStrongEnergy_gt_twelve hx
  have hu := thetaCuspModularMassDrift_nonneg hx
  have hu3 := thetaCuspModularMassDrift_lt_three hx
  have hs : 0 ≤ (1 / 4 : ℝ) - thetaCuspModularMassDrift x ^ (2 : ℕ) / 36 := by
    nlinarith only [hu, hu3]
  have hp := mul_nonneg (sub_nonneg.mpr hv) hs
  nlinarith only [he, hp]


/-- Theta powers rescaled to keep the asymptotic mass slopes equal to one half. -/
def thetaCuspNormalizedPowerMass (v x : ℝ) : ℝ :=
  Real.exp (v * Real.log (Bottcher.completedThetaProfile (x / v)))

/-- The cusp source of the normalized theta power. -/
def thetaCuspNormalizedPowerSource (v x : ℝ) : ℝ :=
  (iteratedDeriv 2 (thetaCuspNormalizedPowerMass v) x -
    thetaCuspNormalizedPowerMass v x / 4) / 2

private theorem mass_deriv (x : ℝ) :
    HasDerivAt Bottcher.completedThetaProfile
      (Bottcher.completedThetaProfile x * thetaCuspModularMassDrift x / 6) x := by
  have h : HasDerivAt (fun y =>
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H y).re)
      (-(1 / 6 : ℂ) * thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x *
        thetaCuspModularReducedState HTGeometry.ModularThetaReducedState.S x).re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_thetaCuspModularMass_reduced x)
  simp only [thetaCuspModularODEState_H_eq_completedThetaProfile, Complex.ofReal_re] at h
  convert h using 1
  simp [thetaCuspModularReducedState, thetaCuspModularMassDrift, Complex.mul_re]
  ring

private theorem powerMass_deriv (v : ℝ) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (thetaCuspNormalizedPowerMass v)
      (thetaCuspNormalizedPowerMass v x * thetaCuspModularMassDrift (x / v) / 6) x := by
  have hH := (thetaCuspCompletedThetaProfile_pos (x / v)).ne'
  have hc : HasDerivAt (fun t => Bottcher.completedThetaProfile (t / v))
      (Bottcher.completedThetaProfile (x / v) * thetaCuspModularMassDrift (x / v) / 6 / v) x := by
    simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
      (mass_deriv (x / v)).comp x ((hasDerivAt_id x).div_const v)
  have h : HasDerivAt (thetaCuspNormalizedPowerMass v)
      (thetaCuspNormalizedPowerMass v x * (v *
        (Bottcher.completedThetaProfile (x / v) * thetaCuspModularMassDrift (x / v) / 6 / v /
          Bottcher.completedThetaProfile (x / v)))) x := ((hc.log hH).const_mul v).exp
  have hcoef : thetaCuspNormalizedPowerMass v x * thetaCuspModularMassDrift (x / v) / 6 =
      thetaCuspNormalizedPowerMass v x * (v *
        (Bottcher.completedThetaProfile (x / v) * thetaCuspModularMassDrift (x / v) / 6 / v /
          Bottcher.completedThetaProfile (x / v))) := by
    field_simp [hv, hH]
  rw [← hcoef] at h
  exact h

private theorem powerMass_second_deriv (v : ℝ) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (deriv (thetaCuspNormalizedPowerMass v))
      (thetaCuspNormalizedPowerMass v x *
        (thetaCuspModularMassDrift (x / v) ^ (2 : ℕ) / 36 +
          (-3 + thetaCuspModularMassDrift (x / v) ^ (2 : ℕ) / 3 +
            3 * thetaCuspModularGapAmplitude (x / v) / 4) / (6 * v))) x := by
  have hf : deriv (thetaCuspNormalizedPowerMass v) = fun t =>
      thetaCuspNormalizedPowerMass v t * thetaCuspModularMassDrift (t / v) / 6 := by
    funext t
    exact (powerMass_deriv v hv t).deriv
  rw [hf]
  have hu : HasDerivAt (fun t => thetaCuspModularMassDrift (t / v))
      ((-3 + thetaCuspModularMassDrift (x / v) ^ (2 : ℕ) / 3 +
        3 * thetaCuspModularGapAmplitude (x / v) / 4) / v) x := by
    simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
      (hasDerivAt_thetaCuspModularMassDrift (x / v)).comp x ((hasDerivAt_id x).div_const v)
  have h : HasDerivAt (fun t => thetaCuspNormalizedPowerMass v t *
      thetaCuspModularMassDrift (t / v) / 6)
      ((thetaCuspNormalizedPowerMass v x * thetaCuspModularMassDrift (x / v) / 6 *
          thetaCuspModularMassDrift (x / v) + thetaCuspNormalizedPowerMass v x *
          ((-3 + thetaCuspModularMassDrift (x / v) ^ (2 : ℕ) / 3 +
            3 * thetaCuspModularGapAmplitude (x / v) / 4) / v)) / 6) x :=
    ((powerMass_deriv v hv x).mul hu).div_const 6
  convert h using 1
  ring

/-- Exact mass-normalized source factor for every nonzero theta-power parameter. -/
theorem thetaCuspNormalizedPowerSource_eq (v : ℝ) (hv : v ≠ 0) (x : ℝ) :
    thetaCuspNormalizedPowerSource v x = thetaCuspNormalizedPowerMass v x / (2 * v) *
      ((-3 + thetaCuspModularMassDrift (x / v) ^ (2 : ℕ) / 3 +
          3 * thetaCuspModularGapAmplitude (x / v) / 4) / 6 -
        v * (1 / 4 - thetaCuspModularMassDrift (x / v) ^ (2 : ℕ) / 36)) := by
  unfold thetaCuspNormalizedPowerSource
  rw [iteratedDeriv_succ, iteratedDeriv_one,
    (powerMass_second_deriv v hv x).deriv]
  field_simp
  ring

private theorem thetaMass_even (x : ℝ) :
    Bottcher.completedThetaProfile (-x) = Bottcher.completedThetaProfile x := by
  rw [Bottcher.completedThetaProfile, Bottcher.completedThetaProfile]
  rw [show 2 * -x = -2 * x by ring]
  have hexp : (Real.exp (-2 * x)) ^ (1 / 2 : ℝ) = Real.exp (-x) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [HurwitzZeta.evenKernel_functional_equation, hexp]
  rw [HurwitzZeta.evenKernel_eq_cosKernel_of_zero]
  have hinv : 1 / Real.exp (-2 * x) = Real.exp (2 * x) := by
    rw [one_div, ← Real.exp_neg]
    congr 1
    ring
  rw [hinv]
  field_simp
  have hprod : Real.exp (-x) * Real.exp (x / 2) = Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (-x) * HurwitzZeta.cosKernel 0 (Real.exp (x * 2)) *
      Real.exp (x / 2) =
      (Real.exp (-x) * Real.exp (x / 2)) *
        HurwitzZeta.cosKernel 0 (Real.exp (x * 2)) by ring,
    hprod]

/-- Reflection symmetry survives normalization and source extraction. -/
theorem thetaCuspNormalizedPowerSource_neg (v x : ℝ) :
    thetaCuspNormalizedPowerSource v (-x) = thetaCuspNormalizedPowerSource v x := by
  have hm (t : ℝ) : thetaCuspNormalizedPowerMass v (-t) = thetaCuspNormalizedPowerMass v t := by
    simp only [thetaCuspNormalizedPowerMass, neg_div, thetaMass_even]
  have hf : (fun t => thetaCuspNormalizedPowerMass v (-t)) = thetaCuspNormalizedPowerMass v :=
    funext hm
  have hd := iteratedDeriv_comp_neg 2 (thetaCuspNormalizedPowerMass v) x
  rw [hf] at hd
  norm_num only [neg_one_sq, one_smul] at hd
  unfold thetaCuspNormalizedPowerSource
  rw [hm, ← hd]

/-- Every normalized theta power with parameter in `(0,4]` has a positive cusp source. -/
theorem thetaCuspNormalizedPowerSource_pos {v : ℝ} (hv0 : 0 < v) (hv4 : v ≤ 4)
    (x : ℝ) : 0 < thetaCuspNormalizedPowerSource v x := by
  have hpos (t : ℝ) (ht : 0 ≤ t) : 0 < thetaCuspNormalizedPowerSource v t := by
    rw [thetaCuspNormalizedPowerSource_eq v hv0.ne']
    exact mul_pos (div_pos (Real.exp_pos _) (mul_pos (by norm_num) hv0))
      (thetaCuspModularPowerSourceBracket_pos (div_nonneg ht hv0.le) hv4)
  rcases le_total 0 x with hx | hx
  · exact hpos x hx
  · have h := hpos (-x) (neg_nonneg.mpr hx)
    rwa [thetaCuspNormalizedPowerSource_neg] at h

/-- Parameter one recovers the literal full theta-cusp source. -/
theorem thetaCuspNormalizedPowerSource_one (x : ℝ) :
    thetaCuspNormalizedPowerSource 1 x = thetaCuspFullSource x := by
  rw [thetaCuspNormalizedPowerSource_eq 1 one_ne_zero]
  have h := congrArg Complex.re
    (ofReal_thetaCuspFullSource_eq_completedThetaProfile_mul_modularFactor x)
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  rw [thetaCuspModularSourceFactor_re_eq_driftCone] at h
  rw [h]
  simp only [thetaCuspNormalizedPowerMass, div_one, one_mul,
    Real.exp_log (thetaCuspCompletedThetaProfile_pos x)]
  dsimp only [thetaCuspModularMassDrift, thetaCuspModularGapAmplitude]
  ring

end
end RHTower
