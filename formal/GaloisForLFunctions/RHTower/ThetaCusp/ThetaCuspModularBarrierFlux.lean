import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularRatioSlopeBarrier
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspModularCompensationDeterminant
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterCompensationFlux
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspEvenFourExplicitTail

/-!
# A zero-integral correction from the actual modular slope barrier

The complete theta orbit supplies a positive profile whose center flux has a
strictly negative derivative past `2/3`. The flux is absolutely admitted and has
zero integral derivative. Subtracting it gives an explicit positive source reserve
on that ray. A fixed coefficient makes the revised even rank-four source matrix
strict there, uniformly in aperture through the proved weighted comparison.

The reserve is a lower comparison for the flux correction only on that ray.
Its cost below `2/3` and the global rank-seven integral sign remain unproved.
-/

open Set Filter Topology MeasureTheory
namespace RHTower.ThetaCuspModularRatio
noncomputable section

/-- The nonnegative defect in the actual one-third drift barrier. -/
def barrierDefect (x : ℝ) : ℝ := u x/3-J x
/-- A nonnegative full-source profile bounded by the literal source square. -/
def barrierMass (x : ℝ) : ℝ := sourceAmplitude x^(2 : ℕ)*barrierDefect x
/-- Center flux built from the actual barrier profile. -/
def barrierFlux (a x : ℝ) : ℝ := x*Real.sinh (2*a*x)*barrierMass x

theorem barrierDefect_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ barrierDefect x :=
  sub_nonneg.mpr (J_le_third_drift hx)

private theorem dBarrier {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt barrierDefect
      (t x*(k x+1/3)*(4/3-k x)+2*u x*(k x+2/3)*barrierDefect x) x := by
  have hk : k x ≠ 0 := ne_of_gt (lt_trans (by norm_num) (k_gt hx))
  convert ((du hx).div_const 3).sub (dJ hx) using 1
  all_goals first | rfl | (dsimp [barrierDefect, D, t]; field_simp [hk]; ring)

private theorem dMass (x : ℝ) : HasDerivAt Bottcher.completedThetaProfile
    (Bottcher.completedThetaProfile x*u x/6) x := by
  have h : HasDerivAt (fun y =>
      (thetaCuspModularODEState HTGeometry.ModularThetaODEState.H y).re)
      (-(1/6 : ℂ)*thetaCuspModularODEState HTGeometry.ModularThetaODEState.H x*
        thetaCuspModularReducedState HTGeometry.ModularThetaReducedState.S x).re x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_thetaCuspModularMass_reduced x)
  simp only [thetaCuspModularODEState_H_eq_completedThetaProfile, Complex.ofReal_re] at h
  convert h using 1
  simp [thetaCuspModularReducedState, thetaCuspModularMassDrift]
  ring

private theorem dAmplitude {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt sourceAmplitude (sourceAmplitude x*u x*(1/6-2*k x)) x := by
  convert ((dMass x).mul (dt hx)).div_const 12 using 1
  all_goals first | rfl | (dsimp [sourceAmplitude]; ring)

theorem dBarrierMass {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt barrierMass
      (sourceAmplitude x^(2 : ℕ)*(t x*(k x+1/3)*(4/3-k x)+
        u x*(5/3-2*k x)*barrierDefect x)) x := by
  convert ((dAmplitude hx).pow 2).mul (dBarrier hx) using 1
  all_goals first | rfl | (simp only [Pi.pow_apply]; ring)

theorem barrierMass_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ barrierMass x :=
  mul_nonneg (sq_nonneg _) (barrierDefect_nonneg hx)

private theorem k_lower_center {x : ℝ} (hx : 0 ≤ x) : 4*x/3+2/3 ≤ k x := by
  have hc := center_le_retained_ratio hx
  have hj := J_nonneg hx
  have hk := k_gt hx
  have hm := mul_le_mul_of_nonneg_right (thetaCuspModularMassDrift_lt_three hx).le
    (show 0 ≤ k x-2/3 by linarith only [hk])
  nlinarith only [hc, hj, hm]

theorem barrierMass_pos {x : ℝ} (hx : 2/3 ≤ x) : 0 < barrierMass x := by
  have hx0 : 0 < x := by linarith only [hx]
  have hk : 4/3 < k x := by linarith only [k_lower_center hx0.le, hx]
  have hB : 0 < barrierDefect x := by
    by_contra hn
    have hz : barrierDefect x = 0 := le_antisymm (le_of_not_gt hn) (barrierDefect_nonneg hx0.le)
    have hmin : IsLocalMin barrierDefect x := by
      filter_upwards [eventually_gt_nhds hx0] with y hy
      rw [hz]
      exact barrierDefect_nonneg hy.le
    have hd := hmin.hasDerivAt_eq_zero (dBarrier hx0.le)
    rw [hz, mul_zero, add_zero] at hd
    have ht := t_pos hx0.le
    have hn := mul_neg_of_pos_of_neg
      (mul_pos ht (show 0 < k x+1/3 by linarith only [hk]))
      (show 4/3-k x < 0 by linarith only [hk])
    linarith only [hd, hn]
  have ha : 0 < sourceAmplitude x := by
    dsimp [sourceAmplitude]
    exact div_pos (mul_pos (thetaCuspCompletedThetaProfile_pos x) (t_pos hx0.le)) (by norm_num)
  exact mul_pos (sq_pos_of_pos ha) hB

theorem barrierMass_deriv_upper {x : ℝ} (hx : 2/3 ≤ x) :
    deriv barrierMass x ≤ -(8*x-1)*barrierMass x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hk : 4/3 ≤ k x := by linarith only [k_lower_center hx0, hx]
  have hfirst : t x*(k x+1/3)*(4/3-k x) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (t_pos hx0).le (by linarith only [hk])) (by linarith only [hk])
  have hc := center_le_retained_ratio hx0
  have hu := thetaCuspModularMassDrift_lt_three hx0
  have hj := J_nonneg hx0
  have hrate : 8*x-1 ≤ u x*(2*k x-5/3) := by nlinarith only [hc, hu, hj]
  have hmul := mul_le_mul_of_nonneg_right hrate (barrierDefect_nonneg hx0)
  have h := mul_le_mul_of_nonneg_left
    (show t x*(k x+1/3)*(4/3-k x)+u x*(5/3-2*k x)*barrierDefect x ≤
      -(8*x-1)*barrierDefect x by nlinarith only [hfirst, hmul]) (sq_nonneg (sourceAmplitude x))
  rw [(dBarrierMass hx0).deriv]
  dsimp [barrierMass]
  nlinarith only [h]

theorem dBarrierFlux {x : ℝ} (hx : 0 ≤ x) (a : ℝ) :
    HasDerivAt (barrierFlux a)
      ((Real.sinh (2*a*x)+2*a*x*Real.cosh (2*a*x))*barrierMass x+
        x*Real.sinh (2*a*x)*deriv barrierMass x) x := by
  convert ((hasDerivAt_id x).mul (((hasDerivAt_id x).const_mul (2*a)).sinh)).mul
    (dBarrierMass hx).differentiableAt.hasDerivAt using 1
  all_goals first | rfl | (dsimp; ring)

private theorem hyperbolic_upper (y : ℝ) :
    y*Real.cosh y ≤ (1+y)*Real.sinh y := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (2*y)) (Real.exp_pos (-y)).le
  have he : Real.exp (2*y)*Real.exp (-y) = Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  rw [Real.cosh_eq, Real.sinh_eq]
  nlinarith only [h]

theorem barrierFlux_deriv_upper {a x : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hx : 2/3 ≤ x) :
    deriv (barrierFlux a) x ≤ -(2/9)*Real.sinh (2*a*x)*barrierMass x := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hs := Real.sinh_nonneg_iff.mpr (show 0 ≤ 2*a*x by positivity)
  have hb := barrierMass_nonneg hx0
  have hh := hyperbolic_upper (2*a*x)
  have ha' : 2*a*x ≤ x := by nlinarith only [mul_le_mul_of_nonneg_right ha hx0]
  have hm := mul_le_mul_of_nonneg_right ha' hs
  have hc := mul_le_mul_of_nonneg_right
    (show Real.sinh (2*a*x)+2*a*x*Real.cosh (2*a*x) ≤ (2+x)*Real.sinh (2*a*x) by
      nlinarith only [hh, hm]) hb
  have hd := mul_le_mul_of_nonneg_left (barrierMass_deriv_upper hx) (mul_nonneg hx0 hs)
  have hq : 2+2*x-8*x^(2 : ℕ) ≤ -(2/9 : ℝ) := by
    have h := mul_nonneg (show 0 ≤ x-2/3 by linarith only [hx])
      (show 0 ≤ 8*x+10/3 by linarith only [hx])
    nlinarith only [h]
  have he := mul_le_mul_of_nonneg_right hq (mul_nonneg hs hb)
  rw [(dBarrierFlux hx0 a).deriv]
  nlinarith only [hc, hd, he]

/-- The negative flux derivative is a strict positive correction on the upper ray. -/
theorem barrierFlux_deriv_neg {a x : ℝ} (ha0 : 0 < a) (ha : a ≤ 1/2)
    (hx : 2/3 ≤ x) : deriv (barrierFlux a) x < 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  have hs : 0 < Real.sinh (2*a*x) := Real.sinh_pos_iff.mpr (by positivity)
  have hb := barrierMass_pos hx
  exact (barrierFlux_deriv_upper ha0.le ha hx).trans_lt
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hs) hb)

theorem barrierMass_le_source_sq {x : ℝ} (hx : 0 ≤ x) :
    barrierMass x ≤ thetaCuspFullSource x^(2 : ℕ) := by
  have hB : barrierDefect x ≤ 1 := by
    dsimp [barrierDefect]
    linarith only [thetaCuspModularMassDrift_lt_three hx, J_nonneg hx]
  have hv : 1 ≤ (k x-1/6)^(2 : ℕ) := by
    have hk := k_gt_fiveFourths hx
    nlinarith only [sq_nonneg (k x-1/6-1), hk]
  have hm := mul_le_mul_of_nonneg_left hB (sq_nonneg (sourceAmplitude x))
  have hn := mul_le_mul_of_nonneg_left hv (sq_nonneg (sourceAmplitude x))
  rw [source_eq_ratio_coordinates hx]
  dsimp [barrierMass]
  nlinarith only [hm, hn]

theorem barrierFlux_nonneg {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    0 ≤ barrierFlux a x := by
  dsimp [barrierFlux]
  exact mul_nonneg (mul_nonneg hx (Real.sinh_nonneg_iff.mpr (by positivity)))
    (barrierMass_nonneg hx)

theorem barrierFlux_tendsto_zero {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) :
    Tendsto (barrierFlux a) atTop (𝓝 0) := by
  have ha1 : |a| < 1 := by rw [abs_of_nonneg ha0]; linarith only [ha]
  let F := thetaCuspTiltedSchwartzReal a ha1
  let S := SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x)
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) F F)
  have hS (x : ℝ) : S x = x*Real.exp (2*a*x)*thetaCuspFullSource x^(2 : ℕ) := by
    rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)]
    change x*((Real.exp (a*x)*thetaCuspFullSource x)*(Real.exp (a*x)*thetaCuspFullSource x)) = _
    have he : Real.exp (a*x)*Real.exp (a*x) = Real.exp (2*a*x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = x*(Real.exp (a*x)*Real.exp (a*x))*thetaCuspFullSource x^(2 : ℕ) := by ring
      _ = _ := by rw [he]
  have ht : Tendsto (S : ℝ → ℝ) atTop (𝓝 0) :=
    S.tendsto_cocompact.mono_left atTop_le_cocompact
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact barrierFlux_nonneg ha0 hx
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    have hs := Real.sinh_nonneg_iff.mpr (show 0 ≤ 2*a*x by positivity)
    have he : Real.sinh (2*a*x) ≤ Real.exp (2*a*x) := by
      rw [Real.sinh_eq]
      linarith only [Real.exp_pos (2*a*x), Real.exp_pos (-(2*a*x))]
    have hb := mul_le_mul_of_nonneg_left (barrierMass_le_source_sq hx) (mul_nonneg hx hs)
    have hg := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hx)
      (sq_nonneg (thetaCuspFullSource x))
    rw [hS]
    exact hb.trans hg

private theorem continuousOn_barrierMass_deriv : ContinuousOn (deriv barrierMass) (Ici 0) := by
  have hS : ContinuousOn sourceAmplitude (Ici 0) := fun x hx =>
    (dAmplitude hx).continuousAt.continuousWithinAt
  have ht : ContinuousOn t (Ici 0) := fun x hx => (dt hx).continuousAt.continuousWithinAt
  have hk : ContinuousOn k (Ici 0) := fun x hx => (dk hx).continuousAt.continuousWithinAt
  have hu : ContinuousOn u (Ici 0) := fun x hx => (du hx).continuousAt.continuousWithinAt
  have hB : ContinuousOn barrierDefect (Ici 0) := fun x hx =>
    (dBarrier hx).continuousAt.continuousWithinAt
  have hc : ContinuousOn (fun x => sourceAmplitude x^(2 : ℕ)*(t x*(k x+1/3)*(4/3-k x)+
        u x*(5/3-2*k x)*barrierDefect x)) (Ici 0) := by fun_prop
  exact hc.congr (fun x hx => (dBarrierMass hx).deriv)

private theorem continuousOn_barrierFlux_deriv (a : ℝ) :
    ContinuousOn (deriv (barrierFlux a)) (Ici 0) := by
  have hB : ContinuousOn barrierMass (Ici 0) := fun x hx =>
    (dBarrierMass hx).continuousAt.continuousWithinAt
  have hd := continuousOn_barrierMass_deriv
  have hc : ContinuousOn (fun x =>
      (Real.sinh (2*a*x)+2*a*x*Real.cosh (2*a*x))*barrierMass x+
        x*Real.sinh (2*a*x)*deriv barrierMass x) (Ici 0) := by fun_prop
  exact hc.congr (fun x hx => (dBarrierFlux hx a).deriv)

theorem integrableOn_barrierFlux_deriv {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) :
    IntegrableOn (deriv (barrierFlux a)) (Ioi 0) := by
  have htail : IntegrableOn (deriv (barrierFlux a)) (Ioi (2/3 : ℝ)) := by
    apply integrableOn_Ioi_deriv_of_nonpos'
      (fun x hx => (dBarrierFlux ((by norm_num : (0 : ℝ) ≤ 2/3).trans hx) a).differentiableAt.hasDerivAt)
      (fun x hx => ?_) (barrierFlux_tendsto_zero ha0 ha)
    have h := barrierFlux_deriv_upper ha0 ha.le hx.le
    have hx0 : 0 ≤ x := (by norm_num : (0 : ℝ) ≤ 2/3).trans hx.le
    have hs := Real.sinh_nonneg_iff.mpr (show 0 ≤ 2*a*x by positivity)
    have hb := barrierMass_nonneg hx0
    exact h.trans (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hs) hb)
  have hcompact : IntegrableOn (deriv (barrierFlux a)) (Icc (0 : ℝ) (2/3)) :=
    ((continuousOn_barrierFlux_deriv a).mono Icc_subset_Ici_self).integrableOn_compact isCompact_Icc
  apply (hcompact.union htail).mono_set
  intro x hx
  by_cases hb : x ≤ 2/3
  · exact Or.inl ⟨hx.le, hb⟩
  · exact Or.inr (lt_of_not_ge hb)

/-- Absolute admission and the two endpoints give an exact zero integral. -/
theorem integral_barrierFlux_deriv {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1/2) :
    ∫ x : ℝ in Ioi 0, deriv (barrierFlux a) x = 0 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := 0)
    (fun x hx => (dBarrierFlux hx a).differentiableAt.hasDerivAt)
    (integrableOn_barrierFlux_deriv ha0 ha) (barrierFlux_tendsto_zero ha0 ha)
  simpa [barrierFlux] using h

/-- Aperture-independent lower source gain, valid for centers at least `2/3`. -/
def barrierReserve (x : ℝ) : ℝ := barrierMass x/(18*x)

theorem barrierReserve_pos {x : ℝ} (hx : 2/3 ≤ x) : 0 < barrierReserve x := by
  exact div_pos (barrierMass_pos hx) (by have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx; positivity)

/-- The literal negative flux derivative dominates the source reserve on the upper ray. -/
theorem barrierReserve_weighted_lower {a x : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ 1/2)
    (hx : 2/3 ≤ x) :
    4*x*Real.sinh (2*a*x)*barrierReserve x ≤ -deriv (barrierFlux a) x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2/3) hx)
  have he : 4*x*Real.sinh (2*a*x)*barrierReserve x =
      (2/9)*Real.sinh (2*a*x)*barrierMass x := by
    dsimp [barrierReserve]
    field_simp [hx0]
    ring
  rw [he]
  linarith only [barrierFlux_deriv_upper ha0 ha hx]

open GaloisForLFunctions.HTGeometry Matrix

/-- Native even matrix with both source corrections retained in the last entry. -/
def barrierRepairedMatrix (K x : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  finiteHankelMatrix (fun n => (-1 : ℝ)^n*thetaCuspNativeReflectionJet (2*n) x+
    if n = 6 then 1000000000000*thetaCuspCenterCompensationSource x+K*barrierReserve x else 0) 4

private theorem repaired_head (K x : ℝ) :
    finiteHankelMatrix (fun n => (-1 : ℝ)^n*thetaCuspNativeReflectionJet (2*n) x+
      if n = 6 then 1000000000000*thetaCuspCenterCompensationSource x+K*barrierReserve x else 0) 3 =
        thetaCuspNativeEvenHead x := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [finiteHankelMatrix, thetaCuspNativeEvenHead]

theorem barrierRepairedMatrix_det (K x : ℝ) :
    (barrierRepairedMatrix K x).det =
      (thetaCuspNativeEvenFourCompensated 1000000000000 x).det+
        K*barrierReserve x*(thetaCuspNativeEvenHead x).det := by
  have hm : barrierRepairedMatrix K x =
      !![thetaCuspNativeReflectionJet 0 x, -thetaCuspNativeReflectionJet 2 x,
          thetaCuspNativeReflectionJet 4 x, -thetaCuspNativeReflectionJet 6 x;
        -thetaCuspNativeReflectionJet 2 x, thetaCuspNativeReflectionJet 4 x,
          -thetaCuspNativeReflectionJet 6 x, thetaCuspNativeReflectionJet 8 x;
        thetaCuspNativeReflectionJet 4 x, -thetaCuspNativeReflectionJet 6 x,
          thetaCuspNativeReflectionJet 8 x, -thetaCuspNativeReflectionJet 10 x;
        -thetaCuspNativeReflectionJet 6 x, thetaCuspNativeReflectionJet 8 x,
          -thetaCuspNativeReflectionJet 10 x,
          thetaCuspNativeReflectionJet 12 x+1000000000000*thetaCuspCenterCompensationSource x+
            K*barrierReserve x] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [barrierRepairedMatrix, finiteHankelMatrix]
    ring
  rw [hm, det_hankelFour, compensated_det_eq, thetaCuspNativeEvenFourDet_eq]
  norm_num [finiteHankelMatrix, thetaCuspNativeEvenHead, Matrix.det_fin_three, hankelFourDet]
  ring

/-- One fixed coefficient repairs the whole upper source ray; the inner sign remains open. -/
theorem exists_barrierRepairedMatrix_posDef_on_upper_ray :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 2/3 ≤ x → (barrierRepairedMatrix K x).PosDef := by
  let D (x : ℝ) := (thetaCuspNativeEvenFourCompensated 1000000000000 x).det
  let W (x : ℝ) := barrierReserve x*(thetaCuspNativeEvenHead x).det
  have hWpos (x : ℝ) (hx : 2/3 ≤ x) : 0 < W x :=
    mul_pos (barrierReserve_pos hx)
      (thetaCuspNativeEvenHead_posDef ((by norm_num : (0 : ℝ) ≤ 2/3).trans hx)).det_pos
  have hD : Continuous D := (continuous_thetaCuspNativeEvenFourCompensated _).matrix_det
  have hH : Continuous (fun x => (thetaCuspNativeEvenHead x).det) :=
    continuous_thetaCuspNativeEvenHead.matrix_det
  have hR : ContinuousOn barrierReserve (Icc (2/3 : ℝ) (6/5)) := by
    have hB : ContinuousOn barrierMass (Icc (2/3 : ℝ) (6/5)) := fun x hx =>
      (dBarrierMass ((by norm_num : (0 : ℝ) ≤ 2/3).trans hx.1)).continuousAt.continuousWithinAt
    exact hB.div (continuous_const.mul continuous_id).continuousOn
      (fun x hx => ne_of_gt (mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2/3) hx.1)))
  have hW : ContinuousOn W (Icc (2/3 : ℝ) (6/5)) := hR.mul hH.continuousOn
  let q (x : ℝ) := -D x/W x
  have hq : ContinuousOn q (Icc (2/3 : ℝ) (6/5)) :=
    hD.neg.continuousOn.div hW (fun x hx => (hWpos x hx.1).ne')
  obtain ⟨b, hb, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (2/3 : ℝ) (6/5)).Nonempty from ⟨2/3, by norm_num⟩) hq
  let K : ℝ := |q b|+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, hK, fun x hx => ?_⟩
  have hdet : 0 < (barrierRepairedMatrix K x).det := by
    rw [barrierRepairedMatrix_det, mul_assoc]
    change 0 < D x+K*W x
    by_cases htail : 6/5 ≤ x
    · have hd : 0 < D x :=
        (thetaCuspNativeEvenFourCompensated_posDef_on_explicit_tail
          (by norm_num : (0 : ℝ) ≤ 1000000000000)
          (by norm_num : (1000000000000 : ℝ) ≤ 3000000000000) htail).det_pos
      exact add_pos hd (mul_pos hK (hWpos x hx))
    · have hqx : q x < K := lt_of_le_of_lt
        ((hmax ⟨hx, (le_of_not_ge htail)⟩).trans (le_abs_self (q b)))
        (by dsimp [K]; linarith)
      have hm : -D x < K*W x := (div_lt_iff₀ (hWpos x hx)).mp hqx
      linarith only [hm]
  let m (n : ℕ) := (-1 : ℝ)^n*thetaCuspNativeReflectionJet (2*n) x+
    if n = 6 then 1000000000000*thetaCuspCenterCompensationSource x+K*barrierReserve x else 0
  have hhead : (finiteHankelMatrix m 3).PosDef := by
    rw [show finiteHankelMatrix m 3 = thetaCuspNativeEvenHead x from repaired_head K x]
    exact thetaCuspNativeEvenHead_posDef ((by norm_num : (0 : ℝ) ≤ 2/3).trans hx)
  have hs : 0 < finiteHankelSuccessorSchur m 3 := by
    have he := finiteHankelMatrix_succ_det_eq_schur hhead
    change (barrierRepairedMatrix K x).det = _ at he
    rw [he] at hdet
    exact (mul_pos_iff_of_pos_left hhead.det_pos).mp hdet
  exact (finiteHankelMatrix_succ_posDef_iff_schur_pos hhead).mpr hs

end
end RHTower.ThetaCuspModularRatio
