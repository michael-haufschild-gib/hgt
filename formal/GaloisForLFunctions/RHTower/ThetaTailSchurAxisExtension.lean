import GaloisForLFunctions.RHTower.ThetaTailJointCenterJets
import GaloisForLFunctions.HTGeometry.ClockParametricDerivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The actual center Schur kernel divided by its two vanishing axes.
Compact averages retain the mixed derivatives at coalescing nodes. -/

noncomputable section
open MeasureTheory Set
namespace RHTower.ThetaJoint
open ThetaConfluent ThetaCoordinate GaloisForLFunctions.HTGeometry

def squareMoment (m n : ℕ) (F : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, u^m*v^n*F (u*x) (v*y)

private theorem innerMoment_continuous (m n : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    Continuous fun p : (ℝ × ℝ) × ℝ =>
      ∫ v in (0 : ℝ)..1, p.2^m*v^n*F (p.2*p.1.1) (v*p.1.2) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hc : Continuous fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      F (p.1.2*p.1.1.1) (p.2*p.1.1.2) :=
    hF.comp (show Continuous (fun p : ((ℝ × ℝ) × ℝ) × ℝ =>
      (p.1.2*p.1.1.1, p.2*p.1.1.2)) from by fun_prop)
  exact ((continuous_fst.snd.pow m).mul (continuous_snd.pow n)).mul hc

theorem squareMoment_continuous (m n : ℕ) {F : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2) :
    Continuous fun p : ℝ × ℝ => squareMoment m n F p.1 p.2 :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (innerMoment_continuous m n hF) 0 1

theorem squareMoment_hasDerivAt_right (m n : ℕ) {F G : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2)
    (hd : ∀ x y, HasDerivAt (F x) (G x y) y) (x y : ℝ) :
    HasDerivAt (squareMoment m n F x) (squareMoment m (n+1) G x y) y := by
  have hc (m n : ℕ) {A : ℝ → ℝ → ℝ}
      (hA : Continuous fun p : ℝ × ℝ => A p.1 p.2) :
      Continuous fun p : ℝ × ℝ =>
        ∫ v in (0 : ℝ)..1, p.2^m*v^n*A (p.2*x) (v*p.1) :=
    (innerMoment_continuous m n hA).comp
      (show Continuous (fun p : ℝ × ℝ => ((x,p.1),p.2)) from by fun_prop)
  unfold squareMoment
  refine hasDerivAt_parametric_intervalIntegral
    (f := fun z u => ∫ v in (0 : ℝ)..1, u^m*v^n*F (u*x) (v*z))
    (f' := fun z u => ∫ v in (0 : ℝ)..1, u^m*v^(n+1)*G (u*x) (v*z))
    (hc m n hF) (hc m (n+1) hG) ?_ 0 1 y
  intro z u
  have hc' {A : ℝ → ℝ → ℝ}
      (hA : Continuous fun p : ℝ × ℝ => A p.1 p.2) (j : ℕ) :
      Continuous fun p : ℝ × ℝ => u^m*p.2^j*A (u*x) (p.2*p.1) :=
    (continuous_const.mul (continuous_snd.pow j)).mul
      (hA.comp (show Continuous (fun p : ℝ × ℝ => (u*x,p.2*p.1)) from by fun_prop))
  refine hasDerivAt_parametric_intervalIntegral
    (f := fun w v => u^m*v^n*F (u*x) (v*w))
    (f' := fun w v => u^m*v^(n+1)*G (u*x) (v*w))
    (hc' hF n) (hc' hG (n+1)) ?_ 0 1 z
  intro w v
  convert! ((hd (u*x) (v*w)).comp w ((hasDerivAt_id w).const_mul v)).const_mul
    (u^m*v^n) using 1
  simp only [pow_succ]
  ring

theorem squareMoment_hasDerivAt_left (m n : ℕ) {F G : ℝ → ℝ → ℝ}
    (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (hG : Continuous fun p : ℝ × ℝ => G p.1 p.2)
    (hd : ∀ x y, HasDerivAt (fun x => F x y) (G x y) x) (x y : ℝ) :
    HasDerivAt (fun x => squareMoment m n F x y) (squareMoment (m+1) n G x y) x := by
  have hc (m n : ℕ) {A : ℝ → ℝ → ℝ}
      (hA : Continuous fun p : ℝ × ℝ => A p.1 p.2) :
      Continuous fun p : ℝ × ℝ =>
        ∫ v in (0 : ℝ)..1, p.2^m*v^n*A (p.2*p.1) (v*y) :=
    (innerMoment_continuous m n hA).comp
      (show Continuous (fun p : ℝ × ℝ => ((p.1,y),p.2)) from by fun_prop)
  unfold squareMoment
  refine hasDerivAt_parametric_intervalIntegral
    (f := fun z u => ∫ v in (0 : ℝ)..1, u^m*v^n*F (u*z) (v*y))
    (f' := fun z u => ∫ v in (0 : ℝ)..1, u^(m+1)*v^n*G (u*z) (v*y))
    (hc m n hF) (hc (m+1) n hG) ?_ 0 1 x
  intro z u
  have hc' {A : ℝ → ℝ → ℝ}
      (hA : Continuous fun p : ℝ × ℝ => A p.1 p.2) (i : ℕ) :
      Continuous fun p : ℝ × ℝ => u^i*p.2^n*A (u*p.1) (p.2*y) :=
    (continuous_const.mul (continuous_snd.pow n)).mul
      (hA.comp (show Continuous (fun p : ℝ × ℝ => (u*p.1,p.2*y)) from by fun_prop))
  refine hasDerivAt_parametric_intervalIntegral
    (f := fun w v => u^m*v^n*F (u*w) (v*y))
    (f' := fun w v => u^(m+1)*v^n*G (u*w) (v*y))
    (hc' hF m) (hc' hG (m+1)) ?_ 0 1 z
  intro w v
  convert! ((hd (u*w) (v*y)).comp w ((hasDerivAt_id w).const_mul u)).const_mul
    (u^m*v^n) using 1
  simp only [pow_succ]
  ring

theorem squareMoment_origin (m n : ℕ) (F : ℝ → ℝ → ℝ) :
    squareMoment m n F 0 0 = F 0 0/((m+1 : ℕ)*(n+1 : ℕ)) := by
  simp only [squareMoment, mul_zero, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_const_mul, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, Nat.cast_add,
    Nat.cast_one]
  have hm : (m : ℝ)+1 ≠ 0 := by positivity
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp [hm, hn]

local notation "H" => thetaTailFirstMomentKernel
local notation "J" => thetaTailFirstMomentKernel 0 0

theorem centerMass_pos : 0 < J := by
  rw [ThetaTailTwoPoint.kernel_diag_eq_cut]
  exact ThetaSourceWard.thetaPrimeGammaCutEnergy_pos 0

def centerSchur (x y : ℝ) : ℝ := H x y-H 0 x*H 0 y/J
def centerSchurLeft (x y : ℝ) : ℝ := firstLeft x y-firstLeft x 0*H 0 y/J
def centerSchurMixed (x y : ℝ) : ℝ := mixed x y-firstLeft x 0*firstLeft y 0/J
def centerSchurMixedRight (x y : ℝ) : ℝ :=
  mixedRight x y-firstLeft x 0*secondLeft y 0/J
def centerSchurMixedBoth (x y : ℝ) : ℝ :=
  mixedBoth x y-secondLeft x 0*secondLeft y 0/J
def centerSchurMixedRightTwice (x y : ℝ) : ℝ :=
  mixedRightTwice x y-firstLeft x 0*thirdLeft y 0/J

theorem centerSchurLeft_continuous :
    Continuous fun p : ℝ × ℝ => centerSchurLeft p.1 p.2 :=
  firstLeft_continuous.sub (((firstLeft_continuous.comp
    (show Continuous (fun p : ℝ × ℝ => (p.1,0)) from by fun_prop)).mul
      (source_kernel_continuous.comp
        (show Continuous (fun p : ℝ × ℝ => (0,p.2)) from by fun_prop))).div_const J)

theorem centerSchurMixed_continuous :
    Continuous fun p : ℝ × ℝ => centerSchurMixed p.1 p.2 :=
  mixed_continuous.sub (((firstLeft_continuous.comp
    (show Continuous (fun p : ℝ × ℝ => (p.1,0)) from by fun_prop)).mul
      (firstLeft_continuous.comp
        (show Continuous (fun p : ℝ × ℝ => (p.2,0)) from by fun_prop))).div_const J)

theorem centerSchurMixedRight_continuous :
    Continuous fun p : ℝ × ℝ => centerSchurMixedRight p.1 p.2 :=
  mixedRight_continuous.sub (((firstLeft_continuous.comp
    (show Continuous (fun p : ℝ × ℝ => (p.1,0)) from by fun_prop)).mul
      (secondLeft_continuous.comp
        (show Continuous (fun p : ℝ × ℝ => (p.2,0)) from by fun_prop))).div_const J)

theorem centerSchurMixedBoth_continuous :
    Continuous fun p : ℝ × ℝ => centerSchurMixedBoth p.1 p.2 :=
  mixedBoth_continuous.sub (((secondLeft_continuous.comp
    (show Continuous (fun p : ℝ × ℝ => (p.1,0)) from by fun_prop)).mul
      (secondLeft_continuous.comp
        (show Continuous (fun p : ℝ × ℝ => (p.2,0)) from by fun_prop))).div_const J)

theorem centerSchurMixedRightTwice_continuous :
    Continuous fun p : ℝ × ℝ => centerSchurMixedRightTwice p.1 p.2 :=
  mixedRightTwice_continuous.sub (((firstLeft_continuous.comp
    (show Continuous (fun p : ℝ × ℝ => (p.1,0)) from by fun_prop)).mul
      (thirdLeft_continuous.comp
        (show Continuous (fun p : ℝ × ℝ => (p.2,0)) from by fun_prop))).div_const J)

theorem centerSchur_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => centerSchur x y) (centerSchurLeft x y) x :=
  (source_hasDerivAt_left x y).sub (((source_hasDerivAt_right 0 x).mul_const (H 0 y)).div_const J)

theorem centerSchurLeft_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (centerSchurLeft x) (centerSchurMixed x y) y :=
  (firstLeft_hasDerivAt_right x y).sub
    (((source_hasDerivAt_right 0 y).const_mul (firstLeft x 0)).div_const J)

theorem centerSchurMixed_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (centerSchurMixed x) (centerSchurMixedRight x y) y :=
  (mixed_hasDerivAt_right x y).sub
    (((firstLeft_hasDerivAt_left y 0).const_mul (firstLeft x 0)).div_const J)

theorem centerSchurMixed_symm (x y : ℝ) : centerSchurMixed x y = centerSchurMixed y x := by
  unfold centerSchurMixed
  rw [mixed_symm x y, mul_comm (firstLeft x 0)]

theorem centerSchurMixed_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => centerSchurMixed x y) (centerSchurMixedRight y x) x := by
  rw [show (fun x => centerSchurMixed x y) = centerSchurMixed y from
    funext fun x => centerSchurMixed_symm x y]
  exact centerSchurMixed_hasDerivAt_right y x

theorem centerSchurMixedRight_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => centerSchurMixedRight x y) (centerSchurMixedBoth x y) x :=
  (mixedRight_hasDerivAt_left x y).sub
    (((firstLeft_hasDerivAt_left x 0).mul_const (secondLeft y 0)).div_const J)

theorem centerSchurMixedRight_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (centerSchurMixedRight x) (centerSchurMixedRightTwice x y) y :=
  (mixedRight_hasDerivAt_right x y).sub
    (((secondLeft_hasDerivAt_left y 0).const_mul (firstLeft x 0)).div_const J)

def dividedSchur := squareMoment 0 0 centerSchurMixed
def dividedSchurRight := squareMoment 0 1 centerSchurMixedRight
def dividedSchurLeft := squareMoment 1 0 (fun x y => centerSchurMixedRight y x)
def dividedSchurBoth := squareMoment 1 1 centerSchurMixedBoth
def dividedSchurRightTwice := squareMoment 0 2 centerSchurMixedRightTwice

theorem dividedSchur_continuous : Continuous fun p : ℝ × ℝ => dividedSchur p.1 p.2 :=
  squareMoment_continuous 0 0 centerSchurMixed_continuous
theorem dividedSchurRight_continuous :
    Continuous fun p : ℝ × ℝ => dividedSchurRight p.1 p.2 :=
  squareMoment_continuous 0 1 centerSchurMixedRight_continuous
theorem dividedSchurLeft_continuous :
    Continuous fun p : ℝ × ℝ => dividedSchurLeft p.1 p.2 :=
  squareMoment_continuous 1 0
    (centerSchurMixedRight_continuous.comp (continuous_snd.prodMk continuous_fst))
theorem dividedSchurBoth_continuous :
    Continuous fun p : ℝ × ℝ => dividedSchurBoth p.1 p.2 :=
  squareMoment_continuous 1 1 centerSchurMixedBoth_continuous
theorem dividedSchurRightTwice_continuous :
    Continuous fun p : ℝ × ℝ => dividedSchurRightTwice p.1 p.2 :=
  squareMoment_continuous 0 2 centerSchurMixedRightTwice_continuous

theorem dividedSchur_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (dividedSchur x) (dividedSchurRight x y) y :=
  squareMoment_hasDerivAt_right 0 0 centerSchurMixed_continuous
    centerSchurMixedRight_continuous centerSchurMixed_hasDerivAt_right x y
theorem dividedSchur_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => dividedSchur x y) (dividedSchurLeft x y) x :=
  squareMoment_hasDerivAt_left 0 0 centerSchurMixed_continuous
    (G := fun x y => centerSchurMixedRight y x)
    (centerSchurMixedRight_continuous.comp (continuous_snd.prodMk continuous_fst))
    centerSchurMixed_hasDerivAt_left x y
theorem dividedSchurRight_hasDerivAt_left (x y : ℝ) :
    HasDerivAt (fun x => dividedSchurRight x y) (dividedSchurBoth x y) x :=
  squareMoment_hasDerivAt_left 0 1 centerSchurMixedRight_continuous
    centerSchurMixedBoth_continuous centerSchurMixedRight_hasDerivAt_left x y
theorem dividedSchurRight_hasDerivAt_right (x y : ℝ) :
    HasDerivAt (dividedSchurRight x) (dividedSchurRightTwice x y) y :=
  squareMoment_hasDerivAt_right 0 1 centerSchurMixedRight_continuous
    centerSchurMixedRightTwice_continuous centerSchurMixedRight_hasDerivAt_right x y

theorem dividedSchur_origin : dividedSchur 0 0 = centerEntry := by
  rw [dividedSchur, squareMoment_origin]
  simp [centerSchurMixed, mixed_origin, firstLeft_origin]

theorem dividedSchurRight_origin : dividedSchurRight 0 0 = 0 := by
  rw [dividedSchurRight, squareMoment_origin]
  simp [centerSchurMixedRight, mixedRight_origin, firstLeft_origin]

theorem dividedSchurLeft_origin : dividedSchurLeft 0 0 = 0 := by
  rw [dividedSchurLeft, squareMoment_origin]
  simp [centerSchurMixedRight, mixedRight_origin, firstLeft_origin]

theorem dividedSchurBoth_origin : dividedSchurBoth 0 0 =
    secondMass/2-derivativeMass^2/J := by
  rw [dividedSchurBoth, squareMoment_origin]
  simp only [centerSchurMixedBoth, mixedBoth_origin, secondLeft_origin]
  norm_num
  ring

theorem dividedSchurRightTwice_origin : dividedSchurRightTwice 0 0 =
    (thetaCuspLogCurvature 0*thetaCuspFullSource 0^2-2*secondMass)/3 := by
  rw [dividedSchurRightTwice, squareMoment_origin]
  simp [centerSchurMixedRightTwice, mixedRightTwice_origin, firstLeft_origin]

private theorem scaledIntegral_eq {F G : ℝ → ℝ} (hG : Continuous G)
    (hd : ∀ t, HasDerivAt F (G t) t) (x : ℝ) :
    x*(∫ t in (0 : ℝ)..1, G (t*x)) = F x-F 0 := by
  have hc : Continuous fun t : ℝ => G (t*x)*x :=
    (hG.comp (continuous_id.mul_const x)).mul_const x
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => F (t*x)) (f' := fun t => G (t*x)*x)
    (a := 0) (b := 1) (fun t _ => by
      simpa only [Function.comp_def, id_eq, one_mul] using
        (hd (t*x)).comp t ((hasDerivAt_id t).mul_const x))
    (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_mul_const] at h
  simpa only [one_mul, zero_mul, mul_one, mul_zero, mul_comm] using h

theorem centerSchur_zero_left (y : ℝ) : centerSchur 0 y = 0 := by
  unfold centerSchur
  field_simp [centerMass_pos.ne']
  ring

theorem centerSchurLeft_zero_right (x : ℝ) : centerSchurLeft x 0 = 0 := by
  unfold centerSchurLeft
  field_simp [centerMass_pos.ne']
  ring

/-- Exact extension across both axes; no nonzero-node premise is needed. -/
theorem dividedSchur_product (x y : ℝ) : x*y*dividedSchur x y = centerSchur x y := by
  have hi (u : ℝ) : y*(∫ v in (0 : ℝ)..1, centerSchurMixed (u*x) (v*y)) =
      centerSchurLeft (u*x) y := by
    have h := scaledIntegral_eq
      (centerSchurMixed_continuous.comp (continuous_const.prodMk continuous_id))
      (centerSchurLeft_hasDerivAt_right (u*x)) y
    simpa only [Function.comp_def, id_eq, centerSchurLeft_zero_right, sub_zero] using h
  have ho := scaledIntegral_eq
    (centerSchurLeft_continuous.comp (continuous_id.prodMk continuous_const))
    (fun t => centerSchur_hasDerivAt_left t y) x
  simp only [centerSchur_zero_left, sub_zero] at ho
  simp only [dividedSchur, squareMoment, pow_zero, one_mul]
  calc
    x*y*(∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, centerSchurMixed (u*x) (v*y)) =
        x*(∫ u in (0 : ℝ)..1, y*(∫ v in (0 : ℝ)..1, centerSchurMixed (u*x) (v*y))) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = x*(∫ u in (0 : ℝ)..1, centerSchurLeft (u*x) y) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      exact hi u
    _ = centerSchur x y := ho

theorem dividedSchur_eq {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    dividedSchur x y = centerSchur x y/(x*y) := by
  apply (eq_div_iff (mul_ne_zero hx hy)).mpr
  rw [mul_comm]
  exact dividedSchur_product x y

end RHTower.ThetaJoint
