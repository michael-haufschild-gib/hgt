import GaloisForLFunctions.RHTower.ThetaFinitePairCanonicalSpeed
import GaloisForLFunctions.RHTower.ThetaTailFinitePairTransport
import GaloisForLFunctions.HTGeometry.ClockParametricDerivative
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The literal finite-pair canonical current and its smooth diagonal coefficient
extensions. Compact source averages identify the node derivatives at the center. -/

noncomputable section
open Set MeasureTheory
namespace RHTower.ThetaFiniteTransport
open GaloisForLFunctions.HTGeometry

local notation "p" => thetaCuspLogDecaySlope
local notation "c" => thetaCuspLogCurvature
local notation "v" => thetaCuspLogCurvatureJet
local notation "c₂" => thetaCuspLogCurvatureJetTwo
local notation "s" => ThetaSturmCrossing.secant

private theorem p_zero : p 0=0 := by
  simp only [thetaCuspLogDecaySlope,
    iteratedDeriv_thetaCuspLogSource_zero_of_odd (m := 1) ⟨0,rfl⟩,neg_zero]

private theorem cont_p : Continuous p := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogDecaySlope t).continuousAt
private theorem cont_c : Continuous c := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvature t).continuousAt
private theorem cont_v : Continuous v := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvatureJet t).continuousAt
private theorem cont_c₂ : Continuous c₂ := continuous_iff_continuousAt.mpr
  fun t => (hasDerivAt_thetaCuspLogCurvatureJetTwo t).continuousAt

private def sourceAverage (n : ℕ) (f : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, u^n*f (t+u*x)

private theorem sourceAverage_hasDerivAt (n : ℕ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hd : ∀ u, HasDerivAt f (g u) u)
    (t x : ℝ) : HasDerivAt (sourceAverage n f t) (sourceAverage (n+1) g t x) x := by
  have hc (n : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
      Continuous fun z : ℝ × ℝ => z.2^n*f (t+z.2*z.1) := by
    exact (continuous_snd.pow n).mul
      (hf.comp (continuous_const.add (continuous_snd.mul continuous_fst)))
  unfold sourceAverage
  refine hasDerivAt_parametric_intervalIntegral
    (f := fun z u => u^n*f (t+u*z)) (f' := fun z u => u^(n+1)*g (t+u*z))
    (hc n hf) (hc (n+1) hg) ?_ 0 1 x
  intro z u
  convert! ((hd (t+u*z)).comp z
    (((hasDerivAt_id z).const_mul u).const_add t)).const_mul (u^n) using 1
  simp only [pow_succ]
  ring

private theorem sourceAverage_zero (n : ℕ) (f : ℝ → ℝ) (t : ℝ) :
    sourceAverage n f t 0=f t/(n+1) := by
  simp only [sourceAverage,mul_zero,add_zero,intervalIntegral.integral_mul_const,integral_pow,
    one_pow,zero_pow (Nat.succ_ne_zero _),sub_zero]
  ring

private theorem average_secant {f g : ℝ → ℝ} (hg : Continuous g)
    (hd : ∀ u, HasDerivAt f (g u) u) (t x : ℝ) :
    x*sourceAverage 0 g t x=f (t+x)-f t := by
  have hi : IntervalIntegrable (fun u => x*g (t+u*x)) volume 0 1 := by
    exact (continuous_const.mul (hg.comp
      (continuous_const.add (continuous_id.mul continuous_const)))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (f := fun u => f (t+u*x))
    (f' := fun u => x*g (t+u*x)) (fun u _ => by
      convert! (hd (t+u*x)).comp u (((hasDerivAt_id u).mul_const x).const_add t) using 1
      ring) hi
  simpa only [sourceAverage,pow_zero,one_mul,intervalIntegral.integral_const_mul,
    zero_mul,mul_one,add_zero] using h

def smoothSecant (x t : ℝ) : ℝ := sourceAverage 0 c t x
def smoothSecantTimeJet (x t : ℝ) : ℝ := sourceAverage 0 v t x
def smoothSecantNodeJet (x t : ℝ) : ℝ := sourceAverage 1 v t x

theorem smoothSecant_eq {x : ℝ} (hx : x ≠ 0) (t : ℝ) : smoothSecant x t=s x t := by
  have h := average_secant cont_c hasDerivAt_thetaCuspLogDecaySlope t x
  change x*smoothSecant x t=p (t+x)-p t at h
  unfold ThetaSturmCrossing.secant
  apply (eq_div_iff hx).mpr
  linarith only [h]

theorem smoothSecantTimeJet_eq {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    smoothSecantTimeJet x t=ThetaSturmCrossing.secantJet x t := by
  have h := average_secant cont_v hasDerivAt_thetaCuspLogCurvature t x
  change x*smoothSecantTimeJet x t=c (t+x)-c t at h
  unfold ThetaSturmCrossing.secantJet
  apply (eq_div_iff hx).mpr
  linarith only [h]

private theorem smoothSecant_hasDerivAt_node (x t : ℝ) :
    HasDerivAt (fun y => smoothSecant y t) (smoothSecantNodeJet x t) x :=
  sourceAverage_hasDerivAt 0 cont_c cont_v hasDerivAt_thetaCuspLogCurvature t x

theorem smoothSecantNodeJet_eq {x : ℝ} (hx : x ≠ 0) (t : ℝ) :
    smoothSecantNodeJet x t=(x*c (t+x)-(p (t+x)-p t))/x^2 := by
  have he : (fun y => y*smoothSecant y t)=(fun y => p (t+y)-p t) :=
    funext fun y => average_secant cont_c hasDerivAt_thetaCuspLogDecaySlope t y
  have h1 := (hasDerivAt_id x).mul (smoothSecant_hasDerivAt_node x t)
  have h2 := ((hasDerivAt_thetaCuspLogDecaySlope (t+x)).comp x
    ((hasDerivAt_id x).const_add t)).sub_const (p t)
  have h := h1.deriv
  change deriv (fun y => y*smoothSecant y t) x=1*smoothSecant x t+x*smoothSecantNodeJet x t at h
  simp only [Function.comp_apply,mul_one] at h2
  rw [he,h2.deriv,smoothSecant_eq hx] at h
  dsimp only [ThetaSturmCrossing.secant,id_eq] at h
  field_simp [hx] at h ⊢
  nlinarith only [h]

/-- The retained primitive coefficient of the literal canonical current. -/
def primitiveCurrentCoefficient (x y t : ℝ) : ℝ :=
  (y*c (t+y)-(p (t+y)-p t))/y^2-
    finiteCanonicalSpeed x y t*ThetaSturmCrossing.secantJet y t-
    (finiteCanonicalSpeed x y t*(p t+p (t+x))+finiteCanonicalSpeedJet x y t)*s y t

/-- The complete signed finite-pair coordinate current, retaining both packets. -/
def finiteCanonicalCurrent (x y t : ℝ) : ℝ :=
  matchedCurrentCoefficient x y t*normalizedPacket x t+
    primitiveCurrentCoefficient x y t*transportPrimitive x t+
    finiteCanonicalSpeed x y t*(s x t-s y t)

def diagonalSpeed (x t : ℝ) : ℝ := 1/2-p x/(2*p (t+x))
def diagonalSpeedTimeJet (x t : ℝ) : ℝ := p x*c (t+x)/(2*p (t+x)^2)
def diagonalPacketCoefficient (x t : ℝ) : ℝ :=
  -diagonalSpeed x t*(x+2*t)*smoothSecant x t-diagonalSpeedTimeJet x t
def diagonalPrimitiveCoefficient (x t : ℝ) : ℝ :=
  smoothSecantNodeJet x t-diagonalSpeed x t*smoothSecantTimeJet x t-
    (diagonalSpeed x t*(p t+p (t+x))+diagonalSpeedTimeJet x t)*smoothSecant x t

private theorem diagonalSpeed_eq {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    diagonalSpeed x t=finiteCanonicalSpeed x x t := by
  unfold diagonalSpeed finiteCanonicalSpeed
  field_simp [(ThetaSturmCrossing.slope_pos (add_pos_of_nonneg_of_pos ht hx)).ne']
  ring

private theorem diagonalSpeedTimeJet_eq {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    diagonalSpeedTimeJet x t=finiteCanonicalSpeedJet x x t := by
  unfold diagonalSpeedTimeJet finiteCanonicalSpeedJet
  field_simp [(ThetaSturmCrossing.slope_pos (add_pos_of_nonneg_of_pos ht hx)).ne']
  ring

theorem finiteCanonicalCurrent_diagonal {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    finiteCanonicalCurrent x x t=
      diagonalPacketCoefficient x t*normalizedPacket x t+
      diagonalPrimitiveCoefficient x t*transportPrimitive x t := by
  unfold finiteCanonicalCurrent matchedCurrentCoefficient primitiveCurrentCoefficient
    diagonalPacketCoefficient diagonalPrimitiveCoefficient
  rw [smoothSecant_eq hx.ne',smoothSecantTimeJet_eq hx.ne',smoothSecantNodeJet_eq hx.ne',
    diagonalSpeed_eq hx ht,diagonalSpeedTimeJet_eq hx ht]
  ring

theorem diagonalPacketCoefficient_zero (t : ℝ) : diagonalPacketCoefficient 0 t=-t*c t := by
  simp only [diagonalPacketCoefficient,diagonalSpeed,diagonalSpeedTimeJet,p_zero,
    zero_div,sub_zero,zero_mul,add_zero,smoothSecant,sourceAverage_zero,Nat.cast_zero,zero_add,div_one]
  ring

theorem diagonalPrimitiveCoefficient_zero (t : ℝ) : diagonalPrimitiveCoefficient 0 t=-p t*c t := by
  simp only [diagonalPrimitiveCoefficient,diagonalSpeed,diagonalSpeedTimeJet,p_zero,
    zero_div,sub_zero,zero_mul,add_zero,smoothSecant,smoothSecantTimeJet,smoothSecantNodeJet,
    sourceAverage_zero,Nat.cast_zero,Nat.cast_one,zero_add,div_one]
  ring

private theorem shifted_p_deriv_zero (t : ℝ) :
    HasDerivAt (fun x => p (t+x)) (c t) 0 := by
  convert! (hasDerivAt_thetaCuspLogDecaySlope (t+0)).comp 0
    ((hasDerivAt_id (0:ℝ)).const_add t) using 1
  simp only [add_zero,mul_one]

private theorem shifted_c_deriv_zero (t : ℝ) :
    HasDerivAt (fun x => c (t+x)) (v t) 0 := by
  convert! (hasDerivAt_thetaCuspLogCurvature (t+0)).comp 0
    ((hasDerivAt_id (0:ℝ)).const_add t) using 1
  simp only [add_zero,mul_one]

private theorem diagonalSpeed_hasDerivAt_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => diagonalSpeed x t) (-c 0/(2*p t)) 0 := by
  have hd := shifted_p_deriv_zero t
  have h := (((hasDerivAt_thetaCuspLogDecaySlope 0).div (hd.const_mul 2)
    (show 2*p (t+0) ≠ 0 by simpa only [add_zero] using
      (mul_pos (by norm_num : (0:ℝ)<2) (ThetaSturmCrossing.slope_pos ht)).ne')).neg).const_add (1/2)
  convert! h using 1
  simp only [p_zero,add_zero]
  field_simp [(ThetaSturmCrossing.slope_pos ht).ne']
  ring

private theorem diagonalSpeedTimeJet_hasDerivAt_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => diagonalSpeedTimeJet x t) (c 0*c t/(2*p t^2)) 0 := by
  have hp := shifted_p_deriv_zero t
  have hc := shifted_c_deriv_zero t
  convert! ((hasDerivAt_thetaCuspLogDecaySlope 0).mul hc).div ((hp.pow 2).const_mul 2)
    (show 2*p (t+0)^2 ≠ 0 by simpa only [add_zero] using
      (mul_pos (by norm_num : (0:ℝ)<2) (sq_pos_of_pos (ThetaSturmCrossing.slope_pos ht))).ne') using 1
  simp only [Pi.pow_apply,Pi.mul_apply,p_zero,add_zero,zero_mul,sub_zero]
  field_simp [(ThetaSturmCrossing.slope_pos ht).ne']

theorem diagonalPacketCoefficient_hasDerivAt_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => diagonalPacketCoefficient x t)
      (-c t/2-t*v t/2+t*c 0*c t/p t-c 0*c t/(2*p t^2)) 0 := by
  have h := ((((diagonalSpeed_hasDerivAt_zero ht).neg).mul
    ((hasDerivAt_id (0:ℝ)).add_const (2*t))).mul
    (smoothSecant_hasDerivAt_node 0 t)).sub (diagonalSpeedTimeJet_hasDerivAt_zero ht)
  convert! h using 1
  simp only [Pi.neg_apply,Pi.mul_apply,diagonalSpeed,p_zero,zero_div,sub_zero,zero_add,add_zero,
    smoothSecant,smoothSecantNodeJet,sourceAverage_zero,Nat.cast_zero,Nat.cast_one,div_one,id_eq]
  ring

theorem diagonalPrimitiveCoefficient_hasDerivAt_zero {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => diagonalPrimitiveCoefficient x t)
      (c₂ t/12+c 0*v t/(2*p t)-p t*v t/2-c t^2/2+c 0*c t-c 0*c t^2/(2*p t^2)) 0 := by
  have hn : HasDerivAt (fun x => smoothSecantNodeJet x t) (sourceAverage 2 c₂ t 0) 0 :=
    sourceAverage_hasDerivAt 1 cont_v cont_c₂ hasDerivAt_thetaCuspLogCurvatureJet t 0
  have hd : HasDerivAt (fun x => smoothSecantTimeJet x t) (sourceAverage 1 c₂ t 0) 0 :=
    sourceAverage_hasDerivAt 0 cont_v cont_c₂ hasDerivAt_thetaCuspLogCurvatureJet t 0
  have hp := shifted_p_deriv_zero t
  have h := (hn.sub ((diagonalSpeed_hasDerivAt_zero ht).mul hd)).sub
    ((((diagonalSpeed_hasDerivAt_zero ht).mul (hp.const_add (p t))).add
      (diagonalSpeedTimeJet_hasDerivAt_zero ht)).mul (smoothSecant_hasDerivAt_node 0 t))
  convert! h using 1
  simp only [diagonalSpeed,diagonalSpeedTimeJet,p_zero,zero_div,sub_zero,zero_mul,add_zero,
    smoothSecant,smoothSecantNodeJet,smoothSecantTimeJet,sourceAverage_zero,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,zero_add,div_one,Pi.add_apply,Pi.mul_apply]
  field_simp [(ThetaSturmCrossing.slope_pos ht).ne']
  ring

end RHTower.ThetaFiniteTransport
