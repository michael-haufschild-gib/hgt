import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalRadialModeMatching
import GaloisForLFunctions.HTGeometry.DispersivePDE.Profiles

/-! The attempted fixed-clock Darboux transport of the actual physical reader.
The reflected reader requires a half shift. The derivative-cancelling first-order
transform retains an explicit forcing, detected by the original Wronskian.
This is a radial identity, not a complete nonlinear action or extinction theorem. -/

set_option autoImplicit false
noncomputable section
namespace RHTower.D4BMPhysicalReaderDarboux
open Complex Set Filter
open scoped Topology
open GaloisForLFunctions.HTGeometry.DispersivePDE
open D4BMJointSource D4BMJointWave D4BMLaplaceRadial

private def eigenvalue (q : XiZeroCopy) : ℂ := physicalAngularParameter q ^ 2 - 1/4
private def slope (q : XiZeroCopy) : ℂ := -(physicalAngularParameter q/2+1/8)
private def Q (t : ℝ) : ℂ := solitonQ t
private def T (t : ℝ) : ℂ := solitonT t
private def f (q : XiZeroCopy) (w : ℂ) (outer : Bool) : ℝ → ℂ :=
  tortoiseMode outer w (physicalRadialFrequency q)
private def f1 (q : XiZeroCopy) (w : ℂ) (outer : Bool) : ℝ → ℂ :=
  tortoiseModeFirst outer w (physicalRadialFrequency q)

/-- The first-order transform whose variable coefficient cancels the first-derivative
defect between the original and reflected physical radial operators. -/
def transformedMode (q : XiZeroCopy) (w : ℂ) (outer : Bool) (t : ℝ) : ℂ :=
  f1 q w outer t + slope q*T t*f q w outer t

private def transformedFirst (q : XiZeroCopy) (w : ℂ) (outer : Bool) (t : ℝ) : ℂ :=
  (w^2+(slope q-eigenvalue q)*Q t)*f q w outer t +
    slope q*T t*f1 q w outer t

/-- The original reflected-reader differential expression, at the unchanged clock. -/
def reflectedResidual (q : XiZeroCopy) (w : ℂ) (outer : Bool) (t : ℝ) : ℂ :=
  deriv (deriv (transformedMode q w outer)) t -
    (w^2-eigenvalue (xiZeroCopyReflectEquiv q)*angularWeight t^2)*
      transformedMode q w outer t

/-- Coefficient of the source retained by the attempted physical reader transport. -/
def defectCoefficient (q : XiZeroCopy) : ℂ :=
  (3/32)* (2*(q.1:ℂ)-3)*(2*(q.1:ℂ)+1)

private theorem Q_eq (t : ℝ) : Q t = angularWeight t^2 := by
  rw [Q,solitonQ_eq_inv_cosh_sq]
  simp [angularWeight,one_div,inv_pow]

private theorem Q_deriv (t : ℝ) : HasDerivAt Q (-2*T t*Q t) t := by
  convert! (hasDerivAt_solitonQ t).ofReal_comp using 1
  simp [solitonQ1,Q,T]

private theorem T_deriv (t : ℝ) : HasDerivAt T (Q t) t :=
  (hasDerivAt_solitonT t).ofReal_comp

private theorem modes_deriv (q : XiZeroCopy) (w : ℂ) (hw : 1/2<w.re)
    (outer : Bool) (t : ℝ) (ht : t<0) :
    HasDerivAt (f q w outer) (f1 q w outer t) t ∧
    HasDerivAt (f1 q w outer) ((w^2-eigenvalue q*Q t)*f q w outer t) t := by
  simpa only [f,f1,eigenvalue,Q_eq] using physicalTortoiseMode_hasDerivAt q w hw outer t ht

private theorem transformed_deriv (q : XiZeroCopy) (w : ℂ) (hw : 1/2<w.re)
    (outer : Bool) (t : ℝ) (ht : t<0) :
    HasDerivAt (transformedMode q w outer) (transformedFirst q w outer t) t := by
  obtain ⟨h0,h1⟩ := modes_deriv q w hw outer t ht
  apply (h1.add (((T_deriv t).const_mul (slope q)).mul h0)).congr_deriv
  dsimp only [transformedFirst]
  ring

private theorem transformed_first_deriv (q : XiZeroCopy) (w : ℂ) (hw : 1/2<w.re)
    (outer : Bool) (t : ℝ) (ht : t<0) :
    HasDerivAt (transformedFirst q w outer)
      (((slope q-eigenvalue q)*(-2*T t*Q t)+
          slope q*T t*(w^2-eigenvalue q*Q t))*f q w outer t +
        (w^2+(2*slope q-eigenvalue q)*Q t)*f1 q w outer t) t := by
  obtain ⟨h0,h1⟩ := modes_deriv q w hw outer t ht
  have hA := ((Q_deriv t).const_mul (slope q-eigenvalue q)).const_add (w^2)
  apply ((hA.mul h0).add (((T_deriv t).const_mul (slope q)).mul h1)).congr_deriv
  ring

private theorem residual_eq (q : XiZeroCopy) (w : ℂ) (hw : 1/2<w.re)
    (outer : Bool) (t : ℝ) (ht : t<0) :
    reflectedResidual q w outer t = defectCoefficient q*Q t*T t*f q w outer t := by
  have he : deriv (transformedMode q w outer) =ᶠ[𝓝 t] transformedFirst q w outer := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
    exact (transformed_deriv q w hw outer x hx).deriv
  have hd := ((transformed_first_deriv q w hw outer t ht).congr_of_eventuallyEq he).deriv
  rw [reflectedResidual,hd,transformedMode,← Q_eq]
  have hR : physicalAngularParameter (xiZeroCopyReflectEquiv q) =
      -(physicalAngularParameter q+1/2) := by
    rw [physicalAngularParameter_eq,physicalAngularParameter_eq]
    change (1-(q.1:ℂ)-1)/2 = -(((q.1:ℂ)-1)/2+1/2)
    ring
  simp only [eigenvalue,hR]
  simp only [slope,defectCoefficient,physicalAngularParameter_eq]
  ring

/-- Exact forcing of each original mode under the reflected-reader transform.
The band and radial subtype are the original mode's domain; no extinction,
covariance, source identification or zero-flux premise is imposed. -/
theorem reflectedResidual_eq (q : XiZeroCopy) (w : {w : ℂ // 1/2<w.re})
    (outer : Bool) (t : Iio (0:ℝ)) :
    reflectedResidual q w outer t = defectCoefficient q*
      angularWeight t^2*(Real.tanh t:ℂ)*
        tortoiseMode outer w (physicalRadialFrequency q) t := by
  simpa only [Q_eq,T,solitonT,f] using residual_eq q w w.property outer t t.property

/-- The mismatch coefficient never vanishes at an actual Xi occurrence. -/
theorem defectCoefficient_ne_zero (q : XiZeroCopy) : defectCoefficient q ≠ 0 := by
  obtain ⟨h0,h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  have ha : 2*(q.1:ℂ)-3 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have hb : 2*(q.1:ℂ)+1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hb

/-- The original Wronskian detects the retained source of the two transformed modes. -/
theorem reflectedResidual_wronskian (q : XiZeroCopy) (w : {w : ℂ // 1/2<w.re})
    (t : Iio (0:ℝ)) :
    reflectedResidual q w false t*tortoiseModeFirst true w (physicalRadialFrequency q) t -
      reflectedResidual q w true t*tortoiseModeFirst false w (physicalRadialFrequency q) t =
    -defectCoefficient q*angularWeight t^2*(Real.tanh t:ℂ)*
      connection w (physicalRadialFrequency q) := by
  rw [reflectedResidual_eq,reflectedResidual_eq]
  have hW := tortoiseMode_wronskian (physicalRadialFrequency_chamber q w w.property) t t.property
  linear_combination defectCoefficient q*angularWeight t^2*(Real.tanh t:ℂ)*hW

/-- At every original radial point the reflected-reader defect is present in at
least one original mode. This obstructs this first-order repair, not the full HB route. -/
theorem reflectedResidual_pair_ne_zero (q : XiZeroCopy) (w : {w : ℂ // 1/2<w.re})
    (t : Iio (0:ℝ)) :
    (reflectedResidual q w false t,reflectedResidual q w true t) ≠ (0,0) := by
  have hQ : angularWeight t^2 ≠ 0 := by
    apply pow_ne_zero
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (ne_of_gt (Real.cosh_pos t)))
  have hT : (Real.tanh t:ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_ne_zero (Real.sinh_ne_zero.mpr (ne_of_lt t.property)) (ne_of_gt (Real.cosh_pos t))
  have hc := connection_ne_zero (physicalRadialFrequency_chamber q w w.property)
  have hn := mul_ne_zero (mul_ne_zero
    (mul_ne_zero (neg_ne_zero.mpr (defectCoefficient_ne_zero q)) hQ) hT) hc
  intro he
  have hW := reflectedResidual_wronskian q w t
  have h0 := congrArg Prod.fst he
  have h1 := congrArg Prod.snd he
  change reflectedResidual q w false t = 0 at h0
  change reflectedResidual q w true t = 0 at h1
  rw [h0,h1,zero_mul,zero_mul,sub_zero] at hW
  exact hn hW.symm

/-- The original overlap band where the complete physical radial response has
its proved classical equation. -/
abbrev ResponseBand := {w : ℂ // 3/2<w.re ∧ w.im ≠ 0 ∧ |w.re|<2}

private theorem band_pos (w : ResponseBand) : 0 < (w:ℂ).re := by
  linarith [w.property.1]

private theorem band_half (w : ResponseBand) : 1/2 < (w:ℂ).re := by
  linarith [w.property.1]

/-- The actual complete projected response, with source and reader independent. -/
def physicalResponse (q r : XiZeroCopy) (branch : Bool) (w : ResponseBand) (a : ℂ) : ℝ → ℂ :=
  physicalCuspProfile q (xiZeroCopyReflectEquiv r) branch w a (band_pos w)
    w.property.1 w.property.2.1 w.property.2.2

/-- Physical Green current tested against the attempted reflected reader. -/
def transportCurrent (q r : XiZeroCopy) (branch : Bool) (w : ResponseBand)
    (a : ℂ) (outer : Bool) (t : ℝ) : ℂ :=
  transformedFirst r w outer t*physicalResponse q r branch w a t -
    transformedMode r w outer t*deriv (physicalResponse q r branch w a) t

/-- Both source work and reader-defect work are retained. -/
def transportWork (q r : XiZeroCopy) (branch : Bool) (w : ResponseBand)
    (a : ℂ) (outer : Bool) (t : ℝ) : ℂ :=
  transformedMode r w outer t*
      continuedAngularSourceProjection q branch
        (physicalAngularParameter (xiZeroCopyReflectEquiv r)) a w t +
    defectCoefficient r*Q t*T t*f r w outer t*physicalResponse q r branch w a t

private theorem current_deriv (q r : XiZeroCopy) (branch : Bool) (w : ResponseBand)
    (a : ℂ) (outer : Bool) (t : ℝ) (ht : t<0) :
    HasDerivAt (transportCurrent q r branch w a outer)
      (transportWork q r branch w a outer t) t := by
  have hD := transformed_deriv r w (band_half w) outer t ht
  have hD1 := transformed_first_deriv r w (band_half w) outer t ht
  have hP := physicalCuspProfile_hasDerivAt q (xiZeroCopyReflectEquiv r) branch w a
    (band_pos w) w.property.1 w.property.2.1 w.property.2.2 t ht
  have he : deriv (transformedMode r w outer) =ᶠ[𝓝 t] transformedFirst r w outer := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
    exact (transformed_deriv r w (band_half w) outer x hx).deriv
  have hs := residual_eq r w (band_half w) outer t ht
  rw [reflectedResidual,he.deriv_eq,hD1.deriv] at hs
  apply ((hD1.mul hP.1).sub (hD.mul hP.2)).congr_deriv
  dsimp only [transportWork,physicalCuspSecond,physicalResponse,eigenvalue]
  simp only [eigenvalue,Q_eq] at hs
  rw [Q_eq]
  linear_combination physicalCuspProfile q (xiZeroCopyReflectEquiv r) branch w a
    (band_pos w) w.property.1 w.property.2.1 w.property.2.2 t * hs

/-- Actual complete-source Green balance under the attempted reader transport.
The additional overlap is derived from the physical equations, not assumed zero. -/
theorem transportCurrent_hasDerivAt (q r : XiZeroCopy) (branch : Bool) (w : ResponseBand)
    (a : ℂ) (outer : Bool) (t : Iio (0:ℝ)) :
    HasDerivAt (transportCurrent q r branch w a outer)
      (transportWork q r branch w a outer t) t :=
  current_deriv q r branch w a outer t t.property

/-- The finite physical source/reader balance retains both actual endpoint currents. -/
theorem transportWork_integral (q r : XiZeroCopy) (branch : Bool) (w : ResponseBand)
    (a : ℂ) (outer : Bool) (s t : Iio (0:ℝ)) :
    (∫ x in (s:ℝ)..(t:ℝ), transportWork q r branch w a outer x) =
      transportCurrent q r branch w a outer t-transportCurrent q r branch w a outer s := by
  have hi : uIcc (s:ℝ) (t:ℝ) ⊆ Iio (0:ℝ) := by
    intro x hx
    rcases mem_uIcc.mp hx with h | h
    · exact h.2.trans_lt t.property
    · exact h.2.trans_lt s.property
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => current_deriv q r branch w a outer x (hi hx))
  apply ContinuousOn.intervalIntegrable
  have hF := continuedAngularSourceProjection_continuousOn q branch
    (physicalAngularParameter (xiZeroCopyReflectEquiv r)) a w w.property.2.1
    (abs_lt.mp w.property.2.2).1
  intro x hx
  have hD := (transformed_deriv r w (band_half w) outer x (hi hx)).continuousAt
  have hf := (modes_deriv r w (band_half w) outer x (hi hx)).1.continuousAt
  have hP := (physicalCuspProfile_hasDerivAt q (xiZeroCopyReflectEquiv r) branch w a
    (band_pos w) w.property.1 w.property.2.1 w.property.2.2 x (hi hx)).1.continuousAt
  exact (hD.continuousWithinAt.mul ((hF x (hi hx)).mono hi)).add
    (((((Q_deriv x).continuousAt.const_mul (defectCoefficient r)).mul
      (T_deriv x).continuousAt).mul hf).mul hP).continuousWithinAt

end RHTower.D4BMPhysicalReaderDarboux
