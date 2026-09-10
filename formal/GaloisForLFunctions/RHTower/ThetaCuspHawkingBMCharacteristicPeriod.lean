import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import GaloisForLFunctions.HTGeometry.ClockParametricDerivative
import Mathlib.Tactic

/-!
# The common positive-delay radial period and its retained zero-delay contact

The source-normalized pole integral equals a moving-endpoint integral and a
fixed-interval regular realization. Its clock equation has homogeneous rate -2.
Successive radial poles reduce to the preceding pole and explicit endpoints.
The regular realization retains the logarithmic contact and its first derivative
at zero delay. These identities do not assert cancellation of the physical current.
-/

namespace RHTower.D4BMCharacteristicPeriod
open MeasureTheory Set Filter Topology
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def power (nu : ℂ) (r : ℝ) : ℂ := Complex.exp (nu*(Real.log r : ℂ))
def density (nu : ℂ) (r : ℝ) : ℂ := power nu r / ((r:ℂ)-1)
def upper (h : ℝ) : ℝ := Real.exp h
def lower (h : ℝ) : ℝ := (Real.exp h+1)/2
def rawPeriod (nu : ℂ) (h : ℝ) : ℂ := ∫ r in lower h..upper h, density nu r
def clockPeriod (delta : ℂ) (h : ℝ) : ℂ :=
  (Real.exp (-2*h):ℂ)*rawPeriod (delta-2) h

def endpointForcing (delta : ℂ) (h : ℝ) : ℂ :=
  (Real.exp (-2*h):ℂ)*(upper h:ℂ)/((upper h:ℂ)-1)*
    (power (delta-2) (upper h)-power (delta-2) (lower h))

private theorem density_continuousAt (nu : ℂ) {r : ℝ} (hr : 1 < r) :
    ContinuousAt (density nu) r := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_trans zero_lt_one hr)
  have hd : (r:ℂ)-1 ≠ 0 := by exact_mod_cast ne_of_gt (sub_pos.mpr hr)
  exact (Complex.continuous_exp.continuousAt.comp
    (continuousAt_const.mul ((Real.continuousAt_log hr0).ofReal))).div
    (Complex.continuous_ofReal.continuousAt.sub continuousAt_const) hd

private theorem lower_gt_one {h : ℝ} (hh : 0 < h) : 1 < lower h := by
  have he := Real.one_lt_exp_iff.mpr hh
  unfold lower
  linarith

private theorem rawPeriod_hasDerivAt (nu : ℂ) {h : ℝ} (hh : 0 < h) :
    HasDerivAt (rawPeriod nu)
      ((upper h:ℂ)*density nu (upper h)-((upper h:ℂ)/2)*density nu (lower h)) h := by
  have ha := lower_gt_one hh
  have hb : 1 < upper h := Real.one_lt_exp_iff.mpr hh
  have hab : lower h ≤ upper h := by unfold lower upper; linarith [Real.one_lt_exp_iff.mpr hh]
  have hc : ContinuousOn (density nu) (Ioi (1:ℝ)) :=
    fun r hr => (density_continuousAt nu hr).continuousWithinAt
  have hi : IntervalIntegrable (density nu) volume (lower h) (upper h) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hc.mono (fun r hr => lt_of_lt_of_le ha hr.1)
  have hm (r : ℝ) (hr : 1 < r) : StronglyMeasurableAtFilter (density nu) (𝓝 r) :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
      (fun x hx => density_continuousAt nu hx) r hr
  have hf := intervalIntegral.integral_hasFDerivAt hi
    (hm _ ha) (hm _ hb) (density_continuousAt nu ha) (density_continuousAt nu hb)
  have hu : HasDerivAt upper (upper h) h := Real.hasDerivAt_exp h
  have hl : HasDerivAt lower (upper h/2) h := by
    convert! ((Real.hasDerivAt_exp h).add_const 1).div_const 2 using 1
  have H := hf.comp_hasDerivAt h (hl.prodMk hu)
  convert! H using 1
  simp [Complex.real_smul]

theorem clockPeriod_hasDerivAt (delta : ℂ) {h : ℝ} (hh : 0 < h) :
    HasDerivAt (clockPeriod delta)
      (-2*clockPeriod delta h+endpointForcing delta h) h := by
  have hr := rawPeriod_hasDerivAt (delta-2) hh
  have he : HasDerivAt (fun x : ℝ => (Real.exp (-2*x):ℂ))
      (-2*(Real.exp (-2*h):ℂ)) h := by
    simpa only [id_eq, mul_one, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Complex.ofReal_one, one_mul, mul_comm] using
      (((hasDerivAt_id h).const_mul (-2)).exp).ofReal_comp
  apply (he.mul hr).congr_deriv
  dsimp [clockPeriod,endpointForcing,density]
  have hden : (upper h:ℂ)-1 ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hh))
  have hlo : (lower h:ℂ)-1 = ((upper h:ℂ)-1)/2 := by
    simp only [lower,upper,Complex.ofReal_div,Complex.ofReal_add,Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  rw [hlo]
  field_simp [hden]

def poleMoment (nu : ℂ) (c : ℝ) (j : ℕ) : ℂ :=
  ∫ r in (1+c)/2..1, power nu r / ((r:ℂ)-(c:ℂ))^j

def sourcePeriod (delta : ℂ) (h : ℝ) : ℂ :=
  power (4-delta) (Real.exp (-h)) * poleMoment (delta-2) (Real.exp (-h)) 1

private theorem power_mul (nu : ℂ) {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    power nu (c*r) = power nu c * power nu r := by
  simp only [power,Real.log_mul hc.ne' hr.ne',Complex.ofReal_add,mul_add,
    Complex.exp_add]

private theorem poleMoment_one_rescale (nu : ℂ) {c : ℝ} (hc : 0 < c) :
    poleMoment nu c 1 = power nu c *
      ∫ z in (1+c)/(2*c)..1/c, density nu z := by
  have hcC : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have ha : 0 < (1+c)/(2*c) := div_pos (by linarith) (by positivity)
  have hb : 0 < 1/c := one_div_pos.mpr hc
  have hsub := intervalIntegral.smul_integral_comp_mul_left
    (a := (1+c)/(2*c)) (b := 1/c)
    (fun r : ℝ => power nu r / ((r:ℂ)-(c:ℂ))) c
  have haeq : c*((1+c)/(2*c)) = (1+c)/2 := by field_simp
  have hbeq : c*(1/c)=1 := by field_simp
  rw [haeq,hbeq] at hsub
  simp only [poleMoment,pow_one]
  rw [← hsub,Complex.real_smul,
    ← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro z hz
  have hz0 : 0 < z := lt_of_lt_of_le (lt_min ha hb) hz.1
  dsimp only
  rw [power_mul nu hc hz0]
  simp only [Complex.ofReal_mul,density]
  by_cases hz1 : (z:ℂ)=1
  · simp [hz1]
  · have hd : (c:ℂ)*(z:ℂ)-(c:ℂ) ≠ 0 := by
      rw [← mul_sub_one]
      exact mul_ne_zero hcC (sub_ne_zero.mpr hz1)
    field_simp [hcC,hd,sub_ne_zero.mpr hz1]

/-- The source-normalized pole period is exactly the finite moving-endpoint integral. -/
theorem sourcePeriod_eq_clockPeriod (delta : ℂ) (h : ℝ) :
    sourcePeriod delta h = clockPeriod delta h := by
  have hc := Real.exp_pos (-h)
  have hinv : 1/Real.exp (-h) = Real.exp h := by rw [Real.exp_neg]; simp
  have hlo : (1+Real.exp (-h))/(2*Real.exp (-h)) = lower h := by
    unfold lower
    have he := Real.exp_ne_zero (-h)
    calc
      (1+Real.exp (-h))/(2*Real.exp (-h)) = (1/Real.exp (-h)+1)/2 := by field_simp
      _ = _ := by rw [hinv]
  rw [sourcePeriod,poleMoment_one_rescale (delta-2) hc,hlo,hinv]
  have hp : power (4-delta) (Real.exp (-h))*power (delta-2) (Real.exp (-h)) =
      (Real.exp (-2*h):ℂ) := by
    simp only [power,Real.log_exp,← Complex.exp_add]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [← mul_assoc,hp]
  rfl

/-- Universal clock rate -2, with its complete endpoint forcing retained. -/
theorem sourcePeriod_hasDerivAt (delta : ℂ) {h : ℝ} (hh : 0 < h) :
    HasDerivAt (sourcePeriod delta)
      (-2*sourcePeriod delta h+endpointForcing delta h) h := by
  have he : sourcePeriod delta = clockPeriod delta := funext (sourcePeriod_eq_clockPeriod delta)
  rw [he]
  exact clockPeriod_hasDerivAt delta hh


private theorem power_add_one (nu : ℂ) {r : ℝ} (hr : 0 < r) :
    power (nu+1) r = power nu r*(r:ℂ) := by
  simp only [power,add_mul,one_mul,Complex.exp_add,← Complex.ofReal_exp,Real.exp_log hr]

private theorem power_hasDerivAt (nu : ℂ) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (power nu) (nu*power nu r/(r:ℂ)) r := by
  have hd := (((Real.hasDerivAt_log hr.ne').ofReal_comp).const_mul nu).cexp
  apply hd.congr_deriv
  simp only [power,Complex.ofReal_inv]
  ring

private theorem polePrimitive_hasDerivAt (nu : ℂ) {c r : ℝ}
    (hc : 0 < c) (hr : c < r) (j : ℕ) :
    HasDerivAt (fun x : ℝ => power (nu+1) x/((x:ℂ)-(c:ℂ))^(j+1))
      ((nu-(j:ℂ))*(power nu r/((r:ℂ)-(c:ℂ))^(j+1))-
        ((j:ℂ)+1)*(c:ℂ)*(power nu r/((r:ℂ)-(c:ℂ))^(j+2))) r := by
  have hr0 : 0 < r := hc.trans hr
  have hd : (r:ℂ)-(c:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (sub_pos.mpr hr)
  have hrC : (r:ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hl : HasDerivAt (fun x : ℝ => (x:ℂ)-(c:ℂ)) 1 r := by
    simpa using ((hasDerivAt_id r).ofReal_comp).sub_const (c:ℂ)
  have H := (power_hasDerivAt (nu+1) hr0).div (hl.pow (j+1)) (pow_ne_zero _ hd)
  apply H.congr_deriv
  dsimp only [Pi.pow_apply]
  rw [power_add_one nu hr0]
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_one,pow_succ]
  field_simp [hrC,hd]
  ring

/-- Each higher pole moment reduces to the preceding moment and its two actual endpoints. -/
theorem poleMoment_recurrence (nu : ℂ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (j : ℕ) :
    ((j:ℂ)+1)*(c:ℂ)*poleMoment nu c (j+2) =
      (nu-(j:ℂ))*poleMoment nu c (j+1)-
        (power (nu+1) 1/(1-(c:ℂ))^(j+1)-
          power (nu+1) ((1+c)/2)/((((1+c)/2:ℝ):ℂ)-(c:ℂ))^(j+1)) := by
  have hlo : c < (1+c)/2 := by linarith
  have hab : (1+c)/2 ≤ 1 := by linarith
  have hin (r : ℝ) (hr : r ∈ uIcc ((1+c)/2) 1) : c < r := by
    rw [uIcc_of_le hab] at hr
    exact lt_of_lt_of_le hlo hr.1
  have hcont (n : ℕ) : ContinuousOn
      (fun r : ℝ => power nu r/((r:ℂ)-(c:ℂ))^n) (uIcc ((1+c)/2) 1) := by
    intro r hr
    have hr0 : 0 < r := hc0.trans (hin r hr)
    have hd : (r:ℂ)-(c:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (sub_pos.mpr (hin r hr))
    exact ((power_hasDerivAt nu hr0).continuousAt.div
      ((Complex.continuous_ofReal.continuousAt.sub continuousAt_const).pow n)
      (pow_ne_zero _ hd)).continuousWithinAt
  have h1 := (hcont (j+1)).intervalIntegrable (μ := volume)
  have h2 := (hcont (j+2)).intervalIntegrable (μ := volume)
  have hi := (h1.const_mul (nu-(j:ℂ))).sub
    (h2.const_mul (((j:ℂ)+1)*(c:ℂ)))
  have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => polePrimitive_hasDerivAt nu hc0 (hin r hr) j) hi
  rw [intervalIntegral.integral_sub (h1.const_mul _) (h2.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at H
  simp only [Complex.ofReal_one] at H
  dsimp only [poleMoment]
  linear_combination -H


/-- Fixed-interval realization retaining the zero-delay limit. -/
def regularPeriod (delta : ℂ) (h : ℝ) : ℂ :=
  (Real.exp (-2*h):ℂ) * ∫ y in (1/2:ℝ)..1,
    power (delta-2) (1+(upper h-1)*y)/(y:ℂ)

/-- The regular realization equals the original positive-delay period. -/
theorem sourcePeriod_eq_regularPeriod (delta : ℂ) {h : ℝ} (hh : 0 < h) :
    sourcePeriod delta h = regularPeriod delta h := by
  rw [sourcePeriod_eq_clockPeriod,clockPeriod,regularPeriod]
  congr 1
  have hb : 1 < upper h := Real.one_lt_exp_iff.mpr hh
  have hc : upper h-1 ≠ 0 := ne_of_gt (sub_pos.mpr hb)
  have hcC : ((upper h-1:ℝ):ℂ) ≠ 0 := by exact_mod_cast hc
  have H := intervalIntegral.smul_integral_comp_mul_add
    (a := (1/2:ℝ)) (b := 1) (density (delta-2)) (upper h-1) 1
  have hA : (upper h-1)*(1/2)+1=lower h := by unfold upper lower; ring
  have hB : (upper h-1)*1+1=upper h := by ring
  rw [hA,hB] at H
  rw [rawPeriod,← H,Complex.real_smul,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y hy
  have hy0 : 0 < y := by
    have hI : y ∈ Icc (1/2:ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] using hy
    linarith [hI.1]
  have hyC : (y:ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  dsimp only [density]
  rw [show (upper h-1)*y+1=1+(upper h-1)*y by ring]
  push_cast
  have hcC' : (upper h:ℂ)-1 ≠ 0 := by exact_mod_cast hc
  rw [show (1:ℂ)+((upper h:ℂ)-1)*(y:ℂ)-1=((upper h:ℂ)-1)*(y:ℂ) by ring]
  field_simp [hcC',hyC]

private def clipped (y : ℝ) : ℝ := max (1/2) (min 1 y)

private theorem clipped_pos (y : ℝ) : 0 < clipped y :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

private theorem clipped_le_one (y : ℝ) : clipped y ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

private theorem base_pos (h y : ℝ) : 0 < 1+(upper h-1)*clipped y := by
  have he := Real.exp_pos h
  have hp := mul_pos he (clipped_pos y)
  have hl := clipped_le_one y
  unfold upper
  nlinarith

/-- The fixed-interval period is continuous through zero delay for every complex frequency. -/
theorem regularPeriod_continuous (delta : ℂ) : Continuous (regularPeriod delta) := by
  let f : ℝ → ℝ → ℂ := fun h y =>
    power (delta-2) (1+(upper h-1)*clipped y)/(clipped y:ℂ)
  have hf : Continuous f.uncurry := by
    have hb : Continuous (fun p : ℝ × ℝ => 1+(upper p.1-1)*clipped p.2) := by
      unfold upper clipped
      fun_prop
    have hd : Continuous (fun p : ℝ × ℝ => (clipped p.2:ℂ)) := by
      unfold clipped
      fun_prop
    exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (hb.log (fun p => (base_pos p.1 p.2).ne'))))).div
      hd (fun p => by exact_mod_cast (clipped_pos p.2).ne')
  have hi := continuous_parametric_integral_of_continuous
    (μ := volume) hf (s := Icc (1/2:ℝ) 1) isCompact_Icc
  have he : Continuous (fun h : ℝ => (Real.exp (-2*h):ℂ)) := by fun_prop
  apply (he.mul hi).congr
  intro h
  dsimp only [Pi.mul_apply]
  unfold regularPeriod
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ) ≤ 1),
    setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  dsimp only [f]
  have hclip : clipped y=y := by
    unfold clipped
    rw [min_eq_right hy.2,max_eq_right hy.1]
  rw [hclip]

/-- The contact limit contains the universal logarithmic endpoint contribution. -/
theorem regularPeriod_zero (delta : ℂ) : regularPeriod delta 0 = (Real.log 2:ℂ) := by
  simp only [regularPeriod,upper,mul_zero,Real.exp_zero,Complex.ofReal_one,
    sub_self,zero_mul,add_zero,power,Real.log_one,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,one_mul,one_div]
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal,
    integral_inv_of_pos (a := (2:ℝ)⁻¹) (b := 1) (by positivity) zero_lt_one]
  norm_num

/-- The literal source period has the retained logarithmic limit from positive delay. -/
theorem sourcePeriod_tendsto_zero (delta : ℂ) :
    Tendsto (sourcePeriod delta) (𝓝[>] (0:ℝ)) (𝓝 (Real.log 2:ℂ)) := by
  have H := (regularPeriod_continuous delta).continuousAt.tendsto.mono_left
    (inf_le_left : 𝓝[>] (0:ℝ) ≤ 𝓝 (0:ℝ))
  rw [regularPeriod_zero] at H
  apply H.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (sourcePeriod_eq_regularPeriod delta hh).symm


/-- Endpoint forcing in a representation regular at zero delay. -/
def regularForcing (delta : ℂ) (h : ℝ) : ℂ :=
  (delta-2)*(Real.exp (-h):ℂ)*∫ y in (1/2:ℝ)..1,
    power (delta-3) (1+(upper h-1)*y)

private theorem clipped_power_continuous (nu : ℂ) :
    Continuous (fun p : ℝ × ℝ => power nu (1+(upper p.1-1)*clipped p.2)) := by
  have hb : Continuous (fun p : ℝ × ℝ => 1+(upper p.1-1)*clipped p.2) := by
    unfold upper clipped
    fun_prop
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (hb.log (fun p => (base_pos p.1 p.2).ne'))))

private theorem clipped_density_derivative (nu : ℂ) (h y : ℝ) :
    HasDerivAt (fun x => power nu (1+(upper x-1)*clipped y)/(clipped y:ℂ))
      (nu*(upper h:ℂ)*power (nu-1) (1+(upper h-1)*clipped y)) h := by
  have hb : HasDerivAt (fun x : ℝ => 1+(upper x-1)*clipped y)
      (upper h*clipped y) h := by
    convert! (((Real.hasDerivAt_exp h).sub_const 1).mul_const (clipped y)).const_add 1 using 1
  have H := ((power_hasDerivAt nu (base_pos h y)).scomp h hb).div_const (clipped y:ℂ)
  apply H.congr_deriv
  have hp := power_add_one (nu-1) (base_pos h y)
  rw [sub_add_cancel] at hp
  simp only [Complex.real_smul]
  rw [hp]
  have hd : ((1+(upper h-1)*clipped y:ℝ):ℂ) ≠ 0 := by exact_mod_cast (base_pos h y).ne'
  have hy : (clipped y:ℂ) ≠ 0 := by exact_mod_cast (clipped_pos y).ne'
  simp only [Complex.ofReal_mul]
  field_simp [hd,hy]

/-- The clock equation extends through zero delay with its original endpoint contribution. -/
theorem regularPeriod_hasDerivAt (delta : ℂ) (h : ℝ) :
    HasDerivAt (regularPeriod delta)
      (-2*regularPeriod delta h+regularForcing delta h) h := by
  let f : ℝ → ℝ → ℂ := fun x y =>
    power (delta-2) (1+(upper x-1)*clipped y)/(clipped y:ℂ)
  let f' : ℝ → ℝ → ℂ := fun x y =>
    (delta-2)*(upper x:ℂ)*power ((delta-2)-1) (1+(upper x-1)*clipped y)
  have hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := by
    exact (clipped_power_continuous (delta-2)).div (by unfold clipped; fun_prop)
      (fun p => by exact_mod_cast (clipped_pos p.2).ne')
  have hf' : Continuous (fun p : ℝ × ℝ => f' p.1 p.2) := by
    exact ((show Continuous (fun p : ℝ × ℝ => (delta-2)*(upper p.1:ℂ)) by
      unfold upper; fun_prop).mul (clipped_power_continuous ((delta-2)-1)))
  have H := GaloisForLFunctions.HTGeometry.hasDerivAt_parametric_intervalIntegral hf hf'
    (fun x y => clipped_density_derivative (delta-2) x y) (1/2) 1 h
  have clip_eq (y : ℝ) (hy : y ∈ uIcc (1/2:ℝ) 1) : clipped y=y := by
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at hy
    unfold clipped
    rw [min_eq_right hy.2,max_eq_right hy.1]
  have hfun : (fun x => ∫ y in (1/2:ℝ)..1, f x y) =
      (fun x => ∫ y in (1/2:ℝ)..1, power (delta-2) (1+(upper x-1)*y)/(y:ℂ)) := by
    funext x
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only [f]
    rw [clip_eq y hy]
  have hval : (∫ y in (1/2:ℝ)..1, f' h y) =
      (delta-2)*(upper h:ℂ)*∫ y in (1/2:ℝ)..1, power (delta-3) (1+(upper h-1)*y) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp only [f']
    rw [clip_eq y hy,show delta-2-1=delta-3 by ring]
  rw [hfun,hval] at H
  have he : HasDerivAt (fun x : ℝ => (Real.exp (-2*x):ℂ))
      (-2*(Real.exp (-2*h):ℂ)) h := by
    simpa only [id_eq,mul_one,Complex.ofReal_mul,Complex.ofReal_neg,
      Complex.ofReal_ofNat,Complex.ofReal_one,one_mul,mul_comm] using
      (((hasDerivAt_id h).const_mul (-2)).exp).ofReal_comp
  apply (he.mul H).congr_deriv
  have heq : (Real.exp (-2*h):ℂ)*(upper h:ℂ)=(Real.exp (-h):ℂ) := by
    unfold upper
    rw [← Complex.ofReal_mul,← Real.exp_add]
    congr 2
    ring
  dsimp only [regularPeriod,regularForcing]
  linear_combination heq*(delta-2)*(∫ y in (1/2:ℝ)..1, power (delta-3) (1+(upper h-1)*y))

/-- The first clock derivative retains the endpoint's frequency term and logarithmic contact. -/
theorem regularPeriod_hasDerivAt_zero (delta : ℂ) :
    HasDerivAt (regularPeriod delta) ((delta-2)/2-2*(Real.log 2:ℂ)) 0 := by
  have H := regularPeriod_hasDerivAt delta 0
  apply H.congr_deriv
  rw [regularPeriod_zero]
  simp [regularForcing,upper,power]
  ring

end
end RHTower.D4BMCharacteristicPeriod
