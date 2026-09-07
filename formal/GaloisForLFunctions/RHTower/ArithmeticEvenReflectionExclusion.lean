import GaloisForLFunctions.RHTower.ArithmeticHardyResponseCoercivity
import GaloisForLFunctions.RHTower.ZetaLineFirstMoment

/-!
# Even arithmetic reflection and explicit midpoint exclusion

The reflected sum of the literal full Fourier source has a quadratic displacement
bound, with its exact Bernoulli mean and rational endpoint corrections retained.
At an actual strip zero this bounds the normalized zeta value at the critical
midpoint, and therefore its Hardy amplitude.

A Hardy amplitude floor excludes an explicit horizontal segment. The unconditional
Hardy second moment supplies such floors arbitrarily high. These are actual
quantitative zero-free segments, not coverage of every height or a proof of RH.
-/

set_option autoImplicit false
noncomputable section
open Complex Real MeasureTheory Set Filter Topology
namespace RHTower.DeletionMixedRefinement

/-- The even horizontal response of the literal centered Bernoulli source. -/
def reflectionEvenKernel (δ x : ℝ) : ℝ :=
  2*(RHTower.bernoulliPeriodic x+1/12)*x^(-(5/2:ℝ))*(Real.cosh (δ*Real.log x)-1)

/-- The full complex even response, retaining its arithmetic phase. -/
def reflectionEvenDensity (δ t x : ℝ) : ℂ :=
  (reflectionEvenKernel δ x : ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*I)

/-- Exact even power pairing at the critical exponent. -/
theorem reflected_power_even_identity {x : ℝ} (hx : 0 < x) (δ : ℝ) :
    x^(-(5/2:ℝ)-δ)+x^(-(5/2:ℝ)+δ)-2*x^(-(5/2:ℝ)) =
      2*x^(-(5/2:ℝ))*(Real.cosh (δ*Real.log x)-1) := by
  rw [sub_eq_add_neg (-(5/2:ℝ)) δ, Real.rpow_add hx, Real.rpow_add hx,
    Real.rpow_def_of_pos hx (-δ), Real.rpow_def_of_pos hx δ, Real.cosh_eq]
  rw [show Real.log x * (-δ)=-(δ*Real.log x) by ring,
    show Real.log x * δ=δ*Real.log x by ring]
  ring

/-- The actual even density has a uniform quadratic logarithmic majorant. -/
theorem norm_reflectionEvenDensity_le {x δ : ℝ} (hx : 1 ≤ x) (hδ : |δ| ≤ 1/2) (t : ℝ) :
    ‖reflectionEvenDensity δ t x‖ ≤ δ^2/12*(x^(-2:ℝ)*(Real.log x)^2) := by
  have hx0 := zero_lt_one.trans_le hx
  have hp := Real.rpow_nonneg hx0.le (-(5/2:ℝ))
  have hc := (reflection_hyperbolic_substrip_bounds (ε := 0) hx (by simpa using hδ)).2
  have hpow : x^(-(5/2:ℝ))*x^(1/2:ℝ)=x^(-2:ℝ) := by
    rw [←Real.rpow_add hx0]; congr 1; norm_num
  simp only [sub_zero] at hc
  unfold reflectionEvenDensity
  rw [norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, sub_self, Real.exp_zero, mul_one]
  unfold reflectionEvenKernel
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2), abs_of_nonneg hp]
  calc
    _ ≤ 2*(1/12)*x^(-(5/2:ℝ))*(|δ|^2*(Real.log x)^2/2*x^(1/2:ℝ)) := by
      gcongr
      exact abs_centeredBernoulliKernel_le x
    _ = δ^2/12*((x^(-(5/2:ℝ))*x^(1/2:ℝ))*(Real.log x)^2) := by rw [sq_abs]; ring
    _ = _ := by rw [hpow]

/-- The complete symmetric source difference is the literal even integral. -/
theorem unitFullFourierSource_even_eq_integral {s : ℂ} (hs : s ∈ minimumStrip) :
    unitFullFourierSource s+unitFullFourierSource (1-star s)-
        2*unitFullFourierSource (criticalResponsePoint s.im) =
      ∫ x in Ioi (1:ℝ), reflectionEvenDensity (s.re-1/2) s.im x := by
  have hr : -1 < (1-star s).re := by simp; linarith [hs.2]
  have hi := integrable_unitFullFourierDensity (by linarith [hs.1] : -1 < s.re)
  have hj := integrable_unitFullFourierDensity hr
  have hc := integrable_unitFullFourierDensity (s := criticalResponsePoint s.im)
    (by norm_num [criticalResponsePoint])
  have hij : IntegrableOn (fun x : ℝ =>
      ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-star s-2)+
      ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-star (1-star s)-2)) (Ioi (1:ℝ)) := hi.add hj
  unfold unitFullFourierSource
  rw [←integral_add hi hj, ←integral_const_mul, ←integral_sub hij (hc.const_mul (2:ℂ))]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (0:ℝ) < x := zero_lt_one.trans (show 1 < x from hx)
  rw [fullFourier_cpow_eq_logMode s hx0, fullFourier_cpow_eq_logMode (1-star s) hx0,
    fullFourier_cpow_eq_logMode (criticalResponsePoint s.im) hx0]
  simp only [criticalResponsePoint, Complex.sub_re, Complex.one_re, Complex.star_def,
    Complex.conj_re, Complex.sub_im, Complex.one_im, Complex.conj_im, zero_sub, neg_neg]
  have hp := congrArg Complex.ofReal (reflected_power_even_identity hx0 (s.re-1/2))
  rw [show -(5/2:ℝ)-(s.re-1/2)=-(s.re+2) by ring,
    show -(5/2:ℝ)+(s.re-1/2)=-((1-s.re)+2) by ring] at hp
  unfold reflectionEvenDensity reflectionEvenKernel
  norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, zero_mul,
    sub_zero, add_zero, Complex.add_im, Complex.div_ofNat_im, Complex.one_im,
    Complex.mul_im, mul_one, zero_add, zero_div]
  push_cast at hp ⊢
  linear_combination (norm := (push_cast; ring)) (((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*
    Complex.exp (((s.im*Real.log x:ℝ):ℂ)*I))*hp

/-- Quadratic control of the complete even source, uniformly in height. -/
theorem norm_unitFullFourierSource_even_le {s : ℂ} (hs : s ∈ minimumStrip) :
    ‖unitFullFourierSource s+unitFullFourierSource (1-star s)-
        2*unitFullFourierSource (criticalResponsePoint s.im)‖ ≤ (s.re-1/2)^2/6 := by
  have hδ : |s.re-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hm : IntegrableOn (fun x : ℝ => x^(-2:ℝ)*(Real.log x)^2) (Ioi (1:ℝ)) := by
    simpa only [show -(1:ℝ)-1=(-2:ℝ) by ring] using
      RHTower.integrableOn_rpow_mul_log_pow_Ioi_one (by norm_num : (0:ℝ)<1) 2
  have h := norm_integral_le_of_norm_le (hm.const_mul ((s.re-1/2)^2/12))
    (show ∀ᵐ x ∂volume.restrict (Ioi (1:ℝ)),
      ‖reflectionEvenDensity (s.re-1/2) s.im x‖ ≤ (s.re-1/2)^2/12*(x^(-2:ℝ)*(Real.log x)^2) by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact norm_reflectionEvenDensity_le hx.le hδ s.im)
  have hmval : (∫ x in Ioi (1:ℝ), x^(-2:ℝ)*(Real.log x)^2)=2 := by
    convert RHTower.integral_rpow_mul_log_pow_Ioi_one (by norm_num : (0:ℝ)<1) 2 using 1 <;>
      norm_num [Nat.factorial]
  rw [←unitFullFourierSource_even_eq_integral hs, integral_const_mul, hmval] at h
  convert h using 1
  ring

/-- The exact rational boundary of the full unconjugated arithmetic source. -/
def reflectionEvenBoundary (s : ℂ) : ℂ := unitPhaseBoundary s+1/(12*(s+1))

/-- The complete rational quadratic correction, with all endpoint factors explicit. -/
def reflectionEvenCorrection (s : ℂ) : ℂ :=
  let c := criticalResponsePoint s.im
  let r := 1-star s;
  -(c*s*r)⁻¹ - ((1-c)*(1-s)*(1-r))⁻¹ + ((c+1)*(s+1)*(r+1))⁻¹ / 6

/-- Partial fractions retain the polar boundary and Bernoulli mean separately. -/
theorem reflectionEvenBoundary_eq {s : ℂ} (hs : s ∈ minimumStrip) :
    reflectionEvenBoundary s = -(s⁻¹+(1-s)⁻¹)/2+(s+1)⁻¹/12 := by
  have hd := unitPhaseStrip_denominators hs
  have h1 : 1-s ≠ 0 := sub_ne_zero.mpr hd.2.1.symm
  unfold reflectionEvenBoundary unitPhaseBoundary
  field_simp [hd.1,h1,hd.2.2]
  ring

/-- Exact centered inverse pairing with its quadratic numerator. -/
theorem inverse_pair_even_identity {u v c : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (hc : c ≠ 0) (hsum : u+v=2*c) :
    u⁻¹+v⁻¹-2*c⁻¹=2*(u-c)^2*(c*u*v)⁻¹ := by
  have hvv : v=2*c-u := by linear_combination hsum
  field_simp
  rw [hvv]
  ring

/-- The complete rational boundary has the exact even quadratic correction. -/
theorem reflectionEvenBoundary_pair {s : ℂ} (hs : s ∈ minimumStrip) :
    reflectionEvenBoundary s+reflectionEvenBoundary (1-star s)-
        2*reflectionEvenBoundary (criticalResponsePoint s.im) =
      (((s.re-1/2)^2:ℝ):ℂ)*reflectionEvenCorrection s := by
  let c := criticalResponsePoint s.im
  let r := 1-star s
  have hr : r ∈ minimumStrip := by
    simp only [r,minimumStrip,mem_setOf_eq,Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]
    constructor <;> linarith [hs.1,hs.2]
  have hc : c ∈ minimumStrip := by norm_num [c,criticalResponsePoint,minimumStrip]
  have ds := unitPhaseStrip_denominators hs
  have dr := unitPhaseStrip_denominators hr
  have dc := unitPhaseStrip_denominators hc
  have hsum : s+r=2*c := by
    apply Complex.ext <;> simp [r,c,criticalResponsePoint]
    ring
  have hdiff : s-c=((s.re-1/2:ℝ):ℂ) := by
    apply Complex.ext <;> simp [c,criticalResponsePoint]
  have h1 := inverse_pair_even_identity ds.1 dr.1 dc.1 hsum
  have h2 := inverse_pair_even_identity (sub_ne_zero.mpr ds.2.1.symm)
    (sub_ne_zero.mpr dr.2.1.symm) (sub_ne_zero.mpr dc.2.1.symm)
    (show (1-s)+(1-r)=2*(1-c) by linear_combination -hsum)
  have h3 := inverse_pair_even_identity ds.2.2 dr.2.2 dc.2.2
    (show (s+1)+(r+1)=2*(c+1) by linear_combination hsum)
  rw [show (1-s)-(1-c)=-(s-c) by ring, neg_sq] at h2
  rw [show (s+1)-(c+1)=s-c by ring] at h3
  rw [hdiff] at h1 h2 h3
  rw [reflectionEvenBoundary_eq hs,reflectionEvenBoundary_eq hr,reflectionEvenBoundary_eq hc]
  change _ = (((s.re-1/2)^2:ℝ):ℂ)*(-(c*s*r)⁻¹-((1-c)*(1-s)*(1-r))⁻¹+
    ((c+1)*(s+1)*(r+1))⁻¹/6)
  push_cast
  linear_combination (norm := (push_cast; ring)) -h1/2-h2/2+h3/12

/-- At an actual strip zero, the even arithmetic source constrains the normalized midpoint value. -/
theorem normalized_value_even_constraint_at_zero {s : ℂ} (hs : s ∈ minimumStrip)
    (hz : riemannZeta s=0) :
    ‖2*normalizedMinimumZeta (criticalResponsePoint s.im)+
      (((s.re-1/2)^2:ℝ):ℂ)*reflectionEvenCorrection s‖ ≤ (s.re-1/2)^2/6 := by
  have hr : 1-star s ∈ minimumStrip := by
    simp only [minimumStrip,mem_setOf_eq,Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]
    constructor <;> linarith [hs.1,hs.2]
  have hc : criticalResponsePoint s.im ∈ minimumStrip := by norm_num [criticalResponsePoint,minimumStrip]
  have hzr := incoming_reflected_zeta_zero hs.1 hs.2 hz
  have h := norm_unitFullFourierSource_even_le hs
  rw [unitFullFourierSource_eq_star_holomorphic hs,
    unitFullFourierSource_eq_star_holomorphic hr,
    unitFullFourierSource_eq_star_holomorphic hc] at h
  have hF : ∀ z, fullUnitHolomorphicSource z=reflectionEvenBoundary z-normalizedMinimumZeta z := by
    intro z; unfold fullUnitHolomorphicSource unitPhaseSource reflectionEvenBoundary; ring
  simp only [hF] at h
  have hsZ : normalizedMinimumZeta s=0 := by simp [normalizedMinimumZeta,hz]
  have hrZ : normalizedMinimumZeta (1-star s)=0 := by simp only [normalizedMinimumZeta,hzr,zero_div]
  rw [hsZ,hrZ,sub_zero,sub_zero] at h
  have he : star (reflectionEvenBoundary s)+star (reflectionEvenBoundary (1-star s))-
      2*star (reflectionEvenBoundary (criticalResponsePoint s.im)-normalizedMinimumZeta (criticalResponsePoint s.im)) =
      star (2*normalizedMinimumZeta (criticalResponsePoint s.im)+
        (((s.re-1/2)^2:ℝ):ℂ)*reflectionEvenCorrection s) := by
    rw [←reflectionEvenBoundary_pair hs]
    simp only [star_add,star_sub,star_mul,star_ofNat]
    ring
  rwa [he,norm_star] at h

/-- Three endpoint norm floors control the exact inverse product. -/
theorem norm_inverse_triple_le {u : ℝ} (hu : 0 < u) {a b c : ℂ}
    (ha : u ≤ ‖a‖) (hb : u ≤ ‖b‖) (hc : u ≤ ‖c‖) :
    ‖(a*b*c)⁻¹‖ ≤ 1/u^3 := by
  have hprod : u^3 ≤ ‖a*b*c‖ := by
    rw [norm_mul,norm_mul]
    calc
      u^3 = (u*u)*u := by ring
      _ ≤ (‖a‖*‖b‖)*‖c‖ :=
        mul_le_mul (mul_le_mul ha hb hu.le (norm_nonneg _)) hc
          hu.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  rw [norm_inv,←one_div]
  exact one_div_le_one_div_of_le (pow_pos hu 3) hprod

/-- Every rational even correction retains cubic inverse-height decay. -/
theorem norm_reflectionEvenCorrection_le {s : ℂ} (ht : s.im ≠ 0) :
    ‖reflectionEvenCorrection s‖ ≤ 13/(6*|s.im|^3) := by
  let c := criticalResponsePoint s.im
  let r := 1-star s
  have hu : 0 < |s.im| := abs_pos.mpr ht
  have hc : |s.im| ≤ ‖c‖ := by simpa [c,criticalResponsePoint] using Complex.abs_im_le_norm c
  have hs : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hr : |s.im| ≤ ‖r‖ := by simpa [r] using Complex.abs_im_le_norm r
  have h1c : |s.im| ≤ ‖1-c‖ := by simpa [c,criticalResponsePoint] using Complex.abs_im_le_norm (1-c)
  have h1s : |s.im| ≤ ‖1-s‖ := by simpa using Complex.abs_im_le_norm (1-s)
  have h1r : |s.im| ≤ ‖1-r‖ := by simpa [r] using Complex.abs_im_le_norm (1-r)
  have hc1 : |s.im| ≤ ‖c+1‖ := by simpa [c,criticalResponsePoint] using Complex.abs_im_le_norm (c+1)
  have hs1 : |s.im| ≤ ‖s+1‖ := by simpa using Complex.abs_im_le_norm (s+1)
  have hr1 : |s.im| ≤ ‖r+1‖ := by simpa [r] using Complex.abs_im_le_norm (r+1)
  have ha := norm_inverse_triple_le hu hc hs hr
  have hb := norm_inverse_triple_le hu h1c h1s h1r
  have hd := norm_inverse_triple_le hu hc1 hs1 hr1
  change ‖-(c*s*r)⁻¹ - ((1-c)*(1-s)*(1-r))⁻¹ + ((c+1)*(s+1)*(r+1))⁻¹/6‖ ≤ _
  have hn : ‖-(c*s*r)⁻¹ - ((1-c)*(1-s)*(1-r))⁻¹ + ((c+1)*(s+1)*(r+1))⁻¹/6‖ ≤
      ‖(c*s*r)⁻¹‖ + ‖((1-c)*(1-s)*(1-r))⁻¹‖ + ‖((c+1)*(s+1)*(r+1))⁻¹‖/6 := by
    have ha := norm_add_le (-(c*s*r)⁻¹ - ((1-c)*(1-s)*(1-r))⁻¹)
      (((c+1)*(s+1)*(r+1))⁻¹/6)
    have hb := norm_sub_le (-(c*s*r)⁻¹) (((1-c)*(1-s)*(1-r))⁻¹)
    norm_num only [norm_neg,norm_div,Complex.norm_ofNat] at ha hb
    linarith
  calc
    _ ≤ ‖(c*s*r)⁻¹‖ + ‖((1-c)*(1-s)*(1-r))⁻¹‖ + ‖((c+1)*(s+1)*(r+1))⁻¹‖/6 := hn
    _ ≤ 1/|s.im|^3+1/|s.im|^3+(1/|s.im|^3)/6 := by linarith
    _ = _ := by ring

/-- Every strip zero forces a quadratic midpoint value bound, with the complete even mean retained. -/
theorem norm_normalized_value_at_zero_le {s : ℂ} (hs : s ∈ minimumStrip)
    (ht : 1 ≤ |s.im|) (hz : riemannZeta s=0) :
    ‖normalizedMinimumZeta (criticalResponsePoint s.im)‖ ≤ 7*(s.re-1/2)^2/6 := by
  have hu : 0 < |s.im| := by linarith
  have he := norm_reflectionEvenCorrection_le (abs_pos.mp hu)
  have hu3 : 1 ≤ |s.im|^3 := one_le_pow₀ ht
  have hE : ‖reflectionEvenCorrection s‖ ≤ 13/6 := by
    apply he.trans
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by nlinarith)
  have h := normalized_value_even_constraint_at_zero hs hz
  have hn := norm_sub_le
    (2*normalizedMinimumZeta (criticalResponsePoint s.im)+(((s.re-1/2)^2:ℝ):ℂ)*reflectionEvenCorrection s)
    ((((s.re-1/2)^2:ℝ):ℂ)*reflectionEvenCorrection s)
  rw [add_sub_cancel_right,norm_mul,Complex.norm_ofNat] at hn
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)] at hn
  nlinarith [mul_le_mul_of_nonneg_left hE (sq_nonneg (s.re-1/2))]

/-- The exact normalization denominator grows at most quadratically in height. -/
theorem hardyResponseDenominator_norm_le {t : ℝ} (ht : 1 ≤ |t|) :
    ‖hardyResponseDenominator t‖ ≤ 6*t^2 := by
  have hc : ‖criticalResponsePoint t‖ ≤ 2*|t| := by
    have h := norm_add_le (1/2:ℂ) ((t:ℂ)*I)
    norm_num [norm_mul] at h
    change ‖1/2+(t:ℂ)*I‖ ≤ _
    simpa only [Real.norm_eq_abs] using h.trans (by simpa only [Real.norm_eq_abs] using (show (1/2:ℝ)+|t| ≤ 2*|t| by linarith))
  have hc1 : ‖criticalResponsePoint t+1‖ ≤ 3*|t| := by
    have h := norm_add_le (criticalResponsePoint t) (1:ℂ)
    rw [norm_one] at h
    linarith
  unfold hardyResponseDenominator
  rw [norm_mul]
  calc
    _ ≤ (2*|t|)*(3*|t|) := mul_le_mul hc hc1 (norm_nonneg _) (by positivity)
    _ = _ := by rw [←sq_abs t]; ring

/-- The even arithmetic balance gives a direct Hardy-amplitude ceiling at every strip zero. -/
theorem hardy_amplitude_at_zero_le {s : ℂ} (hs : s ∈ minimumStrip)
    (ht : 1 ≤ |s.im|) (hz : riemannZeta s=0) :
    |hardyZ s.im| ≤ 7*s.im^2*(s.re-1/2)^2 := by
  have h := norm_normalized_value_at_zero_le hs ht hz
  have hp := hardyResponseDenominator_norm_le ht
  have hc : riemannZeta (criticalResponsePoint s.im) =
      hardyResponseDenominator s.im*normalizedMinimumZeta (criticalResponsePoint s.im) := by
    unfold normalizedMinimumZeta
    change _ = hardyResponseDenominator s.im*(_/hardyResponseDenominator s.im)
    field_simp [hardyResponseDenominator_ne_zero]
  rw [←norm_riemannZeta_line_eq_abs_hardyZ,←criticalResponsePoint_eq_linePt,hc,norm_mul]
  calc
    _ ≤ (6*s.im^2)*(7*(s.re-1/2)^2/6) :=
      mul_le_mul hp h (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- A concrete Hardy floor excludes an explicit horizontal segment at the same height. -/
theorem zeta_ne_zero_of_hardy_floor {s : ℂ} (hs : s ∈ minimumStrip)
    (ht : 1 ≤ |s.im|) (hH : 1/4 ≤ |hardyZ s.im|)
    (hδ : |s.re-1/2| ≤ 1/(8*|s.im|)) : riemannZeta s ≠ 0 := by
  intro hz
  have h := hardy_amplitude_at_zero_le hs ht hz
  have hu : 0 < |s.im| := by linarith
  have hd : |s.im| *|s.re-1/2| ≤ 1/8 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 8*|s.im|)).mp hδ
    linarith
  have hsq : s.im^2*(s.re-1/2)^2 ≤ 1/64 := by
    have hh := mul_self_le_mul_self (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hd
    rw [←pow_two,←pow_two,mul_pow,sq_abs,sq_abs] at hh
    nlinarith
  nlinarith

/-- The unconditional Hardy second moment supplies actual amplitude floors arbitrarily high. -/
theorem exists_high_hardy_amplitude_floor (T : ℝ) :
    ∃ t : ℝ, T < t ∧ 1 ≤ t ∧ 1/4 ≤ |hardyZ t| := by
  obtain ⟨T₀,hT₀,hfloor⟩ := exists_le_integral_hardyZ_sq
  let U := max T₀ (max (T+1) 1)
  have hU0 : 0 < U := lt_of_lt_of_le hT₀ (le_max_left _ _)
  have hUT : T+1 ≤ U := (le_max_left _ _).trans (le_max_right _ _)
  have hU1 : 1 ≤ U := (le_max_right _ _).trans (le_max_right _ _)
  have hUfloor := hfloor U (le_max_left _ _)
  by_contra! h
  have hsmall : ∀ t ∈ Icc U (2*U), (hardyZ t)^2 ≤ 1/16 := by
    intro t ht
    have hh := le_of_lt (h t (by linarith [ht.1]) (by linarith [ht.1]))
    have hsq := mul_self_le_mul_self (abs_nonneg (hardyZ t)) hh
    rw [←pow_two,←pow_two,sq_abs] at hsq
    nlinarith
  have hi := intervalIntegral.integral_mono_on (show U ≤ 2*U by linarith)
    ((continuous_hardyZ.pow 2).intervalIntegrable U (2*U)) (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (1/16:ℝ)) volume U (2*U)) hsmall
  rw [intervalIntegral.integral_const] at hi
  norm_num at hi
  nlinarith

/-- Actual explicit horizontal zero-free segments occur above every prescribed height. -/
theorem exists_high_even_reflection_exclusion (T : ℝ) :
    ∃ t : ℝ, T < t ∧ 1 ≤ t ∧ ∀ s : ℂ, s ∈ minimumStrip → s.im=t →
      |s.re-1/2| ≤ 1/(8*t) → riemannZeta s ≠ 0 := by
  obtain ⟨t,hT,ht,hH⟩ := exists_high_hardy_amplitude_floor T
  refine ⟨t,hT,ht,fun s hs hst hd => ?_⟩
  apply zeta_ne_zero_of_hardy_floor hs
  · simpa only [hst,abs_of_nonneg (by linarith : 0 ≤ t)] using ht
  · simpa only [hst] using hH
  · simpa only [hst,abs_of_nonneg (by linarith : 0 ≤ t)] using hd

end RHTower.DeletionMixedRefinement


