import GaloisForLFunctions.RHTower.ArithmeticIncomingHorizontalComparison
import GaloisForLFunctions.RHTower.RiemannSiegelThresholdLaw
import GaloisForLFunctions.RHTower.PrimeLogPowZetaAbelPole

/-!
# Reflected incoming response and complete zero-pair balance

The actual incoming source has a critical logarithmic response with a uniform
cubic error in horizontal displacement. Its divided reflection difference has
quadratic error away from the wall. The full paired Fourier sum at any strip
zero retains every mode and the exact Bernoulli mean; its required signed value
is positive on the strict right half of the strip at positive height.
These estimates supply no opposing arithmetic sign and do not close RH.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- The hyperbolic factor has an elementary exponential majorant. -/
theorem incoming_cosh_le_exp_abs (a : ℝ) : Real.cosh a ≤ Real.exp |a| := by
  rw [Real.cosh_eq]
  have hp := Real.exp_le_exp.mpr (le_abs_self a)
  have hn := Real.exp_le_exp.mpr (neg_le_abs a)
  linarith

/-- Cubic contact of the actual odd horizontal weight, with a global remainder bound. -/
theorem incoming_abs_sinh_sub_self_le (a : ℝ) :
    |Real.sinh a-a| ≤ |a|^3/6*Real.exp |a| := by
  have he : |Real.sinh a-a|=Real.sinh |a|-|a| := by
    by_cases ha : 0 ≤ a
    · rw [abs_of_nonneg ha,abs_of_nonneg (sub_nonneg.mpr (Real.self_le_sinh_iff.mpr ha))]
    · have hn : 0 ≤ -a := by linarith
      rw [abs_of_neg (lt_of_not_ge ha),show Real.sinh a-a=-(Real.sinh (-a)-(-a)) by rw [Real.sinh_neg]; ring,
        abs_neg,abs_of_nonneg (sub_nonneg.mpr (Real.self_le_sinh_iff.mpr hn))]
  rw [he]
  exact (RHTower.sinh_sub_self_le (abs_nonneg a)).trans
    (mul_le_mul_of_nonneg_left (by simpa only [abs_abs] using incoming_cosh_le_exp_abs |a|) (by positivity))

/-- Exact odd horizontal power pairing around the critical exponent. -/
theorem incoming_reflected_power_identity {x : ℝ} (hx : 0 < x) (δ : ℝ) :
    x^(-(5/2:ℝ)-δ)-x^(-(5/2:ℝ)+δ) = -2*x^(-(5/2:ℝ))*Real.sinh (δ*Real.log x) := by
  rw [sub_eq_add_neg (-(5/2:ℝ)) δ,Real.rpow_add hx,Real.rpow_add hx,
    Real.rpow_def_of_pos hx (-δ),Real.rpow_def_of_pos hx δ,Real.sinh_eq]
  rw [show Real.log x * (-δ)=-(δ*Real.log x) by ring,show Real.log x * δ=δ*Real.log x by ring]
  ring

/-- The paired power amplitude differs from its critical logarithmic response by a cubic majorant. -/
theorem incoming_reflected_power_cubic {x δ : ℝ} (hx : 1 ≤ x) (hδ : |δ| ≤ 1/2) :
    |x^(-(5/2:ℝ)-δ)-x^(-(5/2:ℝ)+δ)+2*δ*x^(-(5/2:ℝ))*Real.log x| ≤
      |δ|^3/3*(x^(-2:ℝ)*(Real.log x)^3) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hp : 0 ≤ x^(-(5/2:ℝ)) := Real.rpow_nonneg hx0.le _
  have h := incoming_abs_sinh_sub_self_le (δ*Real.log x)
  rw [abs_mul,abs_of_nonneg hl,mul_pow] at h
  have hexp : Real.exp (|δ| *Real.log x) ≤ x^(1/2:ℝ) := by
    rw [Real.rpow_def_of_pos hx0]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hδ hl])
  have hs : |Real.sinh (δ*Real.log x)-δ*Real.log x| ≤
      |δ|^3*(Real.log x)^3/6*x^(1/2:ℝ) :=
    h.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  rw [incoming_reflected_power_identity hx0]
  have he : -2*x^(-(5/2:ℝ))*Real.sinh (δ*Real.log x)+2*δ*x^(-(5/2:ℝ))*Real.log x =
      -(2*x^(-(5/2:ℝ)))*(Real.sinh (δ*Real.log x)-δ*Real.log x) := by ring
  rw [he,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0 ≤ 2*x^(-(5/2:ℝ)))]
  apply (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq
  have hpow : x^(-(5/2:ℝ))*x^(1/2:ℝ)=x^(-2:ℝ) := by
    rw [←Real.rpow_add hx0]; congr 1; norm_num
  calc
    _ = |δ|^3/3*((x^(-(5/2:ℝ))*x^(1/2:ℝ))*(Real.log x)^3) := by ring
    _ = _ := by rw [hpow]

/-- The actual critical logarithmic Fourier density. -/
def criticalIncomingLogMode (t : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  (bernoulliModeWeight k:ℂ)*((x^(-(5/2:ℝ))*Real.log x:ℝ):ℂ)*
    Complex.exp (((2*Real.pi*k*x+t*Real.log x:ℝ):ℂ)*Complex.I)

/-- The actual finite critical logarithmic incoming atom. -/
def criticalIncomingLogAtom (t : ℝ) (k : ℕ) : ℂ :=
  ∫ x in Ioc (1:ℝ) (t/(2*Real.pi*k)), criticalIncomingLogMode t (-(k:ℤ)) x

/-- The whole critical logarithmic incoming response, retaining all phases. -/
def criticalIncomingLogSection (t : ℝ) (K : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 K, criticalIncomingLogAtom t k

/-- Pointwise modulus of the actual response density. -/
theorem norm_criticalIncomingLogMode (t : ℝ) (k : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    ‖criticalIncomingLogMode t k x‖ = bernoulliModeWeight k*(x^(-(5/2:ℝ))*Real.log x) := by
  unfold criticalIncomingLogMode
  rw [norm_mul,norm_mul]
  simp [Complex.norm_exp,abs_of_nonneg (Real.rpow_nonneg (zero_lt_one.trans_le hx).le _),
    abs_of_nonneg (Real.log_nonneg hx),abs_of_nonneg (bernoulliModeWeight_nonneg k)]

/-- Absolute integrability of the response uses the exact first logarithmic moment. -/
theorem integrable_criticalIncomingLogMode (t : ℝ) (k : ℤ) :
    IntegrableOn (criticalIncomingLogMode t k) (Ioi (1:ℝ)) := by
  have hm : IntegrableOn (fun x : ℝ => x^(-(5/2:ℝ))*Real.log x) (Ioi (1:ℝ)) := by
    simpa only [show -(3/2:ℝ)-1=-(5/2:ℝ) by norm_num] using
      RHTower.integrableOn_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<3/2)
  apply Integrable.mono (hm.const_mul (bernoulliModeWeight k))
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    intro x hx
    have hx0 : (0:ℝ) < x := zero_lt_one.trans hx
    have hp := (Real.hasDerivAt_rpow_const (p := -(5/2:ℝ)) (Or.inl hx0.ne')).continuousAt
    have hl := (Real.hasDerivAt_log hx0.ne').continuousAt
    unfold criticalIncomingLogMode
    exact ((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp (hp.mul hl))).mul
      (Complex.continuous_exp.continuousAt.comp
        ((Complex.continuous_ofReal.continuousAt.comp
          ((continuousAt_const.mul continuousAt_id).add (continuousAt_const.mul hl))).mul continuousAt_const))).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_criticalIncomingLogMode t k hx.le,Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (bernoulliModeWeight_nonneg k)
        (mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hx).le _) (Real.log_nonneg hx.le)))]

/-- Cubic pointwise control of the literal Fourier pairing with its critical response. -/
theorem norm_bernoulli_reflection_response_le {s : ℂ} (hs : 0 ≤ s.re) (hs' : s.re ≤ 1)
    (k : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    ‖bernoulliFourierTerm k (star s) x-bernoulliFourierTerm k (star (1-star s)) x+
      ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogMode s.im k x‖ ≤
      bernoulliModeWeight k*(|s.re-1/2|^3/3)*(x^(-2:ℝ)*(Real.log x)^3) := by
  have hx0 := zero_lt_one.trans_le hx
  have ht : s.im=(1-star s).im := by simp
  rw [bernoulliFourierTerm_horizontal_difference ht k hx0]
  have hre : (1-star s).re=1-s.re := by simp
  rw [hre]
  have he : (bernoulliModeWeight k:ℂ)*((x^(-(s.re+2))-x^(-((1-s.re)+2)):ℝ):ℂ)*
      Complex.exp (((2*Real.pi*k*x+s.im*Real.log x:ℝ):ℂ)*Complex.I)+
      ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogMode s.im k x =
      (bernoulliModeWeight k:ℂ)*
        ((x^(-(5/2:ℝ)-(s.re-1/2))-x^(-(5/2:ℝ)+(s.re-1/2))+
          2*(s.re-1/2)*x^(-(5/2:ℝ))*Real.log x:ℝ):ℂ)*
        Complex.exp (((2*Real.pi*k*x+s.im*Real.log x:ℝ):ℂ)*Complex.I) := by
    unfold criticalIncomingLogMode
    rw [show -(5/2:ℝ)-(s.re-1/2)=-(s.re+2) by ring,
      show -(5/2:ℝ)+(s.re-1/2)=-((1-s.re)+2) by ring]
    push_cast; ring
  rw [he,norm_mul,norm_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,sub_zero,Real.exp_zero,mul_one,abs_of_nonneg (bernoulliModeWeight_nonneg k)]
  have hd : |s.re-1/2| ≤ 1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h := mul_le_mul_of_nonneg_left (incoming_reflected_power_cubic hx hd) (bernoulliModeWeight_nonneg k)
  simpa only [mul_assoc] using h


/-- Every finite positive-ray logarithmic moment is bounded by its exact full mass. -/
theorem incoming_logMoment_Ioc_le {β : ℝ} (hβ : 1 < β) (m : ℕ) (b : ℝ) :
    (∫ x in Ioc (1:ℝ) b, x^(-β)*(Real.log x)^m) ≤ (Nat.factorial m:ℝ)/(β-1)^(m+1) := by
  have hm : IntegrableOn (fun x : ℝ => x^(-β)*(Real.log x)^m) (Ioi (1:ℝ)) := by
    simpa only [show -(β-1)-1=-β by ring] using
      RHTower.integrableOn_rpow_mul_log_pow_Ioi_one (by linarith : 0 < β-1) m
  have hmass := RHTower.integral_rpow_mul_log_pow_Ioi_one (by linarith : 0 < β-1) m
  rw [show -(β-1)-1=-β by ring] at hmass
  calc
    _ ≤ ∫ x in Ioi (1:ℝ), x^(-β)*(Real.log x)^m := by
      apply setIntegral_mono_set hm ?_ (Eventually.of_forall (fun x hx => hx.1))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hx).le _) (pow_nonneg (Real.log_nonneg hx.le) _)
    _ = _ := hmass

/-- Quantitative bound for one actual critical logarithmic response atom. -/
theorem norm_criticalIncomingLogAtom_le (t : ℝ) (k : ℕ) :
    ‖criticalIncomingLogAtom t k‖ ≤ bernoulliModeWeight (-(k:ℤ))*(4/9) := by
  have hm : IntegrableOn (fun x : ℝ => x^(-(5/2:ℝ))*Real.log x) (Ioi (1:ℝ)) := by
    simpa only [show -(3/2:ℝ)-1=-(5/2:ℝ) by norm_num] using
      RHTower.integrableOn_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<3/2)
  unfold criticalIncomingLogAtom
  have h := norm_integral_le_of_norm_le ((hm.mono_set Ioc_subset_Ioi_self).const_mul (bernoulliModeWeight (-(k:ℤ))))
    (show ∀ᵐ x ∂volume.restrict (Ioc (1:ℝ) (t/(2*Real.pi*k))),
      ‖criticalIncomingLogMode t (-(k:ℤ)) x‖ ≤ bernoulliModeWeight (-(k:ℤ))*(x^(-(5/2:ℝ))*Real.log x) by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact (norm_criticalIncomingLogMode t _ hx.1.le).le)
  rw [integral_const_mul] at h
  have hb : (∫ x in Ioc (1:ℝ) (t/(2*Real.pi*k)), x^(-(5/2:ℝ))*Real.log x) ≤ 4/9 := by
    convert incoming_logMoment_Ioc_le (by norm_num : (1:ℝ)<5/2) 1 (t/(2*Real.pi*k)) using 1 <;> norm_num
  exact h.trans (mul_le_mul_of_nonneg_left hb (bernoulliModeWeight_nonneg _))

/-- The complete critical logarithmic response has uniform bounded mass. -/
theorem norm_criticalIncomingLogSection_le (t : ℝ) (K : ℕ) : ‖criticalIncomingLogSection t K‖ ≤ 1/54 := by
  unfold criticalIncomingLogSection
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ‖criticalIncomingLogAtom t k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, bernoulliModeWeight (-(k:ℤ))*(4/9) :=
      Finset.sum_le_sum (fun k _ => norm_criticalIncomingLogAtom_le t k)
    _ = (∑ k ∈ Finset.Icc 1 K, bernoulliModeWeight (-(k:ℤ)))*(4/9) := (Finset.sum_mul ..).symm
    _ ≤ (1/24)*(4/9) := mul_le_mul_of_nonneg_right (sum_negativeBernoulliWeight_le K) (by norm_num)
    _ = _ := by norm_num

/-- Cubic contact of one complete actual incoming atom with its critical response. -/
theorem norm_stationaryIncomingAtom_reflection_response_le {s : ℂ} (hs : 0 ≤ s.re) (hs' : s.re ≤ 1)
    (k : ℕ) :
    ‖stationaryIncomingAtom s 1 k-stationaryIncomingAtom (1-star s) 1 k+
      ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogAtom s.im k‖ ≤
      2*bernoulliModeWeight (-(k:ℤ))*|s.re-1/2|^3 := by
  have ht : (1-star s).im=s.im := by simp
  have hi : IntegrableOn (bernoulliFourierTerm (-(k:ℤ)) (star s)) (Ioc (1:ℝ) (s.im/(2*Real.pi*k))) :=
    (integrable_bernoulliFourierTerm (by norm_num : (0:ℝ)<1)
      (show -1 < (star s).re by simpa using (show -1 < s.re by linarith)) _).mono_set Ioc_subset_Ioi_self
  have hj : IntegrableOn (bernoulliFourierTerm (-(k:ℤ)) (star (1-star s))) (Ioc (1:ℝ) (s.im/(2*Real.pi*k))) :=
    (integrable_bernoulliFourierTerm (by norm_num : (0:ℝ)<1)
      (show -1 < (star (1-star s)).re by simp only [Complex.star_def,Complex.conj_re,Complex.sub_re,Complex.one_re]; linarith) _).mono_set Ioc_subset_Ioi_self
  have hc := (integrable_criticalIncomingLogMode s.im (-(k:ℤ))).mono_set
    (show Ioc (1:ℝ) (s.im/(2*Real.pi*k)) ⊆ Ioi (1:ℝ) from Ioc_subset_Ioi_self)
  have hm : IntegrableOn (fun x : ℝ => x^(-2:ℝ)*(Real.log x)^3) (Ioi (1:ℝ)) := by
    simpa only [show -(1:ℝ)-1=(-2:ℝ) by norm_num] using
      RHTower.integrableOn_rpow_mul_log_pow_Ioi_one (by norm_num : (0:ℝ)<1) 3
  simp only [stationaryIncomingAtom,criticalIncomingLogAtom,Nat.cast_one,Complex.one_cpow,one_mul,ht]
  have hd : IntegrableOn (fun x => bernoulliFourierTerm (-(k:ℤ)) (star s) x-bernoulliFourierTerm (-(k:ℤ)) (star (1-star s)) x) (Ioc (1:ℝ) (s.im/(2*Real.pi*k))) := hi.sub hj
  rw [←integral_sub hi hj,←integral_const_mul,←integral_add hd (hc.const_mul (((2*(s.re-1/2):ℝ):ℂ)))]
  have h := norm_integral_le_of_norm_le ((hm.mono_set Ioc_subset_Ioi_self).const_mul
    (bernoulliModeWeight (-(k:ℤ))*(|s.re-1/2|^3/3)))
    (show ∀ᵐ x ∂volume.restrict (Ioc (1:ℝ) (s.im/(2*Real.pi*k))),
      ‖bernoulliFourierTerm (-(k:ℤ)) (star s) x-bernoulliFourierTerm (-(k:ℤ)) (star (1-star s)) x+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogMode s.im (-(k:ℤ)) x‖ ≤
      bernoulliModeWeight (-(k:ℤ))*(|s.re-1/2|^3/3)*(x^(-2:ℝ)*(Real.log x)^3) by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact norm_bernoulli_reflection_response_le hs hs' _ hx.1.le)
  rw [integral_const_mul] at h
  have hb : (∫ x in Ioc (1:ℝ) (s.im/(2*Real.pi*k)), x^(-2:ℝ)*(Real.log x)^3) ≤ 6 := by
    convert incoming_logMoment_Ioc_le (by norm_num : (1:ℝ)<2) 3 (s.im/(2*Real.pi*k)) using 1
    norm_num [Nat.factorial]
  apply h.trans
  calc
    _ ≤ (bernoulliModeWeight (-(k:ℤ))*(|s.re-1/2|^3/3))*6 :=
      mul_le_mul_of_nonneg_left hb (by have := bernoulliModeWeight_nonneg (-(k:ℤ)); positivity)
    _ = _ := by ring

/-- The whole reflected incoming head has an actual critical linear response and uniform cubic error. -/
theorem norm_stationaryIncomingSection_reflection_response_le {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (K : ℕ) :
    ‖stationaryIncomingSection s 1 K-stationaryIncomingSection (1-star s) 1 K+
      ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogSection s.im K‖ ≤ |s.re-1/2|^3/12 := by
  have he : stationaryIncomingSection s 1 K-stationaryIncomingSection (1-star s) 1 K+
      ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogSection s.im K =
      ∑ k ∈ Finset.Icc 1 K, (stationaryIncomingAtom s 1 k-stationaryIncomingAtom (1-star s) 1 k+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogAtom s.im k) := by
    simp only [stationaryIncomingSection,criticalIncomingLogSection,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum]
  rw [he]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ‖stationaryIncomingAtom s 1 k-stationaryIncomingAtom (1-star s) 1 k+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogAtom s.im k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, 2*bernoulliModeWeight (-(k:ℤ))*|s.re-1/2|^3 :=
      Finset.sum_le_sum (fun k _ => norm_stationaryIncomingAtom_reflection_response_le hs hs' k)
    _ = (2*|s.re-1/2|^3)*(∑ k ∈ Finset.Icc 1 K, bernoulliModeWeight (-(k:ℤ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ (2*|s.re-1/2|^3)*(1/24) := mul_le_mul_of_nonneg_left (sum_negativeBernoulliWeight_le K) (by positivity)
    _ = _ := by ring

/-- Away from the critical wall, the divided reflection difference has quadratic error. -/
theorem norm_stationaryIncomingSection_divided_reflection_response_le {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (hd : s.re ≠ 1/2) (K : ℕ) :
    ‖(stationaryIncomingSection s 1 K-stationaryIncomingSection (1-star s) 1 K)/
      ((2*(s.re-1/2):ℝ):ℂ)+criticalIncomingLogSection s.im K‖ ≤ (s.re-1/2)^2/24 := by
  have hδ : s.re-1/2 ≠ 0 := sub_ne_zero.mpr hd
  have hc : ((2*(s.re-1/2):ℝ):ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero (by norm_num : (2:ℝ)≠0) hδ
  have he : (stationaryIncomingSection s 1 K-stationaryIncomingSection (1-star s) 1 K)/
      ((2*(s.re-1/2):ℝ):ℂ)+criticalIncomingLogSection s.im K =
      (stationaryIncomingSection s 1 K-stationaryIncomingSection (1-star s) 1 K+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogSection s.im K)/((2*(s.re-1/2):ℝ):ℂ) := by
    rw [add_div, mul_div_cancel_left₀ _ hc]
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (mul_pos (by norm_num) (abs_pos.mpr hδ))).mpr
  have h := norm_stationaryIncomingSection_reflection_response_le hs hs' K
  calc
    _ ≤ |s.re-1/2|^3/12 := h
    _ = _ := by rw [pow_succ, sq_abs]; ring

/-- The rational boundary is conjugated by same-height reflection. -/
theorem minimumZeroBoundary_reflection (s : ℂ) :
    minimumZeroBoundary (1-star s) = star (minimumZeroBoundary s) := by
  simp [minimumZeroBoundary,star_sub,star_inv₀,star_mul,star_div₀,star_neg,mul_comm]

/-- Same-height reflection preserves every strip zero. -/
theorem incoming_reflected_zeta_zero {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1)
    (hz : riemannZeta s=0) : riemannZeta (1-star s)=0 := by
  have hs1 : s ≠ 1 := by intro h; rw [h] at hs'; norm_num at hs'
  have hc : riemannZeta (star s)=0 := by rw [powerSum_zeta_star (by linarith) hs1,hz,star_zero]
  exact (RHTower.riemannZeta_one_sub_eq_zero_iff
    (show 0 < (star s).re by simpa) (show (star s).re < 1 by simpa)).mpr hc

/-- The paired remainder at a zero retains its exact signed displacement. -/
theorem normalizedWeightedRemainder_reflection_im_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s=0) :
    (normalizedWeightedRemainder s 1-normalizedWeightedRemainder (1-star s) 1).im =
      (2*s.re-1)*s.im/Complex.normSq (star s*(1-star s)) := by
  have hr : 0 < (1-star s).re ∧ (1-star s).re < 1 := by
    simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]; constructor <;> linarith
  rw [normalizedWeightedRemainder_one_eq_boundary hs hs',
    normalizedWeightedRemainder_one_eq_boundary hr.1 hr.2,hz,incoming_reflected_zeta_zero hs hs' hz]
  simp only [zero_div,star_zero,sub_zero]
  rw [minimumZeroBoundary_reflection]
  simp only [Complex.sub_im,Complex.star_def,Complex.conj_im]
  rw [minimumZeroBoundary_im]
  simp only [Complex.star_def]
  ring

/-- Exact difference of the two Bernoulli means; no mean is discarded. -/
theorem reciprocalBernoulliMean_reflection_difference {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    s.im/(12*Complex.normSq (s+1))-(1-star s).im/(12*Complex.normSq ((1-star s)+1)) =
      -(2*s.re-1)*s.im/(4*Complex.normSq (s+1)*Complex.normSq (2-s)) := by
  have hA : 0 < Complex.normSq (s+1) := by
    rw [Complex.normSq_apply]
    have : (s+1).re = s.re+1 := by simp
    rw [this]; nlinarith [sq_nonneg (s+1).im]
  have hB : 0 < Complex.normSq (2-s) := by
    rw [Complex.normSq_apply]
    have : (2-s).re = 2-s.re := by simp
    rw [this]; nlinarith [sq_nonneg (2-s).im]
  have he : Complex.normSq ((1-star s)+1)=Complex.normSq (2-s) := by
    simp [Complex.normSq_apply]; ring
  have hab : Complex.normSq (s+1)-Complex.normSq (2-s)=3*(2*s.re-1) := by
    simp [Complex.normSq_apply]; ring
  rw [he,show (1-star s).im=s.im by simp]
  field_simp
  rw [show Complex.normSq (2-s)-Complex.normSq (s+1) = -3*(2*s.re-1) by linarith [hab]]
  ring

/-- All literal Fourier modes of a reflected strip zero obey this exact signed balance. -/
theorem hasSum_scaledBernoulliFourierAtom_reflection_im_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s=0) :
    HasSum (fun k : ℤ => (scaledBernoulliFourierAtom s 1 k-
      scaledBernoulliFourierAtom (1-star s) 1 k).im)
      ((2*s.re-1)*s.im*(1/Complex.normSq (star s*(1-star s))-
        1/(4*Complex.normSq (s+1)*Complex.normSq (2-s)))) := by
  have hr : 0 < (1-star s).re ∧ (1-star s).re < 1 := by
    simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]; constructor <;> linarith
  have h := (hasSum_scaledBernoulliFourierAtom_im hs
    (show s≠1 by intro he; rw [he] at hs'; norm_num at hs') (by omega : 1≤(1:ℕ))).sub
    (hasSum_scaledBernoulliFourierAtom_im hr.1
      (show (1:ℂ)-star s≠1 by intro he; rw [he] at hr; norm_num at hr) (by omega : 1≤(1:ℕ)))
  simp only [Nat.cast_one,Real.one_rpow,one_mul] at h
  have hg := normalizedWeightedRemainder_reflection_im_at_zero hs hs' hz
  have hm := reciprocalBernoulliMean_reflection_difference hs hs'
  simp only [Complex.sub_im] at hg
  have heq : (normalizedWeightedRemainder s 1).im+s.im/(12*Complex.normSq (s+1))-
      ((normalizedWeightedRemainder (1-star s) 1).im+(1-star s).im/(12*Complex.normSq ((1-star s)+1))) =
      (2*s.re-1)*s.im*(1/Complex.normSq (star s*(1-star s))-
        1/(4*Complex.normSq (s+1)*Complex.normSq (2-s))) := by
    rw [show (normalizedWeightedRemainder s 1).im+s.im/(12*Complex.normSq (s+1))-
        ((normalizedWeightedRemainder (1-star s) 1).im+(1-star s).im/(12*Complex.normSq ((1-star s)+1))) =
        ((normalizedWeightedRemainder s 1).im-(normalizedWeightedRemainder (1-star s) 1).im)+
        (s.im/(12*Complex.normSq (s+1))-(1-star s).im/(12*Complex.normSq ((1-star s)+1))) by ring,hg,hm]
    ring
  rw [heq] at h
  simpa only [Complex.sub_im] using h

/-- The reflected mean denominator strictly dominates the boundary denominator throughout the strip. -/
theorem incoming_reflection_denominator_gap {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    0 < Complex.normSq (star s*(1-star s)) ∧
      Complex.normSq (star s*(1-star s)) < Complex.normSq (s+1)*Complex.normSq (2-s) := by
  have hX : 0 < Complex.normSq (star s) := by
    simp only [Complex.normSq_apply,Complex.star_def,Complex.conj_re,Complex.conj_im]
    nlinarith [sq_nonneg s.im]
  have hY : 0 < Complex.normSq (1-star s) := by
    simp only [Complex.normSq_apply,Complex.star_def,Complex.conj_re,Complex.conj_im,
      Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im]
    nlinarith [sq_nonneg s.im]
  have hA : Complex.normSq (star s) < Complex.normSq (s+1) := by
    simp [Complex.normSq_apply]; nlinarith
  have hB : Complex.normSq (1-star s) < Complex.normSq (2-s) := by
    simp [Complex.normSq_apply]; nlinarith
  rw [Complex.normSq_mul]
  exact ⟨mul_pos hX hY, mul_lt_mul hA hB.le hY (hX.trans hA).le⟩

/-- The exact full paired source has positive required value at a strict-right zero of positive height. -/
theorem incoming_reflection_balance_pos {s : ℂ} (hs : 1/2 < s.re) (hs' : s.re < 1)
    (ht : 0 < s.im) :
    0 < (2*s.re-1)*s.im*(1/Complex.normSq (star s*(1-star s))-
      1/(4*Complex.normSq (s+1)*Complex.normSq (2-s))) := by
  obtain ⟨hC,hAB⟩ := incoming_reflection_denominator_gap (by linarith : 0 < s.re) hs'
  have hab0 := hC.trans hAB
  have hg : Complex.normSq (star s*(1-star s)) < 4*Complex.normSq (s+1)*Complex.normSq (2-s) := by
    nlinarith
  exact mul_pos (mul_pos (by linarith) ht) (sub_pos.mpr (one_div_lt_one_div_of_lt hC hg))

end RHTower.DeletionMixedRefinement
