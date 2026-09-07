import GaloisForLFunctions.RHTower.ArithmeticStationaryOutgoingMargin
import GaloisForLFunctions.RHTower.ArithmeticStationaryHeightReserve

/-!
# Horizontal stability of the full incoming stationary source

At equal height, every phase and saddle endpoint agrees. Horizontal variation
changes only the actual Mellin weight. Its logarithmic moment and the complete
Fourier coefficient mass give a uniform complex Lipschitz estimate for the full
incoming aggregate. Positive critical heads consequently persist in explicit
strict-right source neighborhoods. This does not locate zeros in those neighborhoods;
the signed off-line-zero comparison and RH remain open.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- The exponential tangent inequality bounds an ordered change in the actual power weight. -/
theorem incoming_power_difference_le_of_le {x b c : ℝ} (hx : 1 ≤ x) (hb : 2 ≤ b) (hbc : b ≤ c) :
    |x^(-b)-x^(-c)| ≤ (c-b)*(x^(-2:ℝ)*Real.log x) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hp : 0 ≤ x^(-b) := Real.rpow_nonneg hx0.le _
  have horder : x^(-c) ≤ x^(-b) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hbase : x^(-b) ≤ x^(-2:ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have he : x^(-c)=x^(-b)*x^(-(c-b)) := by
    rw [←Real.rpow_add hx0]
    congr 1; ring
  have ht : 1-x^(-(c-b)) ≤ (c-b)*Real.log x := by
    rw [Real.rpow_def_of_pos hx0]
    have h := Real.add_one_le_exp (Real.log x * (-(c-b)))
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr horder),he]
  calc
    _ = x^(-b)*(1-x^(-(c-b))) := by ring
    _ ≤ x^(-b)*((c-b)*Real.log x) := mul_le_mul_of_nonneg_left ht hp
    _ ≤ x^(-2:ℝ)*((c-b)*Real.log x) := mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = _ := by ring

/-- The horizontal power bound is symmetric and uniform for nonnegative strip coordinates. -/
theorem incoming_power_difference_le {x b c : ℝ} (hx : 1 ≤ x) (hb : 2 ≤ b) (hc : 2 ≤ c) :
    |x^(-b)-x^(-c)| ≤ |b-c| *(x^(-2:ℝ)*Real.log x) := by
  rcases le_total b c with hbc | hcb
  · have h := incoming_power_difference_le_of_le hx hb hbc
    simpa only [abs_of_nonpos (sub_nonpos.mpr hbc),neg_sub] using h
  · have h := incoming_power_difference_le_of_le hx hc hcb
    rw [abs_sub_comm] at h
    simpa only [abs_of_nonneg (sub_nonneg.mpr hcb)] using h

/-- Equal height preserves the exact complex phase of every literal Fourier term. -/
theorem bernoulliFourierTerm_horizontal_difference {s z : ℂ} (ht : s.im=z.im)
    (k : ℤ) {x : ℝ} (hx : 0 < x) :
    bernoulliFourierTerm k (star s) x-bernoulliFourierTerm k (star z) x =
      (bernoulliModeWeight k:ℂ)*((x^(-(s.re+2))-x^(-(z.re+2)):ℝ):ℂ)*
        Complex.exp (((2*Real.pi*k*x+s.im*Real.log x:ℝ):ℂ)*Complex.I) := by
  rw [bernoulliFourierTerm,bernoulliFourierTerm,
    fourier_mul_cpow_eq_mode k (star s) hx,fourier_mul_cpow_eq_mode k (star z) hx]
  simp only [Complex.star_def,Complex.conj_re,Complex.conj_im,neg_neg,logarithmicFourierMode,←ht]
  push_cast
  ring

/-- The actual complex mode difference is dominated by one integrable logarithmic moment. -/
theorem norm_bernoulliFourierTerm_horizontal_difference_le {s z : ℂ}
    (hs : 0 ≤ s.re) (hz : 0 ≤ z.re) (ht : s.im=z.im) (k : ℤ) {x : ℝ} (hx : 1 ≤ x) :
    ‖bernoulliFourierTerm k (star s) x-bernoulliFourierTerm k (star z) x‖ ≤
      bernoulliModeWeight k*|s.re-z.re| *(x^(-2:ℝ)*Real.log x) := by
  rw [bernoulliFourierTerm_horizontal_difference ht k (zero_lt_one.trans_le hx),norm_mul,norm_mul]
  simp only [Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,sub_zero,Real.exp_zero,mul_one,abs_of_nonneg (bernoulliModeWeight_nonneg k)]
  have h := mul_le_mul_of_nonneg_left
    (incoming_power_difference_le hx (by linarith : 2 ≤ s.re+2) (by linarith : 2 ≤ z.re+2))
    (bernoulliModeWeight_nonneg k)
  simpa only [show s.re+2-(z.re+2)=s.re-z.re by ring,mul_assoc] using h

/-- Exact same-height difference of a whole incoming atom, with its finite endpoint retained. -/
theorem stationaryIncomingAtom_horizontal_difference {s z : ℂ} (hs : 0 ≤ s.re) (hz : 0 ≤ z.re)
    (ht : s.im=z.im) (k : ℕ) :
    stationaryIncomingAtom s 1 k-stationaryIncomingAtom z 1 k =
      ∫ x in Ioc (1:ℝ) (s.im/(2*Real.pi*k)),
        (bernoulliModeWeight (-(k:ℤ)):ℂ)*((x^(-(s.re+2))-x^(-(z.re+2)):ℝ):ℂ)*
          Complex.exp (((2*Real.pi*(-(k:ℤ))*x+s.im*Real.log x:ℝ):ℂ)*Complex.I) := by
  have hi : IntegrableOn (bernoulliFourierTerm (-(k:ℤ)) (star s)) (Ioc (1:ℝ) (s.im/(2*Real.pi*k))) :=
    (integrable_bernoulliFourierTerm (by norm_num : (0:ℝ)<1)
      (show -1 < (star s).re by simpa using (show -1 < s.re by linarith)) _).mono_set Ioc_subset_Ioi_self
  have hj : IntegrableOn (bernoulliFourierTerm (-(k:ℤ)) (star z)) (Ioc (1:ℝ) (s.im/(2*Real.pi*k))) :=
    (integrable_bernoulliFourierTerm (by norm_num : (0:ℝ)<1)
      (show -1 < (star z).re by simpa using (show -1 < z.re by linarith)) _).mono_set Ioc_subset_Ioi_self
  simp only [stationaryIncomingAtom,Nat.cast_one,Complex.one_cpow,one_mul,←ht]
  rw [←integral_sub hi hj]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  simpa only [Int.cast_neg] using bernoulliFourierTerm_horizontal_difference ht (-(k:ℤ)) (zero_lt_one.trans hx.1)

/-- One incoming atom has a height-independent horizontal Lipschitz bound. -/
theorem norm_stationaryIncomingAtom_horizontal_le {s z : ℂ} (hs : 0 ≤ s.re) (hz : 0 ≤ z.re)
    (ht : s.im=z.im) (k : ℕ) :
    ‖stationaryIncomingAtom s 1 k-stationaryIncomingAtom z 1 k‖ ≤
      bernoulliModeWeight (-(k:ℤ))*|s.re-z.re| := by
  have hi : IntegrableOn (bernoulliFourierTerm (-(k:ℤ)) (star s)) (Ioc (1:ℝ) (s.im/(2*Real.pi*k))) :=
    (integrable_bernoulliFourierTerm (by norm_num : (0:ℝ)<1)
      (show -1 < (star s).re by simpa using (show -1 < s.re by linarith)) _).mono_set Ioc_subset_Ioi_self
  have hj : IntegrableOn (bernoulliFourierTerm (-(k:ℤ)) (star z)) (Ioc (1:ℝ) (s.im/(2*Real.pi*k))) :=
    (integrable_bernoulliFourierTerm (by norm_num : (0:ℝ)<1)
      (show -1 < (star z).re by simpa using (show -1 < z.re by linarith)) _).mono_set Ioc_subset_Ioi_self
  have hm : IntegrableOn (fun x : ℝ => x^(-2:ℝ)*Real.log x) (Ioi (1:ℝ)) := by
    simpa only [show -(1:ℝ)-1=(-2:ℝ) by ring] using RHTower.integrableOn_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<1)
  have hmass : (∫ x in Ioi (1:ℝ), x^(-2:ℝ)*Real.log x) = 1 := by
    simpa only [show -(1:ℝ)-1=(-2:ℝ) by ring,one_pow,div_self (one_ne_zero : (1:ℝ) ≠ 0)] using RHTower.integral_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<1)
  simp only [stationaryIncomingAtom,Nat.cast_one,Complex.one_cpow,one_mul,←ht]
  rw [←integral_sub hi hj]
  have hb := norm_integral_le_of_norm_le ((hm.mono_set Ioc_subset_Ioi_self).const_mul
    (bernoulliModeWeight (-(k:ℤ))*|s.re-z.re|)) (show ∀ᵐ x ∂volume.restrict (Ioc (1:ℝ) (s.im/(2*Real.pi*k))),
      ‖bernoulliFourierTerm (-(k:ℤ)) (star s) x-bernoulliFourierTerm (-(k:ℤ)) (star z) x‖ ≤
        bernoulliModeWeight (-(k:ℤ))*|s.re-z.re| *(x^(-2:ℝ)*Real.log x) by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact norm_bernoulliFourierTerm_horizontal_difference_le hs hz ht _ hx.1.le)
  rw [integral_const_mul] at hb
  have hsmall : (∫ x in Ioc (1:ℝ) (s.im/(2*Real.pi*k)), x^(-2:ℝ)*Real.log x) ≤ 1 := by
    calc
      _ ≤ ∫ x in Ioi (1:ℝ), x^(-2:ℝ)*Real.log x := by
        apply setIntegral_mono_set hm ?_ (Filter.Eventually.of_forall (fun x hx => hx.1))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans hx).le _) (Real.log_nonneg hx.le)
      _ = 1 := hmass
  exact hb.trans ((mul_le_mul_of_nonneg_left hsmall (mul_nonneg (bernoulliModeWeight_nonneg _) (abs_nonneg _))).trans_eq (mul_one _))

/-- Every finite negative-frequency prefix has at most the actual one-sided coefficient mass. -/
theorem sum_negativeBernoulliWeight_le (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, bernoulliModeWeight (-(k:ℤ))) ≤ 1/24 := by
  classical
  let F : Finset ℤ := (Finset.Icc 1 K).image (fun k : ℕ => (k:ℤ))
  have h := summable_positiveBernoulliWeight.sum_le_tsum F
    (fun k _ => by unfold positiveBernoulliWeight; split_ifs; exact bernoulliModeWeight_nonneg k; exact le_rfl)
  rw [tsum_positiveBernoulliWeight] at h
  have he : (∑ k ∈ F, positiveBernoulliWeight k) =
      ∑ k ∈ Finset.Icc 1 K, bernoulliModeWeight (-(k:ℤ)) := by
    dsimp only [F]
    rw [Finset.sum_image (fun a _ b _ hab => by exact_mod_cast hab)]
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : (0:ℤ) < k := by exact_mod_cast (show 0 < k by have := (Finset.mem_Icc.mp hk).1; omega)
    rw [positiveBernoulliWeight,if_pos hk0,bernoulliModeWeight_even]
  rwa [he] at h

/-- Uniform horizontal comparison of the actual full complex incoming aggregate. -/
theorem norm_stationaryIncomingSection_horizontal_le {s z : ℂ}
    (hs : 0 ≤ s.re) (hz : 0 ≤ z.re) (ht : s.im=z.im) (K : ℕ) :
    ‖stationaryIncomingSection s 1 K-stationaryIncomingSection z 1 K‖ ≤ |s.re-z.re|/24 := by
  rw [stationaryIncomingSection,stationaryIncomingSection,←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.Icc 1 K, ‖stationaryIncomingAtom s 1 k-stationaryIncomingAtom z 1 k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, bernoulliModeWeight (-(k:ℤ))*|s.re-z.re| :=
      Finset.sum_le_sum (fun k _ => norm_stationaryIncomingAtom_horizontal_le hs hz ht k)
    _ = (∑ k ∈ Finset.Icc 1 K, bernoulliModeWeight (-(k:ℤ)))*|s.re-z.re| := (Finset.sum_mul ..).symm
    _ ≤ (1/24)*|s.re-z.re| := mul_le_mul_of_nonneg_right (sum_negativeBernoulliWeight_le K) (abs_nonneg _)
    _ = _ := by ring


/-- The complete signed horizontal difference retains each literal finite integral. -/
theorem stationaryIncomingSection_horizontal_difference {s z : ℂ}
    (hs : 0 ≤ s.re) (hz : 0 ≤ z.re) (ht : s.im=z.im) (K : ℕ) :
    stationaryIncomingSection s 1 K-stationaryIncomingSection z 1 K =
      ∑ k ∈ Finset.Icc 1 K, ∫ x in Ioc (1:ℝ) (s.im/(2*Real.pi*k)),
        (bernoulliModeWeight (-(k:ℤ)):ℂ)*((x^(-(s.re+2))-x^(-(z.re+2)):ℝ):ℂ)*
          Complex.exp (((2*Real.pi*(-(k:ℤ))*x+s.im*Real.log x:ℝ):ℂ)*Complex.I) := by
  rw [stationaryIncomingSection,stationaryIncomingSection,←Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun k _ => stationaryIncomingAtom_horizontal_difference hs hz ht k)

/-- The imaginary head comparison inherits the exact displacement factor. -/
theorem stationaryIncomingSection_im_horizontal_le {s z : ℂ}
    (hs : 0 ≤ s.re) (hz : 0 ≤ z.re) (ht : s.im=z.im) (K : ℕ) :
    |(stationaryIncomingSection s 1 K).im-(stationaryIncomingSection z 1 K).im| ≤ |s.re-z.re|/24 := by
  have h := (Complex.abs_im_le_norm (stationaryIncomingSection s 1 K-stationaryIncomingSection z 1 K)).trans
    (norm_stationaryIncomingSection_horizontal_le hs hz ht K)
  simpa only [Complex.sub_im] using h

/-- Reflection comparison vanishes with horizontal displacement, uniformly in height and cutoff. -/
theorem norm_stationaryIncomingSection_reflection_difference_le {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (K : ℕ) :
    ‖stationaryIncomingSection s 1 K-stationaryIncomingSection (1-star s) 1 K‖ ≤ |2*s.re-1|/24 := by
  have hz : 0 ≤ (1-star s).re := by simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]; linarith
  have ht : s.im=(1-star s).im := by simp
  have h := norm_stationaryIncomingSection_horizontal_le hs hz ht K
  rw [show (1-star s).re=1-s.re by simp,show s.re-(1-s.re)=2*s.re-1 by ring] at h
  exact h

/-- A positive actual incoming budget persists through a quantitative horizontal neighborhood. -/
theorem stationaryIncomingSection_positive_horizontal_neighborhood {s z : ℂ}
    (hs : 0 ≤ s.re) (hz : 0 ≤ z.re) (ht : s.im=z.im) (_ht0 : 0 < z.im) (K : ℕ)
    (hhead : 1/(240*z.im) < (stationaryIncomingSection z 1 K).im)
    (hshift : |s.re-z.re| ≤ 1/(20*z.im)) :
    1/(480*z.im) < (stationaryIncomingSection s 1 K).im := by
  have h := stationaryIncomingSection_im_horizontal_le hs hz ht K
  have he : |s.re-z.re|/24 ≤ 1/(480*z.im) := by
    calc
      _ ≤ (1/(20*z.im))/24 := div_le_div_of_nonneg_right hshift (by norm_num)
      _ = _ := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  have hlo := (abs_le.mp h).1
  have hdouble : 1/(240*z.im)=2*(1/(480*z.im)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [hdouble] at hhead
  linarith

/-- Actual critical zeros have a positive incoming neighborhood with explicit reciprocal-height width. -/
theorem stationaryIncomingSection_positive_near_critical_zero {s z : ℂ}
    (hz : z.re=1/2) (hzero : riemannZeta z=0) (ht : 480000 ≤ Real.sqrt z.im)
    (hs : 0 ≤ s.re) (him : s.im=z.im) (hshift : |s.re-z.re| ≤ 1/(20*z.im)) :
    1/(480*z.im) < (stationaryIncomingSection s 1 ⌊z.im/(2*Real.pi)⌋₊).im := by
  have hhead := stationaryIncomingSection_im_gt_reciprocal_height_at_zero
    (by rw [hz]) (by rw [hz]; norm_num) ht hzero
  exact stationaryIncomingSection_positive_horizontal_neighborhood hs
    (by rw [hz]; norm_num) him (Real.sqrt_pos.mp (by linarith)) _ hhead hshift

/-- Positive incoming source points occur strictly right of the critical line above every height.
The shifted source point is not claimed to be a zero or a nonzero of zeta. -/
theorem exists_strict_right_stationaryIncoming_positive_above (T : ℝ) :
    ∃ s : ℂ, 1/2 < s.re ∧ s.re < 1 ∧ T < s.im ∧ 0 < s.im ∧
      1/(480*s.im) < (stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊).im := by
  obtain ⟨z,hz,ht,hzt,hzero,hhead⟩ := exists_critical_stationaryIncoming_positive_above (max T 1)
  have ht1 : 1 < z.im := (le_max_right _ _).trans_lt ht
  let d : ℝ := 1/(40*z.im)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdhalf : d < 1/2 := by
    dsimp only [d]
    apply (div_lt_iff₀ (by positivity : 0 < 40*z.im)).mpr
    linarith
  have hdwidth : d ≤ 1/(20*z.im) := by
    dsimp only [d]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  let s : ℂ := z+(d:ℂ)
  have hre : s.re=z.re+d := by simp [s]
  have him : s.im=z.im := by simp [s]
  have hs : 0 ≤ s.re := by rw [hre,hz]; linarith
  have hshift : |s.re-z.re| ≤ 1/(20*z.im) := by
    rw [hre,add_sub_cancel_left,abs_of_pos hd]
    exact hdwidth
  refine ⟨s,?_,?_,?_,by simpa only [him] using hzt,?_⟩
  · rw [hre,hz]; linarith
  · rw [hre,hz]; linarith
  · rw [him]; exact (le_max_left _ _).trans_lt ht
  · have h := stationaryIncomingSection_positive_horizontal_neighborhood hs
      (by rw [hz]; norm_num) him hzt _ hhead hshift
    simpa only [him] using h

end RHTower.DeletionMixedRefinement
