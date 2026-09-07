import GaloisForLFunctions.RHTower.ArithmeticPositiveFrequencyReserve
import GaloisForLFunctions.RHTower.ArithmeticUnitPhaseNoGo

/-!
# Uniform outgoing aggregate comparison against the strict mean margin

The whole reflected outgoing envelope is at most `2000/(t*sqrt t)` throughout
`0 < Re(s) ≤ 1`, `t ≥ 4π`. This is a bound for the moving stationary family, with
all reflected endpoint and remainder terms retained. At zeros it makes the actual
incoming aggregate carry a strict reciprocal-height budget above an explicit
height. The independent incoming comparison and RH remain open.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- The moving integer cutoff lies between half its positive scale and the full scale. -/
theorem stationary_floor_half_bounds {B : ℝ} (hB : 2 ≤ B) :
    1 ≤ ⌊B⌋₊ ∧ B/2 ≤ (⌊B⌋₊:ℝ) ∧ (⌊B⌋₊:ℝ) ≤ B := by
  have hlow := Nat.lt_floor_add_one B
  have hhigh := Nat.floor_le (by linarith : 0 ≤ B)
  have hhalf : B/2 ≤ (⌊B⌋₊:ℝ) := by linarith
  have hone : (1:ℝ) ≤ (⌊B⌋₊:ℝ) := by linarith
  exact ⟨by exact_mod_cast hone,hhalf,hhigh⟩

/-- The reflected boundary product has a uniform quadratic height bound in the strip. -/
theorem norm_reflected_boundary_product_le {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 1)
    (ht : 4 ≤ s.im) : ‖(1-star s)*(2-star s)‖ ≤ 2*s.im^2 := by
  have ht0 : 0 ≤ s.im := by linarith
  have h1 : ‖1-star s‖ ≤ s.im+1 := by
    have hr : (1-star s).re=1-s.re := by simp
    have hi : (1-star s).im=s.im := by simp
    have h := Complex.norm_le_abs_re_add_abs_im (1-star s)
    rw [hr,hi,abs_of_nonneg ht0,abs_of_nonneg (sub_nonneg.mpr hs')] at h
    linarith
  have h2 : ‖2-star s‖ ≤ s.im+2 := by
    have hr : (2-star s).re=2-s.re := by simp
    have hi : (2-star s).im=s.im := by simp
    have h := Complex.norm_le_abs_re_add_abs_im (2-star s)
    rw [hr,hi,abs_of_nonneg ht0,abs_of_nonneg (show 0 ≤ 2-s.re by linarith)] at h
    linarith
  rw [norm_mul]
  calc
    _ ≤ (s.im+1)*(s.im+2) := mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
    _ ≤ 2*s.im^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht) ht0]

/-- Exact factorization of the reflected endpoint and remainder envelope. -/
theorem reflectedPrefixZeroEnvelope_factor {s : ℂ} {K : ℕ} (hK : 1 ≤ K) :
    reflectedPrefixZeroEnvelope s K = (K:ℝ)^s.re *
      (1/‖s‖+1/(2*(K:ℝ))+‖(1-star s)*(2-star s)‖/((2-s.re)*(K:ℝ)^2)) := by
  have hK0 : (0:ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  unfold reflectedPrefixZeroEnvelope
  rw [Real.rpow_sub hK0,Real.rpow_one,Real.rpow_sub hK0,Real.rpow_two]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- A concrete bound for the reflected partial-sum envelope keeps every source term. -/
theorem reflectedPrefixZeroEnvelope_le_moving_scale {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 1)
    (ht : 4 ≤ s.im) {B : ℝ} (hB : 2 ≤ B) {K : ℕ}
    (hhalf : B/2 ≤ (K:ℝ)) (hKB : (K:ℝ) ≤ B) :
    reflectedPrefixZeroEnvelope s K ≤ B^s.re*(1/s.im+1/B+8*s.im^2/B^2) := by
  have hB0 : 0 < B := by linarith
  have hK0 : (0:ℝ) < K := by linarith
  have hK : 1 ≤ K := by exact_mod_cast (show (1:ℝ) ≤ K by linarith)
  have ht0 : 0 < s.im := by linarith
  have hnorm : 0 < ‖s‖ := ht0.trans_le (Complex.im_le_norm s)
  have hden : 1 ≤ 2-s.re := by linarith
  have hn := norm_reflected_boundary_product_le hs hs' ht
  have hcoef : ‖(1-star s)*(2-star s)‖/(2-s.re) ≤ 2*s.im^2 := by
    apply (div_le_iff₀ (by linarith : 0 < 2-s.re)).mpr
    nlinarith [mul_nonneg (sq_nonneg s.im) (sub_nonneg.mpr hden)]
  have hfirst : 1/‖s‖ ≤ 1/s.im := one_div_le_one_div_of_le ht0 (Complex.im_le_norm s)
  have hsecond : 1/(2*(K:ℝ)) ≤ 1/B := one_div_le_one_div_of_le hB0 (by linarith)
  have hthird : ‖(1-star s)*(2-star s)‖/((2-s.re)*(K:ℝ)^2) ≤ 8*s.im^2/B^2 := by
    calc
      _ = (‖(1-star s)*(2-star s)‖/(2-s.re))/(K:ℝ)^2 := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
      _ ≤ (2*s.im^2)/(K:ℝ)^2 := div_le_div_of_nonneg_right hcoef (sq_nonneg _)
      _ ≤ 8*s.im^2/B^2 := by
        apply (div_le_div_iff₀ (sq_pos_of_pos hK0) (sq_pos_of_pos hB0)).mpr
        have hh : B^2 ≤ 4*(K:ℝ)^2 := by nlinarith [sq_nonneg (2*(K:ℝ)-B)]
        nlinarith [mul_nonneg (sq_nonneg s.im) (sub_nonneg.mpr hh)]
  rw [reflectedPrefixZeroEnvelope_factor hK]
  apply (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hfirst hsecond) hthird)
    (Real.rpow_nonneg hK0.le _)).trans
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hK0.le hKB hs.le) (by positivity)

/-- All real powers cancel in the actual outgoing factor times the reflected scale. -/
theorem stationaryReflectedTailEnvelope_mul_scale {s : ℂ} (ht : 0 < s.im) :
    stationaryReflectedTailEnvelope s 1*(s.im/(2*Real.pi))^s.re =
      28*bernoulliModeWeight (-1)/((s.im/(2*Real.pi))*Real.sqrt s.im) := by
  have hB : 0 < s.im/(2*Real.pi) := by positivity
  unfold stationaryReflectedTailEnvelope
  simp only [Nat.cast_one,Real.one_rpow,mul_one]
  have he : (s.im/(2*Real.pi))^(-s.re-1)*(s.im/(2*Real.pi))^s.re = (s.im/(2*Real.pi))⁻¹ := by
    rw [←Real.rpow_add hB,show -s.re-1+s.re=(-1:ℝ) by ring,Real.rpow_neg_one]
  calc
    _ = 28*bernoulliModeWeight (-1)*
      ((s.im/(2*Real.pi))^(-s.re-1)*(s.im/(2*Real.pi))^s.re)/Real.sqrt s.im := by ring
    _ = _ := by rw [he]; ring

/-- Explicit evaluation of the scale-bound envelope with the actual Fourier coefficient. -/
theorem stationaryOutgoing_scale_bound_identity {t : ℝ} (ht : 0 < t) :
    28*bernoulliModeWeight (-1)/((t/(2*Real.pi))*Real.sqrt t)*
      (1/t+1/(t/(2*Real.pi))+8*t^2/(t/(2*Real.pi))^2) =
      (14/Real.pi+28)/(t^2*Real.sqrt t)+448*Real.pi/(t*Real.sqrt t) := by
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have hr : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  simp only [bernoulliModeWeight,Int.cast_neg,Int.cast_one,neg_one_sq,mul_one]
  field_simp
  ring

/-- The outgoing zero-envelope is uniformly smaller order than a reciprocal height. -/
theorem stationaryOutgoingEnvelope_le_uniform {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 1)
    (ht : 4*Real.pi ≤ s.im) :
    stationaryReflectedTailEnvelope s 1*reflectedPrefixZeroEnvelope s ⌊s.im/(2*Real.pi)⌋₊ ≤
      2000/(s.im*Real.sqrt s.im) := by
  have ht4 : 4 ≤ s.im := by linarith [Real.pi_gt_three]
  have ht1 : 1 ≤ s.im := by linarith
  have ht0 : 0 < s.im := by linarith
  have hB : 2 ≤ s.im/(2*Real.pi) := (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr (by linarith)
  have hK := stationary_floor_half_bounds hB
  have hP := reflectedPrefixZeroEnvelope_le_moving_scale hs hs' ht4 hB hK.2.1 hK.2.2
  have h := mul_le_mul_of_nonneg_left hP (stationaryReflectedTailEnvelope_nonneg ht0 1)
  rw [←mul_assoc,stationaryReflectedTailEnvelope_mul_scale ht0,stationaryOutgoing_scale_bound_identity ht0] at h
  apply h.trans
  have hcoef : 0 ≤ 14/Real.pi+28 := by positivity
  have hcoef' : 14/Real.pi+28 ≤ 33 := by
    have hdiv : 14/Real.pi ≤ 5 := (div_le_iff₀ Real.pi_pos).mpr (by linarith [Real.pi_gt_three])
    linarith
  have hsmall : (14/Real.pi+28)/(s.im^2*Real.sqrt s.im) ≤ 33/(s.im*Real.sqrt s.im) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hcoef' (show 0 ≤ s.im*Real.sqrt s.im by positivity)
    have hsq : s.im ≤ s.im^2 := by nlinarith
    have hpow := mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg s.im)
    nlinarith
  have hlarge : 448*Real.pi/(s.im*Real.sqrt s.im) ≤ 1792/(s.im*Real.sqrt s.im) := by
    exact div_le_div_of_nonneg_right (by linarith [Real.pi_lt_four]) (by positivity)
  have hsum := add_le_add hsmall hlarge
  apply hsum.trans
  rw [←add_div]
  exact div_le_div_of_nonneg_right (by norm_num) (by positivity)


/-- The entire actual outgoing stationary sector obeys the uniform bound at a strip zero. -/
theorem norm_stationary_outgoing_le_uniform_at_zero {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1)
    (ht : 4*Real.pi ≤ s.im) (hz : riemannZeta s=0) :
    ‖stationaryComplexBudget s 1-stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊‖ ≤
      2000/(s.im*Real.sqrt s.im) := by
  have ht1 : 1 ≤ s.im := by linarith [Real.pi_gt_three]
  have hB : 2 ≤ s.im/(2*Real.pi) := (le_div_iff₀ (by positivity : 0 < 2*Real.pi)).mpr (by linarith)
  have hstat := stationary_cutoff_frequency_le (show 0 ≤ s.im by linarith) (by rfl : 1 ≤ (1:ℕ))
  simp only [Nat.cast_one,mul_one] at hstat
  have h := norm_negativeFourierSection_sub_incoming_le_at_zero hs hs' ht1 hz
    (by rfl : 1 ≤ (1:ℕ)) (stationary_floor_half_bounds hB).1
    (by simpa only [Nat.cast_one,mul_one] using hstat)
  have hc : ‖stationaryComplexBudget s 1-stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊‖ ≤
      stationaryReflectedTailEnvelope s 1*reflectedPrefixZeroEnvelope s ⌊s.im/(2*Real.pi)⌋₊ := by
    simpa only [stationaryComplexBudget,Nat.cast_one,mul_one] using h
  exact hc.trans (stationaryOutgoingEnvelope_le_uniform hs hs'.le ht)

/-- The half-mean margin has a uniform reciprocal-height lower bound throughout the strip. -/
theorem stationary_half_mean_ge_reciprocal_height {s : ℂ} (hs : 0 < s.re) (hs' : s.re ≤ 1)
    (ht : 1 ≤ s.im) : 1/(120*s.im) ≤ s.im/(24*Complex.normSq (s+1)) := by
  have ht0 : 0 < s.im := by linarith
  have he : Complex.normSq (s+1) = (s.re+1)^2+s.im^2 := by simp [Complex.normSq_apply,pow_two]
  have hn : 0 < Complex.normSq (s+1) := by rw [he]; positivity
  have hb : Complex.normSq (s+1) ≤ 5*s.im^2 := by
    rw [he]
    nlinarith [sq_nonneg (1-s.re),sq_nonneg (s.im-1)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-- With the moving outgoing family controlled, every strip zero forces an explicit incoming budget. -/
theorem stationaryIncomingSection_im_lowerBound_uniform_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (ht : 4*Real.pi ≤ s.im) (hz : riemannZeta s=0) :
    s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s)))+
      1/(120*s.im)-2000/(s.im*Real.sqrt s.im) <
        (stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊).im := by
  have ht1 : 1 ≤ s.im := by linarith [Real.pi_gt_three]
  have hb := norm_stationary_outgoing_le_uniform_at_zero hs hs' ht hz
  have him := Complex.im_le_norm (stationaryComplexBudget s 1-
    stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊)
  rw [Complex.sub_im,stationaryComplexBudget_im (show 0 ≤ s.im by linarith) (by rfl : 1 ≤ (1:ℕ))] at him
  have hm := stationary_half_mean_ge_reciprocal_height hs hs'.le ht1
  have hl := stationaryFourierBudget_lowerBound_half_mean_at_zero hs hs' ht1 hz
  linarith

/-- The explicit square-root threshold also satisfies the actual stationary cutoff threshold. -/
theorem stationary_large_sqrt_height {t : ℝ} (ht : 480000 ≤ Real.sqrt t) : 4*Real.pi ≤ t := by
  have hpos : 0 < Real.sqrt t := by linarith
  have ht0 : 0 < t := Real.sqrt_pos.mp hpos
  have hs := Real.sq_sqrt ht0.le
  nlinarith [Real.pi_lt_four,sq_nonneg (Real.sqrt t-480000)]

/-- At the explicit height, the complete outgoing error fits one quarter of the mean lower bound. -/
theorem stationaryOutgoingEnvelope_le_quarter_mean_floor {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re ≤ 1) (ht : 480000 ≤ Real.sqrt s.im) :
    stationaryReflectedTailEnvelope s 1*reflectedPrefixZeroEnvelope s ⌊s.im/(2*Real.pi)⌋₊ ≤
      1/(240*s.im) := by
  have ht0 : 0 < s.im := Real.sqrt_pos.mp (by linarith)
  apply (stationaryOutgoingEnvelope_le_uniform hs hs' (stationary_large_sqrt_height ht)).trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_nonneg ht0.le (sub_nonneg.mpr ht)]

/-- Every closed-right zero above the explicit height has a strictly positive actual incoming head. -/
theorem stationaryIncomingSection_im_gt_reciprocal_height_at_zero {s : ℂ}
    (hs : 1/2 ≤ s.re) (hs' : s.re < 1) (ht : 480000 ≤ Real.sqrt s.im) (hz : riemannZeta s=0) :
    1/(240*s.im) < (stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊).im := by
  have hs0 : 0 < s.re := by linarith
  have ht0 : 0 < s.im := Real.sqrt_pos.mp (by linarith)
  have ht1 : 1 ≤ s.im := by have := stationary_large_sqrt_height ht; linarith [Real.pi_gt_three]
  have hl := stationaryIncomingSection_im_lowerBound_half_mean_at_zero hs hs' ht1 hz
  have hq := stationaryOutgoingEnvelope_le_quarter_mean_floor hs0 hs'.le ht
  have hm := stationary_half_mean_ge_reciprocal_height hs0 hs'.le ht1
  have hd : 0 ≤ s.im*(2*s.re-1)/(2*Complex.normSq (star s*(1-star s))) := by
    exact div_nonneg (mul_nonneg ht0.le (by linarith)) (mul_nonneg (by norm_num) (Complex.normSq_nonneg _))
  have he : 1/(120*s.im) = 2*(1/(240*s.im)) := by simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [he] at hm
  linarith


/-- Actual critical-line zeros force positive incoming aggregate above every prescribed height. -/
theorem exists_critical_stationaryIncoming_positive_above (T : ℝ) :
    ∃ s : ℂ, s.re=1/2 ∧ T < s.im ∧ 0 < s.im ∧ riemannZeta s=0 ∧
      1/(240*s.im) < (stationaryIncomingSection s 1 ⌊s.im/(2*Real.pi)⌋₊).im := by
  obtain ⟨t,ht,hz⟩ := RHTower.exists_Xi_zero_gt (max T ((480000:ℝ)^2))
  have htlarge : (480000:ℝ)^2 < t := (le_max_right _ _).trans_lt ht
  have ht0 : 0 < t := by nlinarith
  let s : ℂ := 1/2+(t:ℂ)*Complex.I
  have hre : s.re=1/2 := by simp [s]
  have him : s.im=t := by simp [s]
  have hs : s ∈ minimumStrip := by norm_num [s,minimumStrip]
  have hzero : riemannZeta s=0 := by
    have hd := unitPhaseStrip_denominators hs
    have hxi : RHTower.xi s=0 := by
      change RHTower.XiC (t:ℂ)=0
      rw [RHTower.XiC_ofReal,hz,Complex.ofReal_zero]
    rw [RHTower.xi_eq_archFactor_mul_zeta hd.1 hd.2.1
      (Complex.Gammaℝ_ne_zero_of_re_pos hs.1)] at hxi
    exact (mul_eq_zero.mp hxi).resolve_left (RHTower.archFactor_ne_zero_strip hs)
  have hsqrt : 480000 ≤ Real.sqrt s.im := by
    rw [him]
    have hp := Real.sqrt_nonneg t
    have he := Real.sq_sqrt ht0.le
    nlinarith [sq_nonneg (Real.sqrt t-480000)]
  refine ⟨s,hre,?_,by simpa only [him] using ht0,hzero,?_⟩
  · rw [him]; exact (le_max_left _ _).trans_lt ht
  · exact stationaryIncomingSection_im_gt_reciprocal_height_at_zero
      (by rw [hre]) (by rw [hre]; norm_num) hsqrt hzero

end RHTower.DeletionMixedRefinement
