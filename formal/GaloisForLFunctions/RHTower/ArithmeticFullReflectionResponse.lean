import GaloisForLFunctions.RHTower.ArithmeticIncomingReflectionResponse

/-!
# Complete reflected logarithmic source

The full arithmetic Fourier source has an actual critical logarithmic response.
Absolute coefficient mass and exact logarithmic moments justify reconstruction
of every signed mode and give a uniform cubic reflection remainder. Subtracting
any finite incoming head retains the complementary response. At an off-line
strip zero, the full complex response lies in an explicit quadratic disk around
the rational zero-pair target. No opposing source bound or RH proof is supplied.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Complex Real
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Literal full unit Fourier source, with both frequency sectors present. -/
def unitFullFourierSource (s : ℂ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*(x:ℂ)^(-star s-2)

/-- Full half-line logarithmic response of one literal Fourier mode. -/
def criticalFullLogAtom (t : ℝ) (k : ℤ) : ℂ :=
  ∫ x in Ioi (1:ℝ), criticalIncomingLogMode t k x

/-- Actual full critical logarithmic source, prior to sector decomposition. -/
def criticalFullLogResponse (t : ℝ) : ℂ :=
  ∫ x in Ioi (1:ℝ), ((RHTower.bernoulliPeriodic x+1/12:ℝ):ℂ)*
    ((x^(-(5/2:ℝ))*Real.log x:ℝ):ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)

/-- The complete source reconstructs from all literal unit Fourier atoms. -/
theorem hasSum_unitFullFourierSource {s : ℂ} (hs : -1 < s.re) :
    HasSum (scaledBernoulliFourierAtom s 1) (unitFullFourierSource s) := by
  change HasSum (fun k : ℤ => scaledBernoulliFourierAtom s 1 k) _
  simpa only [scaledBernoulliFourierAtom,Nat.cast_one,Complex.one_cpow,one_mul,unitFullFourierSource] using
    hasSum_integral_bernoulliFourierTerm zero_lt_one (show -1 < (star s).re by simpa)

/-- The actual full Fourier source includes the exact Bernoulli mean. -/
theorem unitFullFourierSource_eq_remainder {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    unitFullFourierSource s=normalizedWeightedRemainder s 1+1/(12*(star s+1)) := by
  have h := (hasSum_unitFullFourierSource (by linarith : -1 < s.re)).unique
    (hasSum_scaledBernoulliFourierAtom hs hs1 (by omega : 1≤(1:ℕ)))
  simpa only [Nat.cast_one,Real.one_rpow,Complex.ofReal_one,mul_one] using h

/-- The logarithmic response preserves the literal Fourier character. -/
theorem criticalIncomingLogMode_eq_fourier (t : ℝ) (k : ℤ) (x : ℝ) :
    criticalIncomingLogMode t k x = (bernoulliModeWeight k:ℂ)*fourier k (x:AddCircle (1:ℝ))*
      (((x^(-(5/2:ℝ))*Real.log x:ℝ):ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I)) := by
  unfold criticalIncomingLogMode
  rw [fourier_coe_apply]
  rw [show (((2*Real.pi*k*x+t*Real.log x:ℝ):ℂ)*Complex.I)=
    (((2*Real.pi*k*x:ℝ):ℂ)*Complex.I)+(((t*Real.log x:ℝ):ℂ)*Complex.I) by push_cast; ring,
    Complex.exp_add]
  simp only [Complex.ofReal_one,div_one]
  rw [show (2:ℂ)*Real.pi*Complex.I*(k:ℂ)*(x:ℂ)=(((2*Real.pi*k*x:ℝ):ℂ)*Complex.I) by push_cast; ring]
  ring

/-- All logarithmic mode norms have the same exact first-moment mass. -/
theorem integral_norm_criticalIncomingLogMode (t : ℝ) (k : ℤ) :
    (∫ x in Ioi (1:ℝ), ‖criticalIncomingLogMode t k x‖) = bernoulliModeWeight k*(4/9) := by
  have he : (∫ x in Ioi (1:ℝ), ‖criticalIncomingLogMode t k x‖) =
      bernoulliModeWeight k*(∫ x in Ioi (1:ℝ), x^(-(5/2:ℝ))*Real.log x) := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact norm_criticalIncomingLogMode t k hx.le
  rw [he]
  congr 1
  convert RHTower.integral_rpow_mul_log_Ioi_one (by norm_num : (0:ℝ)<3/2) using 1 <;> norm_num

/-- Absolute convergence allows reconstruction of the entire critical response. -/
theorem hasSum_criticalFullLogResponse (t : ℝ) :
    HasSum (criticalFullLogAtom t) (criticalFullLogResponse t) := by
  have hsum : Summable (fun k : ℤ => ∫ x in Ioi (1:ℝ), ‖criticalIncomingLogMode t k x‖) := by
    simp_rw [integral_norm_criticalIncomingLogMode]
    exact hasSum_bernoulliModeWeight.summable.mul_right _
  have h := hasSum_integral_of_summable_integral_norm (integrable_criticalIncomingLogMode t) hsum
  change HasSum (fun k : ℤ => ∫ x in Ioi (1:ℝ), criticalIncomingLogMode t k x) _
  convert! h using 1
  apply integral_congr_ae
  filter_upwards with x
  have hx := (hasSum_bernoulliModeWeight_fourier x).mul_right
    (((x^(-(5/2:ℝ))*Real.log x:ℝ):ℂ)*Complex.exp (((t*Real.log x:ℝ):ℂ)*Complex.I))
  simpa only [criticalIncomingLogMode_eq_fourier,mul_assoc] using hx.tsum_eq.symm

/-- Absolute mass bound for one complete critical response mode. -/
theorem norm_criticalFullLogAtom_le (t : ℝ) (k : ℤ) :
    ‖criticalFullLogAtom t k‖ ≤ bernoulliModeWeight k*(4/9) := by
  rw [←integral_norm_criticalIncomingLogMode]
  exact norm_integral_le_integral_norm _

/-- The entire response has a height-independent mass ceiling, with both sectors included. -/
theorem norm_criticalFullLogResponse_le (t : ℝ) : ‖criticalFullLogResponse t‖ ≤ 1/27 := by
  have h := (hasSum_criticalFullLogResponse t).norm_le_of_bounded
    (hasSum_bernoulliModeWeight.mul_right (4/9)) (norm_criticalFullLogAtom_le t)
  convert h using 1
  norm_num

/-- Uniform cubic remainder for a complete half-line mode. -/
theorem norm_fullFourierAtom_reflection_response_le {s : ℂ} (hs : 0 ≤ s.re) (hs' : s.re ≤ 1)
    (k : ℤ) :
    ‖scaledBernoulliFourierAtom s 1 k-scaledBernoulliFourierAtom (1-star s) 1 k+
      ((2*(s.re-1/2):ℝ):ℂ)*criticalFullLogAtom s.im k‖ ≤
      2*bernoulliModeWeight k*|s.re-1/2|^3 := by
  have hi : IntegrableOn (bernoulliFourierTerm k (star s)) (Ioi (1:ℝ)) :=
    integrable_bernoulliFourierTerm zero_lt_one
      (show -1 < (star s).re by simpa using (show -1 < s.re by linarith)) _
  have hj : IntegrableOn (bernoulliFourierTerm k (star (1-star s))) (Ioi (1:ℝ)) :=
    integrable_bernoulliFourierTerm zero_lt_one
      (show -1 < (star (1-star s)).re by simp only [Complex.star_def,Complex.conj_re,Complex.sub_re,Complex.one_re]; linarith) _
  have hc := integrable_criticalIncomingLogMode s.im k
  have hm : IntegrableOn (fun x : ℝ => x^(-2:ℝ)*(Real.log x)^3) (Ioi (1:ℝ)) := by
    simpa only [show -(1:ℝ)-1=(-2:ℝ) by norm_num] using
      RHTower.integrableOn_rpow_mul_log_pow_Ioi_one (by norm_num : (0:ℝ)<1) 3
  simp only [scaledBernoulliFourierAtom,criticalFullLogAtom,Nat.cast_one,Complex.one_cpow,one_mul]
  have hd : IntegrableOn (fun x => bernoulliFourierTerm k (star s) x-
      bernoulliFourierTerm k (star (1-star s)) x) (Ioi (1:ℝ)) := hi.sub hj
  rw [←integral_sub hi hj,←integral_const_mul,←integral_add hd (hc.const_mul (((2*(s.re-1/2):ℝ):ℂ)))]
  have h := norm_integral_le_of_norm_le (hm.const_mul (bernoulliModeWeight k*(|s.re-1/2|^3/3)))
    (show ∀ᵐ x ∂volume.restrict (Ioi (1:ℝ)),
      ‖bernoulliFourierTerm k (star s) x-bernoulliFourierTerm k (star (1-star s)) x+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogMode s.im k x‖ ≤
      bernoulliModeWeight k*(|s.re-1/2|^3/3)*(x^(-2:ℝ)*(Real.log x)^3) by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact norm_bernoulli_reflection_response_le hs hs' _ hx.le)
  rw [integral_const_mul] at h
  have hmval : (∫ x in Ioi (1:ℝ), x^(-2:ℝ)*(Real.log x)^3)=6 := by
    convert RHTower.integral_rpow_mul_log_pow_Ioi_one (by norm_num : (0:ℝ)<1) 3 using 1 <;> norm_num [Nat.factorial]
  rw [hmval] at h
  convert h using 1
  ring

/-- Cubic control of the complete reflected source, retaining every Fourier mode. -/
theorem norm_unitFullFourierSource_reflection_response_le {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) :
    ‖unitFullFourierSource s-unitFullFourierSource (1-star s)+
      ((2*(s.re-1/2):ℝ):ℂ)*criticalFullLogResponse s.im‖ ≤ |s.re-1/2|^3/6 := by
  have hr : -1 < (1-star s).re := by
    simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]; linarith
  have h := ((hasSum_unitFullFourierSource (by linarith : -1 < s.re)).sub
    (hasSum_unitFullFourierSource hr)).add
    ((hasSum_criticalFullLogResponse s.im).mul_left (((2*(s.re-1/2):ℝ):ℂ)))
  have hb := h.norm_le_of_bounded (hasSum_bernoulliModeWeight.mul_right (2*|s.re-1/2|^3))
    (fun k => by simpa only [mul_assoc,mul_left_comm,mul_comm] using norm_fullFourierAtom_reflection_response_le hs hs' k)
  convert hb using 1
  ring

/-- Dividing the full source difference by nonzero displacement retains a uniform quadratic error. -/
theorem norm_unitFullFourierSource_divided_reflection_response_le {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (hd : s.re ≠ 1/2) :
    ‖(unitFullFourierSource s-unitFullFourierSource (1-star s))/((2*(s.re-1/2):ℝ):ℂ)+
      criticalFullLogResponse s.im‖ ≤ (s.re-1/2)^2/12 := by
  have hδ : s.re-1/2 ≠ 0 := sub_ne_zero.mpr hd
  have hc : ((2*(s.re-1/2):ℝ):ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero (by norm_num : (2:ℝ)≠0) hδ
  have he : (unitFullFourierSource s-unitFullFourierSource (1-star s))/((2*(s.re-1/2):ℝ):ℂ)+
      criticalFullLogResponse s.im =
      (unitFullFourierSource s-unitFullFourierSource (1-star s)+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalFullLogResponse s.im)/((2*(s.re-1/2):ℝ):ℂ) := by
    rw [add_div,mul_div_cancel_left₀ _ hc]
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (mul_pos (by norm_num) (abs_pos.mpr hδ))).mpr
  calc
    _ ≤ |s.re-1/2|^3/6 := norm_unitFullFourierSource_reflection_response_le hs hs'
    _ = _ := by rw [pow_succ,sq_abs]; ring

/-- The actual complementary source retains every term outside the selected incoming head. -/
theorem norm_complementaryFourierSource_reflection_response_le {s : ℂ}
    (hs : 0 ≤ s.re) (hs' : s.re ≤ 1) (K : ℕ) :
    ‖(unitFullFourierSource s-stationaryIncomingSection s 1 K)-
      (unitFullFourierSource (1-star s)-stationaryIncomingSection (1-star s) 1 K)+
      ((2*(s.re-1/2):ℝ):ℂ)*(criticalFullLogResponse s.im-criticalIncomingLogSection s.im K)‖ ≤
      |s.re-1/2|^3/4 := by
  have he : (unitFullFourierSource s-stationaryIncomingSection s 1 K)-
      (unitFullFourierSource (1-star s)-stationaryIncomingSection (1-star s) 1 K)+
      ((2*(s.re-1/2):ℝ):ℂ)*(criticalFullLogResponse s.im-criticalIncomingLogSection s.im K) =
      (unitFullFourierSource s-unitFullFourierSource (1-star s)+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalFullLogResponse s.im)-
      (stationaryIncomingSection s 1 K-stationaryIncomingSection (1-star s) 1 K+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogSection s.im K) := by ring
  rw [he]
  calc
    _ ≤ ‖unitFullFourierSource s-unitFullFourierSource (1-star s)+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalFullLogResponse s.im‖+
      ‖stationaryIncomingSection s 1 K-stationaryIncomingSection (1-star s) 1 K+
        ((2*(s.re-1/2):ℝ):ℂ)*criticalIncomingLogSection s.im K‖ := norm_sub_le _ _
    _ ≤ |s.re-1/2|^3/6+|s.re-1/2|^3/12 := add_le_add
      (norm_unitFullFourierSource_reflection_response_le hs hs')
      (norm_stationaryIncomingSection_reflection_response_le hs hs' K)
    _ = _ := by ring

/-- The full source at a reflected zero pair has the exact previously reconstructed signed value. -/
theorem unitFullFourierSource_reflection_im_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s=0) :
    (unitFullFourierSource s-unitFullFourierSource (1-star s)).im =
      (2*s.re-1)*s.im*(1/Complex.normSq (star s*(1-star s))-
        1/(4*Complex.normSq (s+1)*Complex.normSq (2-s))) := by
  have hr : -1 < (1-star s).re := by
    simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]; linarith
  exact (Complex.hasSum_im ((hasSum_unitFullFourierSource (by linarith : -1 < s.re)).sub
    (hasSum_unitFullFourierSource hr))).unique
    (hasSum_scaledBernoulliFourierAtom_reflection_im_at_zero hs hs' hz)

/-- Every off-line strip zero satisfies a complete critical logarithmic source constraint. -/
theorem abs_criticalFullLogResponse_zero_constraint {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hd : s.re ≠ 1/2) (hz : riemannZeta s=0) :
    |(criticalFullLogResponse s.im).im+s.im*(1/Complex.normSq (star s*(1-star s))-
      1/(4*Complex.normSq (s+1)*Complex.normSq (2-s)))| ≤ (s.re-1/2)^2/12 := by
  have h := (Complex.abs_im_le_norm ((unitFullFourierSource s-unitFullFourierSource (1-star s))/
    ((2*(s.re-1/2):ℝ):ℂ)+criticalFullLogResponse s.im)).trans
    (norm_unitFullFourierSource_divided_reflection_response_le hs.le hs'.le hd)
  simp only [Complex.add_im,Complex.div_ofReal_im,unitFullFourierSource_reflection_im_at_zero hs hs' hz] at h
  have hd' : 2*(s.re-1/2) ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr hd)
  have he : ((2*s.re-1)*s.im*(1/Complex.normSq (star s*(1-star s))-
      1/(4*Complex.normSq (s+1)*Complex.normSq (2-s))))/(2*(s.re-1/2)) =
      s.im*(1/Complex.normSq (star s*(1-star s))-
      1/(4*Complex.normSq (s+1)*Complex.normSq (2-s))) := by
    rw [show 2*s.re-1=2*(s.re-1/2) by ring,mul_assoc,mul_div_cancel_left₀ _ hd']
  rw [he,add_comm] at h
  exact h

/-- Full complex reflected zero balance, including the real mean response. -/
theorem unitFullFourierSource_reflection_at_zero {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hz : riemannZeta s=0) :
    unitFullFourierSource s-unitFullFourierSource (1-star s) =
      ((2*s.re-1:ℝ):ℂ)*
        (((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I-
          1/(12*(star s+1)*(2-s))) := by
  have hr : 0 < (1-star s).re ∧ (1-star s).re < 1 := by
    simp only [Complex.sub_re,Complex.one_re,Complex.star_def,Complex.conj_re]; constructor <;> linarith
  have hs1 : s≠1 := by intro h; rw [h] at hs'; norm_num at hs'
  have hr1 : (1:ℂ)-star s≠1 := by intro h; rw [h] at hr; norm_num at hr
  have ha : star s+1≠(0:ℂ) := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith
  have hb : 2-s≠(0:ℂ) := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith
  have hmean : 1/(12*(star s+1))-1/(12*(star (1-star s)+1)) =
      -((2*s.re-1:ℝ):ℂ)/(12*(star s+1)*(2-s)) := by
    rw [star_sub,star_one,star_star,show (1:ℂ)-s+1=2-s by ring]
    field_simp
    apply Complex.ext <;> simp
    ring
  have hboundary : minimumZeroBoundary s-star (minimumZeroBoundary s) =
      (((2*s.re-1)*s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I := by
    rw [Complex.star_def,Complex.sub_conj,minimumZeroBoundary_im]
    simp only [Complex.star_def]
    push_cast
    ring
  rw [unitFullFourierSource_eq_remainder hs hs1,unitFullFourierSource_eq_remainder hr.1 hr1,
    normalizedWeightedRemainder_one_eq_boundary hs hs',normalizedWeightedRemainder_one_eq_boundary hr.1 hr.2,
    hz,incoming_reflected_zeta_zero hs hs' hz]
  simp only [zero_div,star_zero,sub_zero]
  rw [minimumZeroBoundary_reflection,
    show minimumZeroBoundary s+1/(12*(star s+1))-
      (star (minimumZeroBoundary s)+1/(12*(star (1-star s)+1))) =
      (minimumZeroBoundary s-star (minimumZeroBoundary s))+
        (1/(12*(star s+1))-1/(12*(star (1-star s)+1))) by ring,
    hboundary,hmean]
  push_cast
  ring

/-- The complete complex logarithmic source must satisfy both zero-pair equations simultaneously. -/
theorem norm_criticalFullLogResponse_zero_constraint {s : ℂ}
    (hs : 0 < s.re) (hs' : s.re < 1) (hd : s.re ≠ 1/2) (hz : riemannZeta s=0) :
    ‖criticalFullLogResponse s.im+
      (((s.im/Complex.normSq (star s*(1-star s)):ℝ):ℂ)*Complex.I-
        1/(12*(star s+1)*(2-s)))‖ ≤ (s.re-1/2)^2/12 := by
  have hc : ((2*(s.re-1/2):ℝ):ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (2:ℝ)≠0) (sub_ne_zero.mpr hd)
  have h := norm_unitFullFourierSource_divided_reflection_response_le hs.le hs'.le hd
  rw [unitFullFourierSource_reflection_at_zero hs hs' hz,
    show 2*s.re-1=2*(s.re-1/2) by ring,mul_div_cancel_left₀ _ hc,add_comm] at h
  exact h

end RHTower.DeletionMixedRefinement
