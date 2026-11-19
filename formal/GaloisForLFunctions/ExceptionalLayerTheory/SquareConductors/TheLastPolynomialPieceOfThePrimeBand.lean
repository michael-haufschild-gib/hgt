import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheLastTwoQuotientCellsOfTheSpline
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The last polynomial piece of the ordinary-prime band

Each box convolution integrates the preceding terminal monomial over the
distance to the support boundary. On the last first-prime band this gives
a seventh power of the distance in logarithmic coordinates.
-/

noncomputable section
open Set MeasureTheory
open scoped Convolution
open GaloisForLFunctions.CountingHolography.Sections GaloisForLFunctions.ArithmeticWeightTheory
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge _root_.RHTower.WeilDeletion
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem last_box_cell (m : ℕ) :
    ∃ c : ℝ, 0<c ∧ ∀ {z : ℝ}, z ∈ Icc (0:ℝ) 2 →
      upow 1 m ((m:ℝ)+1-z)=c*z^m := by
  induction m with
  | zero =>
    refine ⟨1/2,by norm_num,fun {z} hz => ?_⟩
    obtain ⟨hl,hu⟩ := hz
    change (Icc (-1:ℝ) 1).indicator (fun _ => 1/(2*1:ℝ)) (((0:ℕ):ℝ)+1-z) = _
    rw [indicator_of_mem (show ((0:ℕ):ℝ)+1-z ∈ Icc (-1:ℝ) 1 from
      ⟨by push_cast; linarith only [hu],by push_cast; linarith only [hl]⟩)]
    norm_num
  | succ m ih =>
    obtain ⟨c,hc,h⟩ := ih
    let a := (m:ℝ)+1
    let f := upow 1 m
    have hi : Integrable f := integrable_upow 1 m
    have ha : 0<a := by dsimp only [a]; positivity
    refine ⟨c/(2*a),div_pos hc (mul_pos two_pos ha),fun {z} hz => ?_⟩
    obtain ⟨hl,hu⟩ := hz
    have hleft : a-z≤a := sub_le_self _ hl
    have hright : a≤a+2-z := by linarith only [hu]
    have hoff (t : ℝ) (ht : a<t) : f t=0 := by
      by_contra! hne
      have hs := (support_upow_subset one_pos m hne).2
      dsimp only [a] at ht
      linarith only [hs,ht]
    have hzint : (∫ t in a..a+2-z, f t)=0 := by
      calc _ = ∫ _t in a..a+2-z, (0:ℝ) := by
                 apply intervalIntegral.integral_congr_ae
                 exact ae_of_all _ fun t ht => by
                   rw [uIoc_of_le hright] at ht
                   exact hoff t ht.1
           _ = 0 := by simp
    have hcell : (∫ t in a-z..a, f t) = c*(z^(m+1)/a) := by
      calc _ = ∫ t in a-z..a, c*(a-t)^m := by
                 apply intervalIntegral.integral_congr
                 intro t ht
                 rw [uIcc_of_le hleft] at ht
                 have hdist : a-t ∈ Icc (0:ℝ) 2 :=
                   ⟨sub_nonneg.mpr ht.2,by linarith only [ht.1,hu]⟩
                 have he := h hdist
                 change f (a-(a-t))=c*(a-t)^m at he
                 rwa [show a-(a-t)=t by ring] at he
           _ = _ := by
                 rw [intervalIntegral.integral_const_mul,
                   intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^m) a,
                   sub_self,show a-(a-z)=z by ring,integral_pow,zero_pow (Nat.succ_ne_zero m),sub_zero]
    have hfull := intervalIntegral.integral_add_adjacent_intervals
      (hi.intervalIntegrable (a := a-z) (b := a)) (hi.intervalIntegrable (a := a) (b := a+2-z))
    rw [hzint,add_zero,hcell] at hfull
    have hpr := intervalIntegral.integral_add_adjacent_intervals
      (hi.intervalIntegrable (a := 0) (b := a-z)) (hi.intervalIntegrable (a := a-z) (b := a+2-z))
    rw [←hfull] at hpr
    change (unif 1 ⋆ f) (((m+1:ℕ):ℝ)+1-z) = _
    rw [unif_convolution_eq one_pos hi]
    have h₁ : ((m+1:ℕ):ℝ)+1-z+1=a+2-z := by dsimp only [a]; push_cast; ring
    have h₂ : ((m+1:ℕ):ℝ)+1-z-1=a-z := by dsimp only [a]; push_cast; ring
    rw [h₁,h₂,←hpr]
    field_simp [ha.ne']
    ring

/-- The terminal eight-box autocorrelation is a positive multiple of the
seventh power of the distance to its right boundary. -/
theorem last_polynomial_of_spline_autocorrelation :
    ∃ c : ℝ, 0<c ∧ ∀ {z : ℝ}, z ∈ Icc (0:ℝ) 2 → splineAutoCorr (8-z)=c*z^7 := by
  obtain ⟨c,hc,h⟩ := last_box_cell 7
  refine ⟨c,hc,fun {z} hz => ?_⟩
  rw [splineAutoCorr_eq_eight_boxes]
  have he := h hz
  norm_num at he
  exact he

/-- In the logarithm of twice the prime spacing the ordinary-prime band
has one exponential factor and one degree-seven polynomial. -/
theorem last_prime_band_log_profile :
    ∃ A : ℝ, 0<A ∧ ∀ {t : ℝ}, 8<t → t<8+Real.log 4 →
      (1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1*dyadicSpline (Real.exp t) =
        A*Real.exp (-t/2)*(8+Real.log 4-t)^7 := by
  obtain ⟨c,hc,h⟩ := last_polynomial_of_spline_autocorrelation
  let w := (1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1
  have hw : w<0 := mul_neg_of_pos_of_neg first_even_cofactor_positive first_centered_quotient_negative
  refine ⟨-2*w*c,mul_pos (by linarith only [hw]) hc,fun {t} ht hlo => ?_⟩
  have hlog : Real.log 4 = 2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have hz : 8+Real.log 4-t ∈ Icc (0:ℝ) 2 :=
    ⟨sub_nonneg.mpr hlo.le,by linarith only [ht,hlog,Real.log_two_lt_d9]⟩
  have he := h hz
  rw [show 8-(8+Real.log 4-t)=t-Real.log 4 by ring] at he
  have hzero := splineAutoCorr_zero_outside (ht.trans_le (le_abs_self t))
  simp only [dyadicSpline,if_pos (Real.exp_pos t),squarePrimeWeight,Complex.ofReal_re,
    squareLogProfile,Real.log_exp,hzero,mul_zero,zero_sub,he]
  dsimp only [w]
  ring

/-- The sine integral of a decreasing sharp window is positive at every
positive frequency. The upper jump contributes its signed endpoint value. -/
private theorem sine_on_decreasing_window {L y : ℝ} (hL : 0<L) (hy : 0<y) (A D : ℝ → ℝ)
    (hD : Continuous D) (hder : ∀ t, HasDerivAt A (D t) t)
    (hneg : ∀ t ∈ Icc (0:ℝ) L, D t<0) (hend : 0≤A L) :
    0 < ∫ t in (0:ℝ)..L, A t*Real.sin (y*t) := by
  let G (t : ℝ) := 1-Real.cos (y*t)
  let H (t : ℝ) := y*Real.sin (y*t)
  have hcG : Continuous G := by dsimp only [G]; fun_prop
  have hcH : Continuous H := by dsimp only [H]; fun_prop
  have hG (t : ℝ) : HasDerivAt G (H t) t := by
    have h := (hasDerivAt_const t (1:ℝ)).sub (((hasDerivAt_id t).const_mul y).cos)
    exact h.congr_deriv (by dsimp only [H,id]; ring)
  have hnG (t : ℝ) : 0≤G t := sub_nonneg.mpr (Real.cos_le_one _)
  have hzero : G 0=0 := by simp [G]
  obtain ⟨u,hu,huMin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hL.le) hD.neg.continuousOn
  let c := -D u
  have hc : 0<c := neg_pos.mpr (hneg u hu)
  have hmono : (∫ t in (0:ℝ)..L, D t*G t) ≤ -c*(∫ t in (0:ℝ)..L, G t) := by
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hL.le ((hD.mul hcG).intervalIntegrable _ _)
      ((continuous_const.mul hcG).intervalIntegrable _ _)
    intro t ht
    have h := huMin ht
    apply mul_le_mul_of_nonneg_right _ (hnG t)
    change -D u≤ -D t at h
    dsimp only [c]
    linarith only [h]
  have hInt : 0<∫ t in (0:ℝ)..L, G t := by
    dsimp only [G]
    have hcos : Continuous (fun t : ℝ => Real.cos (y*t)) := by fun_prop
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ))
      (continuous_const.intervalIntegrable _ _) (hcos.intervalIntegrable _ _),
      intervalIntegral.integral_const,smul_eq_mul,sub_zero,mul_one,
      intervalIntegral.integral_comp_mul_left Real.cos hy.ne',integral_cos,mul_zero,Real.sin_zero,
      sub_zero,smul_eq_mul,←div_eq_inv_mul,sub_pos,div_lt_iff₀ hy]
    exact (Real.sin_lt (mul_pos hy hL)).trans_eq (mul_comm _ _)
  have hint := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t (_ : t∈uIcc 0 L) => hder t) (fun t (_ : t∈uIcc 0 L) => hG t)
    (hD.intervalIntegrable 0 L) (hcH.intervalIntegrable 0 L)
  rw [hzero,mul_zero,sub_zero] at hint
  have hs : (∫ t in (0:ℝ)..L, A t*H t) = y*(∫ t in (0:ℝ)..L, A t*Real.sin (y*t)) := by
    rw [←intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t _ => by dsimp only [H]; ring)
  rw [hs] at hint
  have hstrict := hmono.trans_lt (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc) hInt)
  exact pos_of_mul_pos_right (by linarith only [hint,hstrict,mul_nonneg hend (hnG L)] :
    0<y*(∫ t in (0:ℝ)..L, A t*Real.sin (y*t))) hy.le

/-- Rotating the Mellin transform by its left-end phase leaves a strictly
positive imaginary part at positive frequency for every real exponent at
most one. The integrand uses the actual last-cofactor prime profile. -/
theorem last_prime_band_sine_phase {β y : ℝ} (hβ' : β≤1) (hy : 0<y) :
    0 < ∫ u in (0:ℝ)..Real.log (16/15:ℝ),
      Real.exp (β*u)*((1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1*
        dyadicSpline (Real.exp (8+Real.log 3+u)))*Real.sin (y*u) := by
  let L := Real.log (16/15:ℝ)
  let d := Real.log 4-Real.log 3
  let r := β-1/2
  let a := 8+Real.log 3
  let A (t : ℝ) := Real.exp (r*t)*(d-t)^7
  let D (t : ℝ) := Real.exp (r*t)*(d-t)^6*(r*(d-t)-7)
  have hL : 0<L := Real.log_pos (by norm_num)
  have hLd : L<d := by
    dsimp only [L,d]
    rw [←Real.log_div (by norm_num) (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hd2 : d<2 := by
    have h4 : Real.log 4=2*Real.log 2 := by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    dsimp only [d]
    linarith only [h4,Real.log_two_lt_d9,Real.log_pos (by norm_num : (1:ℝ)<3)]
  have hcD : Continuous D := by dsimp only [D]; fun_prop
  have hder (t : ℝ) : HasDerivAt A (D t) t := by
    have h := (((hasDerivAt_id t).const_mul r).exp).mul
      (((hasDerivAt_const t d).sub (hasDerivAt_id t)).pow 7)
    exact h.congr_deriv (by dsimp only [D,id,Pi.sub_apply,Pi.pow_apply]; ring)
  have hneg (t : ℝ) (ht : t∈Icc (0:ℝ) L) : D t<0 := by
    have hv : 0<d-t := sub_pos.mpr (ht.2.trans_lt hLd)
    have hrad : r*(d-t)≤(1:ℝ)*2 := mul_le_mul (by dsimp only [r]; linarith only [hβ'])
      (by linarith only [ht.1,hd2]) hv.le zero_le_one
    exact mul_neg_of_pos_of_neg (mul_pos (Real.exp_pos _) (pow_pos hv 6)) (by linarith only [hrad])
  have hend : 0≤A L := mul_nonneg (Real.exp_pos _).le (pow_nonneg (sub_nonneg.mpr hLd.le) _)
  have hs := sine_on_decreasing_window hL hy A D hcD hder hneg hend
  obtain ⟨k,hk,hprofile⟩ := last_prime_band_log_profile
  have hcon (t : ℝ) (ht : t∈uIcc 0 L) :
      Real.exp (β*t)*((1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1*
        dyadicSpline (Real.exp (a+t)))*Real.sin (y*t) =
      (k*Real.exp (-a/2))*(A t*Real.sin (y*t)) := by
    rw [uIcc_of_le hL.le] at ht
    have hl : 8<a+t := by dsimp only [a]; linarith only [ht.1,Real.log_pos (by norm_num : (1:ℝ)<3)]
    have hr : a+t<8+Real.log 4 := by dsimp only [a,d] at *; linarith only [ht.2,hLd]
    have he : β*t+(-(a+t)/2)=(-a/2)+r*t := by dsimp only [r]; ring
    rw [hprofile hl hr,show 8+Real.log 4-(a+t)=d-t by dsimp only [a,d]; ring]
    have hexp : Real.exp (β*t)*Real.exp (-(a+t)/2)=Real.exp (-a/2)*Real.exp (r*t) := by
      rw [←Real.exp_add,he,Real.exp_add]
    dsimp only [A]
    linear_combination k*(d-t)^7*Real.sin (y*t)*hexp
  change 0 < ∫ t in (0:ℝ)..L, _
  rw [intervalIntegral.integral_congr hcon,intervalIntegral.integral_const_mul]
  exact mul_pos (mul_pos hk (Real.exp_pos _)) hs

/-- The Mellin integral of the sharp prime band in logarithmic coordinates,
with the nonzero left-end factor removed, detects either sign of the ordinate. -/
theorem last_prime_band_mellin_ne_zero {z : ℂ} (hβ : z.re≤1) (hy : z.im≠0) :
    (∫ u in (0:ℝ)..Real.log (16/15:ℝ), Complex.exp (z*u)*
      (((1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1*
        dyadicSpline (Real.exp (8+Real.log 3+u)) : ℝ) : ℂ)) ≠ 0 := by
  let F (u : ℝ) := (1-cofactorDyadicCoefficient)*centeredPrimeWeight 1 1*
    dyadicSpline (Real.exp (8+Real.log 3+u))
  let L := Real.log (16/15:ℝ)
  have hcF : Continuous F := continuous_const.mul
    (contDiff_six_dyadicSpline.continuous.comp (by fun_prop : Continuous
      (fun u : ℝ => Real.exp (8+Real.log 3+u))))
  have hc : Continuous (fun u : ℝ => Complex.exp (z*u) * (F u : ℂ)) :=
    (by fun_prop : Continuous (fun u : ℝ => Complex.exp (z*u))).mul
      (Complex.continuous_ofReal.comp hcF)
  intro hz
  change (∫ u in (0:ℝ)..L, Complex.exp (z*u)*(F u : ℂ)) = 0 at hz
  have hi := intervalIntegral.intervalIntegral_im (μ := volume) (hc.intervalIntegrable 0 L)
  change (∫ u in (0:ℝ)..L, (Complex.exp (z*u)*(F u : ℂ)).im) =
    (∫ u in (0:ℝ)..L, Complex.exp (z*u)*(F u : ℂ)).im at hi
  rw [hz,Complex.zero_im] at hi
  have he (u : ℝ) : (Complex.exp (z*u)*(F u : ℂ)).im =
      Real.exp (z.re*u)*F u*Real.sin (z.im*u) := by
    simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add,
      Complex.exp_im,Complex.mul_re,sub_zero]
    ring
  simp_rw [he] at hi
  rcases lt_or_gt_of_ne hy with hn | hp
  · have hs := last_prime_band_sine_phase hβ (neg_pos.mpr hn)
    change 0 < ∫ u in (0:ℝ)..L, Real.exp (z.re*u)*F u*Real.sin (-z.im*u) at hs
    simp only [neg_mul,Real.sin_neg,mul_neg,intervalIntegral.integral_neg,hi,neg_zero,
      lt_irrefl] at hs
  · exact (last_prime_band_sine_phase hβ hp).ne' hi

#print axioms last_prime_band_mellin_ne_zero
#print axioms last_prime_band_sine_phase
#print axioms last_prime_band_log_profile
#print axioms last_polynomial_of_spline_autocorrelation
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
