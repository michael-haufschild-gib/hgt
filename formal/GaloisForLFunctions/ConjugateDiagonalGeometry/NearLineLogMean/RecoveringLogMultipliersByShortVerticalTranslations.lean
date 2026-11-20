import GaloisForLFunctions.HTGeometry.GeneralizedDirichletMeanValue
import GaloisForLFunctions.RHTower.Sieve.DirichletPoly
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# Recovering a logarithmic multiplier from one-sided vertical translations

On a short arc around 1, the truncated logarithm recovers the frequency
of each exponential mode from its phase. Evaluation of that polynomial
in the translation operator gives a finite one-sided differentiation
formula. Its remainder can have any prescribed order while the signed
steps can all be chosen towards the interior of the observation window.
-/

noncomputable section
open Finset Complex Polynomial MeasureTheory
open _root_.HTGeometry
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Taylor polynomial for log X at X=1, of order m. -/
def translationLog (m : ℕ) : Polynomial ℂ :=
  ∑ j ∈ range (m+1), C ((-1:ℂ)^(j+1)/(j:ℂ))*(X-1)^j

private theorem eval_translationLog (m : ℕ) (z : ℂ) :
    (translationLog m).eval z = Complex.logTaylor (m+1) (z-1) := by
  simp only [translationLog,eval_finsetSum,eval_mul,eval_C,eval_pow,eval_sub,eval_X,
    eval_one,Complex.logTaylor]
  exact sum_congr rfl fun _ _ => by ring

/-- A single signed phase with absolute angle at most one half gives
the frequency multiplier up to an error of order m+1. -/
theorem translationLog_phase_remainder (m : ℕ) {x : ℝ} (hx : |x| ≤ 1/2) :
    ‖(x:ℂ)*I-(translationLog m).eval (exp ((x:ℂ)*I))‖ ≤ 2*|x|^(m+1) := by
  let w := (x:ℂ)*I
  let z := exp w-1
  have hz : ‖z‖ ≤ |x| := by
    simpa only [z,w,mul_comm (x:ℂ) I,Real.norm_eq_abs] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x:=x))
  have hx' := abs_le.mp hx
  have hw : w.im = x := by simp [w]
  have hlog : log (1+z)=w := by
    rw [show 1+z=exp w by dsimp [z]; ring,Complex.log_exp]
    · rw [hw]; linarith only [hx'.1,Real.pi_gt_three]
    · rw [hw]; linarith only [hx'.2,Real.pi_gt_three]
  have hhalf := hz.trans hx
  have hp : 0 < 1-‖z‖ := by linarith only [hhalf]
  have H := Complex.norm_log_sub_logTaylor_le m (z:=z) (sub_pos.mp hp)
  rw [hlog] at H
  rw [eval_translationLog]
  refine H.trans ?_
  have hi : (1-‖z‖)⁻¹ ≤ 2 := by
    rw [←one_div,div_le_iff₀ hp]
    linarith only [hhalf]
  have hj : (1:ℝ) ≤ (m:ℝ)+1 := by linarith only [Nat.cast_nonneg (α:=ℝ) m]
  refine (div_le_self (mul_nonneg (pow_nonneg (norm_nonneg _) _) (inv_nonneg.mpr hp.le)) hj).trans ?_
  rw [mul_comm (2:ℝ)]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz _) hi (inv_nonneg.mpr hp.le)
    (pow_nonneg (abs_nonneg _) _)

/-- A unit exponential mode at a real frequency and height. -/
def verticalMode (freq t : ℝ) := exp (((t*freq:ℝ):ℂ)*I)

theorem genPoly_eq_verticalMode_sum (a : ℕ → ℂ) (freq : ℕ → ℝ) (S : Finset ℕ) (t : ℝ) :
    genPoly a freq S t = ∑ n ∈ S, a n*verticalMode (freq n) t := by
  apply sum_congr rfl
  intro n _
  unfold verticalMode
  congr 2
  push_cast
  ring

private theorem phase_shift (freq t h : ℝ) (j : ℕ) :
    verticalMode freq (t+j*h) = verticalMode freq t*(verticalMode freq h)^j := by
  unfold verticalMode
  rw [←Complex.exp_nat_mul,←exp_add]
  congr 1
  push_cast
  ring

private theorem packet_deriv (a : ℕ → ℂ) (freq : ℕ → ℝ) (S : Finset ℕ) (t : ℝ) :
    deriv (genPoly a freq S) t = ∑ n ∈ S, a n*verticalMode (freq n) t*((freq n:ℂ)*I) := by
  have he : genPoly a freq S = fun t => ∑ n ∈ S, a n*verticalMode (freq n) t :=
    funext (genPoly_eq_verticalMode_sum a freq S)
  rw [he]
  have H := HasDerivAt.fun_sum (u:=S) (fun n _ => (_root_.RHTower.Sieve.hasDerivAt_exp_phase (freq n) t).const_mul (a n))
  simpa only [verticalMode,mul_assoc] using H.deriv

theorem deriv_genPoly_as_packet (a : ℕ → ℂ) (freq : ℕ → ℝ) (S : Finset ℕ) :
    deriv (genPoly a freq S) = genPoly (fun n => (freq n:ℂ)*I*a n) freq S := by
  funext t
  rw [packet_deriv,genPoly_eq_verticalMode_sum]
  exact sum_congr rfl fun _ _ => by ring

/-- Applying a polynomial in vertical translation multiplies each
Dirichlet mode by the same polynomial evaluated at its one-step phase. -/
theorem polynomial_packet_translation (P : Polynomial ℂ) (a : ℕ → ℂ) (freq : ℕ → ℝ)
    (S : Finset ℕ) (t h : ℝ) :
    (∑ j ∈ P.support, P.coeff j*genPoly a freq S (t+j*h)) =
      ∑ n ∈ S, a n*verticalMode (freq n) t*P.eval (verticalMode (freq n) h) := by
  simp_rw [genPoly_eq_verticalMode_sum,mul_sum,phase_shift]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  rw [Polynomial.eval_eq_sum,Polynomial.sum,mul_sum]
  exact sum_congr rfl fun j _ => by ring

/-- A finite one-sided sample recovers the genuine vertical derivative
with uniform error in the height, both for forward and backward steps. -/
theorem short_translation_derivative_error (m : ℕ) (a : ℕ → ℂ) (freq : ℕ → ℝ)
    (S : Finset ℕ) (t h : ℝ) {B : ℝ} (hfreq : ∀ n ∈ S, |freq n| ≤ B)
    (hh : |h| * B ≤ 1/2) :
    ‖(h:ℂ)*deriv (genPoly a freq S) t -
        ∑ j ∈ (translationLog m).support, (translationLog m).coeff j*genPoly a freq S (t+j*h)‖ ≤
      (2*(|h| * B)^(m+1))*∑ n ∈ S, ‖a n‖ := by
  rw [polynomial_packet_translation,packet_deriv,mul_sum,←sum_sub_distrib,mul_sum]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
  have he : (h:ℂ)*(a n*verticalMode (freq n) t*((freq n:ℂ)*I))-
        a n*verticalMode (freq n) t*(translationLog m).eval (verticalMode (freq n) h) =
      a n*verticalMode (freq n) t*(((h*freq n:ℝ):ℂ)*I-(translationLog m).eval (verticalMode (freq n) h)) := by
    push_cast; ring
  have hx : |h*freq n| ≤ |h| * B := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hfreq n hn) (abs_nonneg _)
  have H := translationLog_phase_remainder m (hx.trans hh)
  have hp : ‖verticalMode (freq n) t‖=1 := Complex.norm_exp_ofReal_mul_I _
  rw [he,norm_mul,norm_mul,hp,mul_one,mul_comm (2*(|h| * B)^(m+1))]
  exact mul_le_mul_of_nonneg_left (H.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) hx _) (by norm_num))) (norm_nonneg _)

private theorem sampled_norm_sq {ι : Type*} {J : Finset ι} {g : ℂ} {v : ι → ℂ} {E : ℝ}
    (he : ‖g-∑ j ∈ J, v j‖ ≤ E) :
    ‖g‖^2 ≤ 2*J.card*(∑ j ∈ J, ‖v j‖^2)+2*E^2 := by
  have hg := (norm_le_norm_sub_add g (∑ j ∈ J, v j)).trans
    (add_le_add he (norm_sum_le J v))
  have hsq := pow_le_pow_left₀ (norm_nonneg g) hg 2
  have hc := sq_sum_le_card_mul_sum_sq (s:=J) (f:=fun j => ‖v j‖)
  nlinarith only [hsq,hc,sq_nonneg (E-∑ j ∈ J, ‖v j‖)]

/-- Every translated subinterval lies inside the observation window. Each
translated energy can therefore be bounded by the same observed integral. -/
theorem translated_sample_energy_on_subinterval {ι : Type*} {J : Finset ι} (c : ι → ℂ) (offset : ι → ℝ) (F G : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) {L R A D h E : ℝ} (hLR : L ≤ R)
    (hinside : ∀ j ∈ J, A ≤ L+offset j ∧ R+offset j ≤ D)
    (he : ∀ t, ‖(h:ℂ)*G t-∑ j ∈ J, c j*F (t+offset j)‖ ≤ E) :
    h^2*(∫ t in L..R, ‖G t‖^2) ≤
      2*J.card*(∑ j ∈ J, ‖c j‖^2)*(∫ t in A..D, ‖F t‖^2)+2*(R-L)*E^2 := by
  let Q (j : ι) (t : ℝ) := ‖c j‖^2*‖F (t+offset j)‖^2
  have hQ (j : ι) : Continuous (Q j) := by dsimp [Q]; fun_prop
  have hsum : Continuous (fun t => ∑ j ∈ J, Q j t) := by fun_prop
  have hpt (t : ℝ) : h^2*‖G t‖^2 ≤ 2*J.card*(∑ j ∈ J, Q j t)+2*E^2 := by
    simpa only [Q,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] using
      sampled_norm_sq (he t)
  have hi := intervalIntegral.integral_mono_on (μ:=volume) hLR
    (f:=fun t => h^2*‖G t‖^2) (g:=fun t => 2*J.card*(∑ j ∈ J, Q j t)+2*E^2)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) (fun t _ => hpt t)
  rw [intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _) (continuous_const.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum (fun j _ => (hQ j).intervalIntegrable _ _),
    intervalIntegral.integral_const,smul_eq_mul] at hi
  apply hi.trans
  have hone (j : ι) (hj : j ∈ J) : (∫ t in L..R, Q j t) ≤ ‖c j‖^2*(∫ t in A..D, ‖F t‖^2) := by
    dsimp only [Q]
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_add_right
      (f:=fun t => ‖F t‖^2)]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact intervalIntegral.integral_mono_interval (hinside j hj).1 (add_le_add_left hLR _)
      (hinside j hj).2 (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      ((hF.norm.pow 2).intervalIntegrable _ _)
  have H := mul_le_mul_of_nonneg_left (sum_le_sum hone) (by positivity : 0 ≤ 2*(J.card:ℝ))
  rw [←sum_mul] at H
  linarith only [H]

/-- Squared derivative energy on the original window, using forward shifts
on its left half and backward shifts on its right half. -/
theorem short_translation_window_energy (m : ℕ) (a : ℕ → ℂ) (freq : ℕ → ℝ)
    (S : Finset ℕ) {A D h B : ℝ} (hAD : A ≤ D) (hh : 0 ≤ h)
    (hfreq : ∀ n ∈ S, |freq n| ≤ B) (hsmall : h*B ≤ 1/2)
    (hfit : ∀ j ∈ (translationLog m).support, (j:ℝ)*h ≤ (D-A)/2) :
    h^2*(∫ t in A..D, ‖deriv (genPoly a freq S) t‖^2) ≤
      4*(translationLog m).support.card*(∑ j ∈ (translationLog m).support,
        ‖(translationLog m).coeff j‖^2)*(∫ t in A..D, ‖genPoly a freq S t‖^2)+
      2*(D-A)*((2*(h*B)^(m+1))*∑ n ∈ S, ‖a n‖)^2 := by
  let F := genPoly a freq S
  have hF : Continuous F := by unfold F genPoly; fun_prop
  have hG : Continuous (deriv F) := by
    change Continuous (fun t => deriv (genPoly a freq S) t)
    simp_rw [packet_deriv]
    unfold verticalMode
    fun_prop
  let M := (A+D)/2
  have hAM : A ≤ M := by dsimp [M]; linarith only [hAD]
  have hMD : M ≤ D := by dsimp [M]; linarith only [hAD]
  have hpos (j : ℕ) : 0 ≤ (j:ℝ)*h := mul_nonneg (Nat.cast_nonneg _) hh
  have hleft := translated_sample_energy_on_subinterval (J:=(translationLog m).support) (translationLog m).coeff
    (fun j : ℕ => (j:ℝ)*h) F (deriv F) hF hG hAM (A:=A) (D:=D) (h:=h)
    (fun j hj => ⟨by linarith only [hpos j],by dsimp [M]; linarith only [hfit j hj]⟩)
    (fun t => short_translation_derivative_error m a freq S t h hfreq (by rwa [abs_of_nonneg hh]))
  have hright := translated_sample_energy_on_subinterval (J:=(translationLog m).support) (translationLog m).coeff
    (fun j : ℕ => (j:ℝ)*(-h)) F (deriv F) hF hG hMD (A:=A) (D:=D) (h:=-h)
    (fun j hj => ⟨by dsimp [M]; rw [mul_neg]; linarith only [hfit j hj],
      by rw [mul_neg]; linarith only [hpos j]⟩)
    (fun t => short_translation_derivative_error m a freq S t (-h) hfreq
      (by rwa [abs_neg,abs_of_nonneg hh]))
  rw [abs_of_nonneg hh] at hleft
  rw [abs_neg,abs_of_nonneg hh,neg_sq] at hright
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ:=volume)
    (f:=fun t => ‖deriv (genPoly a freq S) t‖^2)
    ((hG.norm.pow 2).intervalIntegrable A M) ((hG.norm.pow 2).intervalIntegrable M D)
  rw [←hsplit]
  dsimp only [F] at hleft hright ⊢
  linarith only [hleft,hright]

/-- A family of exponential sums with frequencies at most X, coefficient
mass at most X^d and observation horizon at most X^l pays only X^4 in
derivative energy. The stencil order depends on d and l; the additive
remainder is at most eight on the original interval. -/
theorem derivative_energy_of_polynomial_size (d l : ℕ) (a : ℕ → ℂ) (freq : ℕ → ℝ)
    (S : Finset ℕ) {T X : ℝ} (hX : 2 ≤ X) (hT : 1 ≤ T) (hsize : T ≤ X^l)
    (hfreq : ∀ n ∈ S, |freq n| ≤ X) (ha : (∑ n ∈ S, ‖a n‖) ≤ X^d)
    (hfit : ∀ j ∈ (translationLog (d+l+1)).support, (j:ℝ) ≤ (T-1)/2) :
    (∫ t in (1:ℝ)..T, ‖deriv (genPoly a freq S) t‖^2) ≤
      (4*(translationLog (d+l+1)).support.card*(∑ j ∈ (translationLog (d+l+1)).support,
        ‖(translationLog (d+l+1)).coeff j‖^2))*X^4*
        (∫ t in (1:ℝ)..T, ‖genPoly a freq S t‖^2)+8 := by
  have hx : 0 < X := by linarith only [hX]
  have hx1 : 1 ≤ X := by linarith only [hX]
  let m := d+l+1
  let h := (X^2)⁻¹
  have hp : 0 ≤ h := inv_nonneg.mpr (sq_nonneg X)
  have hstep : h*X=X⁻¹ := by dsimp [h]; field_simp
  have hsmall : h*X ≤ 1/2 := by rw [hstep,←one_div]; exact one_div_le_one_div_of_le (by norm_num) hX
  have hshort : h ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hx1)
  have H := short_translation_window_energy m a freq S hT hp hfreq hsmall (fun j hj =>
    (mul_le_of_le_one_right (Nat.cast_nonneg j) hshort).trans (hfit j hj))
  let E := (2*(h*X)^(m+1))*∑ n ∈ S, ‖a n‖
  have hE : E ≤ 2/X^(l+2) := by
    dsimp only [E]
    rw [hstep]
    calc 2*X⁻¹^(m+1)*(∑ n ∈ S, ‖a n‖) ≤ 2*X⁻¹^(m+1)*X^d :=
          mul_le_mul_of_nonneg_left ha (by positivity)
      _ = 2/X^(l+2) := by
        rw [show m+1=d+(l+2) by dsimp [m]; omega,pow_add,inv_pow,inv_pow]
        field_simp
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hL : T-1 ≤ (X^l)^2 := by
    have hxl : 1 ≤ X^l := one_le_pow₀ hx1
    nlinarith only [hsize,hxl,sq_nonneg (X^l-1)]
  have herr : X^4*(2*(T-1)*E^2) ≤ 8 := by
    calc _ ≤ X^4*(2*(X^l)^2*(2/X^(l+2))^2) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hL zero_le_two)
              (pow_le_pow_left₀ hE0 hE 2) (sq_nonneg _) (by positivity)) (by positivity)
      _ = 8 := by rw [pow_add]; field_simp; ring
  have hcancel : X^4*h^2=1 := by dsimp only [h]; field_simp
  have hscaled := mul_le_mul_of_nonneg_left H (by positivity : 0 ≤ X^4)
  rw [←mul_assoc,hcancel,one_mul,mul_add] at hscaled
  dsimp only [m,E] at herr hscaled
  linarith only [hscaled,herr]

#print axioms polynomial_packet_translation
#print axioms short_translation_derivative_error
#print axioms short_translation_window_energy
#print axioms derivative_energy_of_polynomial_size

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
