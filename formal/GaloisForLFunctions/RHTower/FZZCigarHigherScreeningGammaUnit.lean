import GaloisForLFunctions.RHTower.FZZCigarHigherScreeningGammaContinuation

/-!
# Exact cubic source factorization and Gamma-unit cancellation

At the cubic collision, the actual cleared original screening source factors
locally as an explicit rational function times a quotient of positive-argument
Gamma functions. The reciprocal Gamma recurrence is valid even at its zeros,
so the factorization retains the collision point.

The logarithm of the quotient is the additive defect of the odd function
`log Gamma (1+t) - log Gamma (1-t)`. Local analyticity and differentiated
reflection show that the quotient has value one and vanishing first and
second derivatives at the origin. Exact product and quotient differentiation
then gives rational mixed jets of orders two and three. Differentiating the
actual source factorization transfers both values to the original cleared
source: `-12288*pi` and `16176*pi`, respectively.

The original marked and unmarked finite-part cutoff values still require an
exact cutoff-to-jet comparison. No Ward identity or RH conclusion is claimed.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private theorem reciprocal_gamma_analytic (r : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => (Real.Gamma s)⁻¹) r := by
  have hc := Complex.differentiable_one_div_Gamma.analyticAt (r : ℂ)
  convert! hc.re_ofReal using 1
  simp only [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]

private theorem positive_gamma_analytic (r : ℝ) (hr : 0 < r) :
    AnalyticAt ℝ Real.Gamma r := by
  have h := (reciprocal_gamma_analytic r).inv (inv_ne_zero (Real.Gamma_pos_of_pos hr).ne')
  convert! h using 1
  ext s
  simp

def fzzScreeningHigherGammaOddLog (t : ℝ) : ℝ :=
  Real.log (Real.Gamma (1+t))-Real.log (Real.Gamma (1-t))

def fzzScreeningHigherGammaLogUnit (a b : ℝ) : ℝ :=
  fzzScreeningHigherGammaOddLog (a/2)+fzzScreeningHigherGammaOddLog (b/2)-
    fzzScreeningHigherGammaOddLog ((a+b)/2)

def fzzScreeningHigherGammaExpUnit (a b : ℝ) : ℝ :=
  Real.exp (fzzScreeningHigherGammaLogUnit a b)

def fzzScreeningHigherGammaUnit (a b : ℝ) : ℝ :=
  Real.Gamma (1-(a+b)/2)*Real.Gamma (1+a/2)*Real.Gamma (1+b/2)/
    (Real.Gamma (1+(a+b)/2)*Real.Gamma (1-a/2)*Real.Gamma (1-b/2))

private theorem odd_log_analytic (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
    AnalyticAt ℝ fzzScreeningHigherGammaOddLog t := by
  have hp : 0 < 1+t := by linarith [ht.1]
  have hm : 0 < 1-t := by linarith [ht.2]
  have h1 : AnalyticAt ℝ (fun s : ℝ => 1+s) t := by fun_prop
  have h2 : AnalyticAt ℝ (fun s : ℝ => 1-s) t := by fun_prop
  exact (((positive_gamma_analytic (1+t) hp).comp_of_eq h1 rfl).log
    (Real.Gamma_pos_of_pos hp)).sub
      (((positive_gamma_analytic (1-t) hm).comp_of_eq h2 rfl).log (Real.Gamma_pos_of_pos hm))

private theorem odd_log_reflect (t : ℝ) :
    fzzScreeningHigherGammaOddLog (-t) = -fzzScreeningHigherGammaOddLog t := by
  unfold fzzScreeningHigherGammaOddLog
  simp only [← sub_eq_add_neg, sub_neg_eq_add]
  ring

private theorem odd_log_deriv_even : Function.Even (deriv fzzScreeningHigherGammaOddLog) := by
  intro x
  have he : (fun y : ℝ => fzzScreeningHigherGammaOddLog (-y)) =
      fun y : ℝ => -fzzScreeningHigherGammaOddLog y := funext odd_log_reflect
  have h := congrArg (fun f : ℝ → ℝ => deriv f x) he
  rw [deriv_comp_neg] at h
  have hn : deriv (fun y : ℝ => -fzzScreeningHigherGammaOddLog y) x =
      -deriv fzzScreeningHigherGammaOddLog x := by
    change deriv (-fzzScreeningHigherGammaOddLog) x = _
    rw [deriv.neg]
  rw [hn] at h
  linarith

private theorem odd_log_second_zero : deriv (deriv fzzScreeningHigherGammaOddLog) 0 = 0 := by
  have he : (fun y : ℝ => deriv fzzScreeningHigherGammaOddLog (-y)) =
      deriv fzzScreeningHigherGammaOddLog := funext odd_log_deriv_even
  have h := congrArg (fun f : ℝ → ℝ => deriv f 0) he
  rw [deriv_comp_neg, neg_zero] at h
  linarith

private theorem log_unit_axes (a : ℝ) :
    fzzScreeningHigherGammaLogUnit a 0 = 0 ∧ fzzScreeningHigherGammaLogUnit 0 a = 0 := by
  simp [fzzScreeningHigherGammaLogUnit, fzzScreeningHigherGammaOddLog]


private theorem log_unit_hasDeriv_right (a b : ℝ)
    (hb : b/2 ∈ Ioo (-1) 1) (hs : (a+b)/2 ∈ Ioo (-1) 1) :
    HasDerivAt (fun s => fzzScreeningHigherGammaLogUnit a s)
      ((deriv fzzScreeningHigherGammaOddLog (b/2)-
        deriv fzzScreeningHigherGammaOddLog ((a+b)/2))/2) b := by
  have h1 := (odd_log_analytic (b/2) hb).differentiableAt.hasDerivAt.comp b
    ((hasDerivAt_id b).div_const 2)
  have h2 := (odd_log_analytic ((a+b)/2) hs).differentiableAt.hasDerivAt.comp b
    (((hasDerivAt_id b).const_add a).div_const 2)
  convert (h1.const_add (fzzScreeningHigherGammaOddLog (a/2))).sub h2 using 1 <;> first | rfl | ring

private theorem exp_unit_right_deriv_zero (a : ℝ) (ha : a ∈ Ioo (-1) 1) :
    deriv (fun b => fzzScreeningHigherGammaExpUnit a b) 0 =
      (deriv fzzScreeningHigherGammaOddLog 0-deriv fzzScreeningHigherGammaOddLog (a/2))/2 := by
  have h := (log_unit_hasDeriv_right a 0 (by norm_num)
    (by constructor <;> linarith [ha.1,ha.2])).exp
  have hz := (log_unit_axes a).1
  simpa only [fzzScreeningHigherGammaExpUnit, hz, Real.exp_zero, one_mul, zero_div, add_zero]
    using h.deriv

private theorem exp_unit_mixed_zero :
    deriv (fun a => deriv (fun b => fzzScreeningHigherGammaExpUnit a b) 0) 0 = 0 := by
  have he : (fun a => deriv (fun b => fzzScreeningHigherGammaExpUnit a b) 0) =ᶠ[𝓝 0]
      fun a => (deriv fzzScreeningHigherGammaOddLog 0-deriv fzzScreeningHigherGammaOddLog (a/2))/2 := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-1) 1)] with a ha
    exact exp_unit_right_deriv_zero a ha
  rw [he.deriv_eq]
  have hd : HasDerivAt (deriv fzzScreeningHigherGammaOddLog) 0 0 := by
    have h := (odd_log_analytic 0 (by norm_num)).deriv.differentiableAt.hasDerivAt
    rwa [odd_log_second_zero] at h
  have hc := hd.comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).div_const 2) (by simp)
  have h := ((hasDerivAt_const 0 (deriv fzzScreeningHigherGammaOddLog 0)).sub hc).div_const 2
  simpa using h.deriv

private theorem gamma_unit_eq_exp (a b : ℝ)
    (ha : a ∈ Ioo (-1/2) (1/2)) (hb : b ∈ Ioo (-1/2) (1/2)) :
    fzzScreeningHigherGammaUnit a b = fzzScreeningHigherGammaExpUnit a b := by
  have ha1 := Real.Gamma_pos_of_pos (show 0 < 1+a/2 by linarith [ha.1])
  have ha2 := Real.Gamma_pos_of_pos (show 0 < 1-a/2 by linarith [ha.2])
  have hb1 := Real.Gamma_pos_of_pos (show 0 < 1+b/2 by linarith [hb.1])
  have hb2 := Real.Gamma_pos_of_pos (show 0 < 1-b/2 by linarith [hb.2])
  have hs1 := Real.Gamma_pos_of_pos (show 0 < 1+(a+b)/2 by linarith [ha.1,hb.1])
  have hs2 := Real.Gamma_pos_of_pos (show 0 < 1-(a+b)/2 by linarith [ha.2,hb.2])
  unfold fzzScreeningHigherGammaExpUnit fzzScreeningHigherGammaLogUnit
    fzzScreeningHigherGammaOddLog fzzScreeningHigherGammaUnit
  simp only [Real.exp_sub, Real.exp_add, Real.exp_log ha1, Real.exp_log ha2,
    Real.exp_log hb1, Real.exp_log hb2, Real.exp_log hs1, Real.exp_log hs2]
  field_simp

/-- The actual positive-argument Gamma quotient has no mixed second response at the cubic origin. -/
theorem fzzScreeningHigherGammaUnit_mixed_second_zero :
    deriv (fun a => deriv (fun b => fzzScreeningHigherGammaUnit a b) 0) 0 = 0 := by
  have he : (fun a => deriv (fun b => fzzScreeningHigherGammaUnit a b) 0) =ᶠ[𝓝 0]
      fun a => deriv (fun b => fzzScreeningHigherGammaExpUnit a b) 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-1/2) (1/2))] with a ha
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-1/2) (1/2))] with b hb
    exact gamma_unit_eq_exp a b ha hb
  rw [he.deriv_eq]
  exact exp_unit_mixed_zero

/-- Along either axis the actual Gamma quotient has value one and vanishing first and second jets. -/
theorem fzzScreeningHigherGammaUnit_axis_jets :
    fzzScreeningHigherGammaUnit 0 0 = 1 ∧
    deriv (fun a => fzzScreeningHigherGammaUnit a 0) 0 = 0 ∧
    deriv (deriv (fun a => fzzScreeningHigherGammaUnit a 0)) 0 = 0 ∧
    deriv (fun b => fzzScreeningHigherGammaUnit 0 b) 0 = 0 ∧
    deriv (deriv (fun b => fzzScreeningHigherGammaUnit 0 b)) 0 = 0 := by
  have ha : (fun a => fzzScreeningHigherGammaUnit a 0) =ᶠ[𝓝 0] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-1/2) (1/2))] with a ha
    rw [gamma_unit_eq_exp a 0 ha (by norm_num), fzzScreeningHigherGammaExpUnit,
      (log_unit_axes a).1, Real.exp_zero]
  have hb : (fun b => fzzScreeningHigherGammaUnit 0 b) =ᶠ[𝓝 0] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-1/2) (1/2))] with b hb
    rw [gamma_unit_eq_exp 0 b (by norm_num) hb, fzzScreeningHigherGammaExpUnit,
      (log_unit_axes b).2, Real.exp_zero]
  have hz : deriv (fun _ : ℝ => (1:ℝ)) = fun _ => (0:ℝ) := by
    funext x
    simp
  refine ⟨ha.eq_of_nhds, ?_, ?_, ?_, ?_⟩
  · rw [ha.deriv_eq, deriv_const]
  · rw [ha.deriv.deriv_eq, hz, deriv_const]
  · rw [hb.deriv_eq, deriv_const]
  · rw [hb.deriv.deriv_eq, hz, deriv_const]



/-- Rational factor left by the exact Gamma shifts at the cubic collision. -/
def fzzScreeningHigherGammaRational (a b : ℝ) : ℝ :=
  let v := (a+b)/2
  64*Real.pi*v*((v-1)*(v-2)*(v-3)*(v-4))^2 /
    ((1-a/2)*(2-a/2)*(1-b/2)*(2-b/2))

private theorem real_reciprocal_gamma_shift (s : ℝ) :
    (Real.Gamma s)⁻¹ = s*(Real.Gamma (s+1))⁻¹ := by
  have h := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (s:ℂ)
  have hc := Complex.Gamma_ofReal (s+1)
  rw [Complex.ofReal_add, Complex.ofReal_one] at hc
  rw [Complex.Gamma_ofReal, hc] at h
  exact_mod_cast h

private theorem gamma_shift_two (s : ℝ) (hs : 0 < s) :
    Real.Gamma (s+2) = s*(s+1)*Real.Gamma s := by
  have h : Real.Gamma (s+2) = (s+1)*Real.Gamma (s+1) := by
    convert Real.Gamma_add_one (show s+1 ≠ 0 by linarith) using 1; congr 1; ring
  rw [h, Real.Gamma_add_one hs.ne']
  ring

private theorem gamma_shift_four (s : ℝ) (hs : 0 < s) :
    Real.Gamma (s+4) = s*(s+1)*(s+2)*(s+3)*Real.Gamma s := by
  have h := gamma_shift_two (s+2) (by linarith)
  rw [show s+2+2=s+4 by ring, show s+2+1=s+3 by ring,
    gamma_shift_two s hs] at h
  rw [h]
  ring

private theorem cubic_gamma_rational_factorization (a b : ℝ)
    (ha : a ∈ Ioo (-1/2) (1/2)) (hb : b ∈ Ioo (-1/2) (1/2)) :
    fzzScreeningHigherClearedGamma (-6+a) (-6+b) =
      fzzScreeningHigherGammaRational a b*fzzScreeningHigherGammaUnit a b := by
  let v := (a+b)/2
  have hv : 0 < 1-v := by dsimp [v]; linarith [ha.2,hb.2]
  have hg : Real.Gamma (5-v) = (1-v)*(2-v)*(3-v)*(4-v)*Real.Gamma (1-v) := by
    convert gamma_shift_four (1-v) hv using 1 <;> congr 1 <;> first | rfl | ring
  have hga : Real.Gamma (3-a/2) = (1-a/2)*(2-a/2)*Real.Gamma (1-a/2) := by
    convert gamma_shift_two (1-a/2) (by linarith [ha.2]) using 1 <;> congr 1 <;> first | rfl | ring
  have hgb : Real.Gamma (3-b/2) = (1-b/2)*(2-b/2)*Real.Gamma (1-b/2) := by
    convert gamma_shift_two (1-b/2) (by linarith [hb.2]) using 1 <;> congr 1 <;> first | rfl | ring
  have h0 : (Real.Gamma (-4+v))⁻¹ = (-4+v)*(Real.Gamma (-3+v))⁻¹ := by
    convert real_reciprocal_gamma_shift (-4+v) using 1 <;> congr 1 <;> first | rfl | ring
  have h1 : (Real.Gamma (-3+v))⁻¹ = (-3+v)*(Real.Gamma (-2+v))⁻¹ := by
    convert real_reciprocal_gamma_shift (-3+v) using 1 <;> congr 1 <;> first | rfl | ring
  have h2 : (Real.Gamma (-2+v))⁻¹ = (-2+v)*(Real.Gamma (-1+v))⁻¹ := by
    convert real_reciprocal_gamma_shift (-2+v) using 1 <;> congr 1 <;> first | rfl | ring
  have h3 : (Real.Gamma (-1+v))⁻¹ = (-1+v)*(Real.Gamma v)⁻¹ := by
    convert real_reciprocal_gamma_shift (-1+v) using 1 <;> congr 1 <;> first | rfl | ring
  have h4 : (Real.Gamma v)⁻¹ = v*(Real.Gamma (1+v))⁻¹ := by
    convert real_reciprocal_gamma_shift v using 1 <;> congr 1 <;> first | rfl | ring
  unfold fzzScreeningHigherClearedGamma
  rw [show -(-6+a)/2-(-6+b)/2-1=5-v by dsimp [v]; ring,
    show 4+(-6+a)/2=1+a/2 by ring, show 4+(-6+b)/2=1+b/2 by ring,
    show -(-6+a)/2=3-a/2 by ring, show -(-6+b)/2=3-b/2 by ring,
    show 2+(-6+a)/2+(-6+b)/2=-4+v by dsimp [v]; ring]
  rw [hg,hga,hgb,h0,h1,h2,h3,h4]
  unfold fzzScreeningHigherGammaRational fzzScreeningHigherGammaUnit
  change _ = (64*Real.pi*v*((v-1)*(v-2)*(v-3)*(v-4))^2 /
    ((1-a/2)*(2-a/2)*(1-b/2)*(2-b/2))) *
    (Real.Gamma (1-v)*Real.Gamma (1+a/2)*Real.Gamma (1+b/2)/
      (Real.Gamma (1+v)*Real.Gamma (1-a/2)*Real.Gamma (1-b/2)))
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Exact local factorization retains the collision point and the actual Gamma quotient. -/
theorem fzzScreeningHigherClearedGamma_cubic_factorization :
    (fun p : ℝ × ℝ => fzzScreeningHigherClearedGamma (-6+p.1) (-6+p.2)) =ᶠ[𝓝 (0,0)]
      fun p => fzzScreeningHigherGammaRational p.1 p.2 * fzzScreeningHigherGammaUnit p.1 p.2 := by
  have hn : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0),
      p ∈ Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioo (-1/2 : ℝ) (1/2) :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds (by norm_num)
  filter_upwards [hn] with p hp
  exact cubic_gamma_rational_factorization p.1 p.2 hp.1 hp.2



/-- The exact original cleared source has the same local rational-times-Gamma-unit factorization. -/
theorem fzzScreeningHigherClearedSource_cubic_factorization :
    (fun p : ℝ × ℝ => fzzScreeningHigherClearedSource (-6+p.1) (-6+p.2)) =ᶠ[𝓝 (0,0)]
      fun p => fzzScreeningHigherGammaRational p.1 p.2 * fzzScreeningHigherGammaUnit p.1 p.2 := by
  have hn : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0),
      p ∈ Ioo (-1/2 : ℝ) (1/2) ×ˢ Ioo (-1/2 : ℝ) (1/2) :=
    (isOpen_Ioo.prod isOpen_Ioo).mem_nhds (by norm_num)
  filter_upwards [fzzScreeningHigherClearedGamma_cubic_factorization, hn] with p hp hdom
  obtain ⟨u,v,hu,hv⟩ := (fzzScreeningHigherPower_chart_iff (-6+p.1) (-6+p.2)).mpr
    ⟨by linarith [hdom.1.1], by linarith [hdom.2.1], by linarith [hdom.1.2,hdom.2.2]⟩
  calc
    fzzScreeningHigherClearedSource (-6+p.1) (-6+p.2) =
        fzzScreeningHigherClearedGamma (-6+p.1) (-6+p.2) := by
      rw [← hu, ← hv]
      exact fzzScreeningHigherClearedSource_eq_gamma u v
    _ = _ := hp


private def P (t : ℝ) := (t-1)*(t-2)*(t-3)*(t-4)
private def P1 (t : ℝ) := 4*t^3-30*t^2+70*t-50
private def P2 (t : ℝ) := 12*t^2-60*t+70
private def F (t : ℝ) := t*(P t)^2
private def F1 (t : ℝ) := (P t)^2+2*t*P t*P1 t
private def F2 (t : ℝ) := 4*P t*P1 t+2*t*((P1 t)^2+P t*P2 t)
private def D (t : ℝ) := (1-t/2)*(2-t/2)
private def D1 (t : ℝ) := -3/2+t/2
private def G (t : ℝ) := 1/D t
private def G1 (t : ℝ) := -D1 t/(D t)^2

private theorem hP (t : ℝ) : HasDerivAt P (P1 t) t := by
  have h := ((((hasDerivAt_id t).sub_const 1).mul ((hasDerivAt_id t).sub_const 2)).mul
    ((hasDerivAt_id t).sub_const 3)).mul ((hasDerivAt_id t).sub_const 4)
  exact h.congr_deriv (by dsimp [P1]; ring)
private theorem hP1 (t : ℝ) : HasDerivAt P1 (P2 t) t := by
  have h := (((((hasDerivAt_id t).pow 3).const_mul 4).sub
    (((hasDerivAt_id t).pow 2).const_mul 30)).add ((hasDerivAt_id t).const_mul 70)).sub_const 50
  exact h.congr_deriv (by dsimp [P2]; ring)
private theorem hF (t : ℝ) : HasDerivAt F (F1 t) t := by
  exact ((hasDerivAt_id t).mul ((hP t).pow 2)).congr_deriv (by dsimp [F1]; ring)
private theorem hF1 (t : ℝ) : HasDerivAt F1 (F2 t) t := by
  have h := ((hP t).pow 2).add (((((hasDerivAt_id t).const_mul 2).mul (hP t))).mul (hP1 t))
  exact h.congr_deriv (by dsimp [F2]; ring)
private theorem hF2 : HasDerivAt F2 25080 0 := by
  have h2 : DifferentiableAt ℝ P2 0 := by unfold P2; fun_prop
  have h := (((hP 0).const_mul 4).mul (hP1 0)).add
    (((hasDerivAt_id (0:ℝ)).const_mul 2).mul
      (((hP1 0).pow 2).add ((hP 0).mul h2.hasDerivAt)))
  exact h.congr_deriv (by norm_num [P,P1,P2])
private theorem hD (t : ℝ) : HasDerivAt D (D1 t) t := by
  have h := ((hasDerivAt_const t (1:ℝ)).sub ((hasDerivAt_id t).div_const 2)).mul
    ((hasDerivAt_const t (2:ℝ)).sub ((hasDerivAt_id t).div_const 2))
  exact h.congr_deriv (by dsimp [D1]; ring)
private theorem hG (t : ℝ) (ht : t ∈ Ioo (-1) 1) : HasDerivAt G (G1 t) t := by
  have hn : D t ≠ 0 := mul_ne_zero (by dsimp; linarith [ht.2]) (by dsimp; linarith [ht.2])
  exact ((hasDerivAt_const t (1:ℝ)).div (hD t) hn).congr_deriv (by dsimp [G1]; ring)
private theorem hG1 : HasDerivAt G1 (7/16) 0 := by
  have hd1 : HasDerivAt D1 (1/2) 0 := by
    exact (((hasDerivAt_id (0:ℝ)).div_const 2).const_add (-3/2)).congr_deriv (by ring)
  have h := hd1.neg.div ((hD 0).pow 2) (by norm_num [D])
  exact h.congr_deriv (by norm_num [D,D1])

private theorem rational_product (a b : ℝ) :
    fzzScreeningHigherGammaRational a b = 64*Real.pi*F ((a+b)/2)*G a*G b := by
  dsimp [fzzScreeningHigherGammaRational,F,P,G,D]
  simp only [div_eq_mul_inv,mul_inv]
  ring

private def B (a : ℝ) := 64*Real.pi*G a*(F1 (a/2)/4+3*F (a/2)/8)
private def B1 (a : ℝ) :=
  64*Real.pi*(G1 a*(F1 (a/2)/4+3*F (a/2)/8)+
    G a*(F2 (a/2)/8+3*F1 (a/2)/16))

private theorem rational_right_hasDeriv (a : ℝ) :
    HasDerivAt (fun b => fzzScreeningHigherGammaRational a b) (B a) 0 := by
  have hf := (hF (a/2)).comp_of_eq 0
    (((hasDerivAt_id (0:ℝ)).const_add a).div_const 2) (by simp)
  have h := (((hf.const_mul (64*Real.pi)).mul_const (G a)).mul
    (hG 0 (by norm_num))).congr_deriv (show
      (64*Real.pi*(F1 (a/2)*(1/2))*G a)*G 0+
        (64*Real.pi*F ((a+0)/2)*G a)*G1 0 = B a by
          norm_num [G,G1,D,D1,B]; ring)
  have he : (fun b => fzzScreeningHigherGammaRational a b) =
      fun b => 64*Real.pi*F ((a+b)/2)*G a*G b := funext (rational_product a)
  rw [he]
  exact h

private theorem rational_right (a : ℝ) :
    deriv (fun b => fzzScreeningHigherGammaRational a b) 0 = B a :=
  (rational_right_hasDeriv a).deriv

private theorem hB (a : ℝ) (ha : a ∈ Ioo (-1) 1) : HasDerivAt B (B1 a) a := by
  have h1 := (hF1 (a/2)).comp a ((hasDerivAt_id a).div_const 2)
  have h0 := (hF (a/2)).comp a ((hasDerivAt_id a).div_const 2)
  have h := (((hG a ha).const_mul (64*Real.pi)).mul
    ((h1.div_const 4).add ((h0.const_mul 3).div_const 8)))
  exact h.congr_deriv (by dsimp [B1]; ring)

private theorem hB1 : HasDerivAt B1 (16176*Real.pi) 0 := by
  have h0 := (hF 0).comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).div_const 2) (by simp)
  have h1 := (hF1 0).comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).div_const 2) (by simp)
  have h2 := hF2.comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).div_const 2) (by simp)
  have h := ((hG1.mul ((h1.div_const 4).add ((h0.const_mul 3).div_const 8))).add
    ((hG 0 (by norm_num)).mul ((h2.div_const 8).add ((h1.const_mul 3).div_const 16)))).const_mul
      (64*Real.pi)
  exact h.congr_deriv (by norm_num [F,F1,F2,P,P1,P2,G,G1,D,D1]; ring)

/-- Exact mixed quadratic response of the rational factor at the cubic collision. -/
theorem fzzScreeningHigherGammaRational_mixed_second :
    deriv (fun a => deriv (fun b => fzzScreeningHigherGammaRational a b) 0) 0 =
      -12288*Real.pi := by
  simp_rw [rational_right]
  rw [(hB 0 (by norm_num)).deriv]
  norm_num [B1,F,F1,F2,P,P1,P2,G,G1,D,D1]
  ring

/-- Exact mixed cubic response of the rational factor at the cubic collision. -/
theorem fzzScreeningHigherGammaRational_mixed_third :
    deriv (deriv (fun a => deriv (fun b => fzzScreeningHigherGammaRational a b) 0)) 0 =
      16176*Real.pi := by
  simp_rw [rational_right]
  have he : deriv B =ᶠ[𝓝 0] B1 := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-1) 1)] with a ha
    exact (hB a ha).deriv
  rw [he.deriv_eq]
  exact hB1.deriv


private def W (a : ℝ) :=
  (deriv fzzScreeningHigherGammaOddLog 0-deriv fzzScreeningHigherGammaOddLog (a/2))/2
private def W1 (a : ℝ) := -deriv (deriv fzzScreeningHigherGammaOddLog) (a/2)/4
private def X (a : ℝ) := fzzScreeningHigherGammaRational a 0
private def X1 (a : ℝ) :=
  64*Real.pi*(F1 (a/2)/2*G a+F (a/2)*G1 a)*G 0
private def C (a : ℝ) := X a*W a
private def C1 (a : ℝ) := X1 a*W a+X a*W1 a

private theorem hW (a : ℝ) (ha : a ∈ Ioo (-1) 1) : HasDerivAt W (W1 a) a := by
  have h := ((odd_log_analytic (a/2) (by constructor <;> linarith [ha.1,ha.2])).deriv.differentiableAt.hasDerivAt).comp a ((hasDerivAt_id a).div_const 2)
  exact (((hasDerivAt_const a (deriv fzzScreeningHigherGammaOddLog 0)).sub h).div_const 2).congr_deriv (by dsimp [W1]; ring)
private theorem hW1 : DifferentiableAt ℝ W1 0 := by
  have h := (odd_log_analytic 0 (by norm_num)).deriv.deriv.differentiableAt.hasDerivAt
  have hc := h.comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).div_const 2) (by simp)
  exact (hc.neg.div_const 4).differentiableAt
private theorem W_zero : W 0 = 0 := by simp [W]
private theorem W1_zero : W1 0 = 0 := by simp [W1,odd_log_second_zero]
private theorem X_zero : X 0 = 0 := by simp [X,rational_product,F]
private theorem hX (a : ℝ) (ha : a ∈ Ioo (-1) 1) : HasDerivAt X (X1 a) a := by
  have hf := (hF (a/2)).comp a ((hasDerivAt_id a).div_const 2)
  have h := (((hf.const_mul (64*Real.pi)).mul (hG a ha)).mul_const (G 0))
  have he : X = fun a => 64*Real.pi*F (a/2)*G a*G 0 := by
    funext a
    simp only [X,rational_product,add_zero]
  rw [he]
  exact h.congr_deriv (by dsimp [X1]; ring)
private theorem hX1 : DifferentiableAt ℝ X1 0 := by
  have hf := (hF 0).comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).div_const 2) (by simp)
  have hf1 := (hF1 0).comp_of_eq 0 ((hasDerivAt_id (0:ℝ)).div_const 2) (by simp)
  exact ((((hf1.div_const 2).mul (hG 0 (by norm_num))).add (hf.mul hG1)).const_mul
    (64*Real.pi) |>.mul_const (G 0)).differentiableAt
private theorem hC (a : ℝ) (ha : a ∈ Ioo (-1) 1) : HasDerivAt C (C1 a) a :=
  (hX a ha).mul (hW a ha)
private theorem hC1 : HasDerivAt C1 0 0 := by
  change HasDerivAt (fun a : ℝ => X1 a*W a+X a*W1 a) (0:ℝ) (0:ℝ)
  have h := (hX1.hasDerivAt.fun_mul (hW 0 (by norm_num))).fun_add
    ((hX 0 (by norm_num)).fun_mul hW1.hasDerivAt)
  exact h.congr_deriv (by simp only [W_zero,W1_zero,X_zero,mul_zero,zero_mul,add_zero])

private def sourceRight (a : ℝ) :=
  deriv (fun b => fzzScreeningHigherClearedSource (-6+a) (-6+b)) 0

private theorem source_right_germ : sourceRight =ᶠ[𝓝 0] fun a => B a+C a := by
  have hs := fzzScreeningHigherClearedSource_cubic_factorization.curry_nhds
  filter_upwards [hs,isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-1/2) (1/2))]
    with a haeq ha
  have hu : HasDerivAt (fun b => fzzScreeningHigherGammaExpUnit a b) (W a) 0 := by
    have h := (log_unit_hasDeriv_right a 0 (by norm_num)
      (by constructor <;> linarith [ha.1,ha.2])).exp
    simpa only [fzzScreeningHigherGammaExpUnit,W,(log_unit_axes a).1,
      Real.exp_zero,one_mul,zero_div,add_zero] using h
  have he : (fun b => fzzScreeningHigherGammaUnit a b) =ᶠ[𝓝 0]
      fun b => fzzScreeningHigherGammaExpUnit a b := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-1/2) (1/2))]
      with b hb
    exact gamma_unit_eq_exp a b ha hb
  have hv : fzzScreeningHigherGammaUnit a 0 = 1 := by
    rw [he.eq_of_nhds,fzzScreeningHigherGammaExpUnit,(log_unit_axes a).1,Real.exp_zero]
  have h := ((rational_right_hasDeriv a).fun_mul (hu.congr_of_eventuallyEq he)).congr_of_eventuallyEq haeq
  simpa only [sourceRight,C,X,hv,mul_one] using h.deriv

/-- The original cleared source has the exact mixed quadratic jet at its cubic collision. -/
theorem fzzScreeningHigherClearedSource_cubic_second_value :
    deriv (fun a => deriv (fun b => fzzScreeningHigherClearedSource (-6+a) (-6+b)) 0) 0 =
      -12288*Real.pi := by
  change deriv sourceRight 0 = _
  rw [source_right_germ.deriv_eq,((hB 0 (by norm_num)).fun_add (hC 0 (by norm_num))).deriv]
  simp only [C1,W_zero,W1_zero,mul_zero,add_zero]
  norm_num [B1,F,F1,F2,P,P1,P2,G,G1,D,D1]
  ring

/-- The original cleared source has the exact mixed cubic jet at its cubic collision. -/
theorem fzzScreeningHigherClearedSource_cubic_third_value :
    deriv (deriv (fun a => deriv (fun b =>
      fzzScreeningHigherClearedSource (-6+a) (-6+b)) 0)) 0 = 16176*Real.pi := by
  change deriv (deriv sourceRight) 0 = _
  have he : deriv sourceRight =ᶠ[𝓝 0] fun a => B1 a+C1 a := by
    filter_upwards [source_right_germ.deriv,
      isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-1) 1)] with a he ha
    rw [he]
    exact ((hB a ha).fun_add (hC a ha)).deriv
  rw [he.deriv_eq]
  simpa using (hB1.fun_add hC1).deriv

end GaloisForLFunctions.RHTower
