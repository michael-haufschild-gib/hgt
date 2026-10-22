import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
/-! A rational clock envelope with linear growth for the N16 comparison.
A four-step positive derivative chain proves the hyperbolic inequality.
The constant-curvature inverse profile lies strictly above this envelope.
The actual varying-curvature inverse-source order is not asserted. -/

namespace RHTower.ThetaCuspDefect
open Set
noncomputable section

private def clockErrorZero (z : ℝ) : ℝ :=
  Real.exp (2*z)*(3*z^2-12*z+15)-(2*z^3+9*z^2+18*z+15)
private def clockErrorOne (z : ℝ) : ℝ :=
  Real.exp (2*z)*(6*z^2-18*z+18)-(6*z^2+18*z+18)
private def clockErrorTwo (z : ℝ) : ℝ :=
  Real.exp (2*z)*(12*z^2-24*z+18)-(12*z+18)
private def clockErrorThree (z : ℝ) : ℝ :=
  Real.exp (2*z)*(24*z^2-24*z+12)-12

private theorem clockErrorZero_deriv (z : ℝ) : HasDerivAt clockErrorZero (clockErrorOne z) z := by
  have h1 := hasDerivAt_id z
  have h2 := h1.pow 2
  have h3 := h1.pow 3
  have he := (h1.const_mul 2).exp
  convert! (he.mul (((h2.const_mul 3).sub (h1.const_mul 12)).add_const 15)).sub
    (((h3.const_mul 2).add (h2.const_mul 9) |>.add (h1.const_mul 18)).add_const 15) using 1
  simp only [Pi.pow_apply,Pi.sub_apply,id_eq]
  unfold clockErrorOne
  ring
private theorem clockErrorOne_deriv (z : ℝ) : HasDerivAt clockErrorOne (clockErrorTwo z) z := by
  have h1 := hasDerivAt_id z
  have h2 := h1.pow 2
  have he := (h1.const_mul 2).exp
  convert! (he.mul (((h2.const_mul 6).sub (h1.const_mul 18)).add_const 18)).sub
    (((h2.const_mul 6).add (h1.const_mul 18)).add_const 18) using 1
  simp only [Pi.pow_apply,Pi.sub_apply,id_eq]
  unfold clockErrorTwo
  ring
private theorem clockErrorTwo_deriv (z : ℝ) : HasDerivAt clockErrorTwo (clockErrorThree z) z := by
  have h1 := hasDerivAt_id z
  have h2 := h1.pow 2
  have he := (h1.const_mul 2).exp
  convert! (he.mul (((h2.const_mul 12).sub (h1.const_mul 24)).add_const 18)).sub
    ((h1.const_mul 12).add_const 18) using 1
  simp only [Pi.pow_apply,Pi.sub_apply,id_eq]
  unfold clockErrorThree
  ring
private theorem clockErrorThree_deriv (z : ℝ) :
    HasDerivAt clockErrorThree (48*z^2*Real.exp (2*z)) z := by
  have h1 := hasDerivAt_id z
  have h2 := h1.pow 2
  have he := (h1.const_mul 2).exp
  convert! (he.mul (((h2.const_mul 24).sub (h1.const_mul 24)).add_const 12)).sub_const 12 using 1
  simp only [Pi.pow_apply,Pi.sub_apply,id_eq]
  ring

private theorem positive_from_derivative {f g : ℝ → ℝ} (h0 : f 0=0)
    (hd : ∀ z, HasDerivAt f (g z) z) (hg : ∀ z, 0 < z → 0 < g z)
    {z : ℝ} (hz : 0 < z) : 0 < f z := by
  have hm : StrictMonoOn f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici _)
    · intro x _; exact (hd x).continuousAt.continuousWithinAt
    · intro x hx
      rw [(hd x).deriv]
      exact hg x (by simpa only [interior_Ici,mem_Ioi] using hx)
  simpa only [h0] using hm (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) hz.le hz

private theorem clockErrorThree_pos {z : ℝ} (hz : 0 < z) : 0 < clockErrorThree z := by
  apply positive_from_derivative (by norm_num [clockErrorThree]) clockErrorThree_deriv _ hz
  intro x hx
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hx)) (Real.exp_pos _)
private theorem clockErrorTwo_pos {z : ℝ} (hz : 0 < z) : 0 < clockErrorTwo z :=
  positive_from_derivative (by norm_num [clockErrorTwo]) clockErrorTwo_deriv
    (fun _ hx => clockErrorThree_pos hx) hz
private theorem clockErrorOne_pos {z : ℝ} (hz : 0 < z) : 0 < clockErrorOne z :=
  positive_from_derivative (by norm_num [clockErrorOne]) clockErrorOne_deriv
    (fun _ hx => clockErrorTwo_pos hx) hz
private theorem clockErrorZero_pos {z : ℝ} (hz : 0 < z) : 0 < clockErrorZero z :=
  positive_from_derivative (by norm_num [clockErrorZero]) clockErrorZero_deriv
    (fun _ hx => clockErrorOne_pos hx) hz

/-- Rational clock envelope with the required local cancellation and linear growth. -/
def linearClockEnvelope (z : ℝ) : ℝ := (15+3*z+6*z^2+z^3)/(15+3*z+z^2)

theorem clock_coth_lt_linearEnvelope {z : ℝ} (hz : 0 < z) :
    z*Real.cosh z/Real.sinh z < linearClockEnvelope z := by
  have hf := clockErrorZero_pos hz
  have hs := Real.sinh_pos_iff.mpr hz
  have hd : 0 < 15+3*z+z^2 := by positivity
  have hid : 2*Real.exp z*((15+3*z+6*z^2+z^3)*Real.sinh z-
      z*(15+3*z+z^2)*Real.cosh z)=clockErrorZero z := by
    have he : Real.exp (2*z)=(Real.exp z)^2 := by rw [two_mul,Real.exp_add,pow_two]
    unfold clockErrorZero
    rw [he,Real.sinh_eq,Real.cosh_eq,Real.exp_neg]
    field_simp [(Real.exp_pos z).ne']
    ring
  rw [← hid] at hf
  have hc := (mul_pos_iff_of_pos_left (show 0 < 2*Real.exp z by positivity)).mp hf
  unfold linearClockEnvelope
  apply (div_lt_div_iff₀ hs hd).mpr
  nlinarith only [hc]

/-- Exact positive polynomial in the constant-curvature comparison diagnostic. -/
theorem linearClock_constantCurvature_reserve_pos (z : ℝ) :
    0 < (11/90:ℝ)-19*z/450+2*z^2/135-z^3/1125+2*z^4/10125 := by
  have he : (11/90:ℝ)-19*z/450+2*z^2/135-z^3/1125+2*z^4/10125=
      (z-19/10)^2/90+739/9000+z^2*(2*(z-9/4)^2/10125+73/27000) := by ring
  rw [he]
  positivity

/-- Logarithmic clock growth of the constant-curvature inverse profile. -/
def constantInverseClockGrowth (z : ℝ) : ℝ :=
  1+2*z^2/15+(z^2/5+4*z^4/675)/(1+z^2/10+z^4/675)

theorem linearEnvelope_lt_constantInverseClockGrowth {z : ℝ} (hz : 0 < z) :
    linearClockEnvelope z < constantInverseClockGrowth z := by
  let P := 1+z^2/10+z^4/675
  let D := 15+3*z+z^2
  have hP : 0 < P := by dsimp only [P]; positivity
  have hD : 0 < D := by dsimp only [D]; positivity
  have hid : (constantInverseClockGrowth z-linearClockEnvelope z)*P*D=
      z^4*((11/90:ℝ)-19*z/450+2*z^2/135-z^3/1125+2*z^4/10125) := by
    unfold constantInverseClockGrowth linearClockEnvelope
    dsimp only [P,D] at hP hD ⊢
    field_simp [hP.ne',hD.ne']
    ring
  have hp := mul_pos (pow_pos hz 4) (linearClock_constantCurvature_reserve_pos z)
  rw [← hid] at hp
  have hp1 := (mul_pos_iff_of_pos_right hD).mp hp
  exact sub_pos.mp ((mul_pos_iff_of_pos_right hP).mp hp1)


end
end RHTower.ThetaCuspDefect
