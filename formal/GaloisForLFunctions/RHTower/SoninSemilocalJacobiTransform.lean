import GaloisForLFunctions.RHTower.SoninSemilocalJacobiPolynomials
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Exact Fourier transform of the archimedean Jacobi polynomials

Every polynomial is integrable against the normalized Gamma measure because that measure has all
moments.  Differentiation under the integral gives the source three-term differential recurrence.
Together with the degree-zero characteristic function, this proves equation (6) for the actual
recursively defined polynomial family in every degree.
-/

noncomputable section

open Complex Filter MeasureTheory Polynomial Real Set

namespace RHTower

theorem integrable_coe_eval_semilocalArchimedeanGammaMeasure (p : ℝ[X]) :
    Integrable (fun s : ℝ => ((p.eval s : ℝ) : ℂ))
      semilocalArchimedeanGammaMeasure := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      apply (hp.add hq).congr
      filter_upwards with s
      simp
  | monomial n a =>
      have habs :=
        (memLp_id_semilocalArchimedeanGammaMeasure n).integrable_norm_pow'
      have hpow : Integrable (fun s : ℝ => s ^ n)
          semilocalArchimedeanGammaMeasure := by
        apply (integrable_norm_iff (by fun_prop)).mp
        simpa [Real.norm_eq_abs, abs_pow] using habs
      have hpowC : Integrable (fun s : ℝ => ((s ^ n : ℝ) : ℂ))
          semilocalArchimedeanGammaMeasure := hpow.ofReal
      apply (hpowC.const_mul (a : ℂ)).congr
      filter_upwards with s
      simp [eval_monomial]

theorem integrable_coe_mul_eval_semilocalArchimedeanGammaMeasure (p : ℝ[X]) :
    Integrable (fun s : ℝ => (((s * p.eval s : ℝ)) : ℂ))
      semilocalArchimedeanGammaMeasure := by
  apply (integrable_coe_eval_semilocalArchimedeanGammaMeasure (X * p)).congr
  filter_upwards with s
  simp

def semilocalArchimedeanPolynomialFourier (p : ℝ[X]) (t : ℝ) : ℂ :=
  ∫ s : ℝ, ((p.eval s : ℝ) : ℂ) *
    Complex.exp (((t * s : ℝ) : ℂ) * Complex.I)
      ∂semilocalArchimedeanGammaMeasure

theorem integrable_semilocalArchimedeanPolynomialFourier_integrand
    (p : ℝ[X]) (t : ℝ) :
    Integrable (fun s : ℝ => ((p.eval s : ℝ) : ℂ) *
      Complex.exp (((t * s : ℝ) : ℂ) * Complex.I))
      semilocalArchimedeanGammaMeasure := by
  apply (integrable_coe_eval_semilocalArchimedeanGammaMeasure p).mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with s
    simp [Complex.norm_exp]

theorem hasDerivAt_semilocalArchimedeanPolynomialFourier
    (p : ℝ[X]) (t : ℝ) :
    HasDerivAt (semilocalArchimedeanPolynomialFourier p)
      (Complex.I *
        ∫ s : ℝ, ((s * p.eval s : ℝ) : ℂ) *
          Complex.exp (((t * s : ℝ) : ℂ) * Complex.I)
            ∂semilocalArchimedeanGammaMeasure) t := by
  let F : ℝ → ℝ → ℂ := fun u s =>
    ((p.eval s : ℝ) : ℂ) * Complex.exp (((u * s : ℝ) : ℂ) * Complex.I)
  let F' : ℝ → ℝ → ℂ := fun u s =>
    ((p.eval s : ℝ) : ℂ) *
      (((s : ℂ) * Complex.I) *
        Complex.exp (((u * s : ℝ) : ℂ) * Complex.I))
  let bound : ℝ → ℝ := fun s => ‖((s * p.eval s : ℝ) : ℂ)‖
  have hspint := integrable_coe_mul_eval_semilocalArchimedeanGammaMeasure p
  have hFint : Integrable (F t) semilocalArchimedeanGammaMeasure := by
    exact integrable_semilocalArchimedeanPolynomialFourier_integrand p t
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := semilocalArchimedeanGammaMeasure)
    (F := F) (F' := F') (bound := bound) (s := Set.univ)
    (x₀ := t) univ_mem
    (by exact Filter.Eventually.of_forall fun u => by fun_prop)
    hFint
    (by fun_prop)
    (by
      filter_upwards with s
      intro u _hu
      simp [F', bound, Complex.norm_exp]
      rw [mul_comm])
    (by simpa [bound] using hspint.norm)
    (by
      filter_upwards with s
      intro u _hu
      dsimp [F, F']
      have hlin :=
        ((((hasDerivAt_id u).mul_const s).ofReal_comp).mul_const Complex.I)
      have hexp := hlin.cexp
      have hscaled := hexp.const_mul ((p.eval s : ℝ) : ℂ)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled)
  rw [show semilocalArchimedeanPolynomialFourier p = fun u =>
      ∫ s : ℝ, F u s ∂semilocalArchimedeanGammaMeasure by rfl]
  convert hparam.2 using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  dsimp [F']
  push_cast
  ring

def semilocalArchimedeanJacobiFourier (n : ℕ) (t : ℝ) : ℂ :=
  semilocalArchimedeanPolynomialFourier
    (semilocalArchimedeanJacobiPolynomial n) t

theorem hasDerivAt_semilocalArchimedeanJacobiFourier_succ_recurrence
    (n : ℕ) (t : ℝ) :
    HasDerivAt (semilocalArchimedeanJacobiFourier (n + 1))
      (Complex.I *
        ((semilocalArchimedeanJacobiCoefficient n : ℂ) *
            semilocalArchimedeanJacobiFourier n t +
          (semilocalArchimedeanJacobiCoefficient (n + 1) : ℂ) *
            semilocalArchimedeanJacobiFourier (n + 2) t)) t := by
  have h := hasDerivAt_semilocalArchimedeanPolynomialFourier
    (semilocalArchimedeanJacobiPolynomial (n + 1)) t
  convert h using 1
  congr 1
  simp only [semilocalArchimedeanJacobiFourier,
    semilocalArchimedeanPolynomialFourier]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · apply integral_congr_ae
    filter_upwards with s
    have hrec := semilocalArchimedeanJacobiPolynomial_eval_recurrence n s
    have hrecC := congrArg Complex.ofReal hrec
    push_cast at hrecC ⊢
    rw [hrecC]
    ring
  · exact (integrable_semilocalArchimedeanPolynomialFourier_integrand
      (semilocalArchimedeanJacobiPolynomial n) t).const_mul _
  · exact (integrable_semilocalArchimedeanPolynomialFourier_integrand
      (semilocalArchimedeanJacobiPolynomial (n + 2)) t).const_mul _

theorem semilocalArchimedeanJacobiFourier_zero (t : ℝ) :
    semilocalArchimedeanJacobiFourier 0 t =
      semilocalArchimedeanJacobiFourierClosedForm 0 t := by
  simpa [semilocalArchimedeanJacobiFourier,
    semilocalArchimedeanPolynomialFourier,
    semilocalArchimedeanJacobiFourierClosedForm,
    semilocalArchimedeanJacobiNormalization] using
      integral_cexp_semilocalArchimedeanGammaMeasure t

theorem hasDerivAt_semilocalArchimedeanJacobiFourier_zero_recurrence (t : ℝ) :
    HasDerivAt (semilocalArchimedeanJacobiFourier 0)
      (Complex.I * (semilocalArchimedeanJacobiCoefficient 0 : ℂ) *
        semilocalArchimedeanJacobiFourier 1 t) t := by
  have h := hasDerivAt_semilocalArchimedeanPolynomialFourier
    (semilocalArchimedeanJacobiPolynomial 0) t
  convert h using 1
  rw [mul_assoc]
  congr 1
  simp only [semilocalArchimedeanJacobiFourier,
    semilocalArchimedeanPolynomialFourier]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  have ha : semilocalArchimedeanJacobiCoefficient 0 ≠ 0 :=
    (semilocalArchimedeanJacobiCoefficient_pos 0).ne'
  simp only [semilocalArchimedeanJacobiPolynomial_zero,
    semilocalArchimedeanJacobiPolynomial_one, eval_one,
    eval_mul, eval_C, eval_X]
  push_cast
  field_simp [ha]

theorem hasDerivAt_semilocalArchimedeanJacobiFourierClosedForm_zero_recurrence
    (t : ℝ) :
    HasDerivAt (semilocalArchimedeanJacobiFourierClosedForm 0)
      (Complex.I * (semilocalArchimedeanJacobiCoefficient 0 : ℂ) *
        semilocalArchimedeanJacobiFourierClosedForm 1 t) t := by
  have h := (hasDerivAt_semilocalArchimedeanCharacteristic t).ofReal_comp
  have hnorm :=
    semilocalArchimedeanJacobiNormalization_succ_mul_coefficient 0
  have hnormC := congrArg Complex.ofReal hnorm
  push_cast at hnormC
  have hprod :
      (semilocalArchimedeanJacobiCoefficient 0 : ℂ) *
          (semilocalArchimedeanJacobiNormalization 1 : ℂ) = 1 / 2 := by
    rw [mul_comm, hnormC]
    norm_num [semilocalArchimedeanJacobiNormalization]
  convert h using 1
  · funext u
    simp [semilocalArchimedeanJacobiFourierClosedForm,
      semilocalArchimedeanJacobiNormalization]
  · rw [semilocalArchimedeanJacobiFourierClosedForm]
    norm_num
    calc
      Complex.I * (semilocalArchimedeanJacobiCoefficient 0 : ℂ) *
          (Complex.I * (semilocalArchimedeanJacobiNormalization 1 : ℂ) *
            (semilocalArchimedeanCharacteristic t : ℂ) * Complex.tanh t) =
          (Complex.I * Complex.I) *
            (((semilocalArchimedeanJacobiCoefficient 0 : ℂ) *
                (semilocalArchimedeanJacobiNormalization 1 : ℂ)) *
              (semilocalArchimedeanCharacteristic t : ℂ) * Complex.tanh t) := by
        ring
      _ =
          -(((semilocalArchimedeanJacobiCoefficient 0 : ℂ) *
              (semilocalArchimedeanJacobiNormalization 1 : ℂ)) *
            (semilocalArchimedeanCharacteristic t : ℂ) * Complex.tanh t) := by
        rw [Complex.I_mul_I]
        ring
      _ = -(1 / 2 * (semilocalArchimedeanCharacteristic t : ℂ) *
          Complex.tanh t) := by rw [hprod]

theorem semilocalArchimedeanJacobiFourier_one (t : ℝ) :
    semilocalArchimedeanJacobiFourier 1 t =
      semilocalArchimedeanJacobiFourierClosedForm 1 t := by
  have hfun : semilocalArchimedeanJacobiFourier 0 =
      semilocalArchimedeanJacobiFourierClosedForm 0 :=
    funext semilocalArchimedeanJacobiFourier_zero
  have hderiv := congrArg (fun f : ℝ → ℂ => deriv f t) hfun
  change deriv (semilocalArchimedeanJacobiFourier 0) t =
    deriv (semilocalArchimedeanJacobiFourierClosedForm 0) t at hderiv
  rw [(hasDerivAt_semilocalArchimedeanJacobiFourier_zero_recurrence t).deriv,
    (hasDerivAt_semilocalArchimedeanJacobiFourierClosedForm_zero_recurrence t).deriv]
    at hderiv
  have hscalar : Complex.I *
      (semilocalArchimedeanJacobiCoefficient 0 : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr
      (semilocalArchimedeanJacobiCoefficient_pos 0).ne')
  exact mul_left_cancel₀ hscalar hderiv

/-- Equation (6): the Fourier transform of every actual archimedean Jacobi polynomial has the
closed `iⁿ cₙ φ(t) tanh(t)ⁿ` form. -/
theorem semilocalArchimedeanJacobiFourier_eq_closedForm (n : ℕ) (t : ℝ) :
    semilocalArchimedeanJacobiFourier n t =
      semilocalArchimedeanJacobiFourierClosedForm n t := by
  have hfun : ∀ m : ℕ, semilocalArchimedeanJacobiFourier m =
      semilocalArchimedeanJacobiFourierClosedForm m := by
    intro m
    induction m using Nat.twoStepInduction with
    | zero => exact funext semilocalArchimedeanJacobiFourier_zero
    | one => exact funext semilocalArchimedeanJacobiFourier_one
    | more m hm hm1 =>
        funext u
        have hactual :=
          hasDerivAt_semilocalArchimedeanJacobiFourier_succ_recurrence m u
        have hclosed :=
          hasDerivAt_semilocalArchimedeanJacobiFourierClosedForm_succ_recurrence m u
        have hderiv := congrArg (fun f : ℝ → ℂ => deriv f u) hm1
        change deriv (semilocalArchimedeanJacobiFourier (m + 1)) u =
          deriv (semilocalArchimedeanJacobiFourierClosedForm (m + 1)) u at hderiv
        rw [hactual.deriv, hclosed.deriv] at hderiv
        have hsum := mul_left_cancel₀ Complex.I_ne_zero hderiv
        rw [congrFun hm u] at hsum
        have hmul :
            (semilocalArchimedeanJacobiCoefficient (m + 1) : ℂ) *
                semilocalArchimedeanJacobiFourier (m + 2) u =
              (semilocalArchimedeanJacobiCoefficient (m + 1) : ℂ) *
                semilocalArchimedeanJacobiFourierClosedForm (m + 2) u :=
          add_left_cancel hsum
        exact mul_left_cancel₀
          (Complex.ofReal_ne_zero.mpr
            (semilocalArchimedeanJacobiCoefficient_pos (m + 1)).ne') hmul
  exact congrFun (hfun n) t

end RHTower
