import Mathlib

/-!
# A positive, even, log-concave kernel whose Fourier transform violates the Laguerre inequality

The kernel `Φ(u) = e^{−πu²} (cosh(ωu) + 6/5)` with `ω = 2πa`, `a² = 1/(10π)` (so `ω² = 2π/5`) is
positive, even and logarithmically concave.  Its Fourier transform is
`H(t) = e^{−πt²} (A cos(ωt) + 6/5)` with `A = e^{1/10}`, and the first Laguerre expression of `H`
is negative at `t₀ = π/ω`:

`H'(t₀)² − H(t₀)·H''(t₀) = e^{−2πt₀²} · (6/5 − A) · (12π/5) · (1 − A) < 0`, since `1 < A < 6/5`.

Hence positivity, evenness and log-concavity of a kernel do not imply the first Laguerre
inequality for its Fourier transform.
-/

open Real Complex Filter Topology MeasureTheory
open scoped FourierTransform

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The parameters -/

/-- The half-frequency `a = √(1/(10π))`. -/
def laguerreA : ℝ := Real.sqrt (1 / (10 * π))

theorem laguerreA_pos : 0 < laguerreA := by
  unfold laguerreA
  exact Real.sqrt_pos.mpr (by positivity)

theorem pi_mul_laguerreA_sq : π * laguerreA ^ (2 : ℕ) = 1 / 10 := by
  unfold laguerreA
  rw [Real.sq_sqrt (by positivity)]
  field_simp

/-- The frequency `ω = 2πa`. -/
def laguerreOmega : ℝ := 2 * π * laguerreA

theorem laguerreOmega_pos : 0 < laguerreOmega := by
  unfold laguerreOmega
  have := laguerreA_pos
  positivity

theorem laguerreOmega_sq : laguerreOmega ^ (2 : ℕ) = 2 * π / 5 := by
  unfold laguerreOmega
  have h := pi_mul_laguerreA_sq
  nlinarith [h]

/-- The amplitude `A = e^{1/10}`. -/
def laguerreAmp : ℝ := Real.exp (1 / 10)

theorem one_lt_laguerreAmp : 1 < laguerreAmp := by
  unfold laguerreAmp
  have := Real.add_one_lt_exp (x := (1 / 10 : ℝ)) (by norm_num)
  linarith

theorem laguerreAmp_lt : laguerreAmp < 6 / 5 := by
  unfold laguerreAmp
  have := Real.exp_bound_div_one_sub_of_interval' (x := (1 / 10 : ℝ)) (by norm_num) (by norm_num)
  norm_num at this ⊢
  linarith

/-- The kernel `Φ(u) = e^{−πu²} (cosh(ωu) + 6/5)`. -/
def laguerreKernel (u : ℝ) : ℝ :=
  Real.exp (-π * u ^ (2 : ℕ)) * (Real.cosh (laguerreOmega * u) + 6 / 5)

/-- The transform `H(t) = e^{−πt²} (A cos(ωt) + 6/5)`. -/
def laguerreTransform (t : ℝ) : ℝ :=
  Real.exp (-π * t ^ (2 : ℕ)) * (laguerreAmp * Real.cos (laguerreOmega * t) + 6 / 5)

/-! ## Positivity and evenness -/

theorem laguerreKernel_pos (u : ℝ) : 0 < laguerreKernel u := by
  unfold laguerreKernel
  have := Real.cosh_pos (laguerreOmega * u)
  positivity

theorem laguerreKernel_even (u : ℝ) : laguerreKernel (-u) = laguerreKernel u := by
  unfold laguerreKernel
  rw [mul_neg, Real.cosh_neg, neg_sq]

/-! ## Logarithmic concavity -/

theorem cosh_add_ne_zero (u : ℝ) : Real.cosh (laguerreOmega * u) + 6 / 5 ≠ 0 := by
  have := Real.cosh_pos (laguerreOmega * u)
  positivity

/-- The first derivative of `log Φ`. -/
def laguerreLogDeriv1 (u : ℝ) : ℝ :=
  -(2 * π) * u
    + laguerreOmega * Real.sinh (laguerreOmega * u) / (Real.cosh (laguerreOmega * u) + 6 / 5)

/-- The second derivative of `log Φ`. -/
def laguerreLogDeriv2 (u : ℝ) : ℝ :=
  -(2 * π) + laguerreOmega ^ (2 : ℕ) * (1 + 6 / 5 * Real.cosh (laguerreOmega * u))
    / (Real.cosh (laguerreOmega * u) + 6 / 5) ^ (2 : ℕ)

theorem hasDerivAt_omega_mul (u : ℝ) :
    HasDerivAt (fun v : ℝ => laguerreOmega * v) laguerreOmega u := by
  simpa using (hasDerivAt_id u).const_mul laguerreOmega

theorem hasDerivAt_log_laguerreKernel (u : ℝ) :
    HasDerivAt (fun v => Real.log (laguerreKernel v)) (laguerreLogDeriv1 u) u := by
  have hlog : (fun v => Real.log (laguerreKernel v))
      = fun v => -π * v ^ (2 : ℕ) + Real.log (Real.cosh (laguerreOmega * v) + 6 / 5) := by
    funext v
    unfold laguerreKernel
    rw [Real.log_mul (Real.exp_pos _).ne' (cosh_add_ne_zero v), Real.log_exp]
  rw [hlog]
  have h1 : HasDerivAt (fun v : ℝ => -π * v ^ (2 : ℕ)) (-π * (2 * u)) u := by
    have := (hasDerivAt_pow 2 u).const_mul (-π)
    simpa using this
  have hcosh : HasDerivAt (fun v : ℝ => Real.cosh (laguerreOmega * v) + 6 / 5)
      (Real.sinh (laguerreOmega * u) * laguerreOmega) u :=
    (hasDerivAt_omega_mul u).cosh.add_const _
  have h2 := hcosh.log (cosh_add_ne_zero u)
  refine (h1.add h2).congr_deriv ?_
  unfold laguerreLogDeriv1
  ring

theorem hasDerivAt_laguerreLogDeriv1 (u : ℝ) :
    HasDerivAt laguerreLogDeriv1 (laguerreLogDeriv2 u) u := by
  have hsinh : HasDerivAt (fun v : ℝ => laguerreOmega * Real.sinh (laguerreOmega * v))
      (laguerreOmega * (Real.cosh (laguerreOmega * u) * laguerreOmega)) u :=
    (hasDerivAt_omega_mul u).sinh.const_mul laguerreOmega
  have hcosh : HasDerivAt (fun v : ℝ => Real.cosh (laguerreOmega * v) + 6 / 5)
      (Real.sinh (laguerreOmega * u) * laguerreOmega) u :=
    (hasDerivAt_omega_mul u).cosh.add_const _
  have hdiv := hsinh.div hcosh (cosh_add_ne_zero u)
  have hlin : HasDerivAt (fun v : ℝ => -(2 * π) * v) (-(2 * π)) u := by
    simpa using (hasDerivAt_id u).const_mul (-(2 * π))
  have hfun : laguerreLogDeriv1 = fun v => -(2 * π) * v
      + laguerreOmega * Real.sinh (laguerreOmega * v) / (Real.cosh (laguerreOmega * v) + 6 / 5) :=
    rfl
  rw [hfun]
  refine (hlin.add hdiv).congr_deriv ?_
  unfold laguerreLogDeriv2
  have hc := Real.cosh_sq (laguerreOmega * u)
  congr 1
  rw [div_left_inj' (pow_ne_zero 2 (cosh_add_ne_zero u))]
  linear_combination laguerreOmega ^ (2 : ℕ) * hc

theorem laguerreLogDeriv2_nonpos (u : ℝ) : laguerreLogDeriv2 u ≤ 0 := by
  unfold laguerreLogDeriv2
  rw [laguerreOmega_sq]
  set y := Real.cosh (laguerreOmega * u) with hy
  have hy1 : 1 ≤ y := Real.one_le_cosh _
  have hpos : 0 < (y + 6 / 5) ^ (2 : ℕ) := by positivity
  have hπ := Real.pi_pos
  have h0 : (1 + 6 / 5 * y) / 5 ≤ (y + 6 / 5) ^ (2 : ℕ) := by nlinarith [hy1]
  have key : 2 * π / 5 * (1 + 6 / 5 * y) ≤ 2 * π * (y + 6 / 5) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg hπ.le (sub_nonneg.mpr h0)]
  have : 2 * π / 5 * (1 + 6 / 5 * y) / (y + 6 / 5) ^ (2 : ℕ) ≤ 2 * π := by
    rw [div_le_iff₀ hpos]
    exact key
  linarith

/-- **The kernel is logarithmically concave.** -/
theorem laguerreKernel_logConcave :
    ConcaveOn ℝ Set.univ (fun u => Real.log (laguerreKernel u)) := by
  have hd1 : deriv (fun u => Real.log (laguerreKernel u)) = laguerreLogDeriv1 :=
    funext fun u => (hasDerivAt_log_laguerreKernel u).deriv
  refine concaveOn_of_deriv2_nonpos convex_univ ?_ ?_ ?_ ?_
  · exact fun u _ => (hasDerivAt_log_laguerreKernel u).continuousAt.continuousWithinAt
  · exact fun u _ => (hasDerivAt_log_laguerreKernel u).differentiableAt.differentiableWithinAt
  · rw [hd1]
    exact fun u _ => (hasDerivAt_laguerreLogDeriv1 u).differentiableAt.differentiableWithinAt
  · intro u _
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id]
    rw [hd1, (hasDerivAt_laguerreLogDeriv1 u).deriv]
    exact laguerreLogDeriv2_nonpos u

/-! ## The Fourier transform -/

/-- The Gaussian piece `x ↦ exp(−πx² + 2πc x)`. -/
def gaussPiece (c : ℂ) (x : ℝ) : ℂ :=
  cexp (-(π : ℂ) * 1 * (x : ℂ) ^ (2 : ℕ) + 2 * π * c * x)

theorem integrable_gaussPiece (c : ℂ) : Integrable (gaussPiece c) := by
  have h := integrable_cexp_quadratic' (b := -(π : ℂ)) (by simp [Real.pi_pos]) (2 * π * c) 0
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [gaussPiece]
  congr 1
  ring

/-- The kernel is a combination of three Gaussian pieces. -/
theorem laguerreKernel_eq_pieces (u : ℝ) :
    (laguerreKernel u : ℂ)
      = (1 / 2 : ℂ) * gaussPiece (laguerreA : ℂ) u + (1 / 2 : ℂ) * gaussPiece (-(laguerreA : ℂ)) u
        + (6 / 5 : ℂ) * gaussPiece 0 u := by
  unfold laguerreKernel gaussPiece
  rw [Real.cosh_eq]
  have e1 : -(π : ℂ) * 1 * (u : ℂ) ^ (2 : ℕ) + 2 * π * (laguerreA : ℂ) * u
      = ((-π * u ^ (2 : ℕ) : ℝ) : ℂ) + ((laguerreOmega * u : ℝ) : ℂ) := by
    unfold laguerreOmega
    push_cast
    ring
  have e2 : -(π : ℂ) * 1 * (u : ℂ) ^ (2 : ℕ) + 2 * π * (-(laguerreA : ℂ)) * u
      = ((-π * u ^ (2 : ℕ) : ℝ) : ℂ) + ((-(laguerreOmega * u) : ℝ) : ℂ) := by
    unfold laguerreOmega
    push_cast
    ring
  have e3 : -(π : ℂ) * 1 * (u : ℂ) ^ (2 : ℕ) + 2 * π * 0 * u = ((-π * u ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e1, e2, e3, Complex.exp_add, Complex.exp_add]
  simp only [← Complex.ofReal_exp]
  push_cast
  ring

/-- The unit-modulus character factor is integrable against every Gaussian piece. -/
theorem integrable_char_mul_gaussPiece (c : ℂ) (w : ℝ) :
    Integrable (fun v : ℝ => cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece c v) := by
  refine (integrable_gaussPiece c).bdd_mul ?_ (c := 1) (Eventually.of_forall fun v => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · rw [Complex.norm_exp_ofReal_mul_I]

/-- The Fourier transform of a Gaussian piece, pointwise. -/
theorem fourier_gaussPiece (c : ℂ) (w : ℝ) :
    𝓕 (gaussPiece c) w = cexp (-(π : ℂ) * ((w : ℂ) + I * c) ^ (2 : ℕ)) := by
  have h := congrFun (fourier_gaussian_pi' (b := 1) (by simp) c) w
  unfold gaussPiece
  rw [h, one_cpow, div_one, one_mul, div_one]

/-- **The Fourier transform of the kernel.** -/
theorem fourier_laguerreKernel (w : ℝ) :
    𝓕 (fun u : ℝ => (laguerreKernel u : ℂ)) w = (laguerreTransform w : ℂ) := by
  have hsplit : (fun u : ℝ => (laguerreKernel u : ℂ))
      = fun u => (1 / 2 : ℂ) * gaussPiece (laguerreA : ℂ) u
          + (1 / 2 : ℂ) * gaussPiece (-(laguerreA : ℂ)) u + (6 / 5 : ℂ) * gaussPiece 0 u :=
    funext laguerreKernel_eq_pieces
  rw [hsplit, Real.fourier_real_eq]
  simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  have hI1 := integrable_char_mul_gaussPiece (laguerreA : ℂ) w
  have hI2 := integrable_char_mul_gaussPiece (-(laguerreA : ℂ)) w
  have hI3 := integrable_char_mul_gaussPiece 0 w
  have hlin : ∀ v : ℝ, cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I)
      * ((1 / 2 : ℂ) * gaussPiece (laguerreA : ℂ) v
          + (1 / 2 : ℂ) * gaussPiece (-(laguerreA : ℂ)) v + (6 / 5 : ℂ) * gaussPiece 0 v)
      = (1 / 2 : ℂ) * (cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece (laguerreA : ℂ) v)
        + (1 / 2 : ℂ) * (cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece (-(laguerreA : ℂ)) v)
        + (6 / 5 : ℂ) * (cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece 0 v) := by
    intro v; ring
  simp_rw [hlin]
  have hA : Integrable (fun v : ℝ =>
      (1 / 2 : ℂ) * (cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece (laguerreA : ℂ) v)) :=
    hI1.const_mul _
  have hB : Integrable (fun v : ℝ =>
      (1 / 2 : ℂ) * (cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece (-(laguerreA : ℂ)) v)) :=
    hI2.const_mul _
  have hC : Integrable (fun v : ℝ =>
      (6 / 5 : ℂ) * (cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece 0 v)) :=
    hI3.const_mul _
  have hAB : Integrable (fun v : ℝ =>
      (1 / 2 : ℂ) * (cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece (laguerreA : ℂ) v)
        + (1 / 2 : ℂ) * (cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece (-(laguerreA : ℂ)) v)) :=
    hA.add hB
  rw [integral_add hAB hC, integral_add hA hB, integral_const_mul, integral_const_mul,
    integral_const_mul]
  have hF : ∀ c : ℂ, ∫ v : ℝ, cexp (((2 * π * -(v * w) : ℝ) : ℂ) * I) * gaussPiece c v
      = cexp (-(π : ℂ) * ((w : ℂ) + I * c) ^ (2 : ℕ)) := by
    intro c
    rw [← fourier_gaussPiece c w, Real.fourier_real_eq]
    simp only [Circle.smul_def, smul_eq_mul, Real.fourierChar_apply]
  rw [hF, hF, hF]
  -- assemble the transform
  unfold laguerreTransform laguerreAmp laguerreOmega
  have hI : I ^ (2 : ℕ) = -1 := I_sq
  have hpa : (π : ℂ) * (laguerreA : ℂ) ^ (2 : ℕ) = 1 / 10 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, pi_mul_laguerreA_sq]
    norm_num
  have e1 : -(π : ℂ) * ((w : ℂ) + I * (laguerreA : ℂ)) ^ (2 : ℕ)
      = ((-π * w ^ (2 : ℕ) : ℝ) : ℂ) + ((1 / 10 : ℝ) : ℂ) + (-(((2 * π * laguerreA * w : ℝ) : ℂ) * I)) := by
    push_cast
    linear_combination (-(π : ℂ) * (laguerreA : ℂ) ^ (2 : ℕ)) * hI + hpa
  have e2 : -(π : ℂ) * ((w : ℂ) + I * -(laguerreA : ℂ)) ^ (2 : ℕ)
      = ((-π * w ^ (2 : ℕ) : ℝ) : ℂ) + ((1 / 10 : ℝ) : ℂ) + (((2 * π * laguerreA * w : ℝ) : ℂ) * I) := by
    push_cast
    linear_combination (-(π : ℂ) * (laguerreA : ℂ) ^ (2 : ℕ)) * hI + hpa
  have e3 : -(π : ℂ) * ((w : ℂ) + I * 0) ^ (2 : ℕ) = ((-π * w ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e1, e2, e3, Complex.exp_add, Complex.exp_add, Complex.exp_add, Complex.exp_add]
  have hcos : Complex.cos (2 * (π : ℂ) * (laguerreA : ℂ) * (w : ℂ))
      = (cexp (2 * (π : ℂ) * (laguerreA : ℂ) * (w : ℂ) * I)
          + cexp (-(2 * (π : ℂ) * (laguerreA : ℂ) * (w : ℂ)) * I)) / 2 := rfl
  simp only [← Complex.ofReal_exp]
  push_cast
  rw [hcos, neg_mul]
  ring_nf

/-! ## The Laguerre violation -/

/-- The first derivative of `H`. -/
def laguerreTransformD1 (t : ℝ) : ℝ :=
  Real.exp (-π * t ^ (2 : ℕ))
    * (-(laguerreAmp * laguerreOmega * Real.sin (laguerreOmega * t))
        - 2 * π * t * (laguerreAmp * Real.cos (laguerreOmega * t) + 6 / 5))

/-- The second derivative of `H`. -/
def laguerreTransformD2 (t : ℝ) : ℝ :=
  Real.exp (-π * t ^ (2 : ℕ))
    * (-(laguerreAmp * laguerreOmega ^ (2 : ℕ) * Real.cos (laguerreOmega * t))
        + 4 * π * t * (laguerreAmp * laguerreOmega * Real.sin (laguerreOmega * t))
        + (4 * π ^ (2 : ℕ) * t ^ (2 : ℕ) - 2 * π) * (laguerreAmp * Real.cos (laguerreOmega * t) + 6 / 5))

theorem hasDerivAt_gaussFactor (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-π * s ^ (2 : ℕ))) (Real.exp (-π * t ^ (2 : ℕ)) * (-π * (2 * t))) t := by
  have := ((hasDerivAt_pow 2 t).const_mul (-π)).exp
  simpa using this

theorem hasDerivAt_laguerreTransform (t : ℝ) :
    HasDerivAt laguerreTransform (laguerreTransformD1 t) t := by
  have hg : HasDerivAt (fun s : ℝ => laguerreAmp * Real.cos (laguerreOmega * s) + 6 / 5)
      (laguerreAmp * (-Real.sin (laguerreOmega * t) * laguerreOmega)) t :=
    ((hasDerivAt_omega_mul t).cos.const_mul laguerreAmp).add_const _
  have hfun : laguerreTransform = fun s => Real.exp (-π * s ^ (2 : ℕ))
      * (laguerreAmp * Real.cos (laguerreOmega * s) + 6 / 5) := rfl
  rw [hfun]
  refine ((hasDerivAt_gaussFactor t).mul hg).congr_deriv ?_
  unfold laguerreTransformD1
  ring

theorem hasDerivAt_laguerreTransformD1 (t : ℝ) :
    HasDerivAt laguerreTransformD1 (laguerreTransformD2 t) t := by
  have hsin : HasDerivAt (fun s : ℝ => laguerreAmp * laguerreOmega * Real.sin (laguerreOmega * s))
      (laguerreAmp * laguerreOmega * (Real.cos (laguerreOmega * t) * laguerreOmega)) t :=
    (hasDerivAt_omega_mul t).sin.const_mul _
  have hg : HasDerivAt (fun s : ℝ => laguerreAmp * Real.cos (laguerreOmega * s) + 6 / 5)
      (laguerreAmp * (-Real.sin (laguerreOmega * t) * laguerreOmega)) t :=
    ((hasDerivAt_omega_mul t).cos.const_mul laguerreAmp).add_const _
  have hlin : HasDerivAt (fun s : ℝ => 2 * π * s) (2 * π) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * π)
  have hinner : HasDerivAt
      (fun s : ℝ => -(laguerreAmp * laguerreOmega * Real.sin (laguerreOmega * s))
          - 2 * π * s * (laguerreAmp * Real.cos (laguerreOmega * s) + 6 / 5))
      (-(laguerreAmp * laguerreOmega * (Real.cos (laguerreOmega * t) * laguerreOmega))
          - (2 * π * (laguerreAmp * Real.cos (laguerreOmega * t) + 6 / 5)
              + 2 * π * t * (laguerreAmp * (-Real.sin (laguerreOmega * t) * laguerreOmega)))) t :=
    hsin.neg.sub (hlin.mul hg)
  have hfun : laguerreTransformD1 = fun s => Real.exp (-π * s ^ (2 : ℕ))
      * (-(laguerreAmp * laguerreOmega * Real.sin (laguerreOmega * s))
          - 2 * π * s * (laguerreAmp * Real.cos (laguerreOmega * s) + 6 / 5)) := rfl
  rw [hfun]
  refine ((hasDerivAt_gaussFactor t).mul hinner).congr_deriv ?_
  unfold laguerreTransformD2
  ring

/-- The point `t₀ = π/ω`, where `cos(ωt₀) = −1`. -/
def laguerreT0 : ℝ := π / laguerreOmega

theorem laguerreOmega_mul_T0 : laguerreOmega * laguerreT0 = π := by
  unfold laguerreT0
  field_simp [laguerreOmega_pos.ne']

/-- **The Laguerre expression of `H` is negative at `t₀`.** -/
theorem laguerreTransform_laguerre_neg :
    deriv laguerreTransform laguerreT0 ^ (2 : ℕ)
      - laguerreTransform laguerreT0 * deriv (deriv laguerreTransform) laguerreT0 < 0 := by
  have hd1 : deriv laguerreTransform = laguerreTransformD1 :=
    funext fun t => (hasDerivAt_laguerreTransform t).deriv
  rw [hd1, (hasDerivAt_laguerreTransformD1 _).deriv]
  unfold laguerreTransform laguerreTransformD1 laguerreTransformD2
  rw [laguerreOmega_mul_T0, Real.cos_pi, Real.sin_pi]
  set E := Real.exp (-π * laguerreT0 ^ (2 : ℕ)) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hω := laguerreOmega_sq
  set A := laguerreAmp with hA
  have hA1 : 1 < A := one_lt_laguerreAmp
  have hA2 : A < 6 / 5 := laguerreAmp_lt
  have hkey : (E * (-(A * laguerreOmega * 0) - 2 * π * laguerreT0 * (A * -1 + 6 / 5))) ^ (2 : ℕ)
      - E * (A * -1 + 6 / 5)
        * (E * (-(A * laguerreOmega ^ (2 : ℕ) * -1) + 4 * π * laguerreT0 * (A * laguerreOmega * 0)
            + (4 * π ^ (2 : ℕ) * laguerreT0 ^ (2 : ℕ) - 2 * π) * (A * -1 + 6 / 5)))
      = E ^ (2 : ℕ) * ((6 / 5 - A) * (12 * π / 5) * (1 - A)) := by
    linear_combination (-(E ^ (2 : ℕ) * (6 / 5 - A) * A)) * hω
  rw [hkey]
  have hπ := Real.pi_pos
  have h1 : 0 < E ^ (2 : ℕ) * ((6 / 5 - A) * (12 * π / 5)) := by
    have : 0 < 6 / 5 - A := by linarith
    positivity
  have h2 : 1 - A < 0 := by linarith
  have := mul_neg_of_pos_of_neg h1 h2
  linarith [this]

end

end GaloisForLFunctions.HTGeometry
