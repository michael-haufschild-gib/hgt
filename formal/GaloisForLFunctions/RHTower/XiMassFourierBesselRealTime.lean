import GaloisForLFunctions.RHTower.XiMassHyperbolicCurvedContourDecay
import GaloisForLFunctions.HTGeometry.BesselOrderLaplaceAsymptotic

/-!
# The Fourier–Bessel identity at real vertical time

At zero vertical time the mass phase is `σ cosh t + i h sinh t`, and the single real rotation
`θ = arctan(h/σ)` of the hyperbolic contour removes its oscillation entirely:

`σ cosh(x − iθ) + i h sinh(x − iθ) = √(σ²+h²) · cosh x`.

The rotated amplitude splits into an even and an odd part; the odd part integrates to zero, and
the even part is exactly the order-one Schläfli integral.  Hence

`F_0(h) = 2 a σ / √(σ²+h²) · K₁(a√(σ²+h²))`,

which is the Fourier–Bessel identity on the real-time slice.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The rotation that removes the oscillation -/

/-- The contour rotation angle removing the oscillation at zero vertical time. -/
def xiMassRealTimeRotation (sigma h : ℝ) : ℝ := Real.arctan (h / sigma)

theorem xiMassRealTimeRotation_nonneg {sigma h : ℝ} (hsigma : 0 < sigma) (hh : 0 ≤ h) :
    0 ≤ xiMassRealTimeRotation sigma h :=
  Real.arctan_nonneg.2 (div_nonneg hh hsigma.le)

theorem xiMassRealTimeRotation_lt {sigma h : ℝ} :
    xiMassRealTimeRotation sigma h < Real.pi / 2 :=
  Real.arctan_lt_pi_div_two _

theorem sqrt_one_add_sq_div {sigma h : ℝ} (hsigma : 0 < sigma) :
    sigma * Real.sqrt (1 + (h / sigma) ^ 2) = Real.sqrt (sigma ^ 2 + h ^ 2) := by
  have hval : sigma ^ 2 * (1 + (h / sigma) ^ 2) = sigma ^ 2 + h ^ 2 := by
    field_simp
  rw [← hval, Real.sqrt_mul (sq_nonneg sigma), Real.sqrt_sq hsigma.le]

theorem cos_xiMassRealTimeRotation {sigma h : ℝ} (hsigma : 0 < sigma) :
    Real.cos (xiMassRealTimeRotation sigma h) = sigma / Real.sqrt (sigma ^ 2 + h ^ 2) := by
  have hroot : (0 : ℝ) < Real.sqrt (1 + (h / sigma) ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [xiMassRealTimeRotation, Real.cos_arctan, ← sqrt_one_add_sq_div (h := h) hsigma]
  field_simp

theorem sin_xiMassRealTimeRotation {sigma h : ℝ} (hsigma : 0 < sigma) :
    Real.sin (xiMassRealTimeRotation sigma h) = h / Real.sqrt (sigma ^ 2 + h ^ 2) := by
  have hroot : (0 : ℝ) < Real.sqrt (1 + (h / sigma) ^ 2) := Real.sqrt_pos.2 (by positivity)
  rw [xiMassRealTimeRotation, Real.sin_arctan, ← sqrt_one_add_sq_div (h := h) hsigma]
  field_simp

/-- **The rotated mass phase is a pure hyperbolic cosine.** -/
theorem xiMassRealTimePhase_rotated {sigma h : ℝ} (hsigma : 0 < sigma) (x : ℝ) :
    (sigma : ℂ) * Complex.cosh ((x : ℂ) - ((xiMassRealTimeRotation sigma h : ℝ) : ℂ) * I)
        + I * (h : ℂ) * Complex.sinh ((x : ℂ)
          - ((xiMassRealTimeRotation sigma h : ℝ) : ℂ) * I)
      = ((Real.sqrt (sigma ^ 2 + h ^ 2) : ℝ) : ℂ) * Complex.cosh (x : ℂ) := by
  set θ : ℝ := xiMassRealTimeRotation sigma h with hθ
  have hqpos : (0 : ℝ) < Real.sqrt (sigma ^ 2 + h ^ 2) :=
    Real.sqrt_pos.2 (by positivity)
  have hcos : Real.cos θ = sigma / Real.sqrt (sigma ^ 2 + h ^ 2) :=
    cos_xiMassRealTimeRotation hsigma
  have hsin : Real.sin θ = h / Real.sqrt (sigma ^ 2 + h ^ 2) :=
    sin_xiMassRealTimeRotation hsigma
  have hcosh : Complex.cosh ((x : ℂ) - (θ : ℂ) * I)
      = Complex.cosh (x : ℂ) * ((Real.cos θ : ℝ) : ℂ)
        - I * Complex.sinh (x : ℂ) * ((Real.sin θ : ℝ) : ℂ) := by
    rw [Complex.cosh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    ring
  have hsinh : Complex.sinh ((x : ℂ) - (θ : ℂ) * I)
      = Complex.sinh (x : ℂ) * ((Real.cos θ : ℝ) : ℂ)
        - I * Complex.cosh (x : ℂ) * ((Real.sin θ : ℝ) : ℂ) := by
    rw [Complex.sinh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    ring
  rw [hcosh, hsinh, hcos, hsin]
  have hq : ((Real.sqrt (sigma ^ 2 + h ^ 2) : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hqpos
  have hqsq : ((Real.sqrt (sigma ^ 2 + h ^ 2) : ℝ) : ℂ) ^ 2 = ((sigma : ℂ) ^ 2 + (h : ℂ) ^ 2) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
    push_cast
    ring
  push_cast
  field_simp
  linear_combination (-(Complex.cosh (x : ℂ))) * hqsq
    + (-(Complex.cosh (x : ℂ) * (h : ℂ) ^ 2)) * Complex.I_sq

/-! ## The identity -/

/-- **(17.1) at zero vertical time.**  The mass Fourier profile is the order-one Bessel carrier of
its own propagation radius. -/
theorem stripFourier_xiMass_realTime_eq_bessel {a sigma h : ℝ}
    (ha : 0 < a) (hsigma : 0 < sigma) (hh : 0 ≤ h) :
    stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ((0 : ℝ) : ℂ) * I)) (h : ℂ)
      = 2 * (a : ℂ) * (sigma : ℂ) / ((Real.sqrt (sigma ^ 2 + h ^ 2) : ℝ) : ℂ)
        * HTGeometry.besselK1C ((a * Real.sqrt (sigma ^ 2 + h ^ 2) : ℝ) : ℂ) := by
  set θ : ℝ := xiMassRealTimeRotation sigma h with hθ
  set q : ℝ := Real.sqrt (sigma ^ 2 + h ^ 2) with hq
  have hqpos : (0 : ℝ) < q := Real.sqrt_pos.2 (by positivity)
  have haq : (0 : ℝ) < a * q := mul_pos ha hqpos
  have haqre : (0 : ℝ) < (((a * q : ℝ) : ℂ)).re := by simpa using haq
  have hθ0 : 0 ≤ θ := xiMassRealTimeRotation_nonneg hsigma hh
  have hθlt : θ < Real.pi / 2 := xiMassRealTimeRotation_lt
  have hcos : Real.cos θ = sigma / q := cos_xiMassRealTimeRotation hsigma
  have hsin : Real.sin θ = h / q := sin_xiMassRealTimeRotation hsigma
  have hshift := integral_xiMassHyperbolicEntireKernel_shift_eq
    (a := a) (sigma := sigma) (u := 0) (h := h) (theta := θ) ha hsigma le_rfl hh hθ0 hθlt
  have hrot : ∀ x : ℝ, xiMassHyperbolicEntireKernel a sigma 0 h ((x : ℂ) - (θ : ℂ) * I)
      = ((a : ℂ) * (Complex.cosh (x : ℂ) * ((Real.cos θ : ℝ) : ℂ)
            - I * Complex.sinh (x : ℂ) * ((Real.sin θ : ℝ) : ℂ)))
        * Complex.exp (-((a * q : ℝ) : ℂ) * Complex.cosh (x : ℂ)) := by
    intro x
    have hcosh : Complex.cosh ((x : ℂ) - (θ : ℂ) * I)
        = Complex.cosh (x : ℂ) * ((Real.cos θ : ℝ) : ℂ)
          - I * Complex.sinh (x : ℂ) * ((Real.sin θ : ℝ) : ℂ) := by
      rw [Complex.cosh_sub, Complex.cosh_mul_I, Complex.sinh_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
      ring
    have hphase := xiMassRealTimePhase_rotated (sigma := sigma) (h := h) hsigma x
    rw [← hθ, ← hq] at hphase
    rw [xiMassHyperbolicEntireKernel, mul_assoc, ← Complex.exp_add, hcosh]
    have hexp : -((sigma : ℂ) + ((0 : ℝ) : ℂ) * I) * ((a : ℂ)
          * Complex.cosh ((x : ℂ) - (θ : ℂ) * I))
        + -(I * (h : ℂ) * (a : ℂ) * Complex.sinh ((x : ℂ) - (θ : ℂ) * I))
        = -((a * q : ℝ) : ℂ) * Complex.cosh (x : ℂ) := by
      have hcollect : -((sigma : ℂ) + ((0 : ℝ) : ℂ) * I) * ((a : ℂ)
            * Complex.cosh ((x : ℂ) - (θ : ℂ) * I))
          + -(I * (h : ℂ) * (a : ℂ) * Complex.sinh ((x : ℂ) - (θ : ℂ) * I))
          = -(a : ℂ) * ((sigma : ℂ) * Complex.cosh ((x : ℂ) - (θ : ℂ) * I)
              + I * (h : ℂ) * Complex.sinh ((x : ℂ) - (θ : ℂ) * I)) := by
        push_cast
        ring
      rw [hcollect, hphase]
      push_cast
      ring
    rw [hcosh] at hexp
    rw [hexp]
  have hcosh_int : (∫ x : ℝ, Complex.exp (-((a * q : ℝ) : ℂ) * Complex.cosh (x : ℂ))
      * Complex.cosh (x : ℂ)) = 2 * HTGeometry.besselK1C ((a * q : ℝ) : ℂ) :=
    HTGeometry.integral_cosh_mul_exp_neg_cosh haqre
  have hsinh_int : (∫ x : ℝ, Complex.exp (-((a * q : ℝ) : ℂ) * Complex.cosh (x : ℂ))
      * Complex.sinh (x : ℂ)) = 0 := by
    refine HTGeometry.integral_odd_eq_zero fun x => ?_
    rw [Complex.ofReal_neg, Complex.cosh_neg, Complex.sinh_neg]
    ring
  have hcoshint : Integrable fun x : ℝ =>
      Complex.exp (-((a * q : ℝ) : ℂ) * Complex.cosh (x : ℂ)) * Complex.cosh (x : ℂ) :=
    HTGeometry.integrable_besselK1C_integrand haqre
  have hsinhint : Integrable fun x : ℝ =>
      Complex.exp (-((a * q : ℝ) : ℂ) * Complex.cosh (x : ℂ)) * Complex.sinh (x : ℂ) := by
    refine Integrable.mono' hcoshint.norm ?_ ?_
    · exact ((by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (-((a * q : ℝ) : ℂ) * Complex.cosh (x : ℂ))).mul
        (by fun_prop : Continuous fun x : ℝ => Complex.sinh (x : ℂ))).aestronglyMeasurable
    · filter_upwards with x
      rw [norm_mul, norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.cosh_pos x).le]
      have h1 := Real.cosh_sq_sub_sinh_sq x
      have h2 : (0 : ℝ) < Real.cosh x := Real.cosh_pos x
      nlinarith [abs_nonneg (Real.sinh x), sq_abs (Real.sinh x)]
  have hsplit : (∫ x : ℝ, xiMassHyperbolicEntireKernel a sigma 0 h ((x : ℂ) - (θ : ℂ) * I))
      = (a : ℂ) * ((Real.cos θ : ℝ) : ℂ)
          * (∫ x : ℝ, Complex.exp (-((a * q : ℝ) : ℂ) * Complex.cosh (x : ℂ))
              * Complex.cosh (x : ℂ))
        - (a : ℂ) * I * ((Real.sin θ : ℝ) : ℂ)
          * ∫ x : ℝ, Complex.exp (-((a * q : ℝ) : ℂ) * Complex.cosh (x : ℂ))
              * Complex.sinh (x : ℂ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub
      (hcoshint.const_mul _) (hsinhint.const_mul _)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [hrot x]
    ring
  have hleft : stripFourier (xiMassAnalyticTest a ((sigma : ℂ) + ((0 : ℝ) : ℂ) * I)) (h : ℂ)
      = ∫ x : ℝ, xiMassHyperbolicEntireKernel a sigma 0 h (x : ℂ) := by
    rw [stripFourier_xiMass_eq_integral_hyperbolicFourier (u := 0) ha hsigma]
    exact integral_congr_ae (ae_of_all _ fun t => (xiMassHyperbolicEntireKernel_ofReal a sigma 0 h t).symm)
  rw [hleft, ← hshift, hsplit, hcosh_int, hsinh_int, hcos]
  push_cast
  field_simp
  ring

end

end RHTower
