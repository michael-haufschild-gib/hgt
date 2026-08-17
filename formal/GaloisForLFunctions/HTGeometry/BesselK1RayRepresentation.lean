import GaloisForLFunctions.HTGeometry.BesselK1AllOrderAsymptotic

/-!
# The ray representation of the order-one Schläfli integral

Substituting `u = z v²` in the Gaussian form of the order-one Schläfli integral moves the integration
to the ray through `z`; for a real spectral parameter that is an ordinary change of variables on the
half line, and it turns the profile into a pair of binomial powers of `1 + u/(2z)`.

The point of the ray form is that `1 + u/(2z)` stays in the closed right half plane whenever the
spectral parameter does, so the binomial remainder is controlled by the *modulus* of the parameter
rather than by its real part.
-/

open MeasureTheory Set Complex

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section RealRay

/-- The Schläfli profile transported to the ray, for a real spectral parameter. -/
def rayProfileReal (b u : ℝ) : ℝ :=
  Real.exp (-u) / Real.sqrt u
    * (2 * Real.sqrt (1 + u / (2 * b)) - (Real.sqrt (1 + u / (2 * b)))⁻¹)

/-- The substituted Gaussian profile. -/
def gaussProfileSub (b y : ℝ) : ℝ :=
  _root_.HTGeometry.besselLaplaceProfile (Real.sqrt y) * Real.exp (-(b * y)) / (2 * Real.sqrt y)

theorem gaussProfileSub_sq {b x : ℝ} (hx : 0 < x) :
    2 * x * gaussProfileSub b (x ^ 2)
      = _root_.HTGeometry.besselLaplaceProfile x * Real.exp (-(b * x ^ 2)) := by
  rw [gaussProfileSub, Real.sqrt_sq hx.le]
  field_simp

/-- The pointwise identity behind the ray substitution. -/
theorem gaussProfileSub_div_eq {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    b⁻¹ * gaussProfileSub b (u / b) = (2 * Real.sqrt (2 * b))⁻¹ * rayProfileReal b u := by
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hq : (0 : ℝ) < 1 + u / (2 * b) := by positivity
  have hsq : 0 < Real.sqrt (1 + u / (2 * b)) := Real.sqrt_pos.2 hq
  have hub : (0 : ℝ) ≤ u / b := by positivity
  have hbu : b * (u / b) = u := by field_simp
  have hdiv : Real.sqrt (u / b) = Real.sqrt u / Real.sqrt b := Real.sqrt_div hu.le b
  have hsqsq : Real.sqrt (u / b) ^ 2 = u / b := Real.sq_sqrt hub
  have hfac : (2 : ℝ) + u / b = 2 * (1 + u / (2 * b)) := by
    field_simp
  have hsplit : Real.sqrt (2 + u / b) = Real.sqrt 2 * Real.sqrt (1 + u / (2 * b)) := by
    rw [hfac, Real.sqrt_mul (by norm_num)]
  have h2b : Real.sqrt (2 * b) = Real.sqrt 2 * Real.sqrt b :=
    Real.sqrt_mul (by norm_num) b
  have hA : 2 * Real.sqrt (1 + u / (2 * b)) - (Real.sqrt (1 + u / (2 * b)))⁻¹
      = (1 + u / b) / Real.sqrt (1 + u / (2 * b)) := by
    rw [eq_div_iff (ne_of_gt hsq)]
    have h := Real.sq_sqrt hq.le
    have hexp : (2 * Real.sqrt (1 + u / (2 * b)) - (Real.sqrt (1 + u / (2 * b)))⁻¹)
        * Real.sqrt (1 + u / (2 * b)) = 2 * Real.sqrt (1 + u / (2 * b)) ^ 2 - 1 := by
      field_simp
    rw [hexp, h]
    field_simp
    ring
  have hbb : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  rw [gaussProfileSub, rayProfileReal, _root_.HTGeometry.besselLaplaceProfile, hbu,
    Real.sq_sqrt hub, hsplit, hdiv, h2b, hA]
  field_simp
  ring_nf
  exact Real.sq_sqrt hb.le

/-- **The Gaussian form of the Schläfli integral, transported to the ray**, for a real spectral
parameter. -/
theorem integral_gaussProfile_eq_ray {b : ℝ} (hb : 0 < b) :
    ∫ v in Ioi (0 : ℝ), _root_.HTGeometry.besselLaplaceProfile v * Real.exp (-(b * v ^ 2))
      = (2 * Real.sqrt (2 * b))⁻¹ * ∫ u in Ioi (0 : ℝ), rayProfileReal b u := by
  have h1 : ∫ v in Ioi (0 : ℝ), _root_.HTGeometry.besselLaplaceProfile v * Real.exp (-(b * v ^ 2))
      = ∫ y in Ioi (0 : ℝ), gaussProfileSub b y := by
    rw [← integral_comp_rpow_Ioi (gaussProfileSub b) (two_ne_zero)]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hr1 : x ^ ((2 : ℝ) - 1) = x := by norm_num
    have hr2 : x ^ (2 : ℝ) = x ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hr1, hr2, smul_eq_mul, abs_two]
    exact (gaussProfileSub_sq hx0).symm
  have hbinv : (0 : ℝ) < b⁻¹ := by positivity
  have h2 : ∫ y in Ioi (0 : ℝ), gaussProfileSub b y
      = b⁻¹ * ∫ u in Ioi (0 : ℝ), gaussProfileSub b (u / b) := by
    have hmul := MeasureTheory.integral_comp_mul_left_Ioi (gaussProfileSub b) 0 hbinv
    rw [mul_zero, inv_inv, smul_eq_mul] at hmul
    have hfun : ∀ u : ℝ, gaussProfileSub b (b⁻¹ * u) = gaussProfileSub b (u / b) := by
      intro u
      rw [inv_mul_eq_div]
    simp only [hfun] at hmul
    rw [hmul]
    field_simp
  rw [h1, h2, ← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu => gaussProfileSub_div_eq hb hu

end RealRay

section ComplexRay

/-- A shell power on the ray. -/
def rayShellPow (z : ℂ) (u α : ℝ) : ℂ := (1 + (u : ℂ) / (2 * z)) ^ ((α : ℝ) : ℂ)

/-- The integrand of the ray representation of the order-one Schläfli integral. -/
def besselK1RayIntegrand (z : ℂ) (u : ℝ) : ℂ :=
  ((Real.exp (-u) / Real.sqrt u : ℝ) : ℂ)
    * (2 * rayShellPow z u (1 / 2) - rayShellPow z u (-1 / 2))

/-- The ray representation integral. -/
def besselK1Ray (z : ℂ) : ℂ := ∫ u in Ioi (0 : ℝ), besselK1RayIntegrand z u

theorem besselK1RayIntegrand_ofReal {b : ℝ} (hb : 0 < b) {u : ℝ} (hu : 0 ≤ u) :
    besselK1RayIntegrand (b : ℂ) u = ((rayProfileReal b u : ℝ) : ℂ) := by
  have hq0 : (0 : ℝ) ≤ 1 + u / (2 * b) := by positivity
  have hbase : (1 : ℂ) + (u : ℂ) / (2 * (b : ℂ)) = ((1 + u / (2 * b) : ℝ) : ℂ) := by
    push_cast
    ring
  have hpow : ∀ α : ℝ, rayShellPow (b : ℂ) u α = (((1 + u / (2 * b)) ^ α : ℝ) : ℂ) := by
    intro α
    rw [rayShellPow, hbase, Complex.ofReal_cpow hq0]
  have hhalf : ((1 + u / (2 * b)) ^ ((1 : ℝ) / 2) : ℝ) = Real.sqrt (1 + u / (2 * b)) := by
    rw [Real.sqrt_eq_rpow]
  have hneg : ((1 + u / (2 * b)) ^ ((-1 : ℝ) / 2) : ℝ)
      = (Real.sqrt (1 + u / (2 * b)))⁻¹ := by
    rw [Real.sqrt_eq_rpow, show ((-1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hq0]
  rw [besselK1RayIntegrand, hpow, hpow, hhalf, hneg, rayProfileReal]
  push_cast
  ring

theorem besselK1Ray_ofReal {b : ℝ} (hb : 0 < b) :
    besselK1Ray (b : ℂ) = ((∫ u in Ioi (0 : ℝ), rayProfileReal b u : ℝ) : ℂ) := by
  rw [besselK1Ray, ← integral_complex_ofReal]
  exact setIntegral_congr_fun measurableSet_Ioi fun u hu =>
    besselK1RayIntegrand_ofReal hb (le_of_lt hu)

/-- **The ray representation at a real spectral parameter.** -/
theorem besselK1C_ofReal_eq_ray {b : ℝ} (hb : 0 < b) :
    _root_.HTGeometry.besselK1C (b : ℂ)
      = Complex.exp (-(b : ℂ)) * ((Real.sqrt (2 * b) : ℝ) : ℂ)⁻¹ * besselK1Ray (b : ℂ) := by
  have hre : (0 : ℝ) < ((b : ℝ) : ℂ).re := by simpa using hb
  have hgauss := besselK1C_eq_gauss hre
  have hptw : ∀ v : ℝ, ((_root_.HTGeometry.besselLaplaceProfile v : ℝ) : ℂ)
      * Complex.exp (-(b : ℂ) * (v : ℂ) ^ 2)
      = ((_root_.HTGeometry.besselLaplaceProfile v * Real.exp (-(b * v ^ 2)) : ℝ) : ℂ) := by
    intro v
    have hexp : Complex.exp (-(b : ℂ) * (v : ℂ) ^ 2)
        = ((Real.exp (-(b * v ^ 2)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring
  have hint : (∫ v in Ioi (0 : ℝ), ((_root_.HTGeometry.besselLaplaceProfile v : ℝ) : ℂ)
        * Complex.exp (-(b : ℂ) * (v : ℂ) ^ 2))
      = (((2 * Real.sqrt (2 * b))⁻¹ * ∫ u in Ioi (0 : ℝ), rayProfileReal b u : ℝ) : ℂ) := by
    rw [← integral_gaussProfile_eq_ray hb, ← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi fun v _ => hptw v
  have hs2b : (0 : ℝ) < Real.sqrt (2 * b) := Real.sqrt_pos.2 (by linarith)
  have hs2bne : ((Real.sqrt (2 * b) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hs2b
  rw [hgauss, hint, besselK1Ray_ofReal hb]
  push_cast
  field_simp

end ComplexRay

end

end GaloisForLFunctions.HTGeometry
