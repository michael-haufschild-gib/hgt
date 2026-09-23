import GaloisForLFunctions.RHTower.CCMUnitRieszCompletedSourceWeld
import GaloisForLFunctions.RHTower.CCMHankelGapTraceSlope

/-!
# Unit-Riesz four-unit Cesàro curvature

The unit-Riesz completed-source test, after the cubic reweighting forced by the CCM-FU
third-grade source, has an exact two-exponential second derivative.  This file proves its
derivative algebra, the fast/slow polynomial ratio, the limiting signed two-channel kernel, its
four-unit zero at `4 log 2`, and the two-unit loss of origin monotonicity of the original test.

These are unconditional source-side identities.  They assert neither the remaining arithmetic
lower bound nor RH.
-/

open Complex Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Cubically renormalized source test used when the completed current is rewritten through the
CCM-FU third-grade cumulative source. -/
def unitRieszCesaroTest (t s : ℝ) : ℝ :=
  (3 / 32) * (s ^ (3 : ℕ) *
    (Real.exp (-t + s / 2) - Real.exp (-3 * t / 2 + s)))

def unitRieszCesaroTestDeriv (t s : ℝ) : ℝ :=
  (3 / 32) *
    (3 * s ^ (2 : ℕ) * (Real.exp (-t + s / 2) - Real.exp (-3 * t / 2 + s)) +
      s ^ (3 : ℕ) * ((1 / 2) * Real.exp (-t + s / 2) -
        Real.exp (-3 * t / 2 + s)))

/-- Slow half-rate polynomial in the second derivative. -/
def unitRieszCesaroSlowPolynomial (s : ℝ) : ℝ :=
  6 * s + 3 * s ^ (2 : ℕ) + s ^ (3 : ℕ) / 4

/-- Fast unit-rate polynomial in the second derivative. -/
def unitRieszCesaroFastPolynomial (s : ℝ) : ℝ :=
  6 * s + 6 * s ^ (2 : ℕ) + s ^ (3 : ℕ)

def unitRieszCesaroTestSecondDeriv (t s : ℝ) : ℝ :=
  (3 / 32) *
    (6 * s * (Real.exp (-t + s / 2) - Real.exp (-3 * t / 2 + s)) +
      6 * s ^ (2 : ℕ) * ((1 / 2) * Real.exp (-t + s / 2) -
        Real.exp (-3 * t / 2 + s)) +
      s ^ (3 : ℕ) * ((1 / 4) * Real.exp (-t + s / 2) -
        Real.exp (-3 * t / 2 + s)))

private theorem hasDerivAt_slowExp (t s : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-t + x / 2))
      ((1 / 2) * Real.exp (-t + s / 2)) s := by
  simpa only [Function.comp_def, id_eq, mul_comm] using
    (Real.hasDerivAt_exp (-t + s / 2)).comp s
      (((hasDerivAt_id s).div_const 2).const_add (-t))

private theorem hasDerivAt_fastExp (t s : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-3 * t / 2 + x))
      (Real.exp (-3 * t / 2 + s)) s := by
  simpa only [Function.comp_def, id_eq, mul_one] using
    (Real.hasDerivAt_exp (-3 * t / 2 + s)).comp s
      ((hasDerivAt_id s).const_add (-3 * t / 2))

theorem hasDerivAt_unitRieszCesaroTest (t s : ℝ) :
    HasDerivAt (unitRieszCesaroTest t) (unitRieszCesaroTestDeriv t s) s := by
  have hp : HasDerivAt (fun x : ℝ => x ^ (3 : ℕ)) (3 * s ^ (2 : ℕ)) s := by
    exact (hasDerivAt_pow 3 s).congr_deriv (by norm_num)
  have he := (hasDerivAt_slowExp t s).sub (hasDerivAt_fastExp t s)
  unfold unitRieszCesaroTest unitRieszCesaroTestDeriv
  simpa only [Pi.mul_apply, Pi.sub_apply] using
    (hp.mul he).const_mul (3 / 32)

theorem unitRieszCesaroTestDeriv_endpoint (t : ℝ) :
    unitRieszCesaroTestDeriv t t = -(3 / 64) * t ^ (3 : ℕ) * Real.exp (-t / 2) := by
  rw [unitRieszCesaroTestDeriv]
  have he : Real.exp (-t + t / 2) = Real.exp (-3 * t / 2 + t) := by
    congr 1
    ring
  rw [he]
  ring

theorem hasDerivAt_unitRieszCesaroTestDeriv (t s : ℝ) :
    HasDerivAt (unitRieszCesaroTestDeriv t)
      (unitRieszCesaroTestSecondDeriv t s) s := by
  have hs2 : HasDerivAt (fun x : ℝ => x ^ (2 : ℕ)) (2 * s) s := by
    exact (hasDerivAt_pow 2 s).congr_deriv (by norm_num)
  have hs3 : HasDerivAt (fun x : ℝ => x ^ (3 : ℕ)) (3 * s ^ (2 : ℕ)) s := by
    exact (hasDerivAt_pow 3 s).congr_deriv (by norm_num)
  have hA := hasDerivAt_slowExp t s
  have hB := hasDerivAt_fastExp t s
  have hAB := hA.sub hB
  have hhalfRaw := (hA.const_mul (1 / 2)).sub hB
  have hhalf := hhalfRaw.congr_deriv (show
      (1 / 2) * ((1 / 2) * Real.exp (-t + s / 2)) -
          Real.exp (-3 * t / 2 + s) =
        (1 / 4) * Real.exp (-t + s / 2) - Real.exp (-3 * t / 2 + s) by ring)
  have hleft := ((hs2.const_mul 3).mul hAB)
  have hright := hs3.mul hhalf
  have htotal := (hleft.add hright).const_mul (3 / 32)
  have htotal' := htotal.congr_deriv (show
      (3 / 32) *
          (3 * (2 * s) *
              (Real.exp (-t + s / 2) - Real.exp (-3 * t / 2 + s)) +
            3 * s ^ (2 : ℕ) * ((1 / 2) * Real.exp (-t + s / 2) -
              Real.exp (-3 * t / 2 + s)) +
            (3 * s ^ (2 : ℕ) * ((1 / 2) * Real.exp (-t + s / 2) -
                Real.exp (-3 * t / 2 + s)) +
              s ^ (3 : ℕ) * ((1 / 4) * Real.exp (-t + s / 2) -
                Real.exp (-3 * t / 2 + s)))) =
        unitRieszCesaroTestSecondDeriv t s by
          rw [unitRieszCesaroTestSecondDeriv]
          ring)
  simpa only [unitRieszCesaroTestDeriv, Pi.mul_apply, Pi.add_apply,
    Pi.sub_apply] using! htotal'

theorem unitRieszCesaroTestSecondDeriv_eq_polynomials (t s : ℝ) :
    unitRieszCesaroTestSecondDeriv t s =
      (3 / 32) *
        (Real.exp (-t + s / 2) * unitRieszCesaroSlowPolynomial s -
          Real.exp (-3 * t / 2 + s) * unitRieszCesaroFastPolynomial s) := by
  rw [unitRieszCesaroTestSecondDeriv, unitRieszCesaroSlowPolynomial,
    unitRieszCesaroFastPolynomial]
  ring

theorem unitRieszCesaroFast_div_slow
    {s : ℝ} (hs : 0 < s) :
    unitRieszCesaroFastPolynomial s / unitRieszCesaroSlowPolynomial s =
      4 * (s ^ (2 : ℕ) + 6 * s + 6) / (s ^ (2 : ℕ) + 12 * s + 24) := by
  rw [unitRieszCesaroSlowPolynomial, unitRieszCesaroFastPolynomial]
  have hden : s ^ (2 : ℕ) + 12 * s + 24 ≠ 0 := by
    positivity
  field_simp [hs.ne', hden]
  ring

/-- Limiting normalized FU-to-UR Cesàro curvature kernel. -/
def unitRieszCesaroCurvatureKernel (u : ℝ) : ℝ :=
  (3 / 32) * (Real.exp (-u) - (1 / 4) * Real.exp (-u / 2))

/-- Positive fast leak density in the canonical two-channel lift. -/
def unitRieszCesaroFastLeakDensity (u : ℝ) : ℝ :=
  (3 / 32) * Real.exp (-u)

/-- Positive slow leak density in the canonical two-channel lift. -/
def unitRieszCesaroSlowLeakDensity (u : ℝ) : ℝ :=
  (3 / 128) * Real.exp (-u / 2)

theorem unitRieszCesaroCurvatureKernel_eq_fast_sub_slow (u : ℝ) :
    unitRieszCesaroCurvatureKernel u =
      unitRieszCesaroFastLeakDensity u - unitRieszCesaroSlowLeakDensity u := by
  rw [unitRieszCesaroCurvatureKernel, unitRieszCesaroFastLeakDensity,
    unitRieszCesaroSlowLeakDensity]
  ring

theorem unitRieszCesaroCurvatureKernel_eq_factored (u : ℝ) :
    unitRieszCesaroCurvatureKernel u =
      ((3 / 32) * Real.exp (-u / 2)) *
        (Real.exp (-u / 2) - 1 / 4) := by
  rw [unitRieszCesaroCurvatureKernel]
  have he : Real.exp (-u) = Real.exp (-u / 2) * Real.exp (-u / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

private theorem exp_neg_two_log_two :
    Real.exp (-(2 * Real.log 2)) = (1 / 4 : ℝ) := by
  rw [Real.exp_neg,
    show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
    Real.exp_add, Real.exp_log (by norm_num)]
  norm_num [div_eq_mul_inv]

/-- Exact positive side of the limiting four-unit sign wall. -/
theorem unitRieszCesaroCurvatureKernel_pos_iff (u : ℝ) :
    0 < unitRieszCesaroCurvatureKernel u ↔ u < 4 * Real.log 2 := by
  have hfront : 0 < (3 / 32 : ℝ) * Real.exp (-u / 2) := by positivity
  have hbracket :
      0 < Real.exp (-u / 2) - 1 / 4 ↔ u < 4 * Real.log 2 := by
    rw [sub_pos, ← exp_neg_two_log_two, Real.exp_lt_exp]
    constructor <;> intro h <;> linarith
  rw [unitRieszCesaroCurvatureKernel_eq_factored, mul_pos_iff]
  constructor
  · rintro (h | h)
    · exact hbracket.mp h.2
    · linarith
  · intro h
    exact Or.inl ⟨hfront, hbracket.mpr h⟩

/-- Exact negative side of the limiting four-unit sign wall. -/
theorem unitRieszCesaroCurvatureKernel_neg_iff (u : ℝ) :
    unitRieszCesaroCurvatureKernel u < 0 ↔ 4 * Real.log 2 < u := by
  have hfront : 0 < (3 / 32 : ℝ) * Real.exp (-u / 2) := by positivity
  have hbracket :
      Real.exp (-u / 2) - 1 / 4 < 0 ↔ 4 * Real.log 2 < u := by
    rw [sub_neg, ← exp_neg_two_log_two, Real.exp_lt_exp]
    constructor <;> intro h <;> linarith
  rw [unitRieszCesaroCurvatureKernel_eq_factored, mul_neg_iff]
  constructor
  · rintro (h | h)
    · exact hbracket.mp h.2
    · linarith
  · intro h
    exact Or.inl ⟨hfront, hbracket.mpr h⟩

theorem integral_Ioi_mul_rexp_neg_mul
    {b : ℝ} (hb : 0 < b) :
    (∫ u in Set.Ioi (0 : ℝ), u * Real.exp (-(b * u))) = 1 / b ^ (2 : ℕ) := by
  have hbC : 0 < ((b : ℂ)).re := by simpa using hb
  have hc := integral_Ioi_sub_mul_cexp_neg_mul (b := (b : ℂ)) hbC
    (u := (0 : ℝ)) (le_refl 0)
  have hpoint : ∀ u : ℝ,
      (((u * Real.exp (-(b * u)) : ℝ) : ℂ)) =
        ((u : ℂ) - (0 : ℂ)) * Complex.exp (-((b : ℂ) * (u : ℂ))) := by
    intro u
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring
  have hcast :
      (((∫ u in Set.Ioi (0 : ℝ), u * Real.exp (-(b * u))) : ℝ) : ℂ) =
        (((1 / b ^ (2 : ℕ) : ℝ)) : ℂ) := by
    calc
      (((∫ u in Set.Ioi (0 : ℝ), u * Real.exp (-(b * u))) : ℝ) : ℂ) =
          ∫ u in Set.Ioi (0 : ℝ),
            (((u * Real.exp (-(b * u)) : ℝ) : ℂ)) :=
        integral_complex_ofReal.symm
      _ = ∫ u in Set.Ioi (0 : ℝ),
          ((u : ℂ) - (0 : ℂ)) * Complex.exp (-((b : ℂ) * (u : ℂ))) :=
        setIntegral_congr_fun measurableSet_Ioi fun u _ => hpoint u
      _ = Complex.exp (-((b : ℂ) * (0 : ℂ))) * (b : ℂ)⁻¹ ^ (2 : ℕ) := hc
      _ = (((1 / b ^ (2 : ℕ) : ℝ)) : ℂ) := by
        rw [mul_zero, neg_zero, Complex.exp_zero, one_mul]
        push_cast
        field_simp [hb.ne']
  exact_mod_cast hcast

theorem integral_unitRieszCesaroFastLeakDensity :
    (∫ u in Set.Ioi (0 : ℝ), unitRieszCesaroFastLeakDensity u) = 3 / 32 := by
  rw [show (fun u : ℝ => unitRieszCesaroFastLeakDensity u) =
      fun u => (3 / 32) * Real.exp (-(1 * u)) by
    funext u
    rw [unitRieszCesaroFastLeakDensity]
    congr 2
    ring]
  rw [integral_const_mul, integral_Ioi_rexp_neg_mul_shift (by norm_num) 0]
  norm_num

theorem integral_unitRieszCesaroSlowLeakDensity :
    (∫ u in Set.Ioi (0 : ℝ), unitRieszCesaroSlowLeakDensity u) = 3 / 64 := by
  rw [show (fun u : ℝ => unitRieszCesaroSlowLeakDensity u) =
      fun u => (3 / 128) * Real.exp (-((1 / 2) * u)) by
    funext u
    rw [unitRieszCesaroSlowLeakDensity]
    congr 2
    ring]
  rw [integral_const_mul, integral_Ioi_rexp_neg_mul_shift (by norm_num) 0]
  norm_num

theorem integral_mul_unitRieszCesaroFastLeakDensity :
    (∫ u in Set.Ioi (0 : ℝ), u * unitRieszCesaroFastLeakDensity u) = 3 / 32 := by
  rw [show (fun u : ℝ => u * unitRieszCesaroFastLeakDensity u) =
      fun u => (3 / 32) * (u * Real.exp (-(1 * u))) by
    funext u
    rw [unitRieszCesaroFastLeakDensity]
    ring]
  rw [integral_const_mul, integral_Ioi_mul_rexp_neg_mul (by norm_num)]
  norm_num

theorem integral_mul_unitRieszCesaroSlowLeakDensity :
    (∫ u in Set.Ioi (0 : ℝ), u * unitRieszCesaroSlowLeakDensity u) = 3 / 32 := by
  rw [show (fun u : ℝ => u * unitRieszCesaroSlowLeakDensity u) =
      fun u => (3 / 128) * (u * Real.exp (-((1 / 2) * u))) by
    funext u
    rw [unitRieszCesaroSlowLeakDensity]
    ring]
  rw [integral_const_mul, integral_Ioi_mul_rexp_neg_mul (by norm_num)]
  norm_num

/-- The signed interior curvature channel has mass `3/64`, exactly canceled by its boundary
counterterm, while its two positive lifts have the same barycenter. -/
theorem unitRieszCesaro_twoChannel_mass_barycenter :
    (∫ u in Set.Ioi (0 : ℝ), unitRieszCesaroFastLeakDensity u) -
          ∫ u in Set.Ioi (0 : ℝ), unitRieszCesaroSlowLeakDensity u = 3 / 64 ∧
      (∫ u in Set.Ioi (0 : ℝ), u * unitRieszCesaroFastLeakDensity u) =
        ∫ u in Set.Ioi (0 : ℝ), u * unitRieszCesaroSlowLeakDensity u := by
  rw [integral_unitRieszCesaroFastLeakDensity,
    integral_unitRieszCesaroSlowLeakDensity,
    integral_mul_unitRieszCesaroFastLeakDensity,
    integral_mul_unitRieszCesaroSlowLeakDensity]
  norm_num

theorem unitRieszCesaroCurvatureKernel_fourUnitWall :
    unitRieszCesaroCurvatureKernel (4 * Real.log 2) = 0 := by
  rw [unitRieszCesaroCurvatureKernel]
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have hpos2 : Real.exp (2 * Real.log 2) = 4 := by
    rw [show 2 * Real.log 2 = Real.log 2 + Real.log 2 by ring,
      Real.exp_add, h2]
    norm_num
  have hneg2 : Real.exp (-(2 * Real.log 2)) = 1 / 4 := by
    rw [Real.exp_neg, hpos2]
    norm_num [div_eq_mul_inv]
  have hneg4 : Real.exp (-(4 * Real.log 2)) = 1 / 16 := by
    rw [Real.exp_neg,
      show 4 * Real.log 2 = 2 * Real.log 2 + 2 * Real.log 2 by ring,
      Real.exp_add, hpos2]
    norm_num
  rw [show -(4 * Real.log 2) = -(4 * Real.log 2) by rfl,
    show -(4 * Real.log 2) / 2 = -(2 * Real.log 2) by ring,
    hneg4, hneg2]
  ring

theorem unitRieszCompletedSourceTestDeriv_zero_eq (t : ℝ) :
    unitRieszCompletedSourceTestDeriv t 0 =
      Complex.ofReal
        (3 * Real.exp (-3 * t / 2) * (Real.exp (t / 2) / 2 - 1)) := by
  rw [unitRieszCompletedSourceTestDeriv]
  congr 1
  simp only [zero_div, add_zero]
  rw [show Real.exp (-t) = Real.exp (-3 * t / 2) * Real.exp (t / 2) by
    rw [← Real.exp_add]; congr 1; ring]
  ring

/-- Beyond two logarithmic units, the real completed-source test increases at the origin.  Hence
its cofinal half-profile cannot be a differentiable real stationary autocorrelation. -/
theorem unitRieszCompletedSourceTestDeriv_zero_re_pos
    {t : ℝ} (ht : 2 * Real.log 2 < t) :
    0 < (unitRieszCompletedSourceTestDeriv t 0).re := by
  rw [unitRieszCompletedSourceTestDeriv_zero_eq, Complex.ofReal_re]
  have he : 2 < Real.exp (t / 2) := by
    have hlog : Real.log 2 < t / 2 := by linarith
    have := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log (by norm_num)] at this
  have hpos : 0 < Real.exp (-3 * t / 2) := Real.exp_pos _
  have hbracket : 0 < Real.exp (t / 2) / 2 - 1 := by linarith
  positivity

end GaloisForLFunctions.RHTower

end
