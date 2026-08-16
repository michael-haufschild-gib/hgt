import GaloisForLFunctions.RHTower.XiMassFourierBesselIdentity
import GaloisForLFunctions.RHTower.XiMassBesselConeEnvelope
import GaloisForLFunctions.HTGeometry.BesselOrderDerivativeEnvelope

/-!
# The height derivative of the mass Fourier profile

Writing the Fourier–Bessel identity as a function of a complex height variable,

`Φ(w) = 2aτ/z(w) · K₁(a z(w))`,  `z(w) = √(τ² + w²)`,

the principal-root geometry `z'(w) = w/z(w)` gives the closed derivative

`Φ'(w) = 2aτ w (a K₁'(a z) z − K₁(a z)) / z³`.

All three ratios `‖τ‖/‖z‖`, `|h|/‖z‖`, `1/‖z‖` are bounded outside a fixed slope cone, and the
Schläfli envelopes of `K₁` and `K₁'` agree up to a constant, so the derivative obeys the same
exterior envelope as the profile itself.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The height derivative in closed form -/

/-- The Bessel side as a function of a complex height. -/
def xiMassBesselHeightSide (a : ℝ) (τ w : ℂ) : ℂ :=
  2 * (a : ℂ) * τ / HTGeometry.csqrt (τ ^ 2 + w ^ 2)
    * HTGeometry.besselK1C ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + w ^ 2))

theorem xiMassBesselHeightSide_ofReal (a h : ℝ) (τ : ℂ) :
    xiMassBesselHeightSide a τ (h : ℂ) = xiMassBesselSide a h τ := rfl

/-- The closed height derivative of the Bessel side. -/
def xiMassBesselHeightDeriv (a : ℝ) (τ w : ℂ) : ℂ :=
  2 * (a : ℂ) * τ * w
    * ((a : ℂ) * HTGeometry.besselK1CDeriv ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + w ^ 2))
        * HTGeometry.csqrt (τ ^ 2 + w ^ 2)
      - HTGeometry.besselK1C ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + w ^ 2)))
    / HTGeometry.csqrt (τ ^ 2 + w ^ 2) ^ 3

/-- **The height derivative of the Bessel side.** -/
theorem hasDerivAt_xiMassBesselHeightSide {a : ℝ} {τ w : ℂ} (ha : 0 < a)
    (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    HasDerivAt (xiMassBesselHeightSide a τ) (xiMassBesselHeightDeriv a τ w) w := by
  have hzne : HTGeometry.csqrt (τ ^ 2 + w ^ 2) ≠ 0 := HTGeometry.csqrt_ne_zero hw
  have hre : 0 < ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + w ^ 2)).re := by
    have hval : ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + w ^ 2)).re
        = a * HTGeometry.csqrtRe (τ ^ 2 + w ^ 2) := by
      rw [Complex.mul_re, HTGeometry.csqrt_re]
      simp
    rw [hval]
    exact mul_pos ha (HTGeometry.csqrtRe_pos hw)
  have hq : HasDerivAt (fun v : ℂ => τ ^ 2 + v ^ 2) (2 * w) w := by
    have h1 := (hasDerivAt_pow 2 w).const_add (τ ^ 2)
    simpa using h1
  have hz : HasDerivAt (fun v : ℂ => HTGeometry.csqrt (τ ^ 2 + v ^ 2))
      ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)) w := by
    have h1 : HasDerivAt (HTGeometry.csqrt ∘ fun v : ℂ => τ ^ 2 + v ^ 2)
        ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)) w :=
      (HTGeometry.hasStrictDerivAt_csqrt hw).hasDerivAt.comp w hq
    exact h1
  have hconst : HasDerivAt (fun _ : ℂ => 2 * (a : ℂ) * τ) 0 w := hasDerivAt_const w _
  have hdiv : HasDerivAt (fun v : ℂ => 2 * (a : ℂ) * τ / HTGeometry.csqrt (τ ^ 2 + v ^ 2))
      ((0 * HTGeometry.csqrt (τ ^ 2 + w ^ 2)
        - 2 * (a : ℂ) * τ * ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)))
        / HTGeometry.csqrt (τ ^ 2 + w ^ 2) ^ 2) w := by
    have h1 : HasDerivAt ((fun _ : ℂ => 2 * (a : ℂ) * τ)
        / fun v : ℂ => HTGeometry.csqrt (τ ^ 2 + v ^ 2))
        ((0 * HTGeometry.csqrt (τ ^ 2 + w ^ 2)
          - 2 * (a : ℂ) * τ * ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)))
          / HTGeometry.csqrt (τ ^ 2 + w ^ 2) ^ 2) w :=
      hconst.div hz hzne
    exact h1
  have hinner : HasDerivAt (fun v : ℂ => (a : ℂ) * HTGeometry.csqrt (τ ^ 2 + v ^ 2))
      ((a : ℂ) * ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w))) w := hz.const_mul _
  have hbes : HasDerivAt
      (fun v : ℂ => HTGeometry.besselK1C ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + v ^ 2)))
      (HTGeometry.besselK1CDeriv ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + w ^ 2))
        * ((a : ℂ) * ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)))) w := by
    have h1 : HasDerivAt (HTGeometry.besselK1C
        ∘ fun v : ℂ => (a : ℂ) * HTGeometry.csqrt (τ ^ 2 + v ^ 2))
        (HTGeometry.besselK1CDeriv ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + w ^ 2))
          * ((a : ℂ) * ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)))) w :=
      (HTGeometry.hasDerivAt_besselK1C_deriv hre).comp w hinner
    exact h1
  have hprod := hdiv.mul hbes
  have heq : (0 * HTGeometry.csqrt (τ ^ 2 + w ^ 2)
        - 2 * (a : ℂ) * τ * ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w)))
        / HTGeometry.csqrt (τ ^ 2 + w ^ 2) ^ 2
      * HTGeometry.besselK1C ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + w ^ 2))
      + 2 * (a : ℂ) * τ / HTGeometry.csqrt (τ ^ 2 + w ^ 2)
        * (HTGeometry.besselK1CDeriv ((a : ℂ) * HTGeometry.csqrt (τ ^ 2 + w ^ 2))
          * ((a : ℂ) * ((2 * HTGeometry.csqrt (τ ^ 2 + w ^ 2))⁻¹ * (2 * w))))
      = xiMassBesselHeightDeriv a τ w := by
    rw [xiMassBesselHeightDeriv]
    field_simp
    ring
  rw [← heq]
  exact hprod

/-! ## The exterior envelope of the derivative -/

/-- The generic exterior bound for the closed derivative expression. -/
theorem norm_besselHeightDerivCore_le {a t E : ℝ} {τ z : ℂ} (ha : 0 < a) (hz : 0 < z.re)
    (hE : 0 ≤ E)
    (hE1 : ‖HTGeometry.besselK1C ((a : ℂ) * z)‖ ≤ E)
    (hE2 : ‖HTGeometry.besselK1CDeriv ((a : ℂ) * z)‖ ≤ E) :
    ‖2 * (a : ℂ) * τ * (t : ℂ)
        * ((a : ℂ) * HTGeometry.besselK1CDeriv ((a : ℂ) * z) * z
          - HTGeometry.besselK1C ((a : ℂ) * z)) / z ^ 3‖
      ≤ 2 * a * (‖τ‖ / ‖z‖) * (|t| / ‖z‖) * (a + 1 / z.re) * E := by
  have hzn : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le hz (Complex.re_le_norm z)
  have hnum : ‖(a : ℂ) * HTGeometry.besselK1CDeriv ((a : ℂ) * z) * z
      - HTGeometry.besselK1C ((a : ℂ) * z)‖ ≤ (a * ‖z‖ + 1) * E := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖(a : ℂ) * HTGeometry.besselK1CDeriv ((a : ℂ) * z) * z‖
        = a * ‖HTGeometry.besselK1CDeriv ((a : ℂ) * z)‖ * ‖z‖ := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    rw [h1]
    have h2 : a * ‖HTGeometry.besselK1CDeriv ((a : ℂ) * z)‖ * ‖z‖ ≤ a * E * ‖z‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE2 ha.le) hzn.le
    nlinarith [h2, hE1]
  have hsplit : ‖2 * (a : ℂ) * τ * (t : ℂ)
      * ((a : ℂ) * HTGeometry.besselK1CDeriv ((a : ℂ) * z) * z
        - HTGeometry.besselK1C ((a : ℂ) * z)) / z ^ 3‖
      = 2 * a * ‖τ‖ * |t| * ‖(a : ℂ) * HTGeometry.besselK1CDeriv ((a : ℂ) * z) * z
          - HTGeometry.besselK1C ((a : ℂ) * z)‖ / ‖z‖ ^ 3 := by
    have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [norm_div, norm_pow, norm_mul, norm_mul, norm_mul, norm_mul, h2, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha]
  rw [hsplit, div_le_iff₀ (by positivity : (0 : ℝ) < ‖z‖ ^ 3)]
  have hcoef : (0 : ℝ) ≤ 2 * a * ‖τ‖ * |t| := by positivity
  have hstep := mul_le_mul_of_nonneg_left hnum hcoef
  refine hstep.trans ?_
  have hratio : (1 : ℝ) ≤ ‖z‖ / z.re := (one_le_div hz).2 (Complex.re_le_norm z)
  have hkey : a * ‖z‖ + 1 ≤ (a + 1 / z.re) * ‖z‖ := by
    have hd : (a + 1 / z.re) * ‖z‖ = a * ‖z‖ + ‖z‖ / z.re := by
      field_simp
    rw [hd]
    linarith
  have hgoal : 2 * a * (‖τ‖ / ‖z‖) * (|t| / ‖z‖) * (a + 1 / z.re) * E * ‖z‖ ^ 3
      = 2 * a * ‖τ‖ * |t| * (((a + 1 / z.re) * ‖z‖) * E) := by
    field_simp
    ring
  rw [hgoal]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hkey hE) hcoef

end

end RHTower
