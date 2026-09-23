import GaloisForLFunctions.RHTower.InfiniteMobiusCriticalBoundaryLayer

/-!
# The critical Möbius Fisher--Stein contact law

The normalized positive squarefree-Möbius channel converges on its moving logarithmic aperture to
the mean-one exponential density.  This file identifies the canonical centered tangent of that
limit and the exact contact identity it satisfies.

The limiting half-density score is `1 - y`.  It has mean zero and unit squared norm against
`exp (-y) dy`; the completed score `2 (1 - y)` therefore carries exactly four units of energy.
Its Laplace transform is `u / (1 + u)^(2 : ℕ)`.  The reciprocal signed Möbius response `1 + u` turns
this score into `u / (1 + u)`; adding the positive escaped-mass transform `1 / (1 + u)` leaves the
constant contact transform `1`.  Equivalently, on the half-line,

`(D + 1) ((1 - y) exp (-y)) + exp (-y) = delta_0`

in the weak/distributional sense.  The final theorem composes this identity with the already
formalized all-prime signed multiplier and proves the corresponding zeta-normalized critical
contact limit.  No zero-location statement or Riemann-hypothesis assumption is used.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The positive mean-one exponential density selected by the critical squarefree-Möbius
boundary layer. -/
def mobiusCriticalExponentialDensity (y : ℝ) : ℝ :=
  Real.exp (-y)

/-- The canonical centered logarithmic score of the critical exponential density. -/
def mobiusCriticalExponentialScore (y : ℝ) : ℝ :=
  1 - y

/-- Every polynomial moment of the critical exponential density is integrable on the positive
half-line. -/
theorem integrableOn_pow_mul_mobiusCriticalExponentialDensity (n : ℕ) :
    IntegrableOn
      (fun y : ℝ => y ^ n * mobiusCriticalExponentialDensity y) (Ioi 0) := by
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn : (-1 : ℝ) < (n : ℝ) := by linarith
  simpa [mobiusCriticalExponentialDensity, Real.rpow_natCast, Real.rpow_one] using
    (integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (n : ℝ)) (b := (1 : ℝ)) hn (by norm_num) (by norm_num))

/-- Exact factorial moments of the critical exponential density. -/
theorem integral_Ioi_pow_mul_mobiusCriticalExponentialDensity (n : ℕ) :
    (∫ y : ℝ in Ioi 0, y ^ n * mobiusCriticalExponentialDensity y) = n.factorial := by
  have ha : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((n + 1 : ℕ) : ℝ)) (r := (1 : ℝ)) ha (by norm_num)
  rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by norm_num] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    simp only [mobiusCriticalExponentialDensity, one_mul]
    rw [show (n : ℝ) + 1 - 1 = (n : ℝ) by ring, Real.rpow_natCast]
  · norm_num

/-- The critical score is centered. -/
theorem integral_Ioi_mobiusCriticalExponentialScore_mul_density :
    (∫ y : ℝ in Ioi 0,
      mobiusCriticalExponentialScore y * mobiusCriticalExponentialDensity y) = 0 := by
  have h0 : IntegrableOn mobiusCriticalExponentialDensity (Ioi 0) := by
    simpa using integrableOn_pow_mul_mobiusCriticalExponentialDensity 0
  have h1 : IntegrableOn
      (fun y : ℝ => y * mobiusCriticalExponentialDensity y) (Ioi 0) := by
    simpa using integrableOn_pow_mul_mobiusCriticalExponentialDensity 1
  rw [show (fun y : ℝ =>
      mobiusCriticalExponentialScore y * mobiusCriticalExponentialDensity y) =
      mobiusCriticalExponentialDensity -
        (fun y : ℝ => y * mobiusCriticalExponentialDensity y) by
    funext y
    simp only [Pi.sub_apply, mobiusCriticalExponentialScore]
    ring]
  calc
    integral (volume.restrict (Ioi 0))
        (mobiusCriticalExponentialDensity -
          fun y : ℝ => y * mobiusCriticalExponentialDensity y) =
        (∫ y : ℝ in Ioi 0, mobiusCriticalExponentialDensity y) -
          ∫ y : ℝ in Ioi 0, y * mobiusCriticalExponentialDensity y :=
      integral_sub h0 h1
    _ = 0 := by
      rw [show (∫ y : ℝ in Ioi 0, mobiusCriticalExponentialDensity y) = 1 by
          simpa using integral_Ioi_pow_mul_mobiusCriticalExponentialDensity 0,
        show (∫ y : ℝ in Ioi 0, y * mobiusCriticalExponentialDensity y) = 1 by
          simpa using integral_Ioi_pow_mul_mobiusCriticalExponentialDensity 1]
      norm_num

/-- The critical score has unit Fisher energy. -/
theorem integral_Ioi_mobiusCriticalExponentialScore_sq_mul_density :
    (∫ y : ℝ in Ioi 0,
      mobiusCriticalExponentialScore y ^ 2 * mobiusCriticalExponentialDensity y) = 1 := by
  have h0 : IntegrableOn mobiusCriticalExponentialDensity (Ioi 0) := by
    simpa using integrableOn_pow_mul_mobiusCriticalExponentialDensity 0
  have h1 : IntegrableOn
      (fun y : ℝ => y * mobiusCriticalExponentialDensity y) (Ioi 0) := by
    simpa using integrableOn_pow_mul_mobiusCriticalExponentialDensity 1
  have h2 : IntegrableOn
      (fun y : ℝ => y ^ 2 * mobiusCriticalExponentialDensity y) (Ioi 0) :=
    integrableOn_pow_mul_mobiusCriticalExponentialDensity 2
  rw [show (fun y : ℝ =>
      mobiusCriticalExponentialScore y ^ 2 * mobiusCriticalExponentialDensity y) =
      (mobiusCriticalExponentialDensity -
        fun y : ℝ => 2 * (y * mobiusCriticalExponentialDensity y)) +
          (fun y : ℝ => y ^ 2 * mobiusCriticalExponentialDensity y) by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, mobiusCriticalExponentialScore]
    ring]
  calc
    integral (volume.restrict (Ioi 0))
        ((mobiusCriticalExponentialDensity -
          fun y : ℝ => 2 * (y * mobiusCriticalExponentialDensity y)) +
            (fun y : ℝ => y ^ 2 * mobiusCriticalExponentialDensity y)) =
        integral (volume.restrict (Ioi 0))
            (mobiusCriticalExponentialDensity -
              fun y : ℝ => 2 * (y * mobiusCriticalExponentialDensity y)) +
          ∫ y : ℝ in Ioi 0, y ^ 2 * mobiusCriticalExponentialDensity y :=
      integral_add (h0.sub (h1.const_mul 2)) h2
    _ = ((∫ y : ℝ in Ioi 0, mobiusCriticalExponentialDensity y) -
          ∫ y : ℝ in Ioi 0, 2 * (y * mobiusCriticalExponentialDensity y)) +
          ∫ y : ℝ in Ioi 0, y ^ 2 * mobiusCriticalExponentialDensity y := by
      exact congrArg
        (fun x => x + ∫ y : ℝ in Ioi 0,
          y ^ 2 * mobiusCriticalExponentialDensity y)
        (integral_sub h0 (h1.const_mul 2))
    _ = 1 := by
      rw [integral_const_mul,
        show (∫ y : ℝ in Ioi 0, mobiusCriticalExponentialDensity y) = 1 by
          simpa using integral_Ioi_pow_mul_mobiusCriticalExponentialDensity 0,
        show (∫ y : ℝ in Ioi 0, y * mobiusCriticalExponentialDensity y) = 1 by
          simpa using integral_Ioi_pow_mul_mobiusCriticalExponentialDensity 1,
        show (∫ y : ℝ in Ioi 0, y ^ 2 * mobiusCriticalExponentialDensity y) = 2 by
          simpa using integral_Ioi_pow_mul_mobiusCriticalExponentialDensity 2]
      norm_num

/-- The completion factor `2` turns the unit score into the exact four-unit pole budget. -/
theorem integral_Ioi_completedMobiusCriticalExponentialScore_energy :
    (∫ y : ℝ in Ioi 0,
      (2 * mobiusCriticalExponentialScore y) ^ 2 *
        mobiusCriticalExponentialDensity y) = 4 := by
  rw [show (fun y : ℝ =>
      (2 * mobiusCriticalExponentialScore y) ^ 2 *
        mobiusCriticalExponentialDensity y) =
      fun y => 4 *
        (mobiusCriticalExponentialScore y ^ 2 *
          mobiusCriticalExponentialDensity y) by
    funext y
    ring]
  rw [integral_const_mul,
    integral_Ioi_mobiusCriticalExponentialScore_sq_mul_density]
  norm_num

/-- Exact polynomial moments for an arbitrary positive exponential rate. -/
theorem integral_Ioi_pow_mul_exp_neg_rate
    (n : ℕ) {c : ℝ} (hc : 0 < c) :
    (∫ y : ℝ in Ioi 0, y ^ n * Real.exp (-(c * y))) =
      n.factorial / c ^ (n + 1) := by
  have ha : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((n + 1 : ℕ) : ℝ)) (r := c) ha hc
  rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by norm_num] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    rw [show (n : ℝ) + 1 - 1 = (n : ℝ) by ring]
    change y ^ n * Real.exp (-(c * y)) =
      y ^ (n : ℝ) * Real.exp (-(c * y))
    rw [Real.rpow_natCast]
  · rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast]
    field_simp [hc.ne']
    rw [one_div, inv_pow]
    exact (mul_inv_cancel₀ (pow_ne_zero _ hc.ne')).symm

/-- Laplace transform of the centered critical score. -/
def mobiusCriticalBoundaryScoreLaplace (u : ℝ) : ℂ :=
  ((u / (1 + u) ^ 2 : ℝ) : ℂ)

/-- The abstract score transform is the actual Laplace transform of the critical exponential
score-density product. -/
theorem ofReal_integral_mobiusCriticalExponentialScore_eq_scoreLaplace
    {u : ℝ} (hu : 0 ≤ u) :
    ((∫ y : ℝ in Ioi 0,
      mobiusCriticalExponentialScore y * mobiusCriticalExponentialDensity y *
        Real.exp (-u * y) : ℝ) : ℂ) =
      mobiusCriticalBoundaryScoreLaplace u := by
  have hrate : 0 < 1 + u := by linarith
  have h0 := integral_Ioi_pow_mul_exp_neg_rate 0 hrate
  have h1 := integral_Ioi_pow_mul_exp_neg_rate 1 hrate
  have h0int : IntegrableOn
      (fun y : ℝ => Real.exp (-((1 + u) * y))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (0 : ℝ)) (b := 1 + u)
      (by norm_num) (by norm_num) hrate
    convert h using 1
    funext y
    simp only [Real.rpow_zero, one_mul, Real.rpow_one]
    congr 1
    ring
  have h1int : IntegrableOn
      (fun y : ℝ => y * Real.exp (-((1 + u) * y))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (1 : ℝ)) (b := 1 + u)
      (by norm_num) (by norm_num) hrate
    convert h using 1
    funext y
    simp only [Real.rpow_one]
    congr 2
    ring
  rw [show (fun y : ℝ =>
      mobiusCriticalExponentialScore y * mobiusCriticalExponentialDensity y *
        Real.exp (-u * y)) =
      fun y => Real.exp (-((1 + u) * y)) -
        y * Real.exp (-((1 + u) * y)) by
    funext y
    simp only [mobiusCriticalExponentialScore, mobiusCriticalExponentialDensity]
    have hexp : Real.exp (-y) * Real.exp (-u * y) =
        Real.exp (-((1 + u) * y)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hexp]
    ring]
  rw [integral_sub h0int h1int]
  rw [show (∫ y : ℝ in Ioi 0, Real.exp (-((1 + u) * y))) = 1 / (1 + u) by
      simpa using h0,
    show (∫ y : ℝ in Ioi 0, y * Real.exp (-((1 + u) * y))) =
        1 / (1 + u) ^ 2 by simpa using h1]
  rw [mobiusCriticalBoundaryScoreLaplace]
  norm_cast
  have hu1 : 1 + u ≠ 0 := ne_of_gt hrate
  field_simp [hu1]
  ring

/-- **Fisher--Stein contact identity.** The reciprocal signed response applied to the centered
score, plus the positive escaped density, is the unit contact transform. -/
theorem mobiusCriticalBoundaryScore_contact {u : ℝ} (hu : 0 ≤ u) :
    (((1 + u : ℝ) : ℂ) * mobiusCriticalBoundaryScoreLaplace u) +
      (((1 + u : ℝ) : ℂ))⁻¹ = 1 := by
  have hu1 : (1 + u : ℝ) ≠ 0 := by linarith
  have hreal :
      (1 + u) * (u / (1 + u) ^ 2) + (1 + u)⁻¹ = (1 : ℝ) := by
    field_simp [hu1]
    ring
  rw [mobiusCriticalBoundaryScoreLaplace]
  exact_mod_cast hreal

/-- **All-prime critical contact limit.** The actual signed Möbius multiplier applied to the
limiting centered score, together with the actual positive squarefree boundary-layer transform,
converges to the constant zeta-normalized contact channel. -/
theorem tendsto_mobiusCriticalBoundaryScore_contact
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto
      (fun sigma : ℝ =>
        infiniteMobiusLaplaceMultiplier sigma
            (mobiusCriticalBoundaryRate sigma u) / (sigma - 1) ^ 2 *
              mobiusCriticalBoundaryScoreLaplace u +
          riemannZeta (2 : ℂ) * squarefreeMobiusBoundaryLayerLaplace sigma u)
      (𝓝[>] (1 : ℝ)) (𝓝 (riemannZeta (2 : ℂ))) := by
  have hsigned := tendsto_infiniteMobiusLaplaceMultiplier_moving_boundary hu
  have hpositive := tendsto_squarefreeMobiusBoundaryLayerLaplace hu
  have h := (hsigned.mul_const (mobiusCriticalBoundaryScoreLaplace u)).add
    (hpositive.const_mul (riemannZeta (2 : ℂ)))
  have hcontact := mobiusCriticalBoundaryScore_contact hu
  have htarget :
      riemannZeta (2 : ℂ) * (((1 + u : ℝ) : ℂ)) *
            mobiusCriticalBoundaryScoreLaplace u +
          riemannZeta (2 : ℂ) * (((1 + u : ℝ) : ℂ))⁻¹ =
        riemannZeta (2 : ℂ) := by
    calc
      _ = riemannZeta (2 : ℂ) *
          ((((1 + u : ℝ) : ℂ) * mobiusCriticalBoundaryScoreLaplace u) +
            (((1 + u : ℝ) : ℂ))⁻¹) := by ring
      _ = riemannZeta (2 : ℂ) := by rw [hcontact]; ring
  rw [htarget] at h
  simpa only [mul_assoc] using h

end RHTower
