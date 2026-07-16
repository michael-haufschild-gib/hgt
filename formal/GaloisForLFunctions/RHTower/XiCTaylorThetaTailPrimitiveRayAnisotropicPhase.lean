import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayInteriorSquare
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayPolarCoordinates
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedProuhetRankTwoCurrent

/-!
# The anisotropic phase on a complete primitive theta ray

The interior primitive-ray multiplier was previously identified as

`(s^2 + (1/2-a)^2)^2`.

The beta exponent and Fourier frequency forced by an upper-half-plane spectral point `z` are
`a = 1/2-z.im` and `s = z.re`.  Therefore the complete multiplier is not merely nonnegative: it
is exactly `normSq z ^ 2`, the squared modulus of the analytic completion monomial `z^2`.

This module also computes the untruncated symmetric phase current in arithmetic primitive-ray
coordinates.  Its radial decay is `exp (-2*z.im*r)`, while its angular oscillation is the Fourier
character with frequency `z.re`.  These identities isolate the exact parameter match needed for
the later global primitive-ray disintegration.  No sign of the finite core or endpoint seam is
asserted here.
-/

open Complex Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- **Anisotropic perfect-square specialization.**  In the open critical half-strip, the
source-selected primitive-ray multiplier is exactly the squared modulus of `z^2`. -/
theorem thetaCuspPrimitiveRayInteriorSpectralMultiplier_anisotropic
    {z : ℂ} (hz : z.im < 1 / 2) :
    thetaCuspPrimitiveRayInteriorSpectralMultiplier
        (1 / 2 - z.im) z.re = Complex.normSq z ^ 2 := by
  rw [thetaCuspPrimitiveRayInteriorSpectralMultiplier_eq_square (by linarith)]
  rw [Complex.normSq_apply]
  ring

/-- The symmetric current kernel of two untruncated spectral phases is one radial damping factor
times the cosine of their logarithmic separation. -/
theorem symmetricHermitianSpectralTranslationPairCurrent_eq
    (z : ℂ) (x y : ℝ) :
    symmetricHermitianPairCurrentKernel
        (fun t : ℝ => spectralTranslationPhase t z)
        (fun t : ℝ => (t : ℂ) * I * spectralTranslationPhase t z)
        (x, y) =
      ((x + y) / 2) * Real.exp (-z.im * (x + y)) *
        Real.cos (z.re * (x - y)) := by
  unfold symmetricHermitianPairCurrentKernel spectralTranslationPhase
  simp only [map_mul, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.exp_conj]
  simp only [mul_assoc]
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [show ((x : ℂ) * (I * z) +
      (y : ℂ) * (-I * (starRingEnd ℂ) z)) =
      ((-z.im * (x + y) : ℝ) : ℂ) +
        ((z.re * (x - y) : ℝ) : ℂ) * I by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring]
  rw [show ((y : ℂ) * (I * z) +
      (x : ℂ) * (-I * (starRingEnd ℂ) z)) =
      ((-z.im * (x + y) : ℝ) : ℂ) -
        ((z.re * (x - y) : ℝ) : ℂ) * I by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, add_zero,
    zero_add]
  simp only [Complex.exp_re, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero]
  simp only [zero_sub, mul_one, one_mul, Real.cos_neg]
  ring

/-- Sum of the two arithmetic primitive-ray logarithmic coordinates. -/
theorem thetaCuspPrimitiveRayArithmeticPolarX_add_Y
    (a b : ℕ) (r u : ℝ) :
    thetaCuspPrimitiveRayArithmeticPolarX a r u +
        thetaCuspPrimitiveRayArithmeticPolarY b r u =
      2 * r + (Real.log u + Real.log (1 - u)) / 2 -
        (Real.log (a : ℝ) + Real.log (b : ℝ)) := by
  unfold thetaCuspPrimitiveRayArithmeticPolarX
    thetaCuspPrimitiveRayArithmeticPolarY
  ring

/-- On the open angular interval, the coordinate sum is controlled by the primitive angular
moment `u(1-u)`. -/
theorem thetaCuspPrimitiveRayArithmeticPolarX_add_Y_eq_moment
    (a b : ℕ) (r : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    thetaCuspPrimitiveRayArithmeticPolarX a r u +
        thetaCuspPrimitiveRayArithmeticPolarY b r u =
      2 * r + Real.log (thetaCuspPrimitiveRayMoment u) / 2 -
        (Real.log (a : ℝ) + Real.log (b : ℝ)) := by
  rw [thetaCuspPrimitiveRayArithmeticPolarX_add_Y]
  unfold thetaCuspPrimitiveRayMoment
  rw [Real.log_mul hu0.ne' (sub_pos.mpr hu1).ne']

/-- Difference of the two arithmetic primitive-ray logarithmic coordinates. -/
theorem thetaCuspPrimitiveRayArithmeticPolarX_sub_Y
    (a b : ℕ) (r u : ℝ) :
    thetaCuspPrimitiveRayArithmeticPolarX a r u -
        thetaCuspPrimitiveRayArithmeticPolarY b r u =
      (Real.log u - Real.log (1 - u)) / 2 -
        (Real.log (a : ℝ) - Real.log (b : ℝ)) := by
  unfold thetaCuspPrimitiveRayArithmeticPolarX
    thetaCuspPrimitiveRayArithmeticPolarY
  ring

/-- **Exact primitive-ray phase current.**  The radial and angular spectral parameters appearing
after the arithmetic polar substitution are respectively `z.im` and `z.re`.  No endpoint window
or completion term has been separated. -/
theorem symmetricHermitianSpectralTranslationPairCurrent_arithmeticPolar_eq
    (z : ℂ) (a b : ℕ) (r : ℝ) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    symmetricHermitianPairCurrentKernel
        (fun t : ℝ => spectralTranslationPhase t z)
        (fun t : ℝ => (t : ℂ) * I * spectralTranslationPhase t z)
        (thetaCuspPrimitiveRayArithmeticPolarX a r u,
          thetaCuspPrimitiveRayArithmeticPolarY b r u) =
      (r + Real.log (thetaCuspPrimitiveRayMoment u) / 4 -
          (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2) *
        Real.exp (-2 * z.im * r -
          (z.im / 2) * Real.log (thetaCuspPrimitiveRayMoment u) +
          z.im * (Real.log (a : ℝ) + Real.log (b : ℝ))) *
        Real.cos (z.re *
          ((Real.log u - Real.log (1 - u)) / 2 -
            (Real.log (a : ℝ) - Real.log (b : ℝ)))) := by
  rw [symmetricHermitianSpectralTranslationPairCurrent_eq,
    thetaCuspPrimitiveRayArithmeticPolarX_add_Y_eq_moment a b r hu0 hu1,
    thetaCuspPrimitiveRayArithmeticPolarX_sub_Y]
  congr 2
  · ring
  · congr 1
    ring

/-! ## The exact positive-half-line chamber -/

/-- The arithmetic first coordinate is the finite-core polar coordinate with the primitive
translation inserted as `-log a`. -/
theorem thetaCuspPrimitiveRayArithmeticPolarX_eq_corePolarX
    (a : ℕ) (r u : ℝ) :
    thetaCuspPrimitiveRayArithmeticPolarX a r u =
      thetaCuspPrimitiveRayCorePolarX r (-Real.log (a : ℝ)) u := by
  unfold thetaCuspPrimitiveRayArithmeticPolarX
    thetaCuspPrimitiveRayCorePolarX
  ring

/-- The arithmetic second coordinate is the finite-core polar coordinate with the primitive
translation inserted as `-log b`. -/
theorem thetaCuspPrimitiveRayArithmeticPolarY_eq_corePolarY
    (b : ℕ) (r u : ℝ) :
    thetaCuspPrimitiveRayArithmeticPolarY b r u =
      thetaCuspPrimitiveRayCorePolarY r (-Real.log (b : ℝ)) u := by
  unfold thetaCuspPrimitiveRayArithmeticPolarY
    thetaCuspPrimitiveRayCorePolarY
  ring

/-- The lower angular inequality is exactly positivity of the first logarithmic source
coordinate. -/
theorem thetaCuspPrimitiveRayCorePolarLowerEndpoint_lt_iff
    (r alpha : ℝ) {u : ℝ} (hu : 0 < u) :
    thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha < u ↔
      0 < thetaCuspPrimitiveRayCorePolarX r alpha u := by
  unfold thetaCuspPrimitiveRayCorePolarLowerEndpoint
  constructor
  · intro h
    have hlog : -2 * (r + alpha) < Real.log u := by
      rw [← Real.exp_lt_exp, Real.exp_log hu]
      exact h
    unfold thetaCuspPrimitiveRayCorePolarX
    linarith
  · intro h
    have hlog : -2 * (r + alpha) < Real.log u := by
      unfold thetaCuspPrimitiveRayCorePolarX at h
      linarith
    rw [← Real.exp_log hu, Real.exp_lt_exp]
    exact hlog

/-- The upper angular inequality is exactly positivity of the second logarithmic source
coordinate. -/
theorem thetaCuspPrimitiveRayCorePolar_lt_upperEndpoint_iff
    (r beta : ℝ) {u : ℝ} (hu : u < 1) :
    u < thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta ↔
      0 < thetaCuspPrimitiveRayCorePolarY r beta u := by
  have hsub : 0 < 1 - u := sub_pos.mpr hu
  unfold thetaCuspPrimitiveRayCorePolarUpperEndpoint
  constructor
  · intro h
    have hexp : Real.exp (-2 * (r + beta)) < 1 - u := by linarith
    rw [← Real.exp_log hsub, Real.exp_lt_exp] at hexp
    unfold thetaCuspPrimitiveRayCorePolarY
    linarith
  · intro h
    have hexp : Real.exp (-2 * (r + beta)) < 1 - u := by
      rw [← Real.exp_log hsub, Real.exp_lt_exp]
      unfold thetaCuspPrimitiveRayCorePolarY at h
      linarith
    linarith

/-- **Exact active quadrant.**  The active angular interval used by the seam-preserving bridge is
neither a majorant nor an auxiliary cutoff: after inserting the arithmetic primitive direction,
it is exactly the preimage of the original positive-half-line quadrant. -/
theorem thetaCuspPrimitiveRayArithmeticPolar_activeDomain_iff
    (a b : ℕ) (r : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    (thetaCuspPrimitiveRayCorePolarLowerEndpoint r (-Real.log (a : ℝ)) < u ∧
        u < thetaCuspPrimitiveRayCorePolarUpperEndpoint r (-Real.log (b : ℝ))) ↔
      (0 < thetaCuspPrimitiveRayArithmeticPolarX a r u ∧
        0 < thetaCuspPrimitiveRayArithmeticPolarY b r u) := by
  rw [thetaCuspPrimitiveRayCorePolarLowerEndpoint_lt_iff
      r (-Real.log (a : ℝ)) hu0,
    thetaCuspPrimitiveRayCorePolar_lt_upperEndpoint_iff
      r (-Real.log (b : ℝ)) hu1,
    ← thetaCuspPrimitiveRayArithmeticPolarX_eq_corePolarX,
    ← thetaCuspPrimitiveRayArithmeticPolarY_eq_corePolarY]

/-- Arithmetic formula for the lower swept endpoint. -/
theorem thetaCuspPrimitiveRayCorePolarLowerEndpoint_neg_log_nat
    {a : ℕ} (ha : 0 < a) (r : ℝ) :
    thetaCuspPrimitiveRayCorePolarLowerEndpoint r (-Real.log (a : ℝ)) =
      (a : ℝ) ^ 2 * Real.exp (-2 * r) := by
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  unfold thetaCuspPrimitiveRayCorePolarLowerEndpoint
  rw [show -2 * (r + -Real.log (a : ℝ)) =
      2 * Real.log (a : ℝ) + -2 * r by ring,
    Real.exp_add]
  rw [show 2 * Real.log (a : ℝ) =
      Real.log (a : ℝ) + Real.log (a : ℝ) by ring,
    Real.exp_add, Real.exp_log haR]
  ring

/-- Arithmetic formula for the upper swept endpoint. -/
theorem thetaCuspPrimitiveRayCorePolarUpperEndpoint_neg_log_nat
    {b : ℕ} (hb : 0 < b) (r : ℝ) :
    thetaCuspPrimitiveRayCorePolarUpperEndpoint r (-Real.log (b : ℝ)) =
      1 - (b : ℝ) ^ 2 * Real.exp (-2 * r) := by
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb
  unfold thetaCuspPrimitiveRayCorePolarUpperEndpoint
  rw [show -2 * (r + -Real.log (b : ℝ)) =
      2 * Real.log (b : ℝ) + -2 * r by ring,
    Real.exp_add]
  rw [show 2 * Real.log (b : ℝ) =
      Real.log (b : ℝ) + Real.log (b : ℝ) by ring,
    Real.exp_add, Real.exp_log hbR]
  ring

/-- Radial birth height of a primitive direction at the corner of the positive quadrant. -/
theorem thetaCuspPrimitiveRayRadialLog_zero_zero (a b : ℕ) :
    thetaCuspPrimitiveRayRadialLog a b 0 0 =
      (1 / 2 : ℝ) * Real.log ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) := by
  unfold thetaCuspPrimitiveRayRadialLog
  simp

/-- **Primitive-ray birth law.**  A direction has a nonempty active angular window exactly when
the radial coordinate has crossed the Euclidean logarithmic height of that direction.  Thus the
moving endpoint seam is a lattice-shell birth phenomenon, not an arbitrary truncation error. -/
theorem thetaCuspPrimitiveRayArithmeticPolar_activeWindow_iff_radialThreshold
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (r : ℝ) :
    thetaCuspPrimitiveRayCorePolarLowerEndpoint r (-Real.log (a : ℝ)) ≤
        thetaCuspPrimitiveRayCorePolarUpperEndpoint r (-Real.log (b : ℝ)) ↔
      thetaCuspPrimitiveRayRadialLog a b 0 0 ≤ r := by
  rw [thetaCuspPrimitiveRayCorePolarLowerEndpoint_neg_log_nat ha r,
    thetaCuspPrimitiveRayCorePolarUpperEndpoint_neg_log_nat hb r,
    thetaCuspPrimitiveRayRadialLog_zero_zero]
  let S : ℝ := (a : ℝ) ^ 2 + (b : ℝ) ^ 2
  have hS : 0 < S := by
    dsimp only [S]
    positivity
  have halgebra :
      (a : ℝ) ^ 2 * Real.exp (-2 * r) ≤
          1 - (b : ℝ) ^ 2 * Real.exp (-2 * r) ↔
        S * Real.exp (-2 * r) ≤ 1 := by
    dsimp only [S]
    constructor <;> intro h <;> linarith
  rw [halgebra]
  have hrepr : S * Real.exp (-2 * r) =
      Real.exp (Real.log S - 2 * r) := by
    calc
      S * Real.exp (-2 * r) =
          Real.exp (Real.log S) * Real.exp (-2 * r) := by
            rw [Real.exp_log hS]
      _ = Real.exp (Real.log S + -2 * r) := by rw [Real.exp_add]
      _ = Real.exp (Real.log S - 2 * r) := by congr 1; ring
  rw [hrepr]
  conv_lhs =>
    rhs
    rw [← Real.exp_zero]
  rw [Real.exp_le_exp]
  dsimp only [S]
  constructor <;> intro h <;> linarith

end

end RHTower
