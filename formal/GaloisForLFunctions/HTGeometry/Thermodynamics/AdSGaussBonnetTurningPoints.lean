import GaloisForLFunctions.HTGeometry.Thermodynamics.AdSGaussBonnetBoundary
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The charged turning-point boundary

The polynomial controlling radial thermal stability in arXiv:2611.16364,
equation (5.3), has an exact sum-of-squares decomposition at and above
coupling `1/36`. It identifies the only neutral degeneracy and proves that
every nonzero charge removes it.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

def turningPolynomial (ℓ q y : ℝ) : ℝ :=
  3 * y ^ 2 * (2 * y ^ 2 + (12 * ℓ - 1) * y + 2 * ℓ) +
    q ^ 2 * (5 * y + 6 * ℓ)

/-- A sharp algebraic decomposition, including the neutral threshold. -/
theorem turningPolynomial_threshold (a q y : ℝ) :
    turningPolynomial (1 / 36 + a ^ 2) q y =
      6 * y ^ 2 * (y - 1 / 6) ^ 2 +
        3 * a ^ 2 * y ^ 2 * (12 * y + 2) +
        q ^ 2 * (5 * y + 1 / 6 + 6 * a ^ 2) := by
  unfold turningPolynomial
  ring

theorem turningPolynomial_nonneg (a q u : ℝ) :
    0 ≤ turningPolynomial (1 / 36 + a ^ 2) q (Real.exp u) := by
  rw [turningPolynomial_threshold]
  positivity

/-- Any nonzero charge eliminates all turning radii at or above the threshold. -/
theorem turningPolynomial_charged_pos (a v u : ℝ) :
    0 < turningPolynomial (1 / 36 + a ^ 2) (Real.exp v) (Real.exp u) := by
  rw [turningPolynomial_threshold]
  positivity

/-- Strictly larger coupling eliminates turning radii even at zero charge. -/
theorem turningPolynomial_above_threshold_pos (v q u : ℝ) :
    0 < turningPolynomial (1 / 36 + Real.exp v ^ 2) q (Real.exp u) := by
  rw [turningPolynomial_threshold]
  positivity

/-- The remaining degeneracy is precisely the neutral point `ℓ=1/36`, `x²=1/6`. -/
theorem turningPolynomial_zero_iff (a q u : ℝ) :
    turningPolynomial (1 / 36 + a ^ 2) q (Real.exp u) = 0 ↔
      a = 0 ∧ q = 0 ∧ Real.exp u = 1 / 6 := by
  rw [turningPolynomial_threshold]
  have h₁ : 0 ≤ 6 * Real.exp u ^ 2 * (Real.exp u - 1 / 6) ^ 2 := by positivity
  have h₂ : 0 ≤ 3 * a ^ 2 * Real.exp u ^ 2 * (12 * Real.exp u + 2) := by positivity
  have h₃ : 0 ≤ q ^ 2 * (5 * Real.exp u + 1 / 6 + 6 * a ^ 2) := by positivity
  constructor
  · intro h
    have hz₁ : 6 * Real.exp u ^ 2 * (Real.exp u - 1 / 6) ^ 2 = 0 := by
      linarith only [h, h₁, h₂, h₃]
    have hz₂ : 3 * a ^ 2 * Real.exp u ^ 2 * (12 * Real.exp u + 2) = 0 := by
      linarith only [h, h₁, h₂, h₃]
    have hz₃ : q ^ 2 * (5 * Real.exp u + 1 / 6 + 6 * a ^ 2) = 0 := by
      linarith only [h, h₁, h₂, h₃]
    have hc₂ : 12 * Real.exp u + 2 ≠ 0 := by positivity
    have hc₃ : 5 * Real.exp u + 1 / 6 + 6 * a ^ 2 ≠ 0 := by positivity
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, Real.exp_ne_zero, false_or,
      pow_eq_zero_iff (by norm_num : 2 ≠ 0), hc₂, hc₃, or_false, sub_eq_zero] at hz₁ hz₂ hz₃
    exact ⟨hz₂, hz₃, hz₁⟩
  · rintro ⟨rfl, rfl, hx⟩
    rw [hx]
    norm_num

/-- The stability polynomial is the numerator of the actual radial derivative. -/
theorem temperature_hasDerivAt (a q u : ℝ) :
    HasDerivAt (temperature (a ^ 2) q)
      (turningPolynomial (a ^ 2) q (Real.exp u ^ 2) /
        (6 * Real.pi * Real.exp u ^ 4 * (Real.exp u ^ 2 + 2 * a ^ 2) ^ 2))
      (Real.exp u) := by
  have hn := ((((hasDerivAt_id (Real.exp u)).pow 6).const_mul 6).add
    (((hasDerivAt_id (Real.exp u)).pow 4).const_mul 3)).sub_const (q ^ 2)
  have hd := (((hasDerivAt_id (Real.exp u)).pow 3).const_mul (6 * Real.pi)).mul
    (((hasDerivAt_id (Real.exp u)).pow 2).add_const (2 * a ^ 2))
  have hpos : Real.exp u ^ 2 + 2 * a ^ 2 ≠ 0 := by positivity
  apply (hn.div hd (by dsimp; positivity)).congr_deriv
  dsimp [turningPolynomial]
  field_simp [hpos]
  ring

theorem temperature_charged_deriv_pos (a v u : ℝ) :
    0 < deriv (temperature (1 / 36 + a ^ 2) (Real.exp v)) (Real.exp u) := by
  have hs : Real.sqrt (1 / 36 + a ^ 2) ^ 2 = 1 / 36 + a ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hd := (temperature_hasDerivAt (Real.sqrt (1 / 36 + a ^ 2)) (Real.exp v) u).deriv
  rw [hs] at hd
  rw [hd]
  have hx : Real.exp u ^ 2 = Real.exp (2 * u) := by
    rw [two_mul, Real.exp_add]
    ring
  have hn := turningPolynomial_charged_pos a v (2 * u)
  rw [← hx] at hn
  exact div_pos hn (by positivity)

/-- Above the neutral threshold, charged temperature is strictly increasing on all positive radii. -/
theorem temperature_charged_strictMonoOn (a v : ℝ) :
    StrictMonoOn (temperature (1 / 36 + a ^ 2) (Real.exp v)) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro x hx
    have hs : Real.sqrt (1 / 36 + a ^ 2) ^ 2 = 1 / 36 + a ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hd := temperature_hasDerivAt (Real.sqrt (1 / 36 + a ^ 2)) (Real.exp v) (Real.log x)
    rw [hs, Real.exp_log hx] at hd
    exact hd.continuousAt.continuousWithinAt
  · intro x hx
    have hpos : 0 < x := interior_subset hx
    simpa only [Real.exp_log hpos] using temperature_charged_deriv_pos a v (Real.log x)

/-- No two positive radii can share a bath temperature in this regime. -/
theorem temperature_charged_fiber_subsingleton (a v t : ℝ) :
    Set.Subsingleton {x : ℝ | 0 < x ∧ temperature (1 / 36 + a ^ 2) (Real.exp v) x = t} := by
  intro x hx y hy
  exact (temperature_charged_strictMonoOn a v).injOn hx.1 hy.1 (hx.2.trans hy.2.symm)

#print axioms turningPolynomial_zero_iff
#print axioms temperature_charged_deriv_pos
#print axioms temperature_charged_fiber_subsingleton

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
