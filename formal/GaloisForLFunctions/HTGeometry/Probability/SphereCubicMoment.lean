import GaloisForLFunctions.HTGeometry.Probability.ComplexBlockSphereMoments
import GaloisForLFunctions.HTGeometry.CubicMomentLogConcavityCounterexample

/-!
# A spherical realization of the negative cubic moment witness

On the unit sphere in `ℂ × ℝ⁶`, the squared norm of the complex coordinate has moments
`6 / ((k+1)(k+2)(k+3))`. Its even moments agree with the Beta `(1,3)` witness for the cubic
moment functional. Thus the negative cubic occurs for a coordinate statistic of uniform
spherical measure, not merely for an artificially chosen one-dimensional density.
-/

open MeasureTheory

noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- The normalized squared-complex-coordinate moments on the seven-sphere. -/
def sphereSevenComplexMoment (k : ℕ) : ℝ :=
  complexBlockSphereMoment (EuclideanSpace ℝ (Fin 6)) k

/-- Closed moment formula for a squared complex coordinate on the seven-sphere. -/
theorem sphereSevenComplexMoment_eq (k : ℕ) :
    sphereSevenComplexMoment k = 6 / (((k : ℝ) + 1) * (k + 2) * (k + 3)) := by
  have hdim : Module.finrank ℝ (BlockSpace ℂ (EuclideanSpace ℝ (Fin 6))) = 8 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℂ × EuclideanSpace ℝ (Fin 6))).finrank_eq,
      Module.finrank_prod, Complex.finrank_real_complex]
    norm_num
  rw [sphereSevenComplexMoment, complexBlockSphereMoment_eq, hdim]
  have h4 : Real.Gamma (4 : ℝ) = 6 := by
    convert Real.Gamma_nat_eq_factorial 3 using 1 <;> norm_num
  have hk : Real.Gamma ((4 : ℝ) + k) = ((k + 3).factorial : ℝ) := by
    convert Real.Gamma_nat_eq_factorial (k + 3) using 1
    push_cast
    ring
  norm_num only [Nat.cast_ofNat, show (8 : ℝ) / 2 = 4 by norm_num]
  rw [h4, hk]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hfact : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp
  ring

/-- Every even spherical moment agrees with the existing Beta `(1,3)` moment sequence. -/
theorem sphereSevenComplexMoment_even_eq_beta (j : ℕ) :
    sphereSevenComplexMoment (2 * j) = CubicMoment.betaOneThreeRawEvenMoment j := by
  rw [sphereSevenComplexMoment_eq, CubicMoment.betaOneThreeRawEvenMoment_formula]
  push_cast
  have h1 : (2 : ℝ) * j + 1 ≠ 0 := by positivity
  have h2 : (2 : ℝ) * j + 2 ≠ 0 := by positivity
  have h3 : (2 : ℝ) * j + 3 ≠ 0 := by positivity
  field_simp
  ring

/-- Uniform spherical measure gives the same exact negative cubic certificate. -/
theorem sphereSeven_cubicFunctional_eq :
    CubicMoment.cubicFunctional
      (sphereSevenComplexMoment 0) (sphereSevenComplexMoment 2)
      (sphereSevenComplexMoment 4) (sphereSevenComplexMoment 6) = -(3 / 9800 : ℝ) := by
  have h := CubicMoment.betaOneThree_cubicFunctional_eq
  rw [← sphereSevenComplexMoment_even_eq_beta 0,
    ← sphereSevenComplexMoment_even_eq_beta 1,
    ← sphereSevenComplexMoment_even_eq_beta 2,
    ← sphereSevenComplexMoment_even_eq_beta 3] at h
  exact h

/-- Holomorphic monomials have a cubically growing angular fourth-to-second moment ratio. -/
theorem sphereSeven_monomial_concentration (k : ℕ) :
    ((k : ℝ) + 1) ^ 3 / 48 ≤
      sphereSevenComplexMoment (2 * k) / sphereSevenComplexMoment k ^ 2 := by
  let P : ℝ := ((k : ℝ) + 1) * (k + 2) * (k + 3)
  let Q : ℝ := (2 * (k : ℝ) + 1) * (2 * k + 2) * (2 * k + 3)
  have hx : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hp : 0 < P := by dsimp [P]; positivity
  have hq : 0 < Q := by dsimp [Q]; positivity
  have hqp : Q ≤ 8 * P := by
    calc
      Q ≤ (2 * ((k : ℝ) + 1)) * (2 * (k + 2)) * (2 * (k + 3)) := by
        dsimp [Q]
        gcongr <;> linarith only [hx]
      _ = 8 * P := by dsimp [P]; ring
  have hpow : ((k : ℝ) + 1) ^ 3 ≤ P := by
    change ((k : ℝ) + 1) ^ 3 ≤ ((k : ℝ) + 1) * (k + 2) * (k + 3)
    rw [pow_succ, pow_two]
    gcongr <;> linarith only [hx]
  have hratio : sphereSevenComplexMoment (2 * k) / sphereSevenComplexMoment k ^ 2 =
      P ^ 2 / (6 * Q) := by
    rw [sphereSevenComplexMoment_eq, sphereSevenComplexMoment_eq]
    push_cast
    change (6 / Q) / (6 / P) ^ 2 = P ^ 2 / (6 * Q)
    field_simp
  rw [hratio]
  calc
    ((k : ℝ) + 1) ^ 3 / 48 ≤ P / 48 := div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ P ^ 2 / (6 * Q) := by
      apply (le_div_iff₀ (by positivity : 0 < 6 * Q)).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hqp hp.le]

/-- No uniform angular fourth-moment bound by squared second moment holds for these monomials. -/
theorem sphereSeven_no_uniform_monomial_moment_bound :
    ¬ ∃ C : ℝ, ∀ k : ℕ,
      sphereSevenComplexMoment (2 * k) ≤ C * sphereSevenComplexMoment k ^ 2 := by
  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (48 * C)
  have hpos : 0 < sphereSevenComplexMoment k := by
    rw [sphereSevenComplexMoment_eq]
    positivity
  have hratio := (div_le_iff₀ (pow_pos hpos 2)).mpr (hC k)
  have hlower := (sphereSeven_monomial_concentration k).trans hratio
  have hx : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcube : (k : ℝ) ≤ ((k : ℝ) + 1) ^ 3 := by
    nlinarith only [hx, sq_nonneg (k : ℝ), mul_nonneg (sq_nonneg (k : ℝ)) hx]
  linarith only [hk, hlower, hcube]

end GaloisForLFunctions.HTGeometry
