import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Quadratic coordinates for an admissible stress cone

A two-component stress can be resolved into directions parallel and transverse to a prescribed
shear.  In these coordinates, the square-root upper bound defining the admissible cone is
equivalent to one strict quadratic inequality.  The quadratic form makes positive scaling and
covariance constructions transparent.
-/

namespace GaloisForLFunctions.HTGeometry.NavierStokesStressCone

noncomputable section

/-- Slope of the shear vector `(a, -b)` when its first component is nonzero. -/
def shearSlope (a b : ℝ) : ℝ := -b / a

/-- Squared-length density of the shear vector after normalizing its first component. -/
def shearSize (a b : ℝ) : ℝ := a * (1 + shearSlope a b ^ 2)

/-- Component of `(p₁, p₂)` parallel to the unnormalized direction `(1, t)`. -/
def parallelCoordinate (t p₁ p₂ : ℝ) : ℝ := p₁ + t * p₂

/-- Component of `(p₁, p₂)` transverse to the unnormalized direction `(1, t)`. -/
def transverseCoordinate (t p₁ p₂ : ℝ) : ℝ := p₂ - t * p₁

/-- Smaller root of `2 (p - v)² = (v - 2) j²`, written without a division by `j`. -/
def lowerAdmissibleRoot (p j : ℝ) : ℝ :=
  p + j ^ 2 / 4 - |j| * Real.sqrt ((p - 2) / 2 + j ^ 2 / 16)

/-- Square-root presentation of the relaxed stress cone. -/
def RelaxedStressCone (v p j : ℝ) : Prop :=
  2 < p ∧ v < lowerAdmissibleRoot p j

/-- Stress cone including the lower shear-size cutoff. -/
def AdmissibleStressCone (v p j : ℝ) : Prop :=
  2 < v ∧ RelaxedStressCone v p j

/-- Quadratic presentation of the stress cone. -/
def QuadraticStressCone (v p j : ℝ) : Prop :=
  v < p ∧ (v - 2) * j ^ 2 < 2 * (p - v) ^ 2

/-- Cone condition directly on parallel and transverse stress coordinates. -/
def StressCoordinateCone (v parallel transverse : ℝ) : Prop :=
  0 < parallel ∧ (v - 2) * transverse ^ 2 < 2 * parallel ^ 2

theorem shearSize_eq (a b : ℝ) (ha : a ≠ 0) :
    shearSize a b = a + b ^ 2 / a := by
  unfold shearSize shearSlope
  field_simp [ha]

/-- The parallel/transverse coordinate change multiplies squared length by `1 + t²`. -/
theorem parallel_sq_add_transverse_sq (t p₁ p₂ : ℝ) :
    parallelCoordinate t p₁ p₂ ^ 2 + transverseCoordinate t p₁ p₂ ^ 2 =
      (1 + t ^ 2) * (p₁ ^ 2 + p₂ ^ 2) := by
  simp only [parallelCoordinate, transverseCoordinate]
  ring

theorem recover_first_coordinate (t p₁ p₂ : ℝ) :
    p₁ = (parallelCoordinate t p₁ p₂ - t * transverseCoordinate t p₁ p₂) /
      (1 + t ^ 2) := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  unfold parallelCoordinate transverseCoordinate
  field_simp [ht]
  ring

theorem recover_second_coordinate (t p₁ p₂ : ℝ) :
    p₂ = (t * parallelCoordinate t p₁ p₂ + transverseCoordinate t p₁ p₂) /
      (1 + t ^ 2) := by
  have ht : 1 + t ^ 2 ≠ 0 := by positivity
  unfold parallelCoordinate transverseCoordinate
  field_simp [ht]
  ring

private theorem relaxedStressCone_iff_quadratic_of_two_lt {v p j : ℝ} (hv : 2 < v) :
    RelaxedStressCone v p j ↔ QuadraticStressCone v p j := by
  constructor
  · rintro ⟨hp, hvroot⟩
    have hrad : 0 ≤ (p - 2) / 2 + j ^ 2 / 16 := by
      nlinarith [sq_nonneg j]
    have hsqrt : Real.sqrt ((p - 2) / 2 + j ^ 2 / 16) ^ 2 =
        (p - 2) / 2 + j ^ 2 / 16 := Real.sq_sqrt hrad
    have habs : |j| ^ 2 = j ^ 2 := sq_abs j
    have hnonneg :
        0 ≤ |j| * Real.sqrt ((p - 2) / 2 + j ^ 2 / 16) :=
      mul_nonneg (abs_nonneg j) (Real.sqrt_nonneg _)
    have hroot :
        |j| * Real.sqrt ((p - 2) / 2 + j ^ 2 / 16) < p + j ^ 2 / 4 - v := by
      simp only [lowerAdmissibleRoot] at hvroot
      nlinarith
    have hright : 0 < p + j ^ 2 / 4 - v := lt_of_le_of_lt hnonneg hroot
    have hsquares :
        (|j| * Real.sqrt ((p - 2) / 2 + j ^ 2 / 16)) ^ 2 <
          (p + j ^ 2 / 4 - v) ^ 2 := by
      nlinarith
    have hquadratic : (v - 2) * j ^ 2 < 2 * (p - v) ^ 2 := by
      rw [mul_pow, habs, hsqrt] at hsquares
      nlinarith
    have hvp : v < p := by
      by_contra hnot
      have hpv : p - v ≤ 0 := by linarith
      by_cases hpveq : p - v = 0
      · have hj : 0 < j ^ 2 := by nlinarith
        have hprod : 0 < (v - 2) * j ^ 2 := mul_pos (by linarith) hj
        nlinarith
      · have hpvlt : p - v < 0 := lt_of_le_of_ne hpv hpveq
        have hy : -(p - v) < v - 2 := by nlinarith
        have hj : -4 * (p - v) < j ^ 2 := by nlinarith
        have hmul : (-(p - v)) * (-4 * (p - v)) < (v - 2) * j ^ 2 :=
          mul_lt_mul hy hj.le (by nlinarith) (by linarith)
        nlinarith
    exact ⟨hvp, hquadratic⟩
  · rintro ⟨hvp, hquadratic⟩
    have hp : 2 < p := lt_trans hv hvp
    have hrad : 0 ≤ (p - 2) / 2 + j ^ 2 / 16 := by
      nlinarith [sq_nonneg j]
    have hsqrt : Real.sqrt ((p - 2) / 2 + j ^ 2 / 16) ^ 2 =
        (p - 2) / 2 + j ^ 2 / 16 := Real.sq_sqrt hrad
    have habs : |j| ^ 2 = j ^ 2 := sq_abs j
    have hnonneg :
        0 ≤ |j| * Real.sqrt ((p - 2) / 2 + j ^ 2 / 16) :=
      mul_nonneg (abs_nonneg j) (Real.sqrt_nonneg _)
    have hright : 0 < p + j ^ 2 / 4 - v := by
      nlinarith [sq_nonneg j]
    have hsquares :
        (|j| * Real.sqrt ((p - 2) / 2 + j ^ 2 / 16)) ^ 2 <
          (p + j ^ 2 / 4 - v) ^ 2 := by
      rw [mul_pow, habs, hsqrt]
      nlinarith
    have hroot :
        |j| * Real.sqrt ((p - 2) / 2 + j ^ 2 / 16) < p + j ^ 2 / 4 - v := by
      nlinarith
    refine ⟨hp, ?_⟩
    simp only [lowerAdmissibleRoot]
    nlinarith

/-- Exact quadratic characterization of the admissible stress cone. -/
theorem admissibleStressCone_iff (v p j : ℝ) :
    AdmissibleStressCone v p j ↔ 2 < v ∧ QuadraticStressCone v p j := by
  unfold AdmissibleStressCone
  constructor
  · rintro ⟨hv, hrelaxed⟩
    exact ⟨hv, (relaxedStressCone_iff_quadratic_of_two_lt hv).mp hrelaxed⟩
  · rintro ⟨hv, hquadratic⟩
    exact ⟨hv, (relaxedStressCone_iff_quadratic_of_two_lt hv).mpr hquadratic⟩

/-- Parallel residual-stress identity after subtracting the shear. -/
theorem stress_parallel_identity (a t p₁ p₂ scale : ℝ) :
    scale * (p₁ - a) + t * (scale * (p₂ - a * t)) =
      scale * (parallelCoordinate t p₁ p₂ - a * (1 + t ^ 2)) := by
  simp only [parallelCoordinate]
  ring

/-- Transverse residual-stress identity after subtracting the shear. -/
theorem stress_transverse_identity (a t p₁ p₂ scale : ℝ) :
    scale * (p₂ - a * t) - t * (scale * (p₁ - a)) =
      scale * transverseCoordinate t p₁ p₂ := by
  simp only [transverseCoordinate]
  ring

/-- The quadratic stress-coordinate cone is homogeneous under positive scaling. -/
theorem stressCoordinateCone_pos_smul_iff {v x y scale : ℝ} (hscale : 0 < scale) :
    StressCoordinateCone v (scale * x) (scale * y) ↔ StressCoordinateCone v x y := by
  have hscale_sq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  constructor
  · rintro ⟨hx, hxy⟩
    have hxs : 0 < x * scale := by simpa [mul_comm] using hx
    refine ⟨pos_of_mul_pos_left hxs hscale.le, ?_⟩
    have hscaled :
        scale ^ 2 * ((v - 2) * y ^ 2) < scale ^ 2 * (2 * x ^ 2) := by
      nlinarith
    exact lt_of_mul_lt_mul_left hscaled hscale_sq.le
  · rintro ⟨hx, hxy⟩
    refine ⟨mul_pos hscale hx, ?_⟩
    have hscaled :
        scale ^ 2 * ((v - 2) * y ^ 2) < scale ^ 2 * (2 * x ^ 2) :=
      mul_lt_mul_of_pos_left hxy hscale_sq
    nlinarith

/-- A positive physical scale does not alter the scalar quadratic cone test. -/
theorem scaled_stressCoordinateCone_iff_quadratic {v p j scale : ℝ}
    (hscale : 0 < scale) :
    StressCoordinateCone v (scale * (p - v)) (scale * j) ↔
      QuadraticStressCone v p j := by
  rw [stressCoordinateCone_pos_smul_iff hscale]
  simp only [StressCoordinateCone, QuadraticStressCone, sub_pos]

end

end GaloisForLFunctions.HTGeometry.NavierStokesStressCone
