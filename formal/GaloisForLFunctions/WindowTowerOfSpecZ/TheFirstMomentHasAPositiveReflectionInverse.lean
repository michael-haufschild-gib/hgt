import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldHasAPolynomialSpectralBracket

/-!
# Positive first-moment inverses for the first fold

The paired inverse matrix has negative off-diagonal entries, but its action
on the position vector is positive. An explicit polynomial certificate gives
a uniform lower bound for both adjugate numerators. It applies to both the
polynomial and exact logarithmic potentials. The inverse equation bounds the
positive solution above by the multiplication-only inverse.
-/

noncomputable section
open Real MeasureTheory Set
namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-- Determinant of the polynomial reflection block. -/
def firstFoldReflectionDet (u : ℝ) : ℝ :=
  firstFoldPolynomialPotential u * firstFoldPolynomialPotential (2 * Real.log 2 - u) -
    (Real.log 2 / Real.sqrt 2) ^ 2

/-- The explicit inverse of the position source under multiplication and reflection. -/
def firstFoldFirstMomentInverse (u : ℝ) : ℝ :=
  if 2 * Real.log 2 - 1 ≤ u then
    (firstFoldPolynomialPotential (2 * Real.log 2 - u) * u -
      (Real.log 2 / Real.sqrt 2) * (2 * Real.log 2 - u)) / firstFoldReflectionDet u
  else u / firstFoldPolynomialPotential u

private theorem strip_in_unit {u : ℝ} (hu : u ∈ Icc (2 * Real.log 2 - 1) 1) :
    u ∈ Icc (0 : ℝ) 1 :=
  ⟨by linarith only [hu.1, Real.log_two_gt_d9], hu.2⟩

private theorem reflect_in_strip {u : ℝ} (hu : u ∈ Icc (2 * Real.log 2 - 1) 1) :
    2 * Real.log 2 - u ∈ Icc (2 * Real.log 2 - 1) 1 :=
  ⟨by linarith only [hu.2], by linarith only [hu.1]⟩

private theorem potential_pos (u : ℝ) : 0 < firstFoldPolynomialPotential u := by
  unfold firstFoldPolynomialPotential
  linarith only [firstFold_polynomial_mass_bounds.1, firstFoldLogPolynomial_nonneg u]

private theorem potential_polynomial_lower (u : ℝ) :
    (11 / 20 : ℝ) + firstFoldLogPolynomial u ≤ firstFoldPolynomialPotential u := by
  unfold firstFoldPolynomialPotential
  linarith only [firstFold_polynomial_mass_bounds.1]

-- Factoring at the endpoint leaves only nonnegative powers and endpoint distances.
private theorem first_moment_polynomial_certificate {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    (7451 / 60000 : ℝ) ≤
      ((11 / 20 : ℝ) + firstFoldLogPolynomial u) * (693 / 500 - u) - (2451 / 5000 : ℝ) * u := by
  have he : ((11 / 20 : ℝ) + firstFoldLogPolynomial u) * (693 / 500 - u) -
      (2451 / 5000 : ℝ) * u - 7451 / 60000 =
      (1 - u) * (7081 / 30000 + (193 / 480 : ℝ) * (1 - u) + (491 / 6000 : ℝ) * u ^ 2 +
        (2509 / 12000 : ℝ) * u ^ 2 * (1 - u) + (149 / 6000 : ℝ) * u ^ 4 +
        (1351 / 12000 : ℝ) * u ^ 4 * (1 - u) + (421 / 6000 : ℝ) * u ^ 6 +
        (193 / 4000 : ℝ) * u ^ 6 * (1 - u) + u ^ 8 / 8) := by
    unfold firstFoldLogPolynomial
    ring
  have hd : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hr : 0 ≤ (1 - u) * (7081 / 30000 + (193 / 480 : ℝ) * (1 - u) + (491 / 6000 : ℝ) * u ^ 2 +
      (2509 / 12000 : ℝ) * u ^ 2 * (1 - u) + (149 / 6000 : ℝ) * u ^ 4 +
      (1351 / 12000 : ℝ) * u ^ 4 * (1 - u) + (421 / 6000 : ℝ) * u ^ 6 +
      (193 / 4000 : ℝ) * u ^ 6 * (1 - u) + u ^ 8 / 8) := by
    positivity
  rw [← he] at hr
  linarith only [hr]

/-- The adjugate applied to the position vector has uniformly positive components. -/
theorem firstFold_first_moment_numerator_lower {u : ℝ}
    (hu : u ∈ Icc (2 * Real.log 2 - 1) 1) :
    (7451 / 60000 : ℝ) ≤ firstFoldPolynomialPotential (2 * Real.log 2 - u) * u -
      (Real.log 2 / Real.sqrt 2) * (2 * Real.log 2 - u) := by
  let v := 2 * Real.log 2 - u
  have hv : v ∈ Icc (0 : ℝ) 1 := strip_in_unit (reflect_in_strip hu)
  have hb : (693 / 500 : ℝ) ≤ 2 * Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hd : 0 ≤ (693 / 500 : ℝ) - v := by linarith only [hv.2]
  have hvu : (693 / 500 : ℝ) - v ≤ u := by dsimp [v]; linarith only [hb]
  have h1 := mul_le_mul_of_nonneg_right (potential_polynomial_lower v) hd
  have h2 := mul_le_mul_of_nonneg_left hvu (potential_pos v).le
  have hw : Real.log 2 / Real.sqrt 2 ≤ (2451 / 5000 : ℝ) := by
    linarith only [firstFold_prime_weight_bounds.2]
  have h3 := mul_le_mul_of_nonneg_right hw hv.1
  have h4 := first_moment_polynomial_certificate hv
  change (7451 / 60000 : ℝ) ≤ firstFoldPolynomialPotential v * u - (Real.log 2 / Real.sqrt 2) * v
  linarith only [h1, h2, h3, h4]

theorem firstFoldReflectionDet_pos {u : ℝ}
    (hu : u ∈ Icc (2 * Real.log 2 - 1) 1) : 0 < firstFoldReflectionDet u := by
  have ha := (firstFoldPolynomialPotential_bounds (strip_in_unit hu)).1
  have hb := (firstFoldPolynomialPotential_bounds (strip_in_unit (reflect_in_strip hu))).1
  have hd : (Real.log 2 / Real.sqrt 2) ^ 2 ≤
      (firstFoldPolynomialPotential u - 19 / 50) *
        (firstFoldPolynomialPotential (2 * Real.log 2 - u) - 19 / 50) := by
    apply HTGeometry.sq_le_mul_of_quadratic_nonneg (sub_nonneg.mpr hb)
    intro t
    have h := (firstFoldPolynomial_pair_bounds hu 1 t).1
    simp only [one_pow, mul_one] at h
    linarith only [h]
  unfold firstFoldReflectionDet
  nlinarith only [hd, ha, hb]

private theorem det_reflect (u : ℝ) :
    firstFoldReflectionDet (2 * Real.log 2 - u) = firstFoldReflectionDet u := by
  unfold firstFoldReflectionDet
  rw [sub_sub_cancel]
  ring

private theorem inverse_on_strip {u : ℝ} (hu : u ∈ Icc (2 * Real.log 2 - 1) 1) :
    firstFoldFirstMomentInverse u =
      (firstFoldPolynomialPotential (2 * Real.log 2 - u) * u -
        (Real.log 2 / Real.sqrt 2) * (2 * Real.log 2 - u)) / firstFoldReflectionDet u :=
  if_pos hu.1

/-- Multiplication and the retained prime reflection send the explicit inverse to `u`. -/
theorem firstFoldFirstMomentInverse_equation {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    firstFoldPolynomialPotential u * firstFoldFirstMomentInverse u +
      (if 2 * Real.log 2 - 1 ≤ u then
        (Real.log 2 / Real.sqrt 2) * firstFoldFirstMomentInverse (2 * Real.log 2 - u) else 0) = u := by
  by_cases h : 2 * Real.log 2 - 1 ≤ u
  · have hs : u ∈ Icc (2 * Real.log 2 - 1) 1 := ⟨h, hu.2⟩
    have hd := (firstFoldReflectionDet_pos hs).ne'
    rw [if_pos h, inverse_on_strip hs, inverse_on_strip (reflect_in_strip hs),
      det_reflect, sub_sub_cancel]
    calc
      _ = u * (firstFoldReflectionDet u / firstFoldReflectionDet u) := by
        unfold firstFoldReflectionDet
        ring
      _ = u := by rw [div_self hd, mul_one]
  · simp only [firstFoldFirstMomentInverse, if_neg h, add_zero]
    field_simp [(potential_pos u).ne']

theorem firstFoldFirstMomentInverse_nonneg {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    0 ≤ firstFoldFirstMomentInverse u := by
  by_cases h : 2 * Real.log 2 - 1 ≤ u
  · have hs : u ∈ Icc (2 * Real.log 2 - 1) 1 := ⟨h, hu.2⟩
    rw [inverse_on_strip hs]
    exact div_nonneg (by linarith only [firstFold_first_moment_numerator_lower hs])
      (firstFoldReflectionDet_pos hs).le
  · rw [firstFoldFirstMomentInverse, if_neg h]
    exact div_nonneg hu.1 (potential_pos u).le

/-- The exact logarithmic multiplication coefficient in the two-moment lower form. -/
def firstFoldLogarithmicPotential (u : ℝ) : ℝ :=
  137 / 60 - firstFoldMomentMassCost - Real.log (1 - u ^ 2) / 2

/-- Determinant of the exact logarithmic reflection block. -/
def firstFoldLogarithmicDet (u : ℝ) : ℝ :=
  firstFoldLogarithmicPotential u * firstFoldLogarithmicPotential (2 * Real.log 2 - u) -
    (Real.log 2 / Real.sqrt 2) ^ 2

/-- The exact logarithmic first-moment inverse; strip endpoints have no effect on its form. -/
def firstFoldLogarithmicFirstMomentInverse (u : ℝ) : ℝ :=
  if 2 * Real.log 2 - 1 < u then
    (firstFoldLogarithmicPotential (2 * Real.log 2 - u) * u -
      (Real.log 2 / Real.sqrt 2) * (2 * Real.log 2 - u)) / firstFoldLogarithmicDet u
  else u / firstFoldLogarithmicPotential u

private theorem open_strip_in_unit {u : ℝ} (hu : u ∈ Ioo (2 * Real.log 2 - 1) 1) :
    u ∈ Ioo (0 : ℝ) 1 :=
  ⟨by linarith only [hu.1, Real.log_two_gt_d9], hu.2⟩

private theorem reflect_in_open_strip {u : ℝ} (hu : u ∈ Ioo (2 * Real.log 2 - 1) 1) :
    2 * Real.log 2 - u ∈ Ioo (2 * Real.log 2 - 1) 1 :=
  ⟨by linarith only [hu.2], by linarith only [hu.1]⟩

theorem firstFoldPolynomialPotential_le_logarithmic {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    firstFoldPolynomialPotential u ≤ firstFoldLogarithmicPotential u := by
  unfold firstFoldPolynomialPotential firstFoldLogarithmicPotential
  linarith only [firstFoldLogPolynomial_le_log hu]

private theorem logarithmic_potential_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < firstFoldLogarithmicPotential u :=
  (potential_pos u).trans_le (firstFoldPolynomialPotential_le_logarithmic hu)

/-- The exact logarithmic fold has the same positive first-moment numerator. -/
theorem firstFold_logarithmic_first_moment_numerator_lower {u : ℝ}
    (hu : u ∈ Ioo (2 * Real.log 2 - 1) 1) :
    (7451 / 60000 : ℝ) ≤ firstFoldLogarithmicPotential (2 * Real.log 2 - u) * u -
      (Real.log 2 / Real.sqrt 2) * (2 * Real.log 2 - u) := by
  have h := mul_le_mul_of_nonneg_right
    (firstFoldPolynomialPotential_le_logarithmic (open_strip_in_unit (reflect_in_open_strip hu)))
    (open_strip_in_unit hu).1.le
  have hp := firstFold_first_moment_numerator_lower ⟨hu.1.le, hu.2.le⟩
  linarith only [h, hp]

theorem firstFoldLogarithmicDet_pos {u : ℝ}
    (hu : u ∈ Ioo (2 * Real.log 2 - 1) 1) : 0 < firstFoldLogarithmicDet u := by
  have h := mul_le_mul (firstFoldPolynomialPotential_le_logarithmic (open_strip_in_unit hu))
    (firstFoldPolynomialPotential_le_logarithmic (open_strip_in_unit (reflect_in_open_strip hu)))
    (potential_pos _).le (logarithmic_potential_pos (open_strip_in_unit hu)).le
  have hp := firstFoldReflectionDet_pos ⟨hu.1.le, hu.2.le⟩
  unfold firstFoldLogarithmicDet firstFoldReflectionDet at *
  linarith only [h, hp]

private theorem logarithmic_det_reflect (u : ℝ) :
    firstFoldLogarithmicDet (2 * Real.log 2 - u) = firstFoldLogarithmicDet u := by
  unfold firstFoldLogarithmicDet
  rw [sub_sub_cancel]
  ring

private theorem logarithmic_inverse_on_strip {u : ℝ}
    (hu : u ∈ Ioo (2 * Real.log 2 - 1) 1) :
    firstFoldLogarithmicFirstMomentInverse u =
      (firstFoldLogarithmicPotential (2 * Real.log 2 - u) * u -
        (Real.log 2 / Real.sqrt 2) * (2 * Real.log 2 - u)) / firstFoldLogarithmicDet u :=
  if_pos hu.1

/-- The exact logarithmic operator sends its explicit first-moment inverse to `u`. -/
theorem firstFoldLogarithmicFirstMomentInverse_equation {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    firstFoldLogarithmicPotential u * firstFoldLogarithmicFirstMomentInverse u +
      (if 2 * Real.log 2 - 1 < u then
        (Real.log 2 / Real.sqrt 2) * firstFoldLogarithmicFirstMomentInverse (2 * Real.log 2 - u) else 0) = u := by
  by_cases h : 2 * Real.log 2 - 1 < u
  · have hs : u ∈ Ioo (2 * Real.log 2 - 1) 1 := ⟨h, hu.2⟩
    have hd := (firstFoldLogarithmicDet_pos hs).ne'
    rw [if_pos h, logarithmic_inverse_on_strip hs, logarithmic_inverse_on_strip (reflect_in_open_strip hs),
      logarithmic_det_reflect, sub_sub_cancel]
    calc
      _ = u * (firstFoldLogarithmicDet u / firstFoldLogarithmicDet u) := by
        unfold firstFoldLogarithmicDet
        ring
      _ = u := by rw [div_self hd, mul_one]
  · simp only [firstFoldLogarithmicFirstMomentInverse, if_neg h, add_zero]
    field_simp [(logarithmic_potential_pos hu).ne']

/-- The exact logarithmic first-moment inverse is positive on the positive half-window. -/
theorem firstFoldLogarithmicFirstMomentInverse_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < firstFoldLogarithmicFirstMomentInverse u := by
  by_cases h : 2 * Real.log 2 - 1 < u
  · have hs : u ∈ Ioo (2 * Real.log 2 - 1) 1 := ⟨h, hu.2⟩
    rw [logarithmic_inverse_on_strip hs]
    exact div_pos (by linarith only [firstFold_logarithmic_first_moment_numerator_lower hs])
      (firstFoldLogarithmicDet_pos hs)
  · rw [firstFoldLogarithmicFirstMomentInverse, if_neg h]
    exact div_pos hu.1 (logarithmic_potential_pos hu)

/-- On the active strip, the prime reflection strictly reduces the first-moment inverse. -/
theorem firstFoldLogarithmicFirstMomentInverse_lt_local {u : ℝ}
    (hu : u ∈ Ioo (2 * Real.log 2 - 1) 1) :
    firstFoldLogarithmicFirstMomentInverse u < u / firstFoldLogarithmicPotential u := by
  have he := firstFoldLogarithmicFirstMomentInverse_equation (open_strip_in_unit hu)
  rw [if_pos hu.1] at he
  have hw : 0 < Real.log 2 / Real.sqrt 2 := by
    have hb : 0 < Real.log 2 := by linarith only [Real.log_two_gt_d9]
    exact div_pos hb (by positivity)
  have hn := mul_pos hw
    (firstFoldLogarithmicFirstMomentInverse_pos (open_strip_in_unit (reflect_in_open_strip hu)))
  apply (lt_div_iff₀ (logarithmic_potential_pos (open_strip_in_unit hu))).mpr
  linarith only [he, hn]

theorem firstFoldLogarithmicFirstMomentInverse_le_local {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    firstFoldLogarithmicFirstMomentInverse u ≤ u / firstFoldLogarithmicPotential u := by
  by_cases h : 2 * Real.log 2 - 1 < u
  · exact (firstFoldLogarithmicFirstMomentInverse_lt_local ⟨h, hu.2⟩).le
  · rw [firstFoldLogarithmicFirstMomentInverse, if_neg h]

/-- The first-moment inverse is strictly positive throughout the positive half-window. -/
theorem firstFoldFirstMomentInverse_pos {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    0 < firstFoldFirstMomentInverse u := by
  by_cases h : 2 * Real.log 2 - 1 ≤ u
  · have hs : u ∈ Icc (2 * Real.log 2 - 1) 1 := ⟨h, hu.2⟩
    rw [inverse_on_strip hs]
    exact div_pos (by linarith only [firstFold_first_moment_numerator_lower hs])
      (firstFoldReflectionDet_pos hs)
  · rw [firstFoldFirstMomentInverse, if_neg h]
    exact div_pos hu.1 (potential_pos u)

/-- The positive reflected component reduces the first-moment inverse below its local value. -/
theorem firstFoldFirstMomentInverse_le_local {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    firstFoldFirstMomentInverse u ≤ u / firstFoldPolynomialPotential u := by
  by_cases h : 2 * Real.log 2 - 1 ≤ u
  · have hs : u ∈ Icc (2 * Real.log 2 - 1) 1 := ⟨h, hu.2⟩
    have he := firstFoldFirstMomentInverse_equation hu
    rw [if_pos h] at he
    have hn := mul_nonneg firstFold_prime_weight_bounds.1
      (firstFoldFirstMomentInverse_nonneg (strip_in_unit (reflect_in_strip hs)))
    apply (le_div_iff₀ (potential_pos u)).mpr
    linarith only [he, hn]
  · rw [firstFoldFirstMomentInverse, if_neg h]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFold_first_moment_numerator_lower
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldFirstMomentInverse_equation
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldFirstMomentInverse_pos
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldFirstMomentInverse_le_local
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldLogarithmicFirstMomentInverse_equation
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldLogarithmicFirstMomentInverse_pos
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.firstFoldLogarithmicFirstMomentInverse_lt_local
