import GaloisForLFunctions.HTGeometry.ShiftSpectrumSpacing

/-!
# The four verification families of the cusp--spectrum radius law

Specializing the cusp gap `d q^{-1/d}` and the cusp constant `q^{1/d}/(2πd)` to
the four families recorded on the card gives the predicted radii and growth
constants exactly.

In degree one the spectrum is the rational lattice carried by the support of the
coefficients: `{ m/q : a(m) ≠ 0 }`.  For the zeta function that is the integers
and the cusp gap is one; for a Dirichlet character of conductor `q` it is
`(1/q)ℤ` restricted to the residues coprime to `q`, and the cusp gap is `1/q`.
In degree two and conductor one the gap is two and the growth constant is
`1/(4π)`, independently of the archimedean parameters.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section DegreeOne

/-- **In degree one the spectrum is a rational lattice.** -/
theorem shiftSpectrum_degree_one (a : ℕ → ℂ) (q : ℝ) :
    shiftSpectrum a 1 q
      = {x : ℝ | ∃ m : ℕ, 0 < m ∧ a m ≠ 0 ∧ x = (m : ℝ) / q} := by
  ext x
  constructor
  · rintro ⟨m, hm, ham, rfl⟩
    exact ⟨m, hm, ham, by rw [div_one, Real.rpow_one, one_mul]⟩
  · rintro ⟨m, hm, ham, rfl⟩
    exact ⟨m, hm, ham, by rw [div_one, Real.rpow_one, one_mul]⟩

end DegreeOne

section Verification

variable {a : ℕ → ℂ}

/-- **Verification, the zeta function.**  Degree one, conductor one: the cusp gap
is one. -/
theorem infDist_zero_shiftSpectrum_zeta (ha : a 1 ≠ 0) :
    Metric.infDist 0 (shiftSpectrum a 1 1) = 1 := by
  rw [infDist_zero_shiftSpectrum ha one_pos one_pos, Real.one_rpow, mul_one]

/-- **Verification, a Dirichlet character of conductor `q`.**  Degree one: the
cusp gap is `1/q`. -/
theorem infDist_zero_shiftSpectrum_dirichlet (ha : a 1 ≠ 0) {q : ℝ} (hq : 0 < q) :
    Metric.infDist 0 (shiftSpectrum a 1 q) = 1 / q := by
  rw [infDist_zero_shiftSpectrum ha one_pos hq, one_mul, div_one,
    Real.rpow_neg_one, one_div]

/-- **Verification, degree two of conductor one.**  The level-one weight-twelve
form and every level-one Maass form: the cusp gap is two, independently of the
archimedean parameters. -/
theorem infDist_zero_shiftSpectrum_degree_two (ha : a 1 ≠ 0) :
    Metric.infDist 0 (shiftSpectrum a 2 1) = 2 := by
  rw [infDist_zero_shiftSpectrum ha (by norm_num) one_pos, Real.one_rpow, mul_one]

/-- The zeta growth constant. -/
theorem cusp_constant_zeta : 1 / ((2 * Real.pi) * (1 * (1 : ℝ) ^ (-(1 / (1 : ℝ)))))
    = 1 / (2 * Real.pi) := by
  rw [Real.one_rpow, mul_one, mul_one]

/-- The Dirichlet growth constant of conductor `q`. -/
theorem cusp_constant_dirichlet {q : ℝ} (hq : 0 < q) :
    1 / ((2 * Real.pi) * (1 * q ^ (-(1 / (1 : ℝ))))) = q / (2 * Real.pi) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  rw [one_div_one, Real.rpow_neg_one, one_mul]
  field_simp

/-- The degree-two conductor-one growth constant `1/(4π)`. -/
theorem cusp_constant_degree_two :
    1 / ((2 * Real.pi) * (2 * (1 : ℝ) ^ (-(1 / (2 : ℝ))))) = 1 / (4 * Real.pi) := by
  rw [Real.one_rpow, mul_one]
  ring_nf

end Verification

end GaloisForLFunctions.HTGeometry
