import GaloisForLFunctions.HTGeometry.QuadraticResponseHierarchy
/-!
# Cavity interaction coefficients and the eighth-order discrepancy

Ainsworth et al., arXiv:2608.14343v2, Eq. (5) and supplement S2, give
`χ_(n+1) = η L_d / 2 * C_n(2ηqD, η²q)`, where `q = T₀ Lₐ`.
Orders one through seven agree with the displayed list. At order eight that
list has `1 + 8u(8u-1)` where the recurrence forces `1 + 8u(u-1)`.
The residual below is a polynomial identity, not a numerical test.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section
/-- Order `n+1` cavity coupling; `q = T₀ Lₐ`, `d = L_d`, and `D` is shifted detuning. -/
def cavityInteractionCoeff (η q d D : ℝ) (n : ℕ) : ℝ :=
  η * d / 2 * quadraticResponseCoeff (2 * η * q * D) (η ^ (2 : ℕ) * q) n
/-- Exact cooperativity scaling with the normalized response coordinates held fixed. -/
theorem cavityInteractionCoeff_scaling (η q d D : ℝ) (n : ℕ) :
    cavityInteractionCoeff η q d D n = η ^ (n + 1) * cavityInteractionCoeff 1 q d D n := by
  unfold cavityInteractionCoeff
  rw [show 2 * η * q * D = η * (2 * 1 * q * D) by ring,
    show η ^ (2 : ℕ) * q = η ^ (2 : ℕ) * (1 ^ (2 : ℕ) * q) by ring,
    quadraticResponseCoeff_scale, pow_succ]
  ring
/-- The coefficient agrees with Eq. (5) for every nonnegative `q = s²`, without a sign premise. -/
theorem cavityInteractionCoeff_chebyshev (η s d D : ℝ) (n : ℕ) :
    cavityInteractionCoeff η (s ^ (2 : ℕ)) d D n =
      η * d / 2 * (η * s) ^ n * (Polynomial.Chebyshev.U ℝ n).eval (-D * s) := by
  unfold cavityInteractionCoeff
  rw [show 2 * η * s ^ (2 : ℕ) * D = -(2 * (-D * s) * (η * s)) by ring,
    show η ^ (2 : ℕ) * s ^ (2 : ℕ) = (η * s) ^ (2 : ℕ) by ring,
    quadraticResponseCoeff_eq_scaled_chebyshev]
  ring
/-- Every finite Hamiltonian truncation has an exact two-term boundary residual. -/
theorem cavityInteractionCoeff_finite_remainder (η q d D z : ℝ) (n : ℕ) :
    (1 + 2 * η * q * D * z + η ^ (2 : ℕ) * q * z ^ (2 : ℕ)) *
        (∑ k ∈ Finset.range (n + 1), cavityInteractionCoeff η q d D k * z ^ (k + 1)) =
      η * d / 2 * z - cavityInteractionCoeff η q d D (n + 1) * z ^ (n + 2) +
        η ^ (2 : ℕ) * q * cavityInteractionCoeff η q d D n * z ^ (n + 3) := by
  have h := quadraticResponseCoeff_finite_remainder (2 * η * q * D) (η ^ (2 : ℕ) * q) z n
  unfold cavityInteractionCoeff
  have hs : (∑ k ∈ Finset.range (n + 1),
      η * d / 2 * quadraticResponseCoeff (2 * η * q * D) (η ^ (2 : ℕ) * q) k * z ^ (k + 1)) =
      η * d / 2 * z * (∑ k ∈ Finset.range (n + 1),
        quadraticResponseCoeff (2 * η * q * D) (η ^ (2 : ℕ) * q) k * z ^ k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring
  rw [hs]
  simp only [pow_succ] at h ⊢
  linear_combination (η * d / 2 * z) * h
/-- The first four coefficients in the supplemental hierarchy. -/
theorem cavityInteractionCoeff_first_four (η q d D : ℝ) :
    cavityInteractionCoeff η q d D 0 = η * d / 2 ∧
    cavityInteractionCoeff η q d D 1 = -η ^ (2 : ℕ) * q * d * D ∧
    cavityInteractionCoeff η q d D 2 = 2 * η ^ (3 : ℕ) * q * d * (q * D ^ (2 : ℕ) - 1 / 4) ∧
    cavityInteractionCoeff η q d D 3 = 2 * η ^ (4 : ℕ) * q ^ (2 : ℕ) * d * D * (1 - 2 * q * D ^ (2 : ℕ)) := by
  simp only [cavityInteractionCoeff, quadraticResponseCoeff]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring
/-- Orders five through seven in the supplemental hierarchy. -/
theorem cavityInteractionCoeff_five_to_seven (η q d D : ℝ) :
    cavityInteractionCoeff η q d D 4 =
      η ^ (5 : ℕ) / 2 * q ^ (2 : ℕ) * d * (1 + 4 * q * D ^ (2 : ℕ) * (4 * q * D ^ (2 : ℕ) - 3)) ∧
    cavityInteractionCoeff η q d D 5 =
      -η ^ (6 : ℕ) * q ^ (3 : ℕ) * d * D * (4 * q * D ^ (2 : ℕ) - 3) * (4 * q * D ^ (2 : ℕ) - 1) ∧
    cavityInteractionCoeff η q d D 6 =
      η ^ (7 : ℕ) / 2 * q ^ (3 : ℕ) * d *
        (8 * D ^ (2 : ℕ) * q * (2 * D ^ (2 : ℕ) * q - 1) * (4 * D ^ (2 : ℕ) * q - 3) - 1) := by
  simp only [cavityInteractionCoeff, quadraticResponseCoeff]
  constructor
  · ring
  constructor <;> ring
/-- The eighth-order coefficient forced by the generating function. -/
theorem cavityInteractionCoeff_eighth (η q d D : ℝ) :
    cavityInteractionCoeff η q d D 7 =
      -4 * η ^ (8 : ℕ) * q ^ (4 : ℕ) * d * D * (2 * D ^ (2 : ℕ) * q - 1) *
        (1 + 8 * D ^ (2 : ℕ) * q * (D ^ (2 : ℕ) * q - 1)) := by
  simp only [cavityInteractionCoeff, quadraticResponseCoeff]
  ring
/-- Exact discrepancy between the displayed eighth-order formula and Eq. (5). -/
theorem cavityInteractionCoeff_eighth_displayed_residual (η q d D : ℝ) :
    (-4 * η ^ (8 : ℕ) * q ^ (4 : ℕ) * d * D * (2 * D ^ (2 : ℕ) * q - 1) *
      (1 + 8 * D ^ (2 : ℕ) * q * (8 * D ^ (2 : ℕ) * q - 1))) -
        cavityInteractionCoeff η q d D 7 =
      -224 * η ^ (8 : ℕ) * q ^ (6 : ℕ) * d * D ^ (5 : ℕ) * (2 * D ^ (2 : ℕ) * q - 1) := by
  rw [cavityInteractionCoeff_eighth]
  ring
end
end GaloisForLFunctions.HTGeometry
