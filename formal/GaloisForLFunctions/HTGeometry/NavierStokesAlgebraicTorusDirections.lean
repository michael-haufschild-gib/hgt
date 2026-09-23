import GaloisForLFunctions.HTGeometry.NavierStokesFiniteTorusInverse
import GaloisForLFunctions.HTGeometry.NavierStokesTorusHaarCovering
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Algebraic torus directions from the Navier--Stokes construction

This file formalizes equations (6.2) and (6.7) of the supplied Navier--Stokes
paper.  The two auxiliary directions are eigenvectors of the integer covering
matrix `Jg`, are nonresonant with every nonzero integer frequency, and obey an
explicit reciprocal-linear small-divisor bound.

The final two theorems discharge the nonresonance premise of the corpus's
finite Fourier transport inverse for the paper's actual directions.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry.NavierStokesAlgebraicTorusDirections

open NavierStokesFiniteTorusInverse NavierStokesTorusHaarCovering

noncomputable section

/-- The slope `b_g = √2 - 1` from equation (6.2). -/
def navierStokesAuxSlope : ℝ := Real.sqrt 2 - 1

/-- Radial auxiliary direction `v_r = (1, -b_g)`. -/
def navierStokesRadialDirection : Fin 2 → ℝ := ![1, -navierStokesAuxSlope]

/-- Time auxiliary direction `v_t = (b_g, 1)`. -/
def navierStokesTimeDirection : Fin 2 → ℝ := ![navierStokesAuxSlope, 1]

def navierStokesContractingEigenvalue : ℝ := 4 - Real.sqrt 2

def navierStokesExpandingEigenvalue : ℝ := 4 + Real.sqrt 2

/-- The smaller eigenvalue is still expanding, as asserted after equation (6.2). -/
theorem one_lt_navierStokesContractingEigenvalue : 1 < navierStokesContractingEigenvalue := by
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtSq : Real.sqrt 2 ^ (2 : ℕ) = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold navierStokesContractingEigenvalue
  nlinarith

theorem navierStokesContractingEigenvalue_lt_expandingEigenvalue :
    navierStokesContractingEigenvalue < navierStokesExpandingEigenvalue := by
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  unfold navierStokesContractingEigenvalue navierStokesExpandingEigenvalue
  linarith

/-- Product of eigenvalues recovers the covering degree. -/
theorem navierStokesEigenvalue_product :
    navierStokesContractingEigenvalue * navierStokesExpandingEigenvalue = 14 := by
  have hsqrtSq : Real.sqrt 2 ^ (2 : ℕ) = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  unfold navierStokesContractingEigenvalue navierStokesExpandingEigenvalue
  nlinarith

/-- Symmetry of `Jg` makes its two distinct eigen-directions orthogonal. -/
theorem navierStokesRadialDirection_dot_timeDirection :
    ∑ i : Fin 2, navierStokesRadialDirection i * navierStokesTimeDirection i = 0 := by
  simp [navierStokesRadialDirection, navierStokesTimeDirection, Fin.sum_univ_two]

/-- First eigenvector identity in equation (6.2). -/
theorem coverMatrix_mulVec_navierStokesRadialDirection :
    (navierStokesCoverMatrix.map (Int.castRingHom ℝ)).mulVec navierStokesRadialDirection =
      navierStokesContractingEigenvalue • navierStokesRadialDirection := by
  funext i
  fin_cases i <;>
    simp [navierStokesCoverMatrix, Matrix.mulVec, dotProduct,
      navierStokesRadialDirection, navierStokesAuxSlope,
      navierStokesContractingEigenvalue, Fin.sum_univ_succ] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Second eigenvector identity in equation (6.2). -/
theorem coverMatrix_mulVec_navierStokesTimeDirection :
    (navierStokesCoverMatrix.map (Int.castRingHom ℝ)).mulVec navierStokesTimeDirection =
      navierStokesExpandingEigenvalue • navierStokesTimeDirection := by
  funext i
  fin_cases i <;>
    simp [navierStokesCoverMatrix, Matrix.mulVec, dotProduct,
      navierStokesTimeDirection, navierStokesAuxSlope,
      navierStokesExpandingEigenvalue, Fin.sum_univ_succ] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- A nontrivial integer linear form in `1` and `√2` cannot vanish. -/
theorem irrationalLinearForm_ne_zero {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) :
    (a : ℝ) + Real.sqrt 2 * (b : ℝ) ≠ 0 := by
  intro hzero
  by_cases hb : b = 0
  · subst b
    simp only [Int.cast_zero, mul_zero, add_zero] at hzero
    exact (hab.resolve_right (by simp)) (by exact_mod_cast hzero)
  · have hbReal : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hsqrt : Real.sqrt 2 = ((-a : ℤ) : ℝ) / (b : ℝ) := by
      apply (eq_div_iff hbReal).2
      push_cast
      linarith
    exact irrational_sqrt_two.ne_rational (-a) b hsqrt

/-- Quantitative algebraic-conjugate estimate underlying equation (6.7). -/
theorem irrationalLinearForm_smallDivisor {a b : ℤ} (hab : a ≠ 0 ∨ b ≠ 0) :
    (3 * (1 + |(a : ℝ)| + |(b : ℝ)|))⁻¹ ≤
      |(a : ℝ) + Real.sqrt 2 * (b : ℝ)| := by
  have hsqrtSq : Real.sqrt 2 ^ (2 : ℕ) = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hsqrtNonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrtLe : Real.sqrt 2 ≤ 2 := by nlinarith
  have habNeg : a ≠ 0 ∨ -b ≠ 0 := hab.imp_right neg_ne_zero.mpr
  have hleft := irrationalLinearForm_ne_zero hab
  have hright : (a : ℝ) - Real.sqrt 2 * (b : ℝ) ≠ 0 := by
    simpa only [Int.cast_neg, mul_neg, sub_eq_add_neg] using
      irrationalLinearForm_ne_zero habNeg
  have hdisc : a ^ (2 : ℕ) - 2 * b ^ (2 : ℕ) ≠ 0 := by
    intro hzero
    apply mul_ne_zero hleft hright
    have hcast : ((a ^ (2 : ℕ) - 2 * b ^ (2 : ℕ) : ℤ) : ℝ) = 0 := by
      exact_mod_cast hzero
    push_cast at hcast
    nlinarith
  have hdiscAbs : (1 : ℝ) ≤ |((a ^ (2 : ℕ) - 2 * b ^ (2 : ℕ) : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hdisc
  have hproduct :
      ((a : ℝ) + Real.sqrt 2 * (b : ℝ)) *
          ((a : ℝ) - Real.sqrt 2 * (b : ℝ)) =
        ((a ^ (2 : ℕ) - 2 * b ^ (2 : ℕ) : ℤ) : ℝ) := by
    push_cast
    nlinarith
  have hone :
      1 ≤ |(a : ℝ) + Real.sqrt 2 * (b : ℝ)| *
        |(a : ℝ) - Real.sqrt 2 * (b : ℝ)| := by
    rw [← abs_mul, hproduct]
    exact hdiscAbs
  have hconjugate :
      |(a : ℝ) - Real.sqrt 2 * (b : ℝ)| ≤
        3 * (1 + |(a : ℝ)| + |(b : ℝ)|) := by
    calc
      |(a : ℝ) - Real.sqrt 2 * (b : ℝ)| ≤
          |(a : ℝ)| + |Real.sqrt 2 * (b : ℝ)| := abs_sub _ _
      _ = |(a : ℝ)| + Real.sqrt 2 * |(b : ℝ)| := by
        rw [abs_mul, abs_of_nonneg hsqrtNonneg]
      _ ≤ |(a : ℝ)| + 2 * |(b : ℝ)| := by gcongr
      _ ≤ 3 * (1 + |(a : ℝ)| + |(b : ℝ)|) := by
        nlinarith [abs_nonneg (a : ℝ), abs_nonneg (b : ℝ)]
  have hdenom : 0 < 3 * (1 + |(a : ℝ)| + |(b : ℝ)|) := by positivity
  apply (inv_le_iff_one_le_mul₀ hdenom).2
  calc
    1 ≤ |(a : ℝ) + Real.sqrt 2 * (b : ℝ)| *
        |(a : ℝ) - Real.sqrt 2 * (b : ℝ)| := hone
    _ ≤ |(a : ℝ) + Real.sqrt 2 * (b : ℝ)| *
        (3 * (1 + |(a : ℝ)| + |(b : ℝ)|)) :=
      mul_le_mul_of_nonneg_left hconjugate (abs_nonneg _)

theorem transportDetuning_navierStokesRadialDirection (frequency : Fin 2 → ℤ) :
    transportDetuning navierStokesRadialDirection frequency =
      ((frequency 0 + frequency 1 : ℤ) : ℝ) +
        Real.sqrt 2 * ((-frequency 1 : ℤ) : ℝ) := by
  simp [transportDetuning, navierStokesRadialDirection, navierStokesAuxSlope,
    Fin.sum_univ_two]
  ring

theorem transportDetuning_navierStokesTimeDirection (frequency : Fin 2 → ℤ) :
    transportDetuning navierStokesTimeDirection frequency =
      ((frequency 1 - frequency 0 : ℤ) : ℝ) +
        Real.sqrt 2 * (frequency 0 : ℝ) := by
  simp [transportDetuning, navierStokesTimeDirection, navierStokesAuxSlope,
    Fin.sum_univ_two]
  ring

theorem navierStokesRadialDirection_nonresonant {frequency : Fin 2 → ℤ}
    (hfrequency : frequency ≠ 0) :
    transportDetuning navierStokesRadialDirection frequency ≠ 0 := by
  rw [transportDetuning_navierStokesRadialDirection]
  apply irrationalLinearForm_ne_zero
  by_cases hlast : frequency 1 = 0
  · left
    intro hsum
    apply hfrequency
    funext i
    fin_cases i
    · simpa [hlast] using hsum
    · exact hlast
  · exact Or.inr (neg_ne_zero.mpr hlast)

theorem navierStokesTimeDirection_nonresonant {frequency : Fin 2 → ℤ}
    (hfrequency : frequency ≠ 0) :
    transportDetuning navierStokesTimeDirection frequency ≠ 0 := by
  rw [transportDetuning_navierStokesTimeDirection]
  apply irrationalLinearForm_ne_zero
  by_cases hfirst : frequency 0 = 0
  · left
    intro hdiff
    apply hfrequency
    funext i
    fin_cases i
    · exact hfirst
    · simpa [hfirst] using hdiff
  · exact Or.inr hfirst

/-- First explicit lower bound in equation (6.7), in an equivalent integer `ℓ¹` norm. -/
theorem navierStokesRadialDirection_smallDivisor {frequency : Fin 2 → ℤ}
    (hfrequency : frequency ≠ 0) :
    (3 * (1 + |((frequency 0 + frequency 1 : ℤ) : ℝ)| +
        |((-frequency 1 : ℤ) : ℝ)|))⁻¹ ≤
      |transportDetuning navierStokesRadialDirection frequency| := by
  rw [transportDetuning_navierStokesRadialDirection]
  apply irrationalLinearForm_smallDivisor
  by_cases hlast : frequency 1 = 0
  · left
    intro hsum
    apply hfrequency
    funext i
    fin_cases i
    · simpa [hlast] using hsum
    · exact hlast
  · exact Or.inr (neg_ne_zero.mpr hlast)

/-- Second explicit lower bound in equation (6.7), in an equivalent integer `ℓ¹` norm. -/
theorem navierStokesTimeDirection_smallDivisor {frequency : Fin 2 → ℤ}
    (hfrequency : frequency ≠ 0) :
    (3 * (1 + |((frequency 1 - frequency 0 : ℤ) : ℝ)| +
        |(frequency 0 : ℝ)|))⁻¹ ≤
      |transportDetuning navierStokesTimeDirection frequency| := by
  rw [transportDetuning_navierStokesTimeDirection]
  apply irrationalLinearForm_smallDivisor
  by_cases hfirst : frequency 0 = 0
  · left
    intro hdiff
    apply hfrequency
    funext i
    fin_cases i
    · exact hfirst
    · simpa [hfirst] using hdiff
  · exact Or.inr hfirst

/-- Lemma 8.6 on a finite packet for the paper's radial direction. -/
theorem transportDerivative_inverse_navierStokesRadialDirection
    (packet : Finset (Fin 2 → ℤ)) (amplitude : (Fin 2 → ℤ) → ℂ)
    (hzero : (0 : Fin 2 → ℤ) ∉ packet) :
    transportDerivative navierStokesRadialDirection
        (trigLift packet id (inverseAmplitude navierStokesRadialDirection amplitude)) =
      trigLift packet id amplitude := by
  apply transportDerivative_inverse
  intro frequency hmem
  exact navierStokesRadialDirection_nonresonant fun hfrequency =>
    hzero (hfrequency ▸ hmem)

/-- Lemma 8.6 on a finite packet for the paper's time direction. -/
theorem transportDerivative_inverse_navierStokesTimeDirection
    (packet : Finset (Fin 2 → ℤ)) (amplitude : (Fin 2 → ℤ) → ℂ)
    (hzero : (0 : Fin 2 → ℤ) ∉ packet) :
    transportDerivative navierStokesTimeDirection
        (trigLift packet id (inverseAmplitude navierStokesTimeDirection amplitude)) =
      trigLift packet id amplitude := by
  apply transportDerivative_inverse
  intro frequency hmem
  exact navierStokesTimeDirection_nonresonant fun hfrequency =>
    hzero (hfrequency ▸ hmem)

end

end GaloisForLFunctions.HTGeometry.NavierStokesAlgebraicTorusDirections
