import GaloisForLFunctions.HTGeometry.FavardJacobiMomentRealization
import GaloisForLFunctions.HTGeometry.HamburgerExistence
import GaloisForLFunctions.HTGeometry.ChristoffelPointMass
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Positive moment geometries of the two fixed-q edge recurrences

The limiting Jacobi coefficients in arXiv:2609.24149, Propositions 3.1
and 8.1, define actual positive moment forms through the corpus's Favard
construction. Write `q = exp (-exp t)` and `c = exp u`; these coordinates
cover the full ranges `0 < q < 1` and `0 < c` without premise arguments.

The continuous inverse-q Hermite branch has lower monic coefficient
`q⁻ⁿ - 1`. The Al-Salam--Carlitz branch has lower coefficient
`c qⁿ⁻¹ (1-qⁿ)` and diagonal `(1-c)qⁿ`. These moment constructions do
not assert selection of a self-adjoint extension in the indeterminate branch.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace HTGeometry

/-- Squared off-diagonal coefficient of continuous inverse-q Hermite. -/
def inverseQHermiteLower (t : ℝ) (n : ℕ) : ℝ := Real.exp (Real.exp t * n) - 1

/-- The centered inverse-q Hermite moment sequence; `ρ = exp (2u)`. -/
def inverseQHermiteMoment (t u : ℝ) : ℕ → ℝ :=
  favardMoment (fun _ => Real.exp (-u) - Real.exp u) (inverseQHermiteLower t)

theorem inverseQHermiteLower_succ_pos (t : ℝ) (n : ℕ) :
    0 < inverseQHermiteLower t (n + 1) := by
  unfold inverseQHermiteLower
  apply sub_pos.mpr
  exact Real.one_lt_exp_iff.mpr (by positivity)

/-- The inverse-q Hermite branch is positive definite at every finite order. -/
theorem inverseQHermiteMoment_positive (t u : ℝ) :
    PositiveMomentForm (inverseQHermiteMoment t u) :=
  favard_positiveMomentForm _ _ (inverseQHermiteLower_succ_pos t)

theorem inverseQHermiteMoment_zero (t u : ℝ) : inverseQHermiteMoment t u 0 = 1 := by
  simp [inverseQHermiteMoment]

/-- Gram--Schmidt recovers the paper's monic recurrence exactly. -/
theorem inverseQHermiteMoment_monicOrtho (t u : ℝ) (n : ℕ) :
    monicOrtho (inverseQHermiteMoment t u) n =
      favardPoly (fun _ => Real.exp (-u) - Real.exp u) (inverseQHermiteLower t) n :=
  monicOrtho_favardMoment _ _ (inverseQHermiteLower_succ_pos t) n

theorem inverseQHermiteMoment_norm (t u : ℝ) (n : ℕ) :
    monicOrthoNormSq (inverseQHermiteMoment t u) n =
      ∏ j ∈ Finset.range n, (Real.exp (Real.exp t * (j + 1)) - 1) := by
  simpa [inverseQHermiteMoment, inverseQHermiteLower] using
    monicOrthoNormSq_favardMoment (fun _ => Real.exp (-u) - Real.exp u)
      (inverseQHermiteLower t) (inverseQHermiteLower_succ_pos t) n

theorem inverseQHermiteMoment_alpha (t u : ℝ) (n : ℕ) :
    monicOrthoAlpha (inverseQHermiteMoment t u) n = Real.exp (-u) - Real.exp u :=
  monicOrthoAlpha_favardMoment _ _ (inverseQHermiteLower_succ_pos t) n

theorem inverseQHermiteMoment_beta (t u : ℝ) (n : ℕ) :
    monicOrthoBeta (inverseQHermiteMoment t u) (n + 1) =
      Real.exp (Real.exp t * (n + 1)) - 1 := by
  simpa [inverseQHermiteMoment, inverseQHermiteLower] using monicOrthoBeta_favardMoment
    (fun _ => Real.exp (-u) - Real.exp u) (inverseQHermiteLower t)
    (inverseQHermiteLower_succ_pos t) (Nat.succ_pos n)

/-- Lower monic coefficient of the Al-Salam--Carlitz I edge limit. -/
def alSalamCarlitzLower (t u : ℝ) (n : ℕ) : ℝ :=
  Real.exp u * Real.exp (-Real.exp t * (n - 1 : ℝ)) *
    (1 - Real.exp (-Real.exp t * n))

def alSalamCarlitzDiagonal (t u : ℝ) (n : ℕ) : ℝ :=
  (1 - Real.exp u) * Real.exp (-Real.exp t * n)

def alSalamCarlitzMoment (t u : ℝ) : ℕ → ℝ :=
  favardMoment (alSalamCarlitzDiagonal t u) (alSalamCarlitzLower t u)

theorem alSalamCarlitzLower_succ_pos (t u : ℝ) (n : ℕ) :
    0 < alSalamCarlitzLower t u (n + 1) := by
  unfold alSalamCarlitzLower
  apply mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _))
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  have : 0 < Real.exp t * (↑(n + 1) : ℝ) := by positivity
  linarith

/-- The companion branch also has an unconditional positive moment realization. -/
theorem alSalamCarlitzMoment_positive (t u : ℝ) :
    PositiveMomentForm (alSalamCarlitzMoment t u) :=
  favard_positiveMomentForm _ _ (alSalamCarlitzLower_succ_pos t u)

theorem alSalamCarlitzMoment_zero (t u : ℝ) : alSalamCarlitzMoment t u 0 = 1 := by
  simp [alSalamCarlitzMoment]

theorem alSalamCarlitzMoment_monicOrtho (t u : ℝ) (n : ℕ) :
    monicOrtho (alSalamCarlitzMoment t u) n =
      favardPoly (alSalamCarlitzDiagonal t u) (alSalamCarlitzLower t u) n :=
  monicOrtho_favardMoment _ _ (alSalamCarlitzLower_succ_pos t u) n

theorem alSalamCarlitzMoment_norm (t u : ℝ) (n : ℕ) :
    monicOrthoNormSq (alSalamCarlitzMoment t u) n =
      ∏ j ∈ Finset.range n, alSalamCarlitzLower t u (j + 1) :=
  monicOrthoNormSq_favardMoment _ _ (alSalamCarlitzLower_succ_pos t u) n

theorem alSalamCarlitzMoment_alpha (t u : ℝ) (n : ℕ) :
    monicOrthoAlpha (alSalamCarlitzMoment t u) n = alSalamCarlitzDiagonal t u n :=
  monicOrthoAlpha_favardMoment _ _ (alSalamCarlitzLower_succ_pos t u) n

theorem alSalamCarlitzMoment_beta (t u : ℝ) (n : ℕ) :
    monicOrthoBeta (alSalamCarlitzMoment t u) (n + 1) =
      alSalamCarlitzLower t u (n + 1) :=
  monicOrthoBeta_favardMoment _ _ (alSalamCarlitzLower_succ_pos t u) (Nat.succ_pos n)

/-- Actual probability realizations of both edge moment sequences, with every
atom bounded by the limiting Christoffel function as in Proposition 5.1. -/
theorem qKrawtchoukEdge_probability_realizations (t u : ℝ) :
    ∃ μ ν : ProbabilityMeasure ℝ,
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments (inverseQHermiteMoment t u) μ ∧
      GaloisForLFunctions.HTGeometry.HasHamburgerMoments (alSalamCarlitzMoment t u) ν ∧
      (∀ x, (μ : Measure ℝ).real {x} ≤ christoffelLimit (inverseQHermiteMoment t u) x) ∧
      (∀ x, (ν : Measure ℝ).real {x} ≤ christoffelLimit (alSalamCarlitzMoment t u) x) := by
  obtain ⟨μ, hμ⟩ := exists_hasHamburgerMoments_of_moment_zero_eq_one
    (inverseQHermiteMoment_positive t u) (inverseQHermiteMoment_zero t u)
  obtain ⟨ν, hν⟩ := exists_hasHamburgerMoments_of_moment_zero_eq_one
    (alSalamCarlitzMoment_positive t u) (alSalamCarlitzMoment_zero t u)
  exact ⟨μ, ν, hμ, hν,
    measureReal_singleton_le_christoffelLimit_of_hasMoments
      (inverseQHermiteMoment_positive t u) hμ,
    measureReal_singleton_le_christoffelLimit_of_hasMoments
      (alSalamCarlitzMoment_positive t u) hν⟩

end HTGeometry
