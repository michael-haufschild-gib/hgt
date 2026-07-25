/-
# Bourgain's polynomial curve and quantitative jet nondegeneracy

Bourgain's curve-decoupling theorem assumes the nonvanishing Wronskian
condition (1.1).  The Taylor reduction in equations (2.18)--(2.19) produces
two phase functions close in `C⁴` to `t³` and `t⁴`; condition (2.11) is the
corresponding separated `2×2` jet determinant.

This file proves both algebraic inputs without assumptions:

* the full four-dimensional monomial Wronskian equals `288`, even when each
  derivative column is evaluated at an independent point;
* every pair in a unit `C⁴`-jet neighborhood of `(t³,t⁴)` has separated jet
  determinant of absolute value at least `90` on `[0,1]²`.

The remaining Taylor-localization theorem must show that Bourgain's actual
normalized remainders lie in this neighborhood.
-/
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

namespace RHTower

noncomputable section

/-- Cubic limiting phase in Bourgain's normalized Taylor expansion. -/
def bourgainCubicPhase (x : ℝ) : ℝ := x ^ (3 : ℕ)

/-- Quartic limiting phase in Bourgain's normalized Taylor expansion. -/
def bourgainQuarticPhase (x : ℝ) : ℝ := x ^ (4 : ℕ)

/-- Separated `2×2` third/fourth-jet determinant from Bourgain (2.11). -/
def bourgainSeparatedJetDet
    (φ₃ φ₄ : ℝ → ℝ) (s t : ℝ) : ℝ :=
  iteratedDeriv 3 φ₃ s * iteratedDeriv 4 φ₄ t -
    iteratedDeriv 3 φ₄ s * iteratedDeriv 4 φ₃ t

/-- Wronskian matrix in Bourgain's condition (1.1), specialized to the
monomial curve `(t,t²,t³,t⁴)` but retaining independent evaluation points
for each derivative order. -/
def bourgainMonomialJetMatrix
    (t : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j =>
    iteratedDeriv ((j : ℕ) + 1)
      (fun x : ℝ => x ^ ((i : ℕ) + 1)) (t j)

theorem bourgainMonomialJetMatrix_lowerTriangular (t : Fin 4 → ℝ) :
    (bourgainMonomialJetMatrix t).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : (i : ℕ) < (j : ℕ) := hij
  fin_cases i <;> fin_cases j <;>
    norm_num [bourgainMonomialJetMatrix, iteratedDeriv_eq_iterate,
      iter_deriv_pow, Finset.prod_range_succ] at *

@[simp] theorem bourgainMonomialJetMatrix_diagonal
    (t : Fin 4 → ℝ) (i : Fin 4) :
    bourgainMonomialJetMatrix t i i =
      (![1, 2, 6, 24] : Fin 4 → ℝ) i := by
  fin_cases i <;>
    norm_num [bourgainMonomialJetMatrix, iteratedDeriv_eq_iterate,
      iter_deriv_pow]

/-- Exact Wronskian certificate for the monomial curve, uniform in all four
independent evaluation points allowed by Bourgain (1.1). -/
theorem bourgainMonomialJetMatrix_det (t : Fin 4 → ℝ) :
    (bourgainMonomialJetMatrix t).det = 288 := by
  rw [Matrix.det_of_lowerTriangular _
    (bourgainMonomialJetMatrix_lowerTriangular t)]
  simp [Fin.prod_univ_succ]
  norm_num

theorem iteratedDeriv_bourgainCubicPhase_three (x : ℝ) :
    iteratedDeriv 3 bourgainCubicPhase x = 6 := by
  change iteratedDeriv 3 (fun y : ℝ => y ^ (3 : ℕ)) x = 6
  rw [iteratedDeriv_eq_iterate, iter_deriv_pow]
  norm_num

theorem iteratedDeriv_bourgainCubicPhase_four (x : ℝ) :
    iteratedDeriv 4 bourgainCubicPhase x = 0 := by
  change iteratedDeriv 4 (fun y : ℝ => y ^ (3 : ℕ)) x = 0
  rw [iteratedDeriv_eq_iterate, iter_deriv_pow]
  norm_num

theorem iteratedDeriv_bourgainQuarticPhase_three (x : ℝ) :
    iteratedDeriv 3 bourgainQuarticPhase x = 24 * x := by
  change iteratedDeriv 3 (fun y : ℝ => y ^ (4 : ℕ)) x = 24 * x
  rw [iteratedDeriv_eq_iterate, iter_deriv_pow]
  norm_num

theorem iteratedDeriv_bourgainQuarticPhase_four (x : ℝ) :
    iteratedDeriv 4 bourgainQuarticPhase x = 24 := by
  change iteratedDeriv 4 (fun y : ℝ => y ^ (4 : ℕ)) x = 24
  rw [iteratedDeriv_eq_iterate, iter_deriv_pow]
  norm_num

/-- Exact separated determinant for the limiting cubic/quartic phase pair. -/
theorem bourgainSeparatedJetDet_cubic_quartic (s t : ℝ) :
    bourgainSeparatedJetDet bourgainCubicPhase bourgainQuarticPhase s t = 144 := by
  simp [bourgainSeparatedJetDet,
    iteratedDeriv_bourgainCubicPhase_three,
    iteratedDeriv_bourgainCubicPhase_four,
    iteratedDeriv_bourgainQuarticPhase_three,
    iteratedDeriv_bourgainQuarticPhase_four]
  norm_num

/-- Quantitative `C⁴`-jet neighborhood of the cubic/quartic model used in
Bourgain's Taylor reduction (2.18)--(2.19). -/
def BourgainPolynomialJetClose
    (η : ℝ) (φ₃ φ₄ : ℝ → ℝ) : Prop :=
  ∀ x ∈ Set.Icc (0 : ℝ) 1,
    |iteratedDeriv 3 φ₃ x - 6| ≤ η ∧
    |iteratedDeriv 4 φ₃ x| ≤ η ∧
    |iteratedDeriv 3 φ₄ x - 24 * x| ≤ η ∧
    |iteratedDeriv 4 φ₄ x - 24| ≤ η

/-- The exact cubic/quartic phase pair has zero jet error. -/
theorem bourgainPolynomialJetClose_cubic_quartic :
    BourgainPolynomialJetClose 0
      bourgainCubicPhase bourgainQuarticPhase := by
  intro x _
  simp [iteratedDeriv_bourgainCubicPhase_three,
    iteratedDeriv_bourgainCubicPhase_four,
    iteratedDeriv_bourgainQuarticPhase_three,
    iteratedDeriv_bourgainQuarticPhase_four]

/-- Bourgain's separated `2×2` jet determinant remains uniformly bounded
away from zero throughout a unit `C⁴` neighborhood of `(t³,t⁴)`. -/
theorem abs_bourgainSeparatedJetDet_ge_of_polynomialJetClose
    {η : ℝ} {φ₃ φ₄ : ℝ → ℝ}
    (hη1 : η ≤ 1)
    (hclose : BourgainPolynomialJetClose η φ₃ φ₄)
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    90 ≤ |bourgainSeparatedJetDet φ₃ φ₄ s t| := by
  rcases hclose s hs with ⟨hA, _, hC, _⟩
  rcases hclose t ht with ⟨_, hE, _, hB⟩
  let A := iteratedDeriv 3 φ₃ s
  let B := iteratedDeriv 4 φ₄ t
  let C := iteratedDeriv 3 φ₄ s
  let E := iteratedDeriv 4 φ₃ t
  have hA5 : 5 ≤ A := by
    have := (abs_le.mp hA).1
    dsimp [A]
    linarith
  have hB23 : 23 ≤ B := by
    have := (abs_le.mp hB).1
    dsimp [B]
    linarith
  have hprod : 115 ≤ A * B := by
    have hmul : 0 ≤ (A - 5) * (B - 23) :=
      mul_nonneg (sub_nonneg.mpr hA5) (sub_nonneg.mpr hB23)
    nlinarith
  have hC25 : |C| ≤ 25 := by
    calc
      |C| = |(C - 24 * s) + 24 * s| := by ring_nf
      _ ≤ |C - 24 * s| + |24 * s| := abs_add_le _ _
      _ ≤ η + 24 := by
        apply add_le_add
        · simpa [C] using hC
        · rw [abs_of_nonneg (mul_nonneg (by norm_num) hs.1)]
          nlinarith [hs.2]
      _ ≤ 25 := by linarith
  have hE1 : |E| ≤ 1 := by
    exact le_trans (by simpa [E] using hE) hη1
  have hCE : C * E ≤ 25 := by
    calc
      C * E ≤ |C * E| := le_abs_self _
      _ = |C| * |E| := abs_mul C E
      _ ≤ 25 * 1 := mul_le_mul hC25 hE1 (abs_nonneg E) (by norm_num)
      _ = 25 := by norm_num
  have hD : 90 ≤ A * B - C * E := by linarith
  exact le_trans hD (le_abs_self (A * B - C * E))

end

end RHTower
