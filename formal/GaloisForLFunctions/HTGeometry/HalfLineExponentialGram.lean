import GaloisForLFunctions.HTGeometry.CauchyMatrixDeterminant
import GaloisForLFunctions.HTGeometry.FisherOneCornerCoareaTransform
import GaloisForLFunctions.HTGeometry.GramDeterminantDistance

/-!
# The Gram determinant of a half-line exponential system

The half-line features `y ↦ exp (-λ y)` of positive real rates have the Cauchy Gram
`⟪e_λ, e_μ⟫ = 1/(λ + μ)`.  The Cauchy determinant therefore evaluates every finite Gram
determinant of the system in closed form, and the consecutive determinant ratio gives the exact
squared distance from one exponential to the span of the others.
-/

open Finset Matrix MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The half-line exponential of a positive real rate. -/
def expFeature (lam : ℝ) (h : 0 < lam) : Lp ℂ 2 halfLineLaplaceMeasure :=
  halfLineLaplaceFeature (lam : ℂ) (by simpa using h)

theorem inner_expFeature {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    inner ℂ (expFeature a ha) (expFeature b hb) = ((a : ℂ) + (b : ℂ))⁻¹ := by
  rw [expFeature, expFeature, inner_halfLineLaplaceFeature, one_div]
  congr 1
  simp

theorem gram_expFeature {N : ℕ} (lam : Fin N → ℝ) (hpos : ∀ i, 0 < lam i) :
    Matrix.gram ℂ (fun i => expFeature (lam i) (hpos i)) =
      cauchyMatrix (fun i => ((lam i : ℝ) : ℂ)) (fun j => ((lam j : ℝ) : ℂ)) := by
  ext i j
  rw [Matrix.gram_apply, inner_expFeature, cauchyMatrix_apply]

theorem add_ne_zero_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ((a : ℂ) + (b : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
  linarith

/-- **The exponential Gram determinant.** -/
theorem det_gram_expFeature {N : ℕ} (lam : Fin N → ℝ) (hpos : ∀ i, 0 < lam i) :
    (Matrix.gram ℂ (fun i => expFeature (lam i) (hpos i))).det *
        ∏ i, ∏ j, (((lam i : ℝ) : ℂ) + ((lam j : ℝ) : ℂ)) =
      ∏ i, ∏ j ∈ Finset.Ioi i,
        ((((lam i : ℝ) : ℂ) - ((lam j : ℝ) : ℂ)) * (((lam i : ℝ) : ℂ) - ((lam j : ℝ) : ℂ))) := by
  rw [gram_expFeature]
  exact det_cauchyMatrix _ _ (fun i j => add_ne_zero_of_pos (hpos i) (hpos j))

/-- The exponential Gram determinant of distinct positive rates is nonzero. -/
theorem det_gram_expFeature_ne_zero {N : ℕ} (lam : Fin N → ℝ) (hpos : ∀ i, 0 < lam i)
    (hinj : Function.Injective lam) :
    (Matrix.gram ℂ (fun i => expFeature (lam i) (hpos i))).det ≠ 0 := by
  intro hzero
  have hkey := det_gram_expFeature lam hpos
  rw [hzero, zero_mul] at hkey
  have hne : (∏ i, ∏ j ∈ Finset.Ioi i,
      ((((lam i : ℝ) : ℂ) - ((lam j : ℝ) : ℂ)) *
        (((lam i : ℝ) : ℂ) - ((lam j : ℝ) : ℂ)))) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    have hsub : ((lam i : ℝ) : ℂ) - ((lam j : ℝ) : ℂ) ≠ 0 := by
      rw [sub_ne_zero, Ne, Complex.ofReal_inj]
      exact fun h => hij (hinj h)
    exact mul_ne_zero hsub hsub
  exact hne hkey.symm

/-- Distinct positive rates give a linearly independent exponential system. -/
theorem linearIndependent_expFeature {N : ℕ} (lam : Fin N → ℝ) (hpos : ∀ i, 0 < lam i)
    (hinj : Function.Injective lam) :
    LinearIndependent ℂ (fun i => expFeature (lam i) (hpos i)) :=
  Matrix.det_gram_ne_zero_iff_linearIndependent.mp (det_gram_expFeature_ne_zero lam hpos hinj)

end

end GaloisForLFunctions.HTGeometry
