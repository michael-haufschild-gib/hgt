import GaloisForLFunctions.HTGeometry.UniformGridStep
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Rectangle-grid decomposition

A continuous integrand on a finite rectangle decomposes exactly into the
iterated integrals over a uniform product grid.  This is the summation step
needed to turn one-cell Poincaré witnesses into a finite-dimensional
approximation on a bounded two-dimensional core.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite product grid exactly decomposes the iterated integral of a continuous rectangle field. -/
theorem setIntegral_rectangle_grid_sum {F : ℝ × ℝ → ℝ}
    (hF : Continuous F) {a c hx hy : ℝ} (hhx : 0 ≤ hx) (hhy : 0 ≤ hy)
    (M K : ℕ) :
    (∫ y in Set.Ioc c (c + (K : ℝ) * hy),
      ∫ x in Set.Ioc a (a + (M : ℝ) * hx), F (x, y)) =
      ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
        ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
          ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx), F (x, y) := by
  have hEndx : a ≤ a + (M : ℝ) * hx := by
    have hnonneg : 0 ≤ (M : ℝ) * hx := mul_nonneg (Nat.cast_nonneg M) hhx
    linarith
  have hEndy : c ≤ c + (K : ℝ) * hy := by
    have hnonneg : 0 ≤ (K : ℝ) * hy := mul_nonneg (Nat.cast_nonneg K) hhy
    linarith
  have hCellx (j : ℕ) :
      a + (j : ℝ) * hx ≤ a + ((j + 1 : ℕ) : ℝ) * hx := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hCelly (k : ℕ) :
      c + (k : ℝ) * hy ≤ c + ((k + 1 : ℕ) : ℝ) * hy := by
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hFinner (y : ℝ) : Continuous fun x => F (x, y) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hFouter (u v : ℝ) : Continuous fun y => ∫ x in u..v, F (x, y) := by
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y x : ℝ => F (x, y))
      (hF.comp (continuous_snd.prodMk continuous_fst)) u v
  calc
    (∫ y in Set.Ioc c (c + (K : ℝ) * hy),
      ∫ x in Set.Ioc a (a + (M : ℝ) * hx), F (x, y)) =
        ∫ y in c..(c + (K : ℝ) * hy),
          ∫ x in a..(a + (M : ℝ) * hx), F (x, y) := by
            rw [intervalIntegral.integral_of_le hEndy]
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
            intro y _
            exact (intervalIntegral.integral_of_le hEndx).symm
    _ = ∑ k ∈ Finset.range K,
        ∫ y in (c + (k : ℝ) * hy)..(c + ((k + 1 : ℕ) : ℝ) * hy),
          ∫ x in a..(a + (M : ℝ) * hx), F (x, y) := by
            simpa only [Nat.cast_add, Nat.cast_one] using
              (integral_grid_sum (a := c) (h := hy) hhy K
                ((hFouter a (a + (M : ℝ) * hx)).intervalIntegrable _ _))
    _ = ∑ k ∈ Finset.range K,
        ∫ y in (c + (k : ℝ) * hy)..(c + ((k + 1 : ℕ) : ℝ) * hy),
          ∑ j ∈ Finset.range M,
            ∫ x in (a + (j : ℝ) * hx)..(a + ((j + 1 : ℕ) : ℝ) * hx), F (x, y) := by
            apply Finset.sum_congr rfl
            intro k _
            apply intervalIntegral.integral_congr
            intro y _
            simpa only [Nat.cast_add, Nat.cast_one] using
              (integral_grid_sum (a := a) (h := hx) hhx M
                ((hFinner y).intervalIntegrable _ _))
    _ = ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
        ∫ y in (c + (k : ℝ) * hy)..(c + ((k + 1 : ℕ) : ℝ) * hy),
          ∫ x in (a + (j : ℝ) * hx)..(a + ((j + 1 : ℕ) : ℝ) * hx), F (x, y) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [intervalIntegral.integral_finsetSum]
            intro j _
            exact (hFouter _ _).intervalIntegrable _ _
    _ = ∑ k ∈ Finset.range K, ∑ j ∈ Finset.range M,
        ∫ y in Set.Ioc (c + (k : ℝ) * hy) (c + ((k + 1 : ℕ) : ℝ) * hy),
          ∫ x in Set.Ioc (a + (j : ℝ) * hx) (a + ((j + 1 : ℕ) : ℝ) * hx), F (x, y) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro j _
            rw [intervalIntegral.integral_of_le (hCelly k)]
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
            intro y _
            exact intervalIntegral.integral_of_le (hCellx j)

end

end GaloisForLFunctions.HTGeometry
