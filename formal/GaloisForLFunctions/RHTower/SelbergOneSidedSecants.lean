import GaloisForLFunctions.RHTower.SelbergOneSidedCurvatureDecay

/-!
# Quantitative one-sided secant bounds

The actual inverse-square curvature correction gives pointwise forward and
backward unit-secant estimates. A strip of fixed width controls the derivative
independently of the strip offset, enabling uniform source-family estimates.
-/

open Set Filter Topology
namespace GaloisForLFunctions.RHTower.SelbergOneSidedSecants
noncomputable section
open SelbergOneSidedCurvatureDecay

/-- The corrected monotone derivative lies below the forward unit secant with its exact correction. -/
theorem derivative_le_forward_secant {u v a2 : ℝ → ℝ} {A C y : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C)
    (hu : ∀ s ∈ Ici A, HasDerivAt u (v s) s)
    (hv : ∀ s ∈ Ici A, HasDerivAt v (a2 s) s)
    (ha2 : ∀ s ∈ Ici A, -C / s ^ 2 ≤ a2 s) (hy : A ≤ y) :
    v y ≤ u (y + 1) - u y + C / y := by
  have hmono := corrected_derivative_monotone hA hv ha2
  have hs := (convex_Icc y (y + 1)).mul_sub_le_image_sub_of_le_deriv
    (f := u)
    (by intro s hs; exact (hu s (hy.trans hs.1)).continuousAt.continuousWithinAt)
    (by intro s hs
        exact (hu s (hy.trans (interior_subset hs).1)).differentiableAt.differentiableWithinAt)
    (C := v y - C / y)
    (by intro s hs
        have hss : s ∈ Icc y (y + 1) := interior_subset hs
        have hAs := hy.trans hss.1
        rw [(hu s hAs).deriv]
        have hm := hmono hy hAs hss.1
        have hc := div_nonneg hC (hA.trans_le hAs).le
        linarith)
    y (by constructor <;> linarith) (y + 1) (by constructor <;> linarith) (by linarith)
  nlinarith

/-- The backward unit secant lies below the derivative after the exact inverse-height correction. -/
theorem backward_secant_le_derivative {u v a2 : ℝ → ℝ} {A C y : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C)
    (hu : ∀ s ∈ Ici A, HasDerivAt u (v s) s)
    (hv : ∀ s ∈ Ici A, HasDerivAt v (a2 s) s)
    (ha2 : ∀ s ∈ Ici A, -C / s ^ 2 ≤ a2 s) (hy : A + 1 ≤ y) :
    u y - u (y - 1) - C / (y - 1) ≤ v y := by
  have hmono := corrected_derivative_monotone hA hv ha2
  have hAy : A ≤ y := by linarith
  have hprev : 0 < y - 1 := by linarith
  have hs := (convex_Icc (y - 1) y).image_sub_le_mul_sub_of_deriv_le
    (f := u)
    (by intro s hs; exact (hu s (show A ≤ s by linarith [hs.1])).continuousAt.continuousWithinAt)
    (by intro s hs
        have hss : s ∈ Icc (y - 1) y := interior_subset hs
        exact (hu s (show A ≤ s by linarith [hss.1])).differentiableAt.differentiableWithinAt)
    (C := v y - C / y + C / (y - 1))
    (by intro s hs
        have hss : s ∈ Icc (y - 1) y := interior_subset hs
        have hAs : A ≤ s := by linarith [hss.1]
        rw [(hu s hAs).deriv]
        have hm := hmono hAs hAy hss.2
        have hc := div_le_div_of_nonneg_left hC hprev hss.1
        linarith)
    (y - 1) (by constructor <;> linarith) y (by constructor <;> linarith) (by linarith)
  have hc := div_nonneg hC (hA.trans_le hAy).le
  nlinarith

/-- A strip of width delta bounds the actual derivative uniformly, independent of its vertical offset. -/
theorem abs_derivative_le_of_range {u v a2 : ℝ → ℝ} {A C L delta y : ℝ}
    (hA : 0 < A) (hC : 0 ≤ C)
    (hu : ∀ s ∈ Ici A, HasDerivAt u (v s) s)
    (hv : ∀ s ∈ Ici A, HasDerivAt v (a2 s) s)
    (ha2 : ∀ s ∈ Ici A, -C / s ^ 2 ≤ a2 s)
    (hb : ∀ s ∈ Ici A, L ≤ u s ∧ u s ≤ L + delta) (hy : A + 1 ≤ y) :
    |v y| ≤ delta + C / (y - 1) := by
  have hAy : A ≤ y := by linarith
  have hupp := derivative_le_forward_secant hA hC hu hv ha2 hAy
  have hlow := backward_secant_le_derivative hA hC hu hv ha2 hy
  have hb0 := hb y hAy
  have hbp := hb (y + 1) (by linarith : A ≤ y + 1)
  have hbm := hb (y - 1) (by linarith : A ≤ y - 1)
  have hcorr : C / y ≤ C / (y - 1) :=
    div_le_div_of_nonneg_left hC (by linarith : 0 < y - 1) (by linarith)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end GaloisForLFunctions.RHTower.SelbergOneSidedSecants
