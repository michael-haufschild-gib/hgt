import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Exact Cauchy--Volterra reconstruction for the CCM-FU moving wall

The moving FU coefficient has a simple zero at its terminal wall.  Any Cauchy representation
therefore carries a first-order endpoint jet.  This file records the exact finite-interval
identity before it is applied to the completed prime--polar cells: no absolute-value estimate or
source separation occurs here.
-/

open Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A terminal-zero profile is exactly its Cauchy--Volterra curvature mixture, with the
necessary first-order endpoint jet kept explicitly. -/
theorem cauchyVolterra_reconstruction
    {x Y : ℝ} (hxy : x ≤ Y) (hY : Y ≠ 0)
    {f f' f'' : ℝ → ℝ}
    (hterminal : f Y = 0)
    (hderiv : ∀ y ∈ Set.Icc x Y, HasDerivAt f (f' y) y)
    (hderiv' : ∀ y ∈ Set.Icc x Y, HasDerivAt f' (f'' y) y)
    (hint : IntervalIntegrable f' volume x Y)
    (hint' : IntervalIntegrable f'' volume x Y) :
    f x = (-Y * f' Y) * (1 - x / Y) +
      ∫ y in x..Y, f'' y * (y - x) := by
  have hlin : ∀ y ∈ Set.uIcc x Y, HasDerivAt (fun z : ℝ => z - x) 1 y := by
    intro y _
    simpa using (hasDerivAt_id (x := y)).sub_const x
  have hfderiv : ∀ y ∈ Set.uIcc x Y, HasDerivAt f (f' y) y := by
    intro y hy
    rw [Set.uIcc_of_le hxy] at hy
    exact hderiv y hy
  have hfderiv' : ∀ y ∈ Set.uIcc x Y, HasDerivAt f' (f'' y) y := by
    intro y hy
    rw [Set.uIcc_of_le hxy] at hy
    exact hderiv' y hy
  have hlinInt : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume x Y :=
    continuous_const.intervalIntegrable x Y
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := x) (b := Y) (u := fun z : ℝ => z - x) (u' := fun _ : ℝ => 1)
    (v := f') (v' := f'') hlin hfderiv' hlinInt hint'
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := x) (b := Y) (f := f) (f' := f') hfderiv hint
  simp only [one_mul] at hparts
  rw [hfund] at hparts
  simp only [hterminal, sub_self, zero_mul, sub_zero] at hparts
  have hparts' :
      (∫ y in x..Y, f'' y * (y - x)) = (Y - x) * f' Y + f x := by
    calc
      (∫ y in x..Y, f'' y * (y - x)) =
          ∫ y in x..Y, (y - x) * f'' y := by
            apply intervalIntegral.integral_congr
            intro y _
            ring
      _ = (Y - x) * f' Y + f x := by linarith
  have hjet : (-Y * f' Y) * (1 - x / Y) = -(Y - x) * f' Y := by
    field_simp [hY]
  rw [hjet]
  linarith

/-- The same reconstruction in Cauchy coordinates.  Positivity of the kernel on `0 < x ≤ y`
is explicit, while all signed arithmetic information remains in the transported source. -/
theorem cauchyVolterra_reconstruction_cauchy
    {x Y : ℝ} (hx : 0 < x) (hxy : x ≤ Y) (hY : Y ≠ 0)
    {f f' f'' : ℝ → ℝ}
    (hterminal : f Y = 0)
    (hderiv : ∀ y ∈ Set.Icc x Y, HasDerivAt f (f' y) y)
    (hderiv' : ∀ y ∈ Set.Icc x Y, HasDerivAt f' (f'' y) y)
    (hint : IntervalIntegrable f' volume x Y)
    (hint' : IntervalIntegrable f'' volume x Y) :
    f x = (-Y * f' Y) * (1 - x / Y) +
      ∫ y in x..Y, (y ^ 2 * f'' y) * (1 / y - x / y ^ 2) := by
  rw [cauchyVolterra_reconstruction hxy hY hterminal hderiv hderiv' hint hint']
  congr 1
  apply intervalIntegral.integral_congr
  intro y hy
  rw [Set.uIcc_of_le hxy] at hy
  have hy0 : y ≠ 0 := ne_of_gt (hx.trans_le hy.1)
  field_simp [hy0]

/-- Cauchy kernel used to transport the completed finite source in the square-root coordinate. -/
def cauchyVolterraKernel (x y : ℝ) : ℝ := 1 / y - x / y ^ 2

/-- Finite Fubini transport preserves cancellation of arbitrary signed cells exactly.  In the
CCM-FU application, `a` is the literal completed prime-minus-polar cell sequence; no term is
estimated or separated before this identity. -/
theorem cauchyVolterra_finite_signed_transport
    {ι : Type*} (f : ℝ → ℝ) (s : Finset ι) (a : ι → ℝ) (ξ : ι → ℝ)
    {x Y J : ℝ} {q : ℝ → ℝ}
    (hint : ∀ i ∈ s, IntervalIntegrable
      (fun y : ℝ => a i * (q y * cauchyVolterraKernel (ξ i) y)) volume x Y)
    (hrecon : ∀ i ∈ s,
      f (ξ i) = J * (1 - ξ i / Y) +
        ∫ y in x..Y, q y * cauchyVolterraKernel (ξ i) y) :
    (∑ i ∈ s, a i * f (ξ i)) =
      J * ∑ i ∈ s, a i * (1 - ξ i / Y) +
        ∫ y in x..Y, q y * ∑ i ∈ s, a i * cauchyVolterraKernel (ξ i) y := by
  calc
    (∑ i ∈ s, a i * f (ξ i)) =
        ∑ i ∈ s, a i * (J * (1 - ξ i / Y) +
          ∫ y in x..Y, q y * cauchyVolterraKernel (ξ i) y) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hrecon i hi]
    _ =
        (∑ i ∈ s, a i * (J * (1 - ξ i / Y))) +
          ∑ i ∈ s, a i * (∫ y in x..Y, q y * cauchyVolterraKernel (ξ i) y) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = J * ∑ i ∈ s, a i * (1 - ξ i / Y) +
          ∑ i ∈ s, ∫ y in x..Y,
            a i * (q y * cauchyVolterraKernel (ξ i) y) := by
            congr 1
            · rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              ring
            · apply Finset.sum_congr rfl
              intro i hi
              rw [intervalIntegral.integral_const_mul]
    _ = J * ∑ i ∈ s, a i * (1 - ξ i / Y) +
          ∫ y in x..Y, ∑ i ∈ s,
            a i * (q y * cauchyVolterraKernel (ξ i) y) := by
            rw [intervalIntegral.integral_finsetSum hint]
    _ = J * ∑ i ∈ s, a i * (1 - ξ i / Y) +
          ∫ y in x..Y, q y * ∑ i ∈ s,
            a i * cauchyVolterraKernel (ξ i) y := by
            congr 1
            apply intervalIntegral.integral_congr
            intro y _
            change (∑ i ∈ s, a i * (q y * cauchyVolterraKernel (ξ i) y)) =
              q y * ∑ i ∈ s, a i * cauchyVolterraKernel (ξ i) y
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring

end

end RHTower
