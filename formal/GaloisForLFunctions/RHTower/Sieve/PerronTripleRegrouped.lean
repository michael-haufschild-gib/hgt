import GaloisForLFunctions.RHTower.Sieve.PerronVerticalTripleBound
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The triple Perron integrand, regrouped

The corpus's triple bound splits the integrand as `(‖A‖·‖B‖)·(‖f‖·kernel)` and charges the third
factor its supremum.  That grouping cannot reach Halász's bound: the supremum of the long factor
multiplies the whole length of the range.

The right grouping puts the long factor *with the inner prime polynomial*:

```text
∫ ‖A·B·f·x^s/s‖  ≤  √(∫‖A‖²) · √(∫ ‖B‖²‖f‖²·x^{2σ}/‖s‖²) .
```

The first factor is a pure mean square of a prime-supported polynomial — no height, no envelope.
The second is the object that a cell decomposition estimates, with the envelope entering as an
aggregate of per-cell maxima rather than as a global supremum.
-/

noncomputable section
namespace RHTower.Sieve

open Complex MeasureTheory Set

/-- The modulus of the triple Perron integrand, with the long factor grouped against the inner
polynomial. -/
theorem norm_perron_triple_integrand_regrouped {x : ℝ} (hx : 0 < x) (a b f : ℂ) (σ t : ℝ) :
    ‖a * b * f * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖
      = ‖a‖ * (‖b‖ * ‖f‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)) := by
  rw [norm_perron_triple_integrand hx]
  ring

/-- **The regrouped Cauchy–Schwarz bound for the triple Perron integrand.**  The outer polynomial is
separated by itself; the long factor travels with the inner polynomial and the kernel. -/
theorem integral_Icc_norm_perron_triple_regrouped_le
    {A B f : ℕ → ℂ} {sA sB : Finset ℕ}
    (hA0 : 0 ∉ sA) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hB0 : 0 ∉ sB) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    {σ x c d : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    (hFc : Continuous fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℝ) * I)) :
    (∫ y in Set.Icc c d,
        ‖LSeries A ((σ : ℂ) + (y : ℝ) * I) * LSeries B ((σ : ℂ) + (y : ℝ) * I)
          * LSeries f ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      ≤ Real.sqrt (∫ y in Set.Icc c d, ‖LSeries A ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
        * Real.sqrt (∫ y in Set.Icc c d,
            (‖LSeries B ((σ : ℂ) + (y : ℝ) * I)‖ * ‖LSeries f ((σ : ℂ) + (y : ℝ) * I)‖
              * (x ^ σ / ‖(σ : ℂ) + (y : ℝ) * I‖)) ^ 2) := by
  classical
  have hAc : Continuous fun t : ℝ => LSeries A ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hA0 hAsupp σ
  have hBc : Continuous fun t : ℝ => LSeries B ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hB0 hBsupp σ
  set F₁ : ℝ → ℝ := fun y => ‖LSeries A ((σ : ℂ) + (y : ℝ) * I)‖ with hF₁
  set F₂ : ℝ → ℝ := fun y =>
    ‖LSeries B ((σ : ℂ) + (y : ℝ) * I)‖ * ‖LSeries f ((σ : ℂ) + (y : ℝ) * I)‖
      * (x ^ σ / ‖(σ : ℂ) + (y : ℝ) * I‖) with hF₂
  have hF₁c : Continuous F₁ := hAc.norm
  have hF₂c : Continuous F₂ := (hBc.norm.mul hFc.norm).mul (continuous_perron_kernel_norm hσ)
  have hF₁0 : ∀ y, 0 ≤ F₁ y := fun y => norm_nonneg _
  have hF₂0 : ∀ y, 0 ≤ F₂ y := fun y => by
    rw [hF₂]
    have : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
    positivity
  -- the integrand is the product
  have hsplit : (∫ y in Set.Icc c d,
        ‖LSeries A ((σ : ℂ) + (y : ℝ) * I) * LSeries B ((σ : ℂ) + (y : ℝ) * I)
          * LSeries f ((σ : ℂ) + (y : ℝ) * I)
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℝ) * I) / ((σ : ℂ) + (y : ℝ) * I))‖)
      = ∫ y in Set.Icc c d, F₁ y * F₂ y := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [hF₁, hF₂]
    exact norm_perron_triple_integrand_regrouped hx _ _ _ σ y
  rw [hsplit]
  -- Cauchy–Schwarz on the restricted measure
  have hint₁ : Integrable (fun y => F₁ y ^ 2) (volume.restrict (Set.Icc c d)) :=
    (hF₁c.pow 2).integrableOn_Icc
  have hint₂ : Integrable (fun y => F₂ y ^ 2) (volume.restrict (Set.Icc c d)) :=
    (hF₂c.pow 2).integrableOn_Icc
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    (μ := volume.restrict (Set.Icc c d))
    hF₁c.aestronglyMeasurable hF₂c.aestronglyMeasurable hint₁ hint₂
  have hprod0 : (0 : ℝ) ≤ ∫ y in Set.Icc c d, F₁ y * F₂ y :=
    MeasureTheory.integral_nonneg fun y => mul_nonneg (hF₁0 y) (hF₂0 y)
  have hP0 : (0 : ℝ) ≤ ∫ y in Set.Icc c d, F₁ y ^ 2 :=
    MeasureTheory.integral_nonneg fun y => by positivity
  calc (∫ y in Set.Icc c d, F₁ y * F₂ y)
      = Real.sqrt ((∫ y in Set.Icc c d, F₁ y * F₂ y) ^ 2) := (Real.sqrt_sq hprod0).symm
    _ ≤ Real.sqrt ((∫ y in Set.Icc c d, F₁ y ^ 2) * ∫ y in Set.Icc c d, F₂ y ^ 2) :=
        Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (∫ y in Set.Icc c d, F₁ y ^ 2)
          * Real.sqrt (∫ y in Set.Icc c d, F₂ y ^ 2) := Real.sqrt_mul hP0 _

end RHTower.Sieve

end
