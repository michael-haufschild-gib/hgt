import GaloisForLFunctions.RHTower.BanaszczykGammaMixtureBridge
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.HTGeometry.BanaszczykGaussianAbsoluteMoment
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Product chi-square mixing and the Jensen step

Lemma 2.4 of Guo--Fang--Lu conditions a linear form on independent
chi-square-three precisions.  Its conditional Gaussian absolute moment is
proportional to

`sqrt (sum i, u i ^ (2 : ℕ) / s i)`.

This module formalizes the independent product law, its exact inverse-precision
moment, and the paper's Jensen bound.  The positive reciprocal is extended by
zero off the positive ray, so every statement is total and hypothesis-free.
-/

noncomputable section

open MeasureTheory Set

namespace RHTower

/-- Product Lebesgue measure restricted to positive precision coordinates. -/
def chiSquareThreeProductVolume (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ : Fin d => (volume : Measure ℝ).restrict (Ioi 0)

/-- Product of independent chi-square-three densities. -/
def chiSquareThreeProductDensity (d : ℕ) (s : Fin d → ℝ) : ℝ :=
  ∏ i, chiSquareThreeDensity (s i)

theorem chiSquareThreeProductDensity_nonneg (d : ℕ) (s : Fin d → ℝ) :
    0 ≤ chiSquareThreeProductDensity d s := by
  unfold chiSquareThreeProductDensity
  exact Finset.prod_nonneg fun i _ => chiSquareThreeDensity_nonneg (s i)

theorem continuous_chiSquareThreeProductDensity (d : ℕ) :
    Continuous (chiSquareThreeProductDensity d) := by
  unfold chiSquareThreeProductDensity
  exact continuous_finsetProd _ fun i _ =>
    continuous_chiSquareThreeDensity.comp (continuous_apply i)

theorem integrable_chiSquareThreeProductDensity (d : ℕ) :
    Integrable (chiSquareThreeProductDensity d) (chiSquareThreeProductVolume d) := by
  unfold chiSquareThreeProductDensity chiSquareThreeProductVolume
  exact Integrable.fintype_prod fun _ => integrableOn_chiSquareThreeDensity

/-- Independent chi-square-three product law has total mass one. -/
@[simp]
theorem integral_chiSquareThreeProductDensity (d : ℕ) :
    ∫ s, chiSquareThreeProductDensity d s ∂(chiSquareThreeProductVolume d) = 1 := by
  unfold chiSquareThreeProductDensity chiSquareThreeProductVolume
  rw [integral_fintype_prod_eq_pow, integral_chiSquareThreeDensity]
  simp

/-- Reciprocal on the positive ray, extended by zero elsewhere. -/
def positiveReciprocal (s : ℝ) : ℝ := max s⁻¹ 0

theorem positiveReciprocal_nonneg (s : ℝ) : 0 ≤ positiveReciprocal s := by
  exact le_max_right _ _

theorem measurable_positiveReciprocal : Measurable positiveReciprocal := by
  unfold positiveReciprocal
  fun_prop

@[simp]
theorem positiveReciprocal_of_pos {s : ℝ} (hs : 0 < s) : positiveReciprocal s = s⁻¹ := by
  unfold positiveReciprocal
  exact max_eq_left (inv_nonneg.mpr hs.le)

/-- Conditional variance of the Gaussian linear form at precision vector `s`. -/
def inversePrecisionQuadratic {d : ℕ} (u s : Fin d → ℝ) : ℝ :=
  ∑ i, u i ^ (2 : ℕ) * positiveReciprocal (s i)

theorem inversePrecisionQuadratic_nonneg {d : ℕ} (u s : Fin d → ℝ) :
    0 ≤ inversePrecisionQuadratic u s := by
  unfold inversePrecisionQuadratic
  exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (positiveReciprocal_nonneg _)

theorem measurable_inversePrecisionQuadratic {d : ℕ} (u : Fin d → ℝ) :
    Measurable (inversePrecisionQuadratic u) := by
  unfold inversePrecisionQuadratic
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.mul
      (measurable_positiveReciprocal.comp (continuous_apply i).measurable)

private def chiSquareInverseFactor {d : ℕ} (i k : Fin d) (s : ℝ) : ℝ :=
  (if k = i then positiveReciprocal s else 1) * chiSquareThreeDensity s

private theorem integrable_chiSquareInverseFactor {d : ℕ} (i k : Fin d) :
    Integrable (chiSquareInverseFactor i k) ((volume : Measure ℝ).restrict (Ioi 0)) := by
  by_cases hki : k = i
  · subst i
    have hpos : IntegrableOn
        (fun s : ℝ => positiveReciprocal s * chiSquareThreeDensity s) (Ioi 0) := by
      refine MeasureTheory.IntegrableOn.congr_fun
        integrableOn_inv_mul_chiSquareThreeDensity ?_ measurableSet_Ioi
      intro s hs
      change s⁻¹ * chiSquareThreeDensity s =
        positiveReciprocal s * chiSquareThreeDensity s
      rw [positiveReciprocal_of_pos hs]
    have hfun : chiSquareInverseFactor k k =
        fun s => positiveReciprocal s * chiSquareThreeDensity s := by
      funext s
      simp [chiSquareInverseFactor]
    rw [hfun]
    exact hpos
  · have hfun : chiSquareInverseFactor i k = chiSquareThreeDensity := by
      funext s
      simp [chiSquareInverseFactor, hki]
    rw [hfun]
    exact integrableOn_chiSquareThreeDensity

private theorem positiveReciprocal_mul_density_eq_prod {d : ℕ}
    (i : Fin d) (s : Fin d → ℝ) :
    positiveReciprocal (s i) * chiSquareThreeProductDensity d s =
      ∏ k, chiSquareInverseFactor i k (s k) := by
  unfold chiSquareThreeProductDensity chiSquareInverseFactor
  rw [Finset.prod_mul_distrib]
  simp

theorem integrable_positiveReciprocal_mul_chiSquareThreeProductDensity
    {d : ℕ} (i : Fin d) :
    Integrable (fun s : Fin d → ℝ =>
      positiveReciprocal (s i) * chiSquareThreeProductDensity d s)
      (chiSquareThreeProductVolume d) := by
  have hprod : Integrable (fun s : Fin d → ℝ =>
      ∏ k, chiSquareInverseFactor i k (s k)) (chiSquareThreeProductVolume d) := by
    unfold chiSquareThreeProductVolume
    exact Integrable.fintype_prod fun k => integrable_chiSquareInverseFactor i k
  apply hprod.congr
  exact Filter.Eventually.of_forall fun s => (positiveReciprocal_mul_density_eq_prod i s).symm

private theorem integral_chiSquareInverseFactor {d : ℕ} (i k : Fin d) :
    ∫ s : ℝ, chiSquareInverseFactor i k s ∂((volume : Measure ℝ).restrict (Ioi 0)) = 1 := by
  by_cases hki : k = i
  · subst i
    calc
      (∫ s : ℝ, chiSquareInverseFactor k k s
          ∂((volume : Measure ℝ).restrict (Ioi 0))) =
          ∫ s in Ioi (0 : ℝ), s⁻¹ * chiSquareThreeDensity s := by
        exact setIntegral_congr_fun measurableSet_Ioi fun s hs => by
          simp [chiSquareInverseFactor, positiveReciprocal_of_pos hs]
      _ = 1 := integral_inv_mul_chiSquareThreeDensity
  · simp [chiSquareInverseFactor, hki, integral_chiSquareThreeDensity]

/-- Every coordinate has exact inverse-precision mean one under the product law. -/
@[simp]
theorem integral_positiveReciprocal_mul_chiSquareThreeProductDensity
    {d : ℕ} (i : Fin d) :
    ∫ s : Fin d → ℝ,
      positiveReciprocal (s i) * chiSquareThreeProductDensity d s
        ∂(chiSquareThreeProductVolume d) = 1 := by
  rw [show (fun s : Fin d → ℝ =>
      positiveReciprocal (s i) * chiSquareThreeProductDensity d s) =
      fun s => ∏ k, chiSquareInverseFactor i k (s k) by
    funext s
    exact positiveReciprocal_mul_density_eq_prod i s]
  unfold chiSquareThreeProductVolume
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one fun k _ => integral_chiSquareInverseFactor i k

theorem integrable_weighted_inversePrecisionQuadratic {d : ℕ} (u : Fin d → ℝ) :
    Integrable (fun s : Fin d → ℝ =>
      chiSquareThreeProductDensity d s * inversePrecisionQuadratic u s)
      (chiSquareThreeProductVolume d) := by
  have hterm : ∀ i : Fin d, Integrable
      (fun s : Fin d → ℝ => (u i ^ (2 : ℕ)) *
        (positiveReciprocal (s i) * chiSquareThreeProductDensity d s))
      (chiSquareThreeProductVolume d) := fun i =>
        (integrable_positiveReciprocal_mul_chiSquareThreeProductDensity i).const_mul _
  have hsum := integrable_finsetSum Finset.univ fun i _ => hterm i
  apply hsum.congr
  exact Filter.Eventually.of_forall fun s => by
    unfold inversePrecisionQuadratic
    change (∑ i, (u i ^ (2 : ℕ)) *
      (positiveReciprocal (s i) * chiSquareThreeProductDensity d s)) =
      chiSquareThreeProductDensity d s *
        ∑ i, u i ^ (2 : ℕ) * positiveReciprocal (s i)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Exact mean conditional variance: independent chi-square-three mixing
preserves the Euclidean coefficient energy. -/
@[simp]
theorem integral_weighted_inversePrecisionQuadratic {d : ℕ} (u : Fin d → ℝ) :
    ∫ s : Fin d → ℝ,
      chiSquareThreeProductDensity d s * inversePrecisionQuadratic u s
        ∂(chiSquareThreeProductVolume d) = ∑ i, u i ^ (2 : ℕ) := by
  have hterm : ∀ i : Fin d, Integrable
      (fun s : Fin d → ℝ => (u i ^ (2 : ℕ)) *
        (positiveReciprocal (s i) * chiSquareThreeProductDensity d s))
      (chiSquareThreeProductVolume d) := fun i =>
        (integrable_positiveReciprocal_mul_chiSquareThreeProductDensity i).const_mul _
  rw [show (fun s : Fin d → ℝ =>
      chiSquareThreeProductDensity d s * inversePrecisionQuadratic u s) =
      fun s => ∑ i, (u i ^ (2 : ℕ)) *
        (positiveReciprocal (s i) * chiSquareThreeProductDensity d s) by
    funext s
    unfold inversePrecisionQuadratic
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [integral_finsetSum Finset.univ (fun i _ => hterm i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,
    integral_positiveReciprocal_mul_chiSquareThreeProductDensity, mul_one]

/-- Paper's Jensen step: average conditional standard deviation is at most
the Euclidean norm of the coefficient vector. -/
theorem integral_sqrt_inversePrecisionQuadratic_le {d : ℕ} (u : Fin d → ℝ) :
    (∫ s : Fin d → ℝ,
      chiSquareThreeProductDensity d s * Real.sqrt (inversePrecisionQuadratic u s)
        ∂(chiSquareThreeProductVolume d)) ≤ Real.sqrt (∑ i, u i ^ (2 : ℕ)) := by
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_weighted_le
    (μ := chiSquareThreeProductVolume d)
    (w := chiSquareThreeProductDensity d)
    (g := fun s => Real.sqrt (inversePrecisionQuadratic u s))
    (chiSquareThreeProductDensity_nonneg d)
    (continuous_chiSquareThreeProductDensity d).aestronglyMeasurable
    (Real.continuous_sqrt.measurable.comp
      (measurable_inversePrecisionQuadratic u)).aestronglyMeasurable
    (integrable_chiSquareThreeProductDensity d)
    (by
      convert integrable_weighted_inversePrecisionQuadratic u using 1
      funext s
      rw [Real.sq_sqrt (inversePrecisionQuadratic_nonneg u s)])
  have hsqrtSq : (fun s : Fin d → ℝ =>
      chiSquareThreeProductDensity d s * Real.sqrt (inversePrecisionQuadratic u s) ^ (2 : ℕ)) =
      fun s => chiSquareThreeProductDensity d s * inversePrecisionQuadratic u s := by
    funext s
    rw [Real.sq_sqrt (inversePrecisionQuadratic_nonneg u s)]
  rw [integral_chiSquareThreeProductDensity, hsqrtSq,
    integral_weighted_inversePrecisionQuadratic, one_mul] at hcs
  exact Real.le_sqrt_of_sq_le hcs

/-- Conditional absolute moment of the Gaussian linear form with variance
`inversePrecisionQuadratic u s`. -/
def conditionalGaussianAbsoluteMoment {d : ℕ} (u s : Fin d → ℝ) : ℝ :=
  ∫ z : ℝ,
    |Real.sqrt (inversePrecisionQuadratic u s) * z| *
      GaloisForLFunctions.HTGeometry.banaszczykStandardGaussianDensity z

/-- Exact conditional Gaussian absolute moment. -/
@[simp]
theorem conditionalGaussianAbsoluteMoment_eq {d : ℕ} (u s : Fin d → ℝ) :
    conditionalGaussianAbsoluteMoment u s =
      Real.sqrt (2 / Real.pi) * Real.sqrt (inversePrecisionQuadratic u s) := by
  unfold conditionalGaussianAbsoluteMoment
  rw [GaloisForLFunctions.HTGeometry.integral_abs_smul_banaszczykStandardGaussianDensity,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Sharp mixed Gaussian--chi-square estimate from Lemma 2.4.  Averaging the
exact conditional Gaussian moment contributes `sqrt (2 / pi)`, while the
chi-square Jensen step contributes no further loss. -/
theorem integral_conditionalGaussianAbsoluteMoment_le {d : ℕ} (u : Fin d → ℝ) :
    (∫ s : Fin d → ℝ,
      chiSquareThreeProductDensity d s * conditionalGaussianAbsoluteMoment u s
        ∂(chiSquareThreeProductVolume d)) ≤
      Real.sqrt (2 / Real.pi) * Real.sqrt (∑ i, u i ^ (2 : ℕ)) := by
  rw [show (fun s : Fin d → ℝ =>
      chiSquareThreeProductDensity d s * conditionalGaussianAbsoluteMoment u s) =
      fun s => Real.sqrt (2 / Real.pi) *
        (chiSquareThreeProductDensity d s * Real.sqrt (inversePrecisionQuadratic u s)) by
    funext s
    rw [conditionalGaussianAbsoluteMoment_eq]
    ring]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_sqrt_inversePrecisionQuadratic_le u)
    (Real.sqrt_nonneg _)

end RHTower
