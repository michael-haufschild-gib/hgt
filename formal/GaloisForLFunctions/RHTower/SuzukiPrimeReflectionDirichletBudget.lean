import GaloisForLFunctions.RHTower.SuzukiPrimeSeamHankelStrength
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# The prime-reflection Dirichlet budget and log-ratio rigidity

Summing the reflection defects of a weighted family of involutions gives the exact identity

`D(f) = 2W‖f‖² - 2P(f,f)`,

so the whole prime form is the total weight minus half the Dirichlet budget: a negative-edge
witness spends prime mass, and the amount it does not spend is exactly what remains for reflection
rigidity.

Two reflections compose to a translation, and the composite defect obeys

`‖f - R_m R_n f‖² ≤ 2(‖f - R_m f‖² + ‖f - R_n f‖²)`,

because `f - R_m R_n f = (f - R_m f) + R_m(f - R_n f)` and `R_m` is an isometry.  Averaging over the
weight pair therefore bounds the total translation defect by `4W D(f)`, and Chebyshev converts that
into a proportion bound: outside a set of pairs of small normalized weight, every log-ratio
translation moves `f` by less than `ε‖f‖`.
-/

open Finset

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*} [Fintype ι]

/-- The weighted reflection defect of a vector. -/
def reflectionDirichlet (w : ι → ℝ) (R : ι → H → H) (f : H) : ℝ :=
  ∑ i, w i * ‖f - R i f‖ ^ 2

/-- The weighted reflection form. -/
def reflectionForm (w : ι → ℝ) (R : ι → H → H) (f : H) : ℝ :=
  ∑ i, w i * inner ℝ f (R i f)

/-- **`(269)`: the Dirichlet budget is the total weight minus the reflection form.** -/
theorem reflectionDirichlet_eq {w : ι → ℝ} {R : ι → H → H}
    (hiso : ∀ i x, ‖R i x‖ = ‖x‖) (f : H) :
    reflectionDirichlet w R f
      = 2 * (∑ i, w i) * ‖f‖ ^ 2 - 2 * reflectionForm w R f := by
  have hterm : ∀ i : ι, w i * ‖f - R i f‖ ^ 2
      = 2 * w i * ‖f‖ ^ 2 - 2 * (w i * inner ℝ f (R i f)) := by
    intro i
    rw [norm_sub_sq_real f (R i f), hiso i f]
    ring
  rw [reflectionDirichlet, reflectionForm, Finset.sum_congr rfl (fun i _ => hterm i),
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_mul, ← Finset.mul_sum]

omit [InnerProductSpace ℝ H] in
/-- **`(271)`: the composite reflection defect is controlled by the two single defects.** -/
theorem norm_sub_comp_sq_le {Rm Rn : H → H}
    (hiso : ∀ x, ‖Rm x‖ = ‖x‖) (hlin : ∀ x y, Rm (x - y) = Rm x - Rm y) (f : H) :
    ‖f - Rm (Rn f)‖ ^ 2 ≤ 2 * (‖f - Rm f‖ ^ 2 + ‖f - Rn f‖ ^ 2) := by
  have hsplit : f - Rm (Rn f) = (f - Rm f) + Rm (f - Rn f) := by
    rw [hlin f (Rn f)]
    abel
  have htri : ‖f - Rm (Rn f)‖ ≤ ‖f - Rm f‖ + ‖f - Rn f‖ := by
    rw [hsplit]
    calc ‖(f - Rm f) + Rm (f - Rn f)‖ ≤ ‖f - Rm f‖ + ‖Rm (f - Rn f)‖ := norm_add_le _ _
      _ = ‖f - Rm f‖ + ‖f - Rn f‖ := by rw [hiso]
  have h0 : (0 : ℝ) ≤ ‖f - Rm (Rn f)‖ := norm_nonneg _
  nlinarith [htri, h0, norm_nonneg (f - Rm f), norm_nonneg (f - Rn f),
    sq_nonneg (‖f - Rm f‖ - ‖f - Rn f‖)]

omit [InnerProductSpace ℝ H] in
/-- **`(272)`: the total translation defect is four times the weight times the budget.** -/
theorem sum_comp_defect_le {w : ι → ℝ} {R : ι → H → H}
    (hw : ∀ i, 0 ≤ w i)
    (hiso : ∀ i x, ‖R i x‖ = ‖x‖)
    (hlin : ∀ i x y, R i (x - y) = R i x - R i y) (f : H) :
    ∑ p : ι × ι, w p.1 * w p.2 * ‖f - R p.1 (R p.2 f)‖ ^ 2
      ≤ 4 * (∑ i, w i) * reflectionDirichlet w R f := by
  have hterm : ∀ p : ι × ι, w p.1 * w p.2 * ‖f - R p.1 (R p.2 f)‖ ^ 2
      ≤ w p.1 * w p.2 * (2 * (‖f - R p.1 f‖ ^ 2 + ‖f - R p.2 f‖ ^ 2)) := by
    intro p
    exact mul_le_mul_of_nonneg_left
      (norm_sub_comp_sq_le (hiso p.1) (hlin p.1) f)
      (mul_nonneg (hw p.1) (hw p.2))
  calc ∑ p : ι × ι, w p.1 * w p.2 * ‖f - R p.1 (R p.2 f)‖ ^ 2
      ≤ ∑ p : ι × ι, w p.1 * w p.2 * (2 * (‖f - R p.1 f‖ ^ 2 + ‖f - R p.2 f‖ ^ 2)) :=
        Finset.sum_le_sum fun p _ => hterm p
    _ = 4 * (∑ i, w i) * reflectionDirichlet w R f := by
        rw [reflectionDirichlet, Fintype.sum_prod_type]
        dsimp only
        have key : ∀ i : ι, (∑ j : ι, w i * w j * (2 * (‖f - R i f‖ ^ 2 + ‖f - R j f‖ ^ 2)))
            = 2 * (w i * ‖f - R i f‖ ^ 2) * (∑ j, w j)
              + 2 * w i * (∑ j, w j * ‖f - R j f‖ ^ 2) := by
          intro i
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.mul_sum]
        have hpull : (∑ x : ι, 2 * w x * (∑ j, w j * ‖f - R j f‖ ^ 2))
            = 2 * (∑ x : ι, w x) * (∑ j, w j * ‖f - R j f‖ ^ 2) := by
          rw [← Finset.sum_mul]
          congr 1
          rw [← Finset.mul_sum]
        rw [hpull]
        ring

omit [InnerProductSpace ℝ H] in
/-- **Chebyshev's proportion bound.**  Weighted pairs on which the translation defect is large
carry small normalized weight. -/
theorem weight_of_large_defect_le {w : ι → ℝ} {R : ι → H → H} {ε W D : ℝ} (f : H)
    (hw : ∀ i, 0 ≤ w i) (hε : 0 < ε)
    (hbudget : ∑ p : ι × ι, w p.1 * w p.2 * ‖f - R p.1 (R p.2 f)‖ ^ 2 ≤ 4 * W * D)
    (S : Finset (ι × ι))
    (hS : ∀ p ∈ S, ε * ‖f‖ < ‖f - R p.1 (R p.2 f)‖) :
    (∑ p ∈ S, w p.1 * w p.2) * (ε ^ 2 * ‖f‖ ^ 2) ≤ 4 * W * D := by
  have hlow : ∀ p ∈ S, w p.1 * w p.2 * (ε ^ 2 * ‖f‖ ^ 2)
      ≤ w p.1 * w p.2 * ‖f - R p.1 (R p.2 f)‖ ^ 2 := by
    intro p hp
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (hw p.1) (hw p.2))
    have h := hS p hp
    have h0 : (0 : ℝ) ≤ ε * ‖f‖ := by positivity
    nlinarith [h, h0]
  have hsubset : ∑ p ∈ S, w p.1 * w p.2 * ‖f - R p.1 (R p.2 f)‖ ^ 2
      ≤ ∑ p : ι × ι, w p.1 * w p.2 * ‖f - R p.1 (R p.2 f)‖ ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) fun p _ _ => by
      have := hw p.1
      have := hw p.2
      positivity
  calc (∑ p ∈ S, w p.1 * w p.2) * (ε ^ 2 * ‖f‖ ^ 2)
      = ∑ p ∈ S, w p.1 * w p.2 * (ε ^ 2 * ‖f‖ ^ 2) := by rw [Finset.sum_mul]
    _ ≤ ∑ p ∈ S, w p.1 * w p.2 * ‖f - R p.1 (R p.2 f)‖ ^ 2 := Finset.sum_le_sum hlow
    _ ≤ ∑ p : ι × ι, w p.1 * w p.2 * ‖f - R p.1 (R p.2 f)‖ ^ 2 := hsubset
    _ ≤ 4 * W * D := hbudget

end RHTower
