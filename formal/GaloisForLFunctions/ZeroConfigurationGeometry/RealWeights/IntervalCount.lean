import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic


/-!
# Interval counts under convolution

A nonnegative integrable kernel preserves an interval mass bound with its
exact density coefficient. Reflection of each translated interval turns
the finite sum of integrals into a pointwise interval count.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- Interval mass bounds survive convolution by a nonnegative integrable kernel,
with no loss in the density coefficient. -/
theorem finite_interval_convolution_le_of_count {α : Type*}
    (s : Finset α) (t w : α → ℝ) {K : ℝ → ℝ}
    (hKi : Integrable K) (hK : ∀ v, 0 ≤ K v) {D C l r : ℝ} (hlr : l ≤ r)
    (hcount : ∀ x y : ℝ, x ≤ y → ∀ p : Finset α, p ⊆ s →
      (∀ z ∈ p, t z ∈ Icc x y) → (∑ z ∈ p, w z) ≤ D * (y - x) + C) :
    (∑ z ∈ s, w z * ∫ u in l..r, K (t z - u)) ≤
      (D * (r - l) + C) * ∫ v, K v := by
  classical
  let F : α → ℝ → ℝ := fun z =>
    (Icc (t z - r) (t z - l)).indicator (fun v => w z * K v)
  have hFi (z : α) : Integrable (F z) :=
    (hKi.const_mul (w z)).indicator measurableSet_Icc
  have hFt (z : α) : (∫ v, F z v) = w z * ∫ u in l..r, K (t z - u) := by
    rw [intervalIntegral.integral_comp_sub_left]
    rw [show F z = (Icc (t z - r) (t z - l)).indicator (fun v => w z * K v) from rfl,
      integral_indicator measurableSet_Icc, integral_const_mul,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith only [hlr])]
  have hpoint (v : ℝ) : (∑ z ∈ s, F z v) ≤ (D * (r - l) + C) * K v := by
    let p := s.filter fun z => t z ∈ Icc (l + v) (r + v)
    have hc := hcount (l + v) (r + v) (by linarith only [hlr]) p
      (Finset.filter_subset _ _) (fun z hz => (Finset.mem_filter.mp hz).2)
    have he : (∑ z ∈ s, F z v) = (∑ z ∈ p, w z) * K v := by
      rw [Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro z hz
      have hm : v ∈ Icc (t z - r) (t z - l) ↔ t z ∈ Icc (l + v) (r + v) := by
        constructor <;> intro hh <;> constructor <;> linarith only [hh.1, hh.2]
      simp only [F, Set.indicator_apply, hm]
    rw [he]
    have hh := mul_le_mul_of_nonneg_right hc (hK v)
    rw [show r + v - (l + v) = r - l by ring] at hh
    exact hh
  calc
    _ = ∫ v, ∑ z ∈ s, F z v := by
      rw [integral_finsetSum s (fun z _ => hFi z)]
      apply Finset.sum_congr rfl
      intro z _
      exact (hFt z).symm
    _ ≤ ∫ v, (D * (r - l) + C) * K v :=
      integral_mono (integrable_finsetSum s (fun z _ => hFi z))
        (hKi.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.finite_interval_convolution_le_of_count
