import GaloisForLFunctions.RHTower.WeilLogShiftFiniteCouplingCost

/-! Exact dual slack and pointwise support restrictions for finite optimal couplings. -/

open scoped BigOperators NNReal

namespace RHTower

theorem finiteWeilCoupling_ext {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma eta : HTGeometry.FiniteNNCoupling P Q)
    (h : ∀ u v, gamma.plan u v = eta.plan u v) : gamma = eta := by
  cases gamma with
  | mk g gr gc =>
    cases eta with
    | mk e er ec =>
      have he : g = e := funext (fun u => funext (fun v => h u v))
      cases he
      rfl

theorem finiteWeilCoupling_slack_sum {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (c : ι → ι → ℝ) (f : ι → ℝ) :
    (∑ u, ∑ v, (gamma.plan u v : ℝ) * (c u v - (f u - f v))) =
      finiteWeilCouplingCost gamma c -
        ((∑ u, (P u : ℝ) * f u) - (∑ v, (Q v : ℝ) * f v)) := by
  rw [finiteWeilCoupling_pairing gamma f]
  simp only [finiteWeilCouplingCost, mul_sub, Finset.sum_sub_distrib]

theorem finiteWeilCoupling_slack_zero {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (c : ι → ι → ℝ) (f : ι → ℝ)
    (hcf : ∀ u v, f u - f v ≤ c u v)
    (hopt : finiteWeilCouplingCost gamma c =
      (∑ u, (P u : ℝ) * f u) - (∑ v, (Q v : ℝ) * f v)) (u v : ι) :
    (gamma.plan u v : ℝ) * (c u v - (f u - f v)) = 0 := by
  have hn (a b : ι) : 0 ≤ (gamma.plan a b : ℝ) * (c a b - (f a - f b)) :=
    mul_nonneg (gamma.plan a b).coe_nonneg (sub_nonneg.mpr (hcf a b))
  have hz : (∑ a, ∑ b, (gamma.plan a b : ℝ) * (c a b - (f a - f b))) = 0 := by
    rw [finiteWeilCoupling_slack_sum, hopt, sub_self]
  have hr := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ => Finset.sum_nonneg (fun b _ => hn a b))).mp hz u (Finset.mem_univ u)
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hn u b)).mp hr v (Finset.mem_univ v)

theorem finiteWeilCoupling_zero_of_strict_dual {ι : Type*} [Fintype ι] {P Q : ι → ℝ≥0}
    (gamma : HTGeometry.FiniteNNCoupling P Q) (c : ι → ι → ℝ) (f : ι → ℝ)
    (hcf : ∀ u v, f u - f v ≤ c u v)
    (hopt : finiteWeilCouplingCost gamma c =
      (∑ u, (P u : ℝ) * f u) - (∑ v, (Q v : ℝ) * f v)) (u v : ι)
    (hstrict : f u - f v < c u v) : gamma.plan u v = 0 := by
  have hz := finiteWeilCoupling_slack_zero gamma c f hcf hopt u v
  have hc : c u v - (f u - f v) ≠ 0 := ne_of_gt (sub_pos.mpr hstrict)
  apply NNReal.coe_injective
  exact (mul_eq_zero.mp hz).resolve_right hc

end RHTower
