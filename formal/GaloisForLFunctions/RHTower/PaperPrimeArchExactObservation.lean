import GaloisForLFunctions.RHTower.PaperPrimeArchCurrentCutoff
import GaloisForLFunctions.HTGeometry.L2PhysicalMultiplierObservation
import GaloisForLFunctions.HTGeometry.LpDisjointEnergy

/-! # Exact physical observations of the prime–Gamma source

The original input maximizes the full, retained and discarded multiplier
responses. Their energies split exactly. Cutoff recovery is uniform across
all admitted source heights and all inputs dominated by one fixed history.
-/

namespace RHTower.PaperPrimeArch
noncomputable section
open Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal

def cutoffDefect (a : Height) (R : ℝ≥0) : Space →L[ℂ] Space := operator a - cutoffOperator a R

theorem cutoffDefect_apply_ae (a : Height) (R : ℝ≥0) (f : Space) :
    (cutoffDefect a R f : ℝ → ℂ) =ᵐ[volume]
      fun t => ((current a t : ℂ) - cutoffSymbol a R t) * f t := by
  filter_upwards [Lp.coeFn_sub (operator a f) (cutoffOperator a R f),
    operator_apply_ae a f, cutoffOperator_apply_ae a R f] with t hsub hA hC
  change (operator a f - cutoffOperator a R f : Space) t = _
  rw [hsub, Pi.sub_apply, hA, hC, sub_mul]

theorem operator_physicalObservation (a : Height) (x : Space) :
    l2PhysicalObservation (operator a) x = ‖operator a x‖ :=
  l2PhysicalObservation_eq_norm_of_ae_mul _ _ (operator_apply_ae a) x

theorem cutoffOperator_physicalObservation (a : Height) (R : ℝ≥0) (x : Space) :
    l2PhysicalObservation (cutoffOperator a R) x = ‖cutoffOperator a R x‖ :=
  l2PhysicalObservation_eq_norm_of_ae_mul _ _ (cutoffOperator_apply_ae a R) x

theorem cutoffDefect_physicalObservation (a : Height) (R : ℝ≥0) (x : Space) :
    l2PhysicalObservation (cutoffDefect a R) x = ‖cutoffDefect a R x‖ :=
  l2PhysicalObservation_eq_norm_of_ae_mul _ _ (cutoffDefect_apply_ae a R) x

theorem cutoff_physicalObservation_energy_split (a : Height) (R : ℝ≥0) (x : Space) :
    l2PhysicalObservation (cutoffOperator a R) x ^ 2 +
      l2PhysicalObservation (cutoffDefect a R) x ^ 2 = l2PhysicalObservation (operator a) x ^ 2 := by
  rw [cutoffOperator_physicalObservation, cutoffDefect_physicalObservation, operator_physicalObservation]
  have hd : ∀ᵐ t ∂volume, cutoffOperator a R x t = 0 ∨ cutoffDefect a R x t = 0 := by
    filter_upwards [cutoffOperator_apply_ae a R x, cutoffDefect_apply_ae a R x] with t hC hD
    by_cases ht : t ∈ Set.Icc (-(R : ℝ)) R
    · right
      rw [hD]
      simp only [cutoffSymbol, Set.indicator_of_mem ht, sub_self, zero_mul]
    · left
      rw [hC]
      simp only [cutoffSymbol, Set.indicator_of_notMem ht, zero_mul]
  have h := l2_norm_sq_add_of_ae_disjoint (cutoffOperator a R x) (cutoffDefect a R x) hd
  have he : cutoffOperator a R x + cutoffDefect a R x = operator a x := by
    simp only [cutoffDefect, sub_apply]
    abel
  simpa only [he] using h

theorem cutoffDefect_physicalObservation_le (a : Height) (R : ℝ≥0) (x : Space) :
    l2PhysicalObservation (cutoffDefect a R) x ≤
      (decayBudget * Real.exp (-(Real.pi / 4 * (R : ℝ)))) * ‖x‖ := by
  rw [cutoffDefect_physicalObservation]
  exact ((cutoffDefect a R).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (norm_operator_sub_cutoff_le a R) (norm_nonneg x))

theorem cutoffDefect_uniform_all_heights :
    TendstoUniformly (fun (n : ℕ) a => cutoffDefect a n) (fun _ => 0) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [cutoff_error_tendsto.eventually_lt_const hε] with n hn
  intro a
  rw [dist_zero_left]
  have hb : ‖cutoffDefect a n‖ ≤ decayBudget * Real.exp (-(Real.pi / 4 * (n : ℝ))) := by
    simpa only [cutoffDefect, NNReal.coe_natCast] using norm_operator_sub_cutoff_le a n
  exact hb.trans_lt hn

theorem cutoffObservation_uniform_all_heights (x : Space) :
    TendstoUniformly (fun (n : ℕ) a => l2PhysicalObservation (cutoffDefect a n) x)
      (fun _ => 0) atTop := by
  have h : Tendsto (fun n : ℕ =>
      (decayBudget * Real.exp (-(Real.pi / 4 * (n : ℝ)))) * ‖x‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using cutoff_error_tendsto.mul_const ‖x‖
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [h.eventually_lt_const hε] with n hn
  intro a
  rw [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg (l2PhysicalObservation_nonneg _ _)]
  have hb : l2PhysicalObservation (cutoffDefect a n) x ≤
      (decayBudget * Real.exp (-(Real.pi / 4 * (n : ℝ)))) * ‖x‖ := by
    simpa only [NNReal.coe_natCast] using cutoffDefect_physicalObservation_le a n x
  exact hb.trans_lt hn

theorem cutoffDefect_uniform_all_physical_histories (x : Space) :
    TendstoUniformlyOn (fun (n : ℕ) (q : Height × Space) => cutoffDefect q.1 n q.2)
      (fun _ => 0) atTop {q | q.2 ∈ l2PhysicalSolidHull x} := by
  have h := Metric.tendstoUniformly_iff.mp (cutoffObservation_uniform_all_heights x)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h ε hε] with n hn
  intro q hq
  rw [dist_zero_left]
  apply (norm_apply_le_l2PhysicalObservation (cutoffDefect q.1 n) hq).trans_lt
  simpa only [dist_zero_left, Real.norm_eq_abs,
    abs_of_nonneg (l2PhysicalObservation_nonneg (cutoffDefect q.1 n) x)] using hn q.1

theorem cutoffDefect_uniform_physicalHull_iff {A : Type*} (l : Filter A)
    (a : A → Height) (R : A → ℝ≥0) (x : Space) :
    TendstoUniformlyOn (fun i y => cutoffDefect (a i) (R i) y) (fun _ => 0) l (l2PhysicalSolidHull x) ↔
      Tendsto (fun i => cutoffDefect (a i) (R i) x) l (𝓝 0) :=
  tendstoUniformlyOn_l2PhysicalSolidHull_ae_mul_iff _ _ (fun i => cutoffDefect_apply_ae (a i) (R i)) x

end
end RHTower.PaperPrimeArch
