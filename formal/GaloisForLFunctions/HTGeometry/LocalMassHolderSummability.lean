import GaloisForLFunctions.HTGeometry.BoundedFiberMassHasSummablePowerTails
import Mathlib.Analysis.MeanInequalities

/-!
# Hölder summability with locally bounded mass

A uniform mass bound in height windows supplies the conjugate inverse-height
moment. Hölder then turns an `ℓᵖ` perturbation into a summable weighted error.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A summable positive power of the norm forces cofinite convergence to zero. -/
theorem tendsto_zero_of_summable_norm_rpow {ι E : Type*} [NormedAddCommGroup E]
    {f : ι → E} {p : ℝ} (hp : 0 < p) (hf : Summable (fun i => ‖f i‖ ^ p)) :
    Tendsto f cofinite (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall := hf.tendsto_cofinite_zero.eventually
    (gt_mem_nhds (Real.rpow_pos_of_pos hε p))
  filter_upwards [hsmall] with i hi
  rw [dist_zero_right]
  exact (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le hp).mp hi

/-- Increasing a positive exponent preserves summability of norm powers. -/
theorem summable_norm_rpow_of_le {ι E : Type*} [NormedAddCommGroup E]
    {f : ι → E} {p r : ℝ} (hp : 0 < p) (hpr : p ≤ r)
    (hf : Summable (fun i => ‖f i‖ ^ p)) : Summable (fun i => ‖f i‖ ^ r) := by
  have ht := (tendsto_zero_of_summable_norm_rpow hp hf).norm
  rw [norm_zero] at ht
  refine hf.of_norm_bounded_eventually ?_
  filter_upwards [ht.eventually (gt_mem_nhds zero_lt_one)] with i hi
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hi.le hp.le hpr

/-- Local mass control pairs an `ℓᵖ` family with height decay whenever the
decay exponent times the conjugate exponent exceeds one. -/
theorem summable_mass_mul_div_of_lp {ι : Type*} (t : ι → ℝ)
    {w a : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (ha : ∀ i, 0 ≤ a i)
    {L B : ℝ} (hL : 0 < L)
    (hlocal : ∀ x : ℝ, ∀ s : Finset ι,
      (∀ i ∈ s, x ≤ t i ∧ t i ≤ x + L) → ∑ i ∈ s, w i ≤ B)
    {p q α : ℝ} (hpq : p.HolderConjugate q) (hαq : 1 < α * q)
    (ha_sum : Summable (fun i => a i ^ p)) :
    Summable (fun i => w i * a i / (1 + |t i|) ^ α) := by
  classical
  have hwB : ∀ i, w i ≤ B := by
    intro i
    simpa only [Finset.sum_singleton] using hlocal (t i) {i} (by
      intro j hj
      have hj' : j = i := Finset.mem_singleton.mp hj
      subst j
      exact ⟨le_rfl, le_add_of_nonneg_right hL.le⟩)
  let K := max B 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hwK : ∀ i, w i ≤ K := fun i => (hwB i).trans (le_max_left _ _)
  have hq1 : 0 < q - 1 := hpq.symm.sub_one_pos
  have hwpow : ∀ i, w i ^ q ≤ K ^ (q - 1) * w i := by
    intro i
    rcases eq_or_lt_of_le (hw i) with hi | hi
    · rw [← hi, Real.zero_rpow hpq.symm.ne_zero, mul_zero]
    · calc w i ^ q = w i ^ (q - 1) * w i := by
             conv_lhs => rw [show q = (q - 1) + 1 by ring]
             rw [Real.rpow_add hi, Real.rpow_one]
           _ ≤ K ^ (q - 1) * w i := mul_le_mul_of_nonneg_right
             (Real.rpow_le_rpow (hw i) (hwK i) hq1.le) (hw i)
  have htail := summable_div_height_power_of_local_mass t hw hL hlocal hαq
  have hqsum : Summable (fun i => (w i / (1 + |t i|) ^ α) ^ q) := by
    refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (by positivity [hw i]) _) ?_
      (htail.mul_left (K ^ (q - 1)))
    intro i
    rw [Real.div_rpow (hw i) (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_mul (by positivity : 0 ≤ 1 + |t i|)]
    calc w i ^ q / (1 + |t i|) ^ (α * q) ≤
        (K ^ (q - 1) * w i) / (1 + |t i|) ^ (α * q) :=
          div_le_div_of_nonneg_right (hwpow i) (by positivity)
      _ = K ^ (q - 1) * (w i / (1 + |t i|) ^ (α * q)) := by ring
  exact (Real.summable_mul_of_Lp_Lq_of_nonneg hpq ha
    (fun i => by positivity [hw i]) ha_sum hqsum).congr fun i => by ring

end GaloisForLFunctions.HTGeometry
