import GaloisForLFunctions.RHTower.ThetaCutoffCommutatorShell
import GaloisForLFunctions.RHTower.SteinhausEulerSecondMoment

open Filter Set
open scoped Topology

noncomputable section
namespace RHTower

/-- The exact rough density is the reciprocal of the critical Euler partition. -/
theorem steinhausEulerPartition_half_inv (P : Finset ℕ) :
    (steinhausEulerPartition P (1 / 2))⁻¹ = ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
  rw [steinhausEulerPartition_half, ← Finset.prod_inv_distrib]
  simp only [inv_inv]

/-- Finite-prime discrepancy controls the normalized coefficient uniformly in the pair scale. -/
theorem abs_roughCount_scaled_sub_steinhausEulerPartition_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    |(roughCount P (x / d) : ℝ) / x - (steinhausEulerPartition P (1 / 2))⁻¹ / d| ≤
      (P.powerset.card : ℝ) / x := by
  have h := abs_roughDiscrepancy_le P (x / d)
  rw [roughDiscrepancy_eq P hP (div_pos hx hd).le] at h
  have heq : (roughCount P (x / d) : ℝ) / x - (steinhausEulerPartition P (1 / 2))⁻¹ / d =
      -((x / d) * ∏ p ∈ P, (1 - (p : ℝ)⁻¹) - roughCount P (x / d)) / x := by
    rw [steinhausEulerPartition_half_inv]
    field_simp
    ring
  rw [heq, abs_div, abs_neg, abs_of_pos hx]
  exact div_le_div_of_nonneg_right h hx.le

/-- The actual rough coefficient is dominated by the reciprocal pair scale. -/
theorem roughCount_scaled_div_le (P : Finset ℕ) {x d : ℝ} (hx : 0 < x) (hd : 0 < d) :
    (roughCount P (x / d) : ℝ) / x ≤ 1 / d := by
  have hcount : roughCount P (x / d) ≤ ⌊x / d⌋₊ := by
    unfold roughCount
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hbound : (roughCount P (x / d) : ℝ) ≤ x / d :=
    (Nat.cast_le.mpr hcount).trans (Nat.floor_le (div_pos hx hd).le)
  calc
    _ ≤ (x / d) / x := div_le_div_of_nonneg_right hbound hx.le
    _ = 1 / d := by field_simp

/-- The pair coefficient has its exact inverse-partition limit for each fixed finite prefix. -/
theorem tendsto_roughCount_scaled_div (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun x : ℝ => (roughCount P (x / d) : ℝ) / x) atTop
      (𝓝 ((steinhausEulerPartition P (1 / 2))⁻¹ / d)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hlim : Tendsto (fun x : ℝ => (P.powerset.card : ℝ) / x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((hlim.eventually (gt_mem_nhds hε)).and (eventually_gt_atTop (0 : ℝ)))
  refine ⟨X, fun x hx => ?_⟩
  rw [Real.dist_eq]
  exact (abs_roughCount_scaled_sub_steinhausEulerPartition_le P hP (hX x hx).2 hd).trans_lt
    (hX x hx).1

theorem tendsto_roughCount_nat_scaled_div (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {d : ℝ} (hd : 0 < d) :
    Tendsto (fun N : ℕ => (roughCount P ((N : ℝ) / d) : ℝ) / N) atTop
      (𝓝 ((steinhausEulerPartition P (1 / 2))⁻¹ / d)) :=
  (tendsto_roughCount_scaled_div P hP hd).comp tendsto_natCast_atTop_atTop

/-- The literal smooth-pair maximum kernel required by conditional second moments. -/
theorem tendsto_roughCount_smoothPair_div (y : ℕ) (a b : y.smoothNumbers) :
    Tendsto (fun N : ℕ =>
      (roughCount (Nat.primesBelow y) ((N : ℝ) / (max (a : ℕ) (b : ℕ) : ℕ)) : ℝ) / N)
      atTop (𝓝 ((steinhausEulerPartition (Nat.primesBelow y) (1 / 2))⁻¹ /
        (max (a : ℕ) (b : ℕ) : ℕ))) := by
  apply tendsto_roughCount_nat_scaled_div _ (fun _ hp => (Nat.mem_primesBelow.mp hp).2)
  exact_mod_cast (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers a.property)).trans_le
    (le_max_left (a : ℕ) (b : ℕ))

end RHTower
