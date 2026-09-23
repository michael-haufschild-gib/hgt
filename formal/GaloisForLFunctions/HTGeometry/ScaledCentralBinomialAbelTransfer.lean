import GaloisForLFunctions.HTGeometry.CentralBinomialAbelTransfer

open Filter Topology
open scoped BigOperators Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A sharp `B^(2n) / sqrt n` coefficient asymptotic gives the corresponding square-root Abel
boundary at the positive radius `B⁻²`. -/
theorem tendsto_sqrt_scaled_boundary_mul_tsum_of_halfOrder
    {a : ℕ → ℝ} {B L : ℝ} (hB : 0 < B)
    (h : Tendsto
      (fun n : ℕ => Real.sqrt n * a n / (B ^ (2 : ℕ)) ^ n)
      atTop (nhds L)) :
    Tendsto
      (fun t : ℝ => Real.sqrt (1 - B ^ (2 : ℕ) * t) * ∑' n : ℕ, a n * t ^ n)
      (nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ))))
      (nhds (Real.sqrt Real.pi * L)) := by
  let b : ℕ → ℝ := fun n => a n / (B ^ (2 : ℕ)) ^ n
  have hb : Tendsto (fun n : ℕ => Real.sqrt n * b n) atTop (nhds L) := by
    convert h using 1
    funext n
    dsimp only [b]
    ring
  have hab := tendsto_sqrt_one_sub_mul_tsum_of_sqrtNat_mul hb
  have hBsq : 0 < B ^ (2 : ℕ) := sq_pos_of_pos hB
  have hmap_nhds : Tendsto (fun t : ℝ => B ^ (2 : ℕ) * t)
      (nhds (1 / B ^ (2 : ℕ))) (nhds 1) := by
    have hc : ContinuousAt (fun t : ℝ => B ^ (2 : ℕ) * t) (1 / B ^ (2 : ℕ)) := by fun_prop
    change Tendsto (fun t : ℝ => B ^ (2 : ℕ) * t) (nhds (1 / B ^ (2 : ℕ)))
      (nhds (B ^ (2 : ℕ) * (1 / B ^ (2 : ℕ)))) at hc
    convert hc using 1
    field_simp [hBsq.ne']
  have hmap_mem : ∀ᶠ t : ℝ in nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ))),
      B ^ (2 : ℕ) * t ∈ Set.Ico (0 : ℝ) 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨mul_nonneg hBsq.le ht.1, by
      simpa only [mul_comm] using (lt_div_iff₀ hBsq).1 ht.2⟩
  have hmap : Tendsto (fun t : ℝ => B ^ (2 : ℕ) * t)
      (nhdsWithin (1 / B ^ (2 : ℕ)) (Set.Ico 0 (1 / B ^ (2 : ℕ))))
      (nhdsWithin 1 (Set.Ico 0 1)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hmap_nhds.mono_left inf_le_left) hmap_mem
  have hcomp := hab.comp hmap
  refine Tendsto.congr' ?_ hcomp
  filter_upwards with t
  change Real.sqrt (1 - B ^ (2 : ℕ) * t) *
      (∑' n : ℕ, b n * (B ^ (2 : ℕ) * t) ^ n) =
    Real.sqrt (1 - B ^ (2 : ℕ) * t) * ∑' n : ℕ, a n * t ^ n
  congr 1
  exact tsum_congr fun n => by
    dsimp only [b]
    rw [mul_pow]
    field_simp [pow_ne_zero n hBsq.ne']

end

end GaloisForLFunctions.HTGeometry

