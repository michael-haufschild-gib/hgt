import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.HeightIndex

/-! # Relative partitions are uniformly sublinear in clock height at fixed rank -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Filter Topology

private theorem complexDrop_norm_le_two {r : ℕ} (b : SpectralBand r) (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    ‖complexDrop b n z‖ ≤ 2 := by
  have h := norm_sub_le ((occupationWeight n:ℂ)^z) (((b n).val:ℂ)^z)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (occupationWeight_pos n),Complex.norm_cpow_eq_rpow_re_of_pos (band_pos b n)] at h
  exact h.trans ((add_le_add (Real.rpow_le_one (occupation_in_unit n).1 (occupation_in_unit n).2 hz.le)
    (Real.rpow_le_one (band_in_unit b n).1 (band_in_unit b n).2 hz.le)).trans_eq (by norm_num))

private theorem complex_partition_tail {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    ‖∑' k, complexDrop b (k+N) z‖ ≤ (‖z‖/z.re)*((r:ℝ)*occupationWeight N^z.re) := by
  let β : GibbsExponent := ⟨z.re,hz⟩
  let f := powerResponse β
  have he : (∑' k, spectralDrop f (coldEdge r) (k+N)) = tailCeiling f r N := by
    calc
      _ = detectorTail f (hotEdge r) (coldEdge r) N := by
        apply tsum_congr
        intro k
        exact (abs_of_nonneg (drop_nonneg f (coldEdge r) (k+N))).symm
      _ = _ := detectorTail_edges f r N
  have hnorm := ((summable_nat_add_iff N).mpr (summable_complexDrop b hz)).norm
  have hcost := ((summable_nat_add_iff N).mpr (summable_spectralDrop f (coldEdge r))).mul_left (‖z‖/z.re)
  have hK := div_nonneg (norm_nonneg z) hz.le
  refine (norm_tsum_le_tsum_norm hnorm).trans ?_
  calc
    _ ≤ ∑' k, (‖z‖/z.re)*spectralDrop f (coldEdge r) (k+N) := hnorm.tsum_le_tsum
      (fun k => (complexDrop_bound b (k+N) β (z := z) le_rfl).trans (mul_le_mul_of_nonneg_left (drop_le_edge f b _) hK)) hcost
    _ = (‖z‖/z.re)*tailCeiling f r N := by rw [tsum_mul_left,he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (power_tailCeiling_le β r N) hK

/-- A finite prefix costs at most two per level; the remaining clock-dependent term is arbitrarily small relative to the clock height. -/
theorem clock_partition_head_tail {r : ℕ} (b : SpectralBand r) {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    ‖relativePartition b z‖ ≤ 2*(N:ℝ)+(‖z‖/z.re)*((r:ℝ)*occupationWeight N^z.re) := by
  have he := (summable_complexDrop b hz).sum_add_tsum_nat_add N
  change _ = relativePartition b z at he
  rw [← he]
  apply (norm_add_le _ _).trans (add_le_add _ (complex_partition_tail b hz N))
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ range N, (2:ℝ) := sum_le_sum (fun k _ => complexDrop_norm_le_two b k hz)
    _ = _ := by simp [mul_comm]

/-- Sublinearity holds uniformly over all interlacing spectra of each fixed missing rank. -/
theorem uniform_sublinear_clock (r : ℕ) {σ : ℝ} (hσ : 0 < σ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ b : SpectralBand r, ‖relativePartition b (⟨σ,t⟩:ℂ)‖ ≤ ε*t := by
  let A := (σ+1)/σ*(r:ℝ)
  have htail : Tendsto (fun n => A*occupationWeight n^σ) atTop (𝓝 0) := by
    have he := (((Real.continuous_rpow_const hσ.le).tendsto 0).comp occupationWeight_tendsto).const_mul A
    simpa only [Function.comp_def,Real.zero_rpow hσ.ne',mul_zero] using he
  obtain ⟨N,hN⟩ := (htail.eventually_lt_const (half_pos hε)).exists
  have hprefix : Tendsto (fun t : ℝ => (2*(N:ℝ))/t) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_ge_atTop (1:ℝ),hprefix.eventually_lt_const (half_pos hε)] with t ht hhead
  intro b
  let z : ℂ := ⟨σ,t⟩
  have ht' := zero_lt_one.trans_le ht
  have hz : ‖z‖/σ ≤ (σ+1)/σ*t :=
    (div_le_div_of_nonneg_right (clock_height_norm_bounds hσ ht).2 hσ.le).trans_eq (by ring)
  have hu := mul_le_mul_of_nonneg_right hz (mul_nonneg (Nat.cast_nonneg r) (Real.rpow_nonneg (occupationWeight_pos N).le σ))
  have he := clock_partition_head_tail b (z := z) hσ N
  have hhead' := (div_lt_iff₀ ht').mp hhead
  have htail' := mul_le_mul_of_nonneg_right hN.le ht'.le
  change ((σ+1)/σ*(r:ℝ)*occupationWeight N^σ)*t ≤ _ at htail'
  change _ ≤ 2*(N:ℝ)+‖z‖/σ*((r:ℝ)*occupationWeight N^σ) at he
  calc
    _ ≤ 2*(N:ℝ)+‖z‖/σ*((r:ℝ)*occupationWeight N^σ) := he
    _ ≤ 2*(N:ℝ)+((σ+1)/σ*t)*((r:ℝ)*occupationWeight N^σ) := add_le_add le_rfl hu
    _ = 2*(N:ℝ)+((σ+1)/σ*(r:ℝ)*occupationWeight N^σ)*t := by ring
    _ ≤ (ε/2)*t+(ε/2)*t := add_le_add hhead'.le htail'
    _ = _ := by ring

#print axioms clock_partition_head_tail
#print axioms uniform_sublinear_clock

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
