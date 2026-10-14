import GaloisForLFunctions.HTGeometry.HarmonicResidueTransfer

/-! # Fixed shifts of logarithmic residues -/

namespace GaloisForLFunctions
noncomputable section
open Filter
open scoped Topology

theorem tendsto_log_nat_add_div_log_nat_add (k l : ℕ) :
    Tendsto (fun n : ℕ => Real.log (n + k : ℝ) / Real.log (n + l : ℝ))
      atTop (𝓝 1) := by
  have hk := (Real.tendsto_log_comp_add_sub_log (k : ℝ)).comp tendsto_natCast_atTop_atTop
  have hl := (Real.tendsto_log_comp_add_sub_log (l : ℝ)).comp tendsto_natCast_atTop_atTop
  have htop : Tendsto (fun n : ℕ => Real.log (n + l : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (l : ℝ))))
  have hd := (hk.sub hl).div_atTop htop
  have h := hd.add_const 1
  simp only [zero_add] at h
  refine h.congr' ?_
  filter_upwards [htop.eventually_gt_atTop 0] with n hn
  simp only [Function.comp_def]
  field_simp
  ring

theorem tendsto_logResidue_succ_of_mul_succ_tendsto {a : ℕ → ℝ} {R : ℝ}
    (ha : Tendsto (fun n : ℕ => a n * (n + 1 : ℝ)) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / Real.log (N + 1))
      atTop (𝓝 R) := by
  have h := (tendsto_logResidue_of_mul_succ_tendsto ha).mul
    (tendsto_log_nat_add_div_log_nat_add 0 1)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  simp only [Nat.cast_zero, Nat.cast_one, add_zero]
  field_simp

theorem tendsto_logResidue_shift {a : ℕ → ℝ} {R : ℝ}
    (ha : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a n) / Real.log (N + 1))
      atTop (𝓝 R)) (k : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, a (n + k)) / Real.log (N + 1))
      atTop (𝓝 R) := by
  have h := (ha.comp (tendsto_add_atTop_nat k)).mul
    (tendsto_log_nat_add_div_log_nat_add (k + 1) 1)
  have htop : Tendsto (fun N : ℕ => Real.log (N + 1 : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hh : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range k, a n) / Real.log (N + 1))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop htop
  have ht := h.sub hh
  simp only [mul_one, sub_zero] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : Real.log ((N + k : ℕ) + 1 : ℝ) ≠ 0 :=
    (Real.log_pos (by push_cast; nlinarith [show (2 : ℝ) ≤ N by exact_mod_cast hN])).ne'
  have he : (∑ n ∈ Finset.range (N + k), a n) =
      (∑ n ∈ Finset.range k, a n) + ∑ n ∈ Finset.range N, a (n + k) := by
    simpa only [Nat.add_comm] using Finset.sum_range_add a k N
  simp only [Function.comp_def, Nat.cast_add, Nat.cast_one] at hn ⊢
  rw [← add_assoc, div_mul_div_cancel₀ hn, he, add_div, add_sub_cancel_left]

end
end GaloisForLFunctions
