import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.FiniteDiagonal
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.BlockMultiplier

/-! # Simultaneous complex readout of independently attenuated occupations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

private theorem finite_prefix (N : ℕ) {r : ℕ} (t : Fin r → Ioc (0:ℝ) 1) :
    ∃ M, N+r ≤ M ∧ ∀ i : Fin M, occupationWeight M ≤ retainedWeight N t i.val := by
  have h : ∀ᶠ M in atTop, ∀ j : Fin r, occupationWeight M < (t j).val * occupationWeight (N+j.val) :=
    eventually_all.mpr (fun j => occupationWeight_tendsto.eventually_lt_const
      (mul_pos (t j).property.1 (occupationWeight_pos _)))
  obtain ⟨M,hM,hm⟩ := ((eventually_ge_atTop (N+r)).and h).exists
  refine ⟨M,hM,fun i => ?_⟩
  by_cases hi : N ≤ i.val ∧ i.val < N+r
  · let j : Fin r := ⟨i.val-N,by omega⟩
    have hj : N+j.val = i.val := by dsimp only [j]; omega
    rw [← hj,retainedWeight_slot]
    exact (hm j).le
  · rw [retainedWeight_outside t hi]
    exact occupationWeight_antitone i.isLt.le

private theorem sum_prefix_block {N r M : ℕ} (hM : N+r ≤ M) (t : Fin r → Ioc (0:ℝ) 1) (z : ℂ) :
    (∑ k ∈ Finset.range M, ((occupationWeight k:ℂ)^z-(retainedWeight N t k:ℂ)^z)) =
      ∑ j : Fin r, ((occupationWeight (N+j.val):ℂ)^z-(((t j).val*occupationWeight (N+j.val):ℝ):ℂ)^z) := by
  let d (k : ℕ) := (occupationWeight k:ℂ)^z-(retainedWeight N t k:ℂ)^z
  have ho {k : ℕ} (h : ¬ (N ≤ k ∧ k < N+r)) : d k = 0 := by
    simp only [d,retainedWeight_outside t h,sub_self]
  have hr : (∑ k ∈ Finset.range (N+r), d k) = ∑ k ∈ Finset.range M, d k :=
    Finset.sum_subset (Finset.range_mono hM) (fun k _ hk => ho (fun h => hk (Finset.mem_range.mpr h.2)))
  have hp : (∑ k ∈ Finset.range N, d k) = 0 := Finset.sum_eq_zero (fun k hk =>
    ho (fun h => (Finset.mem_range.mp hk).not_ge h.1))
  change (∑ k ∈ Finset.range M, d k) = _
  rw [← hr,Finset.sum_range_add,hp,zero_add,← Fin.sum_univ_eq_sum_range]
  simp only [d,retainedWeight_slot]

/-- At unchanged missing rank, every prescribed positive attenuation of a finite block is visible at all complex temperatures at once. -/
theorem exists_attenuated_readout (N : ℕ) {r : ℕ} (t : Fin r → Ioc (0:ℝ) 1) :
    ∃ b ∈ closure (physicalSpectra r), ∀ {z : ℂ}, 0 < z.re →
      relativePartition b z = ∑ j : Fin r, ((occupationWeight (N+j.val):ℂ)^z-
        (((t j).val*occupationWeight (N+j.val):ℝ):ℂ)^z) := by
  obtain ⟨b,hb,he⟩ := spectral_limit_of_square_limit (attenuatedSquare_mem_closure N t)
  obtain ⟨M,hM,hmin⟩ := finite_prefix N t
  have ht (k : ℕ) (hk : M ≤ k) : retainedWeight N t k = occupationWeight k :=
    retainedWeight_outside t (fun h => (hM.trans hk).not_gt h.2)
  refine ⟨b,hb,fun {z} hz => ?_⟩
  exact (relativePartition_finite_diagonal _ _ (fun k => (retainedWeight_pos N t k).le)
    (attenuatedSquare_apply N t) ht hmin b he hz).trans (sum_prefix_block hM t z)

#print axioms exists_attenuated_readout

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
