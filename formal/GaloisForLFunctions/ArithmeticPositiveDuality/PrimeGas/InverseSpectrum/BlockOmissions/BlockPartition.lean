import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockResponse
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.EdgeProfiles

/-! # Finite-gap Dirichlet polynomials throughout the positive half-plane -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

theorem continuous_relativePartition_spectrum {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    Continuous (fun b : SpectralBand r => relativePartition b z) := by
  let δ : GibbsExponent := ⟨z.re,hz⟩
  have hp : Continuous (fun x : ℝ => (x:ℂ)^z) := continuous_iff_continuousAt.mpr
    (fun x => Complex.continuousAt_ofReal_cpow_const x z (Or.inl hz))
  apply continuous_tsum (u := fun j => (‖z‖/δ.val) * spectralDrop (powerResponse δ) (coldEdge r) j)
  · intro j
    exact continuous_const.sub (hp.comp (continuous_subtype_val.comp (continuous_apply j)))
  · exact (hasSum_edge_drop (powerResponse δ) r).summable.mul_left _
  · intro j b
    exact (complexDrop_bound b j δ (z := z) le_rfl).trans
      (mul_le_mul_of_nonneg_left (drop_le_edge _ _ _) (div_nonneg (norm_nonneg _) hz.le))

/-- Exact complex loss for an interior deletion, including critical and subcritical arguments. -/
theorem relativePartition_block (N r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    relativePartition (blockSpectrum N r) z = ∑ j ∈ Finset.range r, (occupationWeight (N+j) : ℂ)^z := by
  let a (n : ℕ) := (occupationWeight n : ℂ)^z
  have hp : (∑ n ∈ Finset.range N, complexDrop (blockSpectrum N r) n z) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [complexDrop,blockSpectrum,skipIndex,if_pos (Finset.mem_range.mp hn),sub_self]
  have ht (n : ℕ) : complexDrop (blockSpectrum N r) (n+N) z = complexDrop (coldEdge r) (n+N) z := by
    have hn : ¬ n+N < N := by omega
    simp only [complexDrop,blockSpectrum,skipIndex,if_neg hn,coldEdge]
  have hc := (summable_complexDrop (coldEdge r) hz).sum_add_tsum_nat_add N
  have hb := (summable_complexDrop (blockSpectrum N r) hz).sum_add_tsum_nat_add N
  rw [hp,zero_add] at hb
  simp only [ht] at hb
  change _ = relativePartition (coldEdge r) z at hc
  rw [relativePartition_cold r hz] at hc
  change (∑ n ∈ Finset.range N, (a n-a (n+r))) + _ = ∑ j ∈ Finset.range r, a j at hc
  have hn := Finset.sum_range_add a N r
  have hr := Finset.sum_range_add a r N
  rw [Nat.add_comm r N] at hr
  simp only [Nat.add_comm r] at hr
  rw [Finset.sum_sub_distrib] at hc
  change relativePartition (blockSpectrum N r) z = ∑ j ∈ Finset.range r, a (N+j)
  change _ = relativePartition (blockSpectrum N r) z at hb
  linear_combination hb.symm + hc + hn - hr

/-- Phase-corrected complex reading of the block. Every summand tends to one at each fixed height. -/
def complexBlock (z : ℂ) (r N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range r, ((occupationWeight (N+j)/occupationWeight N : ℝ):ℂ)^z

theorem complexBlock_tendsto (z : ℂ) (r : ℕ) : Tendsto (complexBlock z r) atTop (𝓝 (r:ℂ)) := by
  have h (j : ℕ) : Tendsto (fun N => ((occupationWeight (N+j)/occupationWeight N : ℝ):ℂ)^z) atTop (𝓝 1) := by
    have ht : Tendsto (fun N => ((occupationWeight (N+j)/occupationWeight N : ℝ):ℂ)^z)
        atTop (𝓝 (((1:ℝ):ℂ)^z)) :=
      (Complex.continuousAt_ofReal_cpow_const 1 z (Or.inr one_ne_zero)).tendsto.comp (tendsto_block_weight_ratio j)
    simpa only [Complex.ofReal_one,Complex.one_cpow] using ht
  unfold complexBlock
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] using
    tendsto_finsetSum (Finset.range r) (fun j _ => h j)

theorem relativePartition_block_scaled (N r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    relativePartition (blockSpectrum N r) z = (occupationWeight N : ℂ)^z * complexBlock z r N := by
  rw [relativePartition_block N r hz,complexBlock,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.mul_cpow_ofReal_nonneg (occupationWeight_pos N).le
    (div_nonneg (occupationWeight_pos _).le (occupationWeight_pos _).le),← Complex.ofReal_mul,
    mul_comm _ (_/_),div_mul_cancel₀ _ (occupationWeight_pos N).ne']

#print axioms continuous_relativePartition_spectrum
#print axioms relativePartition_block
#print axioms complexBlock_tendsto
#print axioms relativePartition_block_scaled

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
