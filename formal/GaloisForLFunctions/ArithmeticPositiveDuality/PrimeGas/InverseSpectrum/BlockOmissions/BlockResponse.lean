import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.BlockIndex
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.SharpTail
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.ParabolicBudget

/-! # Exact block readouts and high-occupation scaling -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

/-- Removing a block records exactly the response of its r missing occupations. -/
theorem detectorError_block (f : SpectralResponse) (N r : ℕ) :
    detectorError f (hotEdge r) (blockSpectrum N r) = tailCeiling f r N := by
  have hp : (∑ n ∈ Finset.range N, levelError f (hotEdge r) (blockSpectrum N r) n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [levelError,hotEdge,blockSpectrum,skipIndex,if_pos (Finset.mem_range.mp hn),sub_self,abs_zero]
  have ht : detectorTail f (hotEdge r) (blockSpectrum N r) N = detectorTail f (hotEdge r) (coldEdge r) N := by
    apply tsum_congr
    intro n
    have hn : ¬ n+N < N := by omega
    simp only [levelError,blockSpectrum,skipIndex,if_neg hn,coldEdge]
  rw [detectorError_eq_prefix_add_tail f _ _ N,hp,zero_add,ht,detectorTail_edges]

theorem relativeReading_block (f : SpectralResponse) (N r : ℕ) :
    relativeReading f (blockSpectrum N r) = tailCeiling f r N := by
  have he : detectorError f (hotEdge r) (blockSpectrum N r) = relativeReading f (blockSpectrum N r) := by
    apply tsum_congr
    intro n
    exact abs_of_nonneg (drop_nonneg f _ n)
  exact he.symm.trans (detectorError_block f N r)

/-- Relative occupation widths of a fixed finite block tend to one as the block moves out. -/
theorem tendsto_block_weight_ratio (j : ℕ) : Tendsto (fun N => occupationWeight (N+j)/occupationWeight N) atTop (𝓝 1) := by
  have he (N : ℕ) : occupationWeight (N+j)/occupationWeight N = 1-(j:ℝ)*occupationWeight (N+j) := by
    simp only [occupationWeight_eq,Nat.cast_add,inv_div_inv]
    field_simp [show (N:ℝ)+(j:ℝ)+1 ≠ 0 by positivity]
    ring
  have ht : Tendsto (fun N => occupationWeight (N+j)) atTop (𝓝 0) :=
    occupationWeight_tendsto.comp (tendsto_add_atTop_nat j)
  simpa only [he,mul_zero,sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub (ht.const_mul (j:ℝ))

/-- Power response divided by the first deleted weight, raised to the same exponent. -/
def normalizedBlock (β : GibbsExponent) (r N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range r, (occupationWeight (N+j)/occupationWeight N)^β.val

theorem normalizedBlock_tendsto (β : GibbsExponent) (r : ℕ) : Tendsto (normalizedBlock β r) atTop (𝓝 (r:ℝ)) := by
  have h (j : ℕ) : Tendsto (fun N => (occupationWeight (N+j)/occupationWeight N)^β.val) atTop (𝓝 1) := by
    have ht : Tendsto (fun N => (occupationWeight (N+j)/occupationWeight N)^β.val) atTop (𝓝 ((1:ℝ)^β.val)) :=
      ((Real.continuous_rpow_const β.property.le).tendsto 1).comp (tendsto_block_weight_ratio j)
    simpa only [Real.one_rpow] using ht
  unfold normalizedBlock
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one] using
    tendsto_finsetSum (Finset.range r) (fun j _ => h j)

theorem power_tailCeiling_eq_scaled (β : GibbsExponent) (r N : ℕ) :
    tailCeiling (powerResponse β) r N = occupationWeight N ^ β.val * normalizedBlock β r N := by
  rw [normalizedBlock,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change occupationWeight (N+j)^β.val - (0:ℝ)^β.val = _
  rw [Real.zero_rpow β.property.ne',sub_zero,Real.div_rpow (occupationWeight_pos _).le (occupationWeight_pos _).le]
  rw [mul_comm _ (_/_),div_mul_cancel₀ _ (Real.rpow_pos_of_pos (occupationWeight_pos _) _).ne']

#print axioms detectorError_block
#print axioms tendsto_block_weight_ratio
#print axioms normalizedBlock_tendsto
#print axioms power_tailCeiling_eq_scaled

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
