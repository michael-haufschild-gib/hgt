import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InsertionSpectrum.BlockSum
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ComplexGibbs.GermRecovery

/-! # Multiplicative action on ordered interlacing spectra -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

private theorem partial_refined (a : ℕ+) (b : SpectralBand 1) (z : ℂ) (n : ℕ) :
    ∑ j ∈ Finset.range (sectorStart a n), complexDrop (refinedSpectrum a b) j z =
      heat z a*∑ j ∈ Finset.range n, complexDrop b j z := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero,mul_zero]
    apply Finset.sum_eq_zero
    intro j hj
    have h : j < a.val-1 := by simpa only [sectorStart,Nat.mul_zero,Nat.add_zero] using Finset.mem_range.mp hj
    rw [complexDrop,refined_prefix a b h,sub_self]
  | succ n ih =>
    rw [sectorStart_succ,Finset.sum_range_add,ih,refined_block_drop,Finset.sum_range_succ,mul_add]

/-- Refinement intertwines the full partition by the occupation amplitude for every interlacing band. -/
theorem relativePartition_refined (a : ℕ+) (b : SpectralBand 1) {z : ℂ} (hz : 0 < z.re) :
    relativePartition (refinedSpectrum a b) z = heat z a*relativePartition b z := by
  have h := (summable_complexDrop (refinedSpectrum a b) hz).hasSum.tendsto_sum_nat.comp (sectorStart_tendsto a)
  have g := ((summable_complexDrop b hz).hasSum.tendsto_sum_nat).const_mul (heat z a)
  exact tendsto_nhds_unique h (g.congr (fun n => (partial_refined a b z n).symm))

private theorem band_decreasing (b : SpectralBand 1) : Antitone (fun n => (b n).val) :=
  antitone_nat_of_succ_le (fun n => (b (n+1)).property.2.trans (b n).property.1)

/-- On a rank-one band the adjacent slot bounds already order all levels. -/
theorem band_eq_of_partition {b c : SpectralBand 1}
    (h : ∀ z : ℂ, 0 < z.re → relativePartition b z = relativePartition c z) : b = c := by
  have hz : 0 < (1:ℂ).re := by norm_num
  have hu : {z : ℂ | 0 < z.re} ∈ 𝓝 (1:ℂ) := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hg : relativePartition b =ᶠ[𝓝 (1:ℂ)] relativePartition c := by
    filter_upwards [hu] with z hpos
    exact h z hpos
  have he := (ordered_germ_iff_levels b c (band_decreasing b) (band_decreasing c) hz).mp hg
  exact funext (fun n => Subtype.ext (he n))

theorem refined_one (b : SpectralBand 1) : refinedSpectrum 1 b = b := by
  apply band_eq_of_partition
  intro z hz
  rw [relativePartition_refined _ _ hz]
  simp [heat,energy]

theorem refined_mul (a d : ℕ+) (b : SpectralBand 1) :
    refinedSpectrum a (refinedSpectrum d b) = refinedSpectrum (a*d) b := by
  apply band_eq_of_partition
  intro z hz
  rw [relativePartition_refined _ _ hz,relativePartition_refined _ _ hz,relativePartition_refined _ _ hz,heat_mul,mul_assoc]

theorem refined_injective (a : ℕ+) : Function.Injective (refinedSpectrum a : SpectralBand 1 → SpectralBand 1) := by
  intro b c he
  apply band_eq_of_partition
  intro z hz
  have h := congrArg (fun v : SpectralBand 1 => relativePartition v z) he
  change relativePartition (refinedSpectrum a b) z = relativePartition (refinedSpectrum a c) z at h
  rw [relativePartition_refined _ _ hz,relativePartition_refined _ _ hz] at h
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) h

#print axioms relativePartition_refined
#print axioms band_eq_of_partition
#print axioms refined_one
#print axioms refined_mul
#print axioms refined_injective

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
