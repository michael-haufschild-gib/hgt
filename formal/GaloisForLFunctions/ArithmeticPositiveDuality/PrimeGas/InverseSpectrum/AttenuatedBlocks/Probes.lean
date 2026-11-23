import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.Readouts

/-! # Single-level and uniform block attenuation probes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

private def groundFraction (r : ℕ) (t : Ioc (0:ℝ) 1) (j : Fin (r+1)) : Ioc (0:ℝ) 1 :=
  if j = 0 then t else ⟨1,zero_lt_one,le_rfl⟩

/-- At every positive missing rank, the same limiting spectrum reads a single attenuated ground occupation at every positive real part. -/
theorem exists_ground_attenuation (r : ℕ) (t : Ioc (0:ℝ) 1) :
    ∃ b ∈ closure (physicalSpectra (r+1)), ∀ {z : ℂ}, 0 < z.re →
      relativePartition b z = 1-(t.val:ℂ)^z := by
  obtain ⟨b,hb,he⟩ := exists_attenuated_readout 0 (groundFraction r t)
  refine ⟨b,hb,fun {z} hz => ?_⟩
  rw [he hz,Finset.sum_eq_single (0 : Fin (r+1))]
  · simp only [Fin.val_zero,Nat.zero_add,occupationWeight_zero,Complex.ofReal_one,Complex.one_cpow,
      groundFraction,if_pos rfl,mul_one]
  · intro j _ hj
    simp only [groundFraction,if_neg hj,one_mul,sub_self]
  · exact fun h => (h (Finset.mem_univ _)).elim

/-- Constant attenuation multiplies the deleted block polynomial by a single complex chord. -/
theorem exists_uniform_attenuation (N r : ℕ) (t : Ioc (0:ℝ) 1) :
    ∃ b ∈ closure (physicalSpectra r), ∀ {z : ℂ}, 0 < z.re →
      relativePartition b z = (1-(t.val:ℂ)^z)*relativePartition (blockSpectrum N r) z := by
  obtain ⟨b,hb,he⟩ := exists_attenuated_readout N (fun _ : Fin r => t)
  refine ⟨b,hb,fun {z} hz => ?_⟩
  rw [he hz,relativePartition_block N r hz,← Fin.sum_univ_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg t.property.1.le (occupationWeight_pos _).le]
  ring

#print axioms exists_ground_attenuation
#print axioms exists_uniform_attenuation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
