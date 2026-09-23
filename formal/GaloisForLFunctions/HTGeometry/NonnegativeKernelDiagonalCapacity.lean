import GaloisForLFunctions.HTGeometry.PositiveDefinitePacketCauchy

/-!
# Diagonal and zero-scale laws for nonnegative coherent kernels

A pointwise nonnegative normalized translation kernel retains the complete diagonal mass of every
nonnegative packet.  If a scaled kernel converges to one at zero, its finite-packet energy converges
to the square of total mass.  These two boundary laws distinguish diagonal persistence from
rank-one coherence without requiring a spectral representation.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped BigOperators

noncomputable section

/-- Every nonnegative packet retains its full diagonal mass under a pointwise nonnegative
normalized translation kernel. -/
theorem realKernelPacketDiagonal_le_energy_of_nonneg
    (K : ℝ → ℝ) (hK : ∀ y, 0 ≤ K y) (hK0 : K 0 = 1)
    {N : ℕ} (t b : Fin N → ℝ) (hb : ∀ i, 0 ≤ b i) :
    ∑ i, b i ^ (2 : ℕ) ≤ realKernelPacketEnergy K t b := by
  rw [realKernelPacketEnergy]
  calc
    ∑ i, b i ^ (2 : ℕ) = ∑ i, b i * K (t i - t i) * b i := by
      apply Finset.sum_congr rfl
      intro i _
      simp [hK0, pow_two]
    _ ≤ ∑ i, ∑ j, b i * K (t j - t i) * b j := by
      apply Finset.sum_le_sum
      intro i _
      have hi := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j => b i * K (t j - t i) * b j)
        (fun j _ => mul_nonneg (mul_nonneg (hb i) (hK _)) (hb j))
        (Finset.mem_univ i)
      exact hi

/-- Scaling every packet node to the origin makes coherent energy converge to the square of total
packet mass whenever the kernel converges to one at the origin. -/
theorem realKernelPacketEnergy_scale_tendsto_mass_sq
    (K : ℝ → ℝ) (hK : Tendsto K (𝓝 0) (𝓝 1))
    {N : ℕ} (t b : Fin N → ℝ) :
    Tendsto (fun x => realKernelPacketEnergy K (fun i => x * t i) b)
      (𝓝 0) (𝓝 ((∑ i, b i) ^ (2 : ℕ))) := by
  unfold realKernelPacketEnergy
  have hterm : ∀ i j, Tendsto
      (fun x => b i * K (x * t j - x * t i) * b j)
      (𝓝 0) (𝓝 (b i * 1 * b j)) := by
    intro i j
    have harg : Tendsto (fun x : ℝ => x * t j - x * t i)
        (𝓝 0) (𝓝 0) := by
      convert (tendsto_id.const_mul (t j)).sub
        (tendsto_id.const_mul (t i)) using 1 <;> simp [mul_comm]
    exact (tendsto_const_nhds.mul (hK.comp harg)).mul tendsto_const_nhds
  have hsum := tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ => hterm i j
  simpa [pow_two, Finset.sum_mul, Finset.mul_sum, mul_comm] using hsum

/-- Subtracting the diagonal after forming coherent energy cannot preserve the normalized anchor
capacity inequality: the one-node unit packet would force `1 ≤ 0`. -/
theorem normalizedKernel_anchor_sq_not_le_energy_sub_diagonal
    (K : ℝ → ℝ) (hK0 : K 0 = 1) :
    ¬ ((∑ _i : Fin 1, (1 : ℝ) * K 0) ^ (2 : ℕ) ≤
        realKernelPacketEnergy K (fun _i : Fin 1 => 0) (fun _i => 1) -
          ∑ _i : Fin 1, (1 : ℝ) ^ (2 : ℕ)) := by
  simp [realKernelPacketEnergy, hK0]

end

end GaloisForLFunctions.HTGeometry
