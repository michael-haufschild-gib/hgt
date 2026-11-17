import GaloisForLFunctions.RHTower.DilatedVonMangoldtSignLimit

/-!
# Prime-weighted square-wave packets

On dilations between zero and pi, the prime-weighted square wave has an affine
limiting response. A finite packet is read only through its total coefficient
and first dilation moment. The two-endpoint normalization cancels the logarithmic
diagonal term exactly.
-/

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

open Finset Filter Topology ArithmeticFunction

noncomputable section

/-- The normalized prime-weighted square-wave response at dilation `a`. -/
def primeSquareWave (a T : ℝ) : ℝ :=
  (∑ m ∈ Ioc 0 ⌊T⌋₊, (vonMangoldt m : ℝ) * Real.sign (Real.sin (a * T / m))) / T

/-- A finite packet sees only its mass and first dilation moment. -/
theorem tendsto_primeSquareWave_packet {ι : Type*} (s : Finset ι) (c a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i ∧ a i ≤ Real.pi) :
    Tendsto (fun T => ∑ i ∈ s, c i * primeSquareWave (a i) T) atTop
      (𝓝 ((∑ i ∈ s, c i) - (2 * Real.log 2 / Real.pi) * ∑ i ∈ s, c i * a i)) := by
  have h : Tendsto (fun T => ∑ i ∈ s, c i * primeSquareWave (a i) T) atTop
      (𝓝 (∑ i ∈ s, c i * (1 - 2 * a i * Real.log 2 / Real.pi))) := by
    apply tendsto_finsetSum
    intro i hi
    exact (_root_.RHTower.tendsto_dilated_vonMangoldt_sign_sum
      (ha i hi).1 (ha i hi).2).const_mul _
  convert h using 1
  rw [mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun i _ => by ring

/-- A second dilation difference annihilates the affine prime response. -/
theorem tendsto_primeSquareWave_second_difference :
    Tendsto (fun T => primeSquareWave (1 / 2) T - 2 * primeSquareWave 1 T +
      primeSquareWave (3 / 2) T) atTop (𝓝 0) := by
  have hhalf := _root_.RHTower.tendsto_dilated_vonMangoldt_sign_sum
    (by norm_num : (0 : ℝ) < 1 / 2) (by linarith [Real.two_le_pi] : (1 / 2 : ℝ) ≤ Real.pi)
  have hone := _root_.RHTower.tendsto_dilated_vonMangoldt_sign_sum_one
  have hthree := _root_.RHTower.tendsto_dilated_vonMangoldt_sign_sum
    (by norm_num : (0 : ℝ) < 3 / 2) (by linarith [Real.two_le_pi] : (3 / 2 : ℝ) ≤ Real.pi)
  have h := (hhalf.sub (hone.const_mul 2)).add hthree
  have heq : (1 - 2 * (1 / 2) * Real.log 2 / Real.pi) -
      2 * (1 - 2 * Real.log 2 / Real.pi) +
      (1 - 2 * (3 / 2) * Real.log 2 / Real.pi) = 0 := by ring
  rw [heq] at h
  simpa only [primeSquareWave, one_mul] using h

/-- The parity-corrected endpoint coefficient cancels the even-prime diagonal coefficient. -/
theorem tendsto_primeSquareWave_endpoint_cancellation :
    Tendsto (fun T => (primeSquareWave 1 T - primeSquareWave 2 T) / 4 -
      Real.log 2 / (2 * Real.pi)) atTop (𝓝 0) := by
  have h := (_root_.RHTower.tendsto_dilated_vonMangoldt_sign_sum_difference.div_const 4).sub_const
    (Real.log 2 / (2 * Real.pi))
  have heq : (2 / Real.pi * Real.log 2) / 4 - Real.log 2 / (2 * Real.pi) = 0 := by ring
  rw [heq] at h
  simpa only [primeSquareWave, one_mul] using h

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
