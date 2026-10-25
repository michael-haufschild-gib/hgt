import GaloisForLFunctions.ArithmeticDefectRigidity.ContractingHorizonsProducesActualCofactorLimits
import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitCarriesACyclicDilationAction
import GaloisForLFunctions.HTGeometry.RealPositiveKernelComplexification

/-!
# Numeric horizon order controls the cofactor action

Contracted horizons order every finite real Gram packet. Complexification
and density extend this order to scaled dilation norms on the complete
actual Hilbert module. Its scale-one diagonal bounds all contracted masses.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- Every actual contracted-energy ratio lies between zero and the scale-one mass. -/
theorem scaled_diagonal_mem_Icc {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (p : ℕ+) : (p : ℝ) * L.kernel p p ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · rw [← norm_vector_sq]
    exact mul_nonneg (by positivity) (sq_nonneg _)
  · have h := scaled_diagonal_antitone L (show (1 : ℕ+) ≤ p from p.property)
    have hone : ((1 : ℕ+) : ℝ) = 1 := by norm_num
    simpa only [hone, one_mul, L.kernel_one_one] using h

/-- Numeric scale order holds for every actual quadratic packet, not just each cofactor norm. -/
theorem scaled_packet_antitone {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    Antitone (fun p : ℕ+ => (p : ℝ) *
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * L.kernel (p * j) (p * k)) := by
  intro p q hpq
  rcases admits_or_contracted_pairing_tendsto L with hpaid | hpair
  · simp_rw [kernel_mul_mul_of_admits L hpaid]
    have hid (a : ℕ+) : (a : ℝ) *
        (∑ j ∈ S, ∑ k ∈ S, c j * c k * ((1 / (a : ℝ)) * L.kernel j k)) =
        ∑ j ∈ S, ∑ k ∈ S, c j * c k * L.kernel j k := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      have ha : (a : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hid, hid]
  · let A := pmPowerDampedCenteredDivisorPrefix (ε : ℝ)
    let T (m : ℕ) := L.subsequence m + 1
    let P (a : ℕ+) (m : ℕ) :=
      ∑ j ∈ S, ∑ k ∈ S, c j * c k *
        (pronicPairing (T m / a) (rowDilate j A) (rowDilate k A) /
          dampedMobiusEnergy ε (T m))
    have hlim (a : ℕ+) : Tendsto (P a) atTop
        (𝓝 ((a : ℝ) * ∑ j ∈ S, ∑ k ∈ S, c j * c k * L.kernel (a * j) (a * k))) := by
      have h : Tendsto (P a) atTop (𝓝 (∑ j ∈ S, ∑ k ∈ S,
          c j * c k * ((a : ℝ) * L.kernel (a * j) (a * k)))) := by
        apply tendsto_finsetSum
        intro j _
        apply tendsto_finsetSum
        intro k _
        exact (hpair a j k).const_mul (c j * c k)
      convert h using 1
      congr 1
      simp only [mul_sum]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k _
      ring
    apply le_of_tendsto_of_tendsto' (hlim q) (hlim p)
    intro m
    have hpacket (a : ℕ+) : P a m =
        pronicNorm (T m / a) (fun n => ∑ j ∈ S, c j * A (n / j)) ^ 2 /
          dampedMobiusEnergy ε (T m) := by
      exact pronicPairing_packet_energy_eq (T m / a) (dampedMobiusEnergy ε (T m)) S c
        (fun j n => A (n / j))
    rw [hpacket, hpacket]
    apply div_le_div_of_nonneg_right ?_ (receiverEnergy_succ_pos ε (L.subsequence m)).le
    apply pronicNorm_sq_monotone
    exact Nat.div_le_div_left hpq p.property

/-- Numeric horizon order extends from real packets to every complex coefficient packet. -/
theorem scaled_kernelForm_antitone {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (c : ℕ+ →₀ ℂ) :
    Antitone (fun p : ℕ+ => (p : ℝ) *
      (kernelForm (fun j k => complexKernel L (p * j) (p * k)) c c).re) := by
  intro p q hpq
  simp only [complexKernel, kernelForm_real_re_eq, mul_add]
  exact add_le_add (scaled_packet_antitone L c.support (fun j => (c j).re) hpq)
    (scaled_packet_antitone L c.support (fun j => (c j).im) hpq)

/-- The scaled dilation quadratic forms decrease in numeric scale on the complete actual module. -/
theorem scaled_dilation_norm_sq_antitone {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (x : Hilbert L) :
    Antitone (fun p : ℕ+ => (p : ℝ) * ‖dilation L p x‖ ^ 2) := by
  intro p q hpq
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      exact isClosed_le (continuous_const.mul ((dilation L q).continuous.norm.pow 2))
        (continuous_const.mul ((dilation L p).continuous.norm.pow 2))
  | ih c =>
      simp only [dilation, KernelHilbert.pushforward_coe, UniformSpace.Completion.norm_coe,
        norm_sq_eq_re_inner (𝕜 := ℂ), KernelPre.inner_def]
      change (q : ℝ) * (kernelForm (complexKernel L)
        (Finsupp.mapDomain (fun j => q * j) c) (Finsupp.mapDomain (fun j => q * j) c)).re ≤
        (p : ℝ) * (kernelForm (complexKernel L)
        (Finsupp.mapDomain (fun j => p * j) c) (Finsupp.mapDomain (fun j => p * j) c)).re
      rw [kernelForm_mapDomain, kernelForm_mapDomain]
      exact scaled_kernelForm_antitone L c hpq

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.scaled_packet_antitone
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.scaled_diagonal_mem_Icc
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.scaled_dilation_norm_sq_antitone
end
