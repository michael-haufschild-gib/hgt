import GaloisForLFunctions.CriticalScaleArithmeticRigidity.SuccessorProjection
import GaloisForLFunctions.BezoutValuationIncidence.LargeSieveWithTheMontgomeryVaughanConstant
import GaloisForLFunctions.BezoutValuationIncidence.CanonicalPrimitiveSpectralFormAndJordanWindowEnergy
import GaloisForLFunctions.BezoutValuationIncidence.UniformLagWindowCovarianceAtQuadraticOrder
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.HarmonicMassFollowsDelayedCounting

/-!
# Relative sampling of actual affine packet differences

Integer dilation merges primitive-root frequencies; translation changes their
phases. Both operations stay inside the same Farey spectrum. Keeping these
collisions before taking norms transfers the exact affine difference energy
to every window with loss `Q(Q-1)`, uniformly in all affine parameters.
-/

noncomputable section

open Finset
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open BezoutValuationIncidence CriticalArithmeticCorrelationTheory

/-- Difference of two actual affine pullbacks of conductor packets. -/
def affinePacketDifference (Q : ℕ) (a b : ℕ → ℝ) (k h l j n : ℕ) : ℝ :=
  conductorPacket Q a (k * n + h) - conductorPacket Q b (l * n + j)

/-- The exact complete-period energy of the affine difference, including all cross terms. -/
def affinePacketEnergy (Q : ℕ) (a b : ℕ → ℝ) (k h l j : ℕ) : ℝ :=
  packetMean Q (fun n => affinePacketDifference Q a b k h l j n ^ 2)

theorem affinePacketEnergy_nonneg (Q : ℕ) (a b : ℕ → ℝ) (k h l j : ℕ) :
    0 ≤ affinePacketEnergy Q a b k h l j :=
  packetMean_sq_nonneg Q _

private theorem responseRoot_bounded_order {Q : ℕ} {ζ : ℂ}
    (hζ : ζ ∈ responseRoots Q) : ∃ d, 1 ≤ d ∧ d ≤ Q ∧ ζ ^ d = 1 := by
  have ho := mem_Icc.mp (orderOf_mem_Icc_of_mem_responseRoots hζ)
  exact ⟨orderOf ζ, ho.1, ho.2, (IsPrimitiveRoot.orderOf ζ).pow_eq_one⟩

private theorem responseRoot_pow_mem {Q : ℕ} {ζ : ℂ}
    (hζ : ζ ∈ responseRoots Q) (k : ℕ) : ζ ^ k ∈ responseRoots Q := by
  obtain ⟨d, hd, hdQ, hpow⟩ := responseRoot_bounded_order hζ
  apply mem_biUnion.mpr
  refine ⟨d, mem_Icc.mpr ⟨hd, hdQ⟩, ?_⟩
  apply (Polynomial.mem_nthRootsFinset hd 1).mpr
  rw [← pow_mul, Nat.mul_comm k d, pow_mul, hpow, one_pow]

private theorem responseRoot_factorial {Q : ℕ} {ζ : ℂ}
    (hζ : ζ ∈ responseRoots Q) : ζ ^ Q.factorial = 1 := by
  obtain ⟨d, hd, hdQ, hpow⟩ := responseRoot_bounded_order hζ
  obtain ⟨r, hr⟩ := Nat.dvd_factorial hd hdQ
  rw [hr, pow_mul, hpow, one_pow]

/-- The affine spectrum aggregates exactly those primitive roots that dilation identifies. -/
def affinePacketSpectrum (Q : ℕ) (a : ℕ → ℝ) (k h : ℕ) (ξ : ℂ) : ℂ :=
  ∑ ζ ∈ responseRoots Q, if ζ ^ k = ξ then (a (orderOf ζ) : ℂ) * ζ ^ h else 0

/-- Exact source transport, with no loss from frequency collisions. -/
theorem affinePacketSpectrum_sum (Q : ℕ) (a : ℕ → ℝ) (k h n : ℕ) :
    (∑ ξ ∈ responseRoots Q, affinePacketSpectrum Q a k h ξ * ξ ^ n) =
      (conductorPacket Q a (k * n + h) : ℂ) := by
  have hfiber (ζ : ℂ) (hζ : ζ ∈ responseRoots Q) :
      (∑ ξ ∈ responseRoots Q,
        (if ζ ^ k = ξ then (a (orderOf ζ) : ℂ) * ζ ^ h else 0) * ξ ^ n) =
      (a (orderOf ζ) : ℂ) * ζ ^ (k * n + h) := by
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq, if_pos (responseRoot_pow_mem hζ k), pow_add, pow_mul]
    ring
  simp only [affinePacketSpectrum, sum_mul]
  rw [sum_comm, sum_congr rfl hfiber, sum_responseRoots_orderOf_mul_pow]
  simp only [ramanujanLagWeight_eq_ramanujanLagCoefficient, conductorPacket]

private theorem affineDifference_spectrum (Q : ℕ) (a b : ℕ → ℝ) (k h l j n : ℕ) :
    (∑ ξ ∈ responseRoots Q,
      (affinePacketSpectrum Q a k h ξ - affinePacketSpectrum Q b l j ξ) * ξ ^ n) =
      (affinePacketDifference Q a b k h l j n : ℂ) := by
  simp only [sub_mul, sum_sub_distrib, affinePacketSpectrum_sum,
    affinePacketDifference, Complex.ofReal_sub]

/-- Parseval identifies the collided spectral mass with the actual affine difference energy. -/
theorem affinePacketEnergy_eq_spectral_mass (Q : ℕ) (a b : ℕ → ℝ) (k h l j : ℕ) :
    affinePacketEnergy Q a b k h l j =
      ∑ ξ ∈ responseRoots Q,
        ‖affinePacketSpectrum Q a k h ξ - affinePacketSpectrum Q b l j ξ‖ ^ 2 := by
  have hp := sum_range_norm_sq_sum_mul_pow
    (fun _ hξ => responseRoot_factorial hξ) (Nat.factorial_pos Q)
    (fun ξ => affinePacketSpectrum Q a k h ξ - affinePacketSpectrum Q b l j ξ)
  simp only [affineDifference_spectrum, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hp
  rw [affinePacketEnergy, packetMean, hp, mul_div_cancel_left₀]
  exact_mod_cast (Nat.factorial_pos Q).ne'

/-- The sampling error is relative to the full affine difference energy, uniformly in every
shift, dilation, window phase, and coefficient family. -/
theorem abs_affinePacketDifference_window_sub_le {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : ℕ → ℝ) (k h l j A K : ℕ) :
    |(∑ n ∈ Icc (A + 1) (A + K), affinePacketDifference Q a b k h l j n ^ 2) -
      K * affinePacketEnergy Q a b k h l j| ≤
        ((Q : ℝ) * ((Q : ℝ) - 1)) * affinePacketEnergy Q a b k h l j := by
  have hw := abs_window_rootsOfUnity_sub_le hQ
    (fun _ hξ => responseRoot_bounded_order hξ)
    (fun ξ => affinePacketSpectrum Q a k h ξ - affinePacketSpectrum Q b l j ξ) A K
  simpa only [affineDifference_spectrum, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    ← affinePacketEnergy_eq_spectral_mass] using hw

/-- A quadratic counting horizon preserves the exact complete-period energy from below. -/
theorem affinePacketDifference_window_lower {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : ℕ → ℝ) (k h l j A K : ℕ) :
    ((K : ℝ) - (Q : ℝ) * ((Q : ℝ) - 1)) * affinePacketEnergy Q a b k h l j ≤
      ∑ n ∈ Icc (A + 1) (A + K), affinePacketDifference Q a b k h l j n ^ 2 := by
  have hw := (abs_le.mp (abs_affinePacketDifference_window_sub_le hQ a b k h l j A K)).1
  linarith only [hw]

private theorem affinePacketDifference_prefix_lower {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : ℕ → ℝ) (k h l j L : ℕ) :
    ((L : ℝ) - (Q * (Q - 1) : ℕ)) * affinePacketEnergy Q a b k h l j ≤
      ∑ i ∈ range L, affinePacketDifference Q a b k h l j (i + 1) ^ 2 := by
  have hw := affinePacketDifference_window_lower hQ a b k h l j 0 L
  simp only [zero_add] at hw
  rw [_root_.RHTower.RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range] at hw
  have hcast : ((Q * (Q - 1) : ℕ) : ℝ) = (Q : ℝ) * ((Q : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
  simpa only [hcast] using hw

/-- Harmonic sampling loses only the logarithm of the quadratic conductor horizon. -/
theorem affinePacketDifference_harmonic_lower {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : ℕ → ℝ) (k h l j N : ℕ) :
    (Real.log ((N : ℝ) + 1) - Real.log (((Q * (Q - 1) : ℕ) : ℝ) + 1)) *
        affinePacketEnergy Q a b k h l j ≤
      ∑ n ∈ Icc 1 N, affinePacketDifference Q a b k h l j n ^ 2 / (n : ℝ) := by
  have hw := logarithmic_mass_ge_of_delayed_prefix
    (fun i => affinePacketDifference Q a b k h l j (i + 1) ^ 2)
    (fun _ => sq_nonneg _) (affinePacketEnergy_nonneg Q a b k h l j)
    (Q * (Q - 1)) (affinePacketDifference_prefix_lower hQ a b k h l j) N
  rw [_root_.RHTower.RegularizedDivisorHarmonic.sum_Icc_one_eq_sum_range]
  simpa only [Nat.cast_add, Nat.cast_one] using hw

#print axioms affinePacketSpectrum_sum
#print axioms abs_affinePacketDifference_window_sub_le
#print axioms affinePacketDifference_harmonic_lower

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
