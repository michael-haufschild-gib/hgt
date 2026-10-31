import GaloisForLFunctions.CriticalScaleArithmeticRigidity.AffineWindowEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.DyadicPoleRigidity

/-!
# Joint arithmetic rigidity at quadratic sampling horizons

Successor approximation and actual dyadic dilation cannot both be small
on a nonconstant conductor packet. The complete-period gap survives on
every window longer than `Q(Q-1)` and under harmonic sampling beyond the
same conductor scale. Every coefficient of the approximating packet is free.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

/-- The two literal arithmetic square defects observed at one integer. -/
def successorDilationSquare (Q : ℕ) (a b : ℕ → ℝ) (n : ℕ) : ℝ :=
  (conductorPacket Q a (n + 1) - conductorPacket Q b n) ^ 2 +
    (conductorPacket Q a (2 * n) - conductorPacket Q a n) ^ 2

/-- Joint arithmetic observations on a consecutive window. -/
def jointWindowEnergy (Q : ℕ) (a b : ℕ → ℝ) (A K : ℕ) : ℝ :=
  ∑ n ∈ Icc (A + 1) (A + K), successorDilationSquare Q a b n

/-- Joint arithmetic observations with the harmonic measure used by conductor vectors. -/
def jointHarmonicEnergy (Q : ℕ) (a b : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 N, successorDilationSquare Q a b n / (n : ℝ)

theorem jointWindowEnergy_nonneg (Q : ℕ) (a b : ℕ → ℝ) (A K : ℕ) :
    0 ≤ jointWindowEnergy Q a b A K :=
  sum_nonneg fun _ _ => add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem jointHarmonicEnergy_nonneg (Q : ℕ) (a b : ℕ → ℝ) (N : ℕ) :
    0 ≤ jointHarmonicEnergy Q a b N :=
  sum_nonneg fun n _ => div_nonneg
    (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Nat.cast_nonneg n)

private theorem joint_complete_energy_lower (Q : ℕ) (a b : ℕ → ℝ) :
    (3 / 4 : ℝ) * nonconstantPacketMass Q a ≤
      affinePacketEnergy Q a b 1 1 1 0 + affinePacketEnergy Q a a 2 0 1 0 := by
  simpa only [affinePacketEnergy, affinePacketDifference, one_mul, Nat.add_zero] using
    three_quarters_mass_le_successor_add_dilation_energy Q a b

/-- Uniform joint rigidity on every window; the conductor loss is quadratic, not factorial. -/
theorem jointWindowEnergy_lower {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : ℕ → ℝ) (A K : ℕ) :
    (3 / 4 : ℝ) * ((K : ℝ) - (Q : ℝ) * ((Q : ℝ) - 1)) *
        nonconstantPacketMass Q a ≤ jointWindowEnergy Q a b A K := by
  by_cases hscale : 0 ≤ (K : ℝ) - (Q : ℝ) * ((Q : ℝ) - 1)
  · have hs := affinePacketDifference_window_lower hQ a b 1 1 1 0 A K
    have hd := affinePacketDifference_window_lower hQ a a 2 0 1 0 A K
    have hsum := add_le_add hs hd
    rw [← mul_add, ← sum_add_distrib] at hsum
    have hgap := mul_le_mul_of_nonneg_left (joint_complete_energy_lower Q a b) hscale
    have h := hgap.trans hsum
    simpa only [affinePacketDifference, one_mul, Nat.add_zero, jointWindowEnergy,
      successorDilationSquare, mul_left_comm, mul_assoc] using h
  · exact (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_ge hscale))
      (nonconstantPacketMass_nonneg Q a)).trans (jointWindowEnergy_nonneg Q a b A K)

/-- Beyond twice the separation horizon, a fixed positive fraction of nonconstant mass
is visible in the observed arithmetic differences. -/
theorem jointWindowEnergy_lower_at_twice_horizon {Q K : ℕ} (hQ : 2 ≤ Q)
    (hK : 2 * Q * (Q - 1) ≤ K) (a b : ℕ → ℝ) (A : ℕ) :
    (3 / 8 : ℝ) * K * nonconstantPacketMass Q a ≤ jointWindowEnergy Q a b A K := by
  have hKR : 2 * (Q : ℝ) * ((Q : ℝ) - 1) ≤ K := by
    exact_mod_cast hK
  have hc : (3 / 8 : ℝ) * K ≤ (3 / 4 : ℝ) *
      ((K : ℝ) - (Q : ℝ) * ((Q : ℝ) - 1)) := by linarith only [hKR]
  exact (mul_le_mul_of_nonneg_right hc (nonconstantPacketMass_nonneg Q a)).trans
    (jointWindowEnergy_lower hQ a b A K)

/-- Harmonic joint rigidity has only the logarithmic cost of the conductor horizon. -/
theorem jointHarmonicEnergy_lower {Q : ℕ} (hQ : 2 ≤ Q)
    (a b : ℕ → ℝ) (N : ℕ) :
    (3 / 4 : ℝ) *
        (Real.log ((N : ℝ) + 1) - Real.log (((Q * (Q - 1) : ℕ) : ℝ) + 1)) *
      nonconstantPacketMass Q a ≤ jointHarmonicEnergy Q a b N := by
  by_cases hscale : 0 ≤ Real.log ((N : ℝ) + 1) -
      Real.log (((Q * (Q - 1) : ℕ) : ℝ) + 1)
  · have hs := affinePacketDifference_harmonic_lower hQ a b 1 1 1 0 N
    have hd := affinePacketDifference_harmonic_lower hQ a a 2 0 1 0 N
    have hsum := add_le_add hs hd
    rw [← mul_add, ← sum_add_distrib] at hsum
    have hgap := mul_le_mul_of_nonneg_left (joint_complete_energy_lower Q a b) hscale
    have h := hgap.trans hsum
    simpa only [affinePacketDifference, one_mul, Nat.add_zero, jointHarmonicEnergy,
      successorDilationSquare, add_div, mul_left_comm, mul_assoc] using h
  · exact (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_ge hscale))
      (nonconstantPacketMass_nonneg Q a)).trans (jointHarmonicEnergy_nonneg Q a b N)

/-- Vanishing joint observations beyond the separation horizon force zero nonconstant mass. -/
theorem nonconstantPacketMass_eq_zero_of_jointWindowEnergy_eq_zero
    {Q K : ℕ} (hQ : 2 ≤ Q) (hK : Q * (Q - 1) < K)
    (a b : ℕ → ℝ) (A : ℕ) (hz : jointWindowEnergy Q a b A K = 0) :
    nonconstantPacketMass Q a = 0 := by
  have hKR : (Q : ℝ) * ((Q : ℝ) - 1) < K := by
    have hcast : ((Q * (Q - 1) : ℕ) : ℝ) = (Q : ℝ) * ((Q : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
    rw [← hcast]
    exact_mod_cast hK
  have h := jointWindowEnergy_lower hQ a b A K
  rw [hz] at h
  have hcoef : 0 < (3 / 4 : ℝ) * ((K : ℝ) - (Q : ℝ) * ((Q : ℝ) - 1)) :=
    mul_pos (by norm_num) (sub_pos.mpr hKR)
  have hm := nonconstantPacketMass_nonneg Q a
  nlinarith only [h, hm, hcoef]

#print axioms jointWindowEnergy_lower
#print axioms jointHarmonicEnergy_lower
#print axioms nonconstantPacketMass_eq_zero_of_jointWindowEnergy_eq_zero

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
