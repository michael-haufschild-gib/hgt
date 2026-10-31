import GaloisForLFunctions.CriticalScaleArithmeticRigidity.AffineWindowEnergy
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.DyadicPoleRigidity
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorHeadNorm

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

open BezoutValuationIncidence SuccessorShellArithmetic

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
    have hcast : ((2 * Q * (Q - 1) : ℕ) : ℝ) = 2 * (Q : ℝ) * ((Q : ℝ) - 1) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
    rw [← hcast]
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

/-- A window longer than the separation horizon has the exact same constant-packet kernel. -/
theorem jointWindowEnergy_eq_zero_iff {Q K : ℕ} (hQ : 2 ≤ Q)
    (hK : Q * (Q - 1) < K) (a b : ℕ → ℝ) (A : ℕ) :
    jointWindowEnergy Q a b A K = 0 ↔
      (∀ m ∈ Icc 2 Q, a m = 0) ∧ (∀ m ∈ Icc 1 Q, b m = a m) := by
  constructor
  · intro hz
    have hKR : (Q : ℝ) * ((Q : ℝ) - 1) < K := by
      have hcast : ((Q * (Q - 1) : ℕ) : ℝ) = (Q : ℝ) * ((Q : ℝ) - 1) := by
        rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
      rw [← hcast]
      exact_mod_cast hK
    have hsum := add_le_add (affinePacketDifference_window_lower hQ a b 1 1 1 0 A K)
      (affinePacketDifference_window_lower hQ a a 2 0 1 0 A K)
    rw [← mul_add, ← sum_add_distrib] at hsum
    simp only [affinePacketDifference, one_mul, Nat.add_zero] at hsum
    change _ ≤ jointWindowEnergy Q a b A K at hsum
    rw [hz] at hsum
    have hE : affinePacketEnergy Q a b 1 1 1 0 + affinePacketEnergy Q a a 2 0 1 0 ≤ 0 := by
      by_contra hn
      have hp := mul_pos (sub_pos.mpr hKR) (lt_of_not_ge hn)
      linarith only [hp, hsum]
    have hJ : jointRigidityEnergy Q a b ≤
        affinePacketEnergy Q a b 1 1 1 0 + affinePacketEnergy Q a a 2 0 1 0 := by
      simpa only [jointRigidityEnergy, dyadicPoleDefect, affinePacketEnergy,
        affinePacketDifference, one_mul, Nat.add_zero] using
          add_le_add (le_refl (packetMean Q (fun n =>
            (conductorPacket Q a (n + 1) - conductorPacket Q b n) ^ 2)))
            (packetMean_sq_le_mean_sq Q (fun n => conductorPacket Q a (2 * n) - conductorPacket Q a n))
    exact (jointRigidityEnergy_eq_zero_iff Q a b).mp
      (le_antisymm (hJ.trans hE) (jointRigidityEnergy_nonneg Q a b))
  · rintro ⟨ha, hb⟩
    have hM := (nonconstantPacketMass_eq_zero_iff Q a).mpr ha
    have hbPacket (n : ℕ) : conductorPacket Q b n = conductorPacket Q a n := by
      exact sum_congr rfl fun m hm =>
        congrArg (fun z => z * ramanujanLagCoefficient m n) (hb m hm)
    apply sum_eq_zero
    intro n _
    simp only [successorDilationSquare, hbPacket,
      conductorPacket_of_nonconstant_mass_eq_zero Q a hM,
      sub_self, zero_pow two_ne_zero, add_zero]

/-- The complete-period constant for the two literal difference energies is exactly three quarters. -/
theorem universal_successor_dilation_lower_iff (C : ℝ) :
    (∀ Q a b, C * nonconstantPacketMass Q a ≤
      packetMean Q (fun n => (conductorPacket Q a (n + 1) - conductorPacket Q b n) ^ 2) +
        packetMean Q (fun n => (conductorPacket Q a (2 * n) - conductorPacket Q a n) ^ 2)) ↔
      C ≤ (3 / 4 : ℝ) := by
  constructor
  · intro hC
    let a : ℕ → ℝ := fun m => if m = 3 then 1 else 0
    have hM : nonconstantPacketMass 3 a = 2 := by
      norm_num [nonconstantPacketMass, a, Finset.sum_Icc_succ_top,
        Nat.totient_prime Nat.prime_three]
    have hE : packetMean 3 (fun n =>
        (conductorPacket 3 a (n + 1) - conductorPacket 3 (shiftProjection 1 a) n) ^ 2) = 3 / 2 := by
      rw [packetMean_shift_error_eq_projection_add_leakage]
      simp only [sub_self, zero_pow two_ne_zero, mul_zero, sum_const_zero, zero_add]
      norm_num [shiftLeakageWeight, a, Finset.sum_Icc_succ_top,
        sieveLagMultiplier_eq_moebius_totient_quotient, moebiusReal,
        ArithmeticFunction.moebius_apply_prime Nat.prime_three,
        Nat.totient_prime Nat.prime_three]
    have hpacket (n : ℕ) : conductorPacket 3 a n = ramanujanLagCoefficient 3 n := by
      norm_num [conductorPacket, a]
    have hd (n : ℕ) : conductorPacket 3 a (2 * n) = conductorPacket 3 a n := by
      have hr := ramanujanLagCoefficient_dilate_reduced (show 0 < (3 : ℕ) by decide) 2 n
      norm_num [Nat.totient_prime Nat.prime_three] at hr
      rw [hpacket, hpacket]
      linarith only [hr]
    have hD : packetMean 3 (fun n => (conductorPacket 3 a (2 * n) - conductorPacket 3 a n) ^ 2) = 0 := by
      simp only [hd, sub_self, zero_pow two_ne_zero, packetMean, sum_const_zero, zero_div]
    have hw := hC 3 a (shiftProjection 1 a)
    rw [hM, hE, hD, add_zero] at hw
    linarith only [hw]
  · intro hC Q a b
    exact (mul_le_mul_of_nonneg_right hC (nonconstantPacketMass_nonneg Q a)).trans
      (three_quarters_mass_le_successor_add_dilation_energy Q a b)

#print axioms jointWindowEnergy_lower
#print axioms jointHarmonicEnergy_lower
#print axioms nonconstantPacketMass_eq_zero_of_jointWindowEnergy_eq_zero
#print axioms jointWindowEnergy_eq_zero_iff
#print axioms universal_successor_dilation_lower_iff

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
