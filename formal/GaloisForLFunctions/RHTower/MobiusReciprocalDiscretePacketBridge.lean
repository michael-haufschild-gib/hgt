import GaloisForLFunctions.RHTower.MobiusRenewalPacketEnergy
import GaloisForLFunctions.RHTower.MobiusReciprocalGammaHankelBridge

/-!
# The cubic Route L source as a discrete packet second difference

The generic Gamma--Hankel packet expansion is specialized to the literal cubic
Möbius coefficient. The source packet becomes the step-two second difference
of the order-one Möbius packet. The resulting positive square sum is an exact
identity; its cutoff-uniform bound remains the arithmetic RH obstacle.
-/

open Finset

namespace RHTower

private theorem sum_Icc_one_eq_shifted_range_packet (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  symm
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    simp only [Finset.mem_range] at hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a ha b hb he
    omega
  · intro b hb
    have hb := Finset.mem_Icc.mp hb
    exact ⟨b - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro n hn
    rfl

private theorem cubic_packet_atom_factor (n : ℕ) (δ : ℝ) :
    ((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) ^ (-(5 + δ))) =
      (((n : ℝ) + 2) ^ (-(1 + δ))) *
        (1 - MobiusPacketDifference.node n ^ 2) ^ 2 / 16 := by
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hpow : (((n : ℝ) + 2) ^ (-(5 + δ))) =
      (((n : ℝ) + 2) ^ (-(1 + δ))) /
        (((n : ℝ) + 2) ^ 4) := by
    rw [show -(5 + δ) = -(1 + δ) + (-(4 : ℝ)) by ring,
      Real.rpow_add hn]
    simp only [Real.rpow_neg hn.le, div_eq_mul_inv]
    rw [← Real.rpow_natCast ((n : ℝ) + 2) 4]
    norm_num
  rw [hpow]
  unfold MobiusPacketDifference.node
  field_simp
  ring

/-- Literal shifted cubic Möbius coefficient `mu(n+1) * (n+1)^2`. -/
def cubicShiftedCoefficient (n : ℕ) : ℝ :=
  shiftedMobiusRealCoefficient n * ((n : ℝ) + 1) ^ 2

/-- The cubic source packet is the step-two second difference of order-one packets. -/
theorem cubic_sourcePacket_eq_stepTwoDifference (N k : ℕ) (δ : ℝ) :
    MobiusRenewalPacketEnergy.sourcePacket cubicShiftedCoefficient N (5 + δ) k =
      (MobiusPacketDifference.packet N (1 + δ) k -
        2 * MobiusPacketDifference.packet N (1 + δ) (k + 2) +
        MobiusPacketDifference.packet N (1 + δ) (k + 4)) / 16 := by
  let q := MobiusPacketDifference.node
  let w := MobiusPacketDifference.coefficient (1 + δ)
  have hatom (n : ℕ) :
      cubicShiftedCoefficient n * MobiusPacketDifference.weight (5 + δ) n * q n ^ k =
        (w n * q n ^ k - 2 * (w n * q n ^ (k + 2)) +
          w n * q n ^ (k + 4)) / 16 := by
    dsimp [cubicShiftedCoefficient, w, MobiusPacketDifference.coefficient,
      MobiusPacketDifference.weight]
    calc
      _ = shiftedMobiusRealCoefficient n *
          (((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) ^ (-(5 + δ)))) * q n ^ k := by
            congr 1
            ring
      _ = shiftedMobiusRealCoefficient n *
          (((n : ℝ) + 2) ^ (-(1 + δ)) * (1 - q n ^ 2) ^ 2 / 16) * q n ^ k := by
            rw [cubic_packet_atom_factor]
      _ = _ := by
        rw [pow_add, pow_add]
        ring
  change (∑ n ∈ range N,
      cubicShiftedCoefficient n * MobiusPacketDifference.weight (5 + δ) n * q n ^ k) =
    ((∑ n ∈ range N, w n * q n ^ k) -
      2 * (∑ n ∈ range N, w n * q n ^ (k + 2)) +
      (∑ n ∈ range N, w n * q n ^ (k + 4))) / 16
  calc
    _ = ∑ n ∈ range N,
        (w n * q n ^ k - 2 * (w n * q n ^ (k + 2)) +
          w n * q n ^ (k + 4)) / 16 := by
          apply sum_congr rfl
          intro n _
          exact hatom n
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]

/-- Exact positive square expansion of the literal cubic Gamma--Hankel energy. -/
theorem cubicGammaHankelEnergy_eq_stepTwoDifference (N : ℕ) (δ : ℝ) :
    finiteGammaHankelEnergy cubicShiftedCoefficient N (5 + δ) =
      Real.Gamma (5 + δ) * 2 ^ (5 + δ) * ∑' k : ℕ,
        MobiusRenewalPacketEnergy.binomialWeight (5 + δ) k *
          ((MobiusPacketDifference.packet N (1 + δ) k -
            2 * MobiusPacketDifference.packet N (1 + δ) (k + 2) +
            MobiusPacketDifference.packet N (1 + δ) (k + 4)) / 16) ^ 2 := by
  simpa only [cubic_sourcePacket_eq_stepTwoDifference] using
    (MobiusRenewalPacketEnergy.finiteGammaHankelEnergy_packetExpansion
      cubicShiftedCoefficient N (5 + δ))

/-- The cubic coefficient energy is precisely Route L's coupled-order source. -/
theorem cubicGammaHankelEnergy_eq_routeL (N : ℕ) (δ : ℝ) :
    finiteGammaHankelEnergy cubicShiftedCoefficient N (5 + δ) =
      Real.Gamma (5 + δ) * finiteGeneralReciprocalEnergy (3 + δ) δ N := by
  unfold finiteGammaHankelEnergy
  congr 1
  unfold finiteGeneralReciprocalEnergy
  rw [sum_Icc_one_eq_shifted_range_packet]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_Icc_one_eq_shifted_range_packet]
  apply Finset.sum_congr rfl
  intro n hn
  rw [generalReciprocalMomentKernel_three_add_delta]
  unfold cubicShiftedCoefficient shiftedMobiusRealCoefficient mobiusRealCoefficient
  push_cast
  have hsum : (m : ℝ) + 1 + ((n : ℝ) + 1) = (m : ℝ) + n + 2 := by ring
  rw [hsum]
  ring

/-- Route L's full cubic source energy is one weighted step-two packet norm. -/
theorem routeLCubicEnergy_eq_packetSecondDifference (N : ℕ) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    finiteGeneralReciprocalEnergy (3 + δ) δ N =
      2 ^ (5 + δ) * ∑' k : ℕ,
        MobiusRenewalPacketEnergy.binomialWeight (5 + δ) k *
          ((MobiusPacketDifference.packet N (1 + δ) k -
            2 * MobiusPacketDifference.packet N (1 + δ) (k + 2) +
            MobiusPacketDifference.packet N (1 + δ) (k + 4)) / 16) ^ 2 := by
  have hg : Real.Gamma (5 + δ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith : 0 < 5 + δ)).ne'
  apply mul_left_cancel₀ hg
  calc
    _ = finiteGammaHankelEnergy cubicShiftedCoefficient N (5 + δ) :=
      (cubicGammaHankelEnergy_eq_routeL N δ).symm
    _ = _ := cubicGammaHankelEnergy_eq_stepTwoDifference N δ
    _ = _ := by ring

end RHTower
