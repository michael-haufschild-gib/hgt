import GaloisForLFunctions.BiScaleUncertainty.AlternatingPhysicalPackets

/-!
# Unconditional affine commutator producers

Scaled finite alternating cells realize every physical gap. Normalization
constructs actual unit vectors at nonzero gap and zero at zero gap, with
an exact commutator deficit of `2*|a|/(n+1)`.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def scaledAlternatingPacket (c : ℝ) (n : ℕ) : Velocity :=
  physicalDilation c⁻¹ (alternatingCellPacket (n+1))

theorem scaledAlternatingPacket_zero (n : ℕ) : scaledAlternatingPacket 0 n = 0 := by
  simp only [scaledAlternatingPacket, inv_zero, physicalDilation_zero]

theorem scaledAlternatingPacket_energy (c : ℝ) (n : ℕ) :
    ‖scaledAlternatingPacket c n‖^2 = |c⁻¹| * ((n : ℝ)+1) := by
  rw [scaledAlternatingPacket, physicalDilation_energy, alternatingCellPacket_energy]
  simp only [Nat.cast_add, Nat.cast_one]

theorem scaledAlternatingPacket_translate (c : ℝ) (n : ℕ) :
    physicalTranslation c (scaledAlternatingPacket c n) =
      physicalDilation c⁻¹ (physicalTranslation 1 (alternatingCellPacket (n+1))) := by
  by_cases hc : c = 0
  · simp [hc, scaledAlternatingPacket_zero, physicalDilation_zero]
  · rw [scaledAlternatingPacket, physicalTranslation_dilation, inv_mul_cancel₀ hc]

theorem scaledAlternatingPacket_shift_energy (c : ℝ) (n : ℕ) :
    ‖physicalTranslation c (scaledAlternatingPacket c n)-scaledAlternatingPacket c n‖^2 =
      |c⁻¹| * (4*((n : ℝ)+1)-2) := by
  rw [scaledAlternatingPacket_translate, scaledAlternatingPacket, ← map_sub,
    physicalDilation_energy, alternatingCellPacket_shift_energy]

def normalizedAffinePacket (c : ℝ) (n : ℕ) : Velocity :=
  (Real.sqrt (|c⁻¹| * ((n : ℝ)+1)))⁻¹ • scaledAlternatingPacket c n

theorem normalizedAffinePacket_zero (n : ℕ) : normalizedAffinePacket 0 n = 0 := by
  simp [normalizedAffinePacket, scaledAlternatingPacket_zero]

theorem normalizedAffinePacket_energy (c : ℝ) (n : ℕ) :
    ‖normalizedAffinePacket c n‖^2 = if c = 0 then 0 else 1 := by
  by_cases hc : c = 0
  · simp [hc, normalizedAffinePacket_zero]
  · rw [if_neg hc]
    have hk : 0 < |c⁻¹| * ((n : ℝ)+1) :=
      mul_pos (abs_pos.mpr (inv_ne_zero hc)) (by positivity)
    rw [normalizedAffinePacket, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      inv_pow, Real.sq_sqrt hk.le, scaledAlternatingPacket_energy, inv_mul_cancel₀ hk.ne']

theorem normalizedAffinePacket_norm (c : ℝ) (n : ℕ) :
    ‖normalizedAffinePacket c n‖ = if c = 0 then 0 else 1 := by
  by_cases hc : c = 0
  · simp [hc, normalizedAffinePacket_zero]
  · rw [if_neg hc]
    have h := normalizedAffinePacket_energy c n
    rw [if_neg hc] at h
    nlinarith only [h, norm_nonneg (normalizedAffinePacket c n)]

theorem normalizedAffinePacket_shift_energy (c : ℝ) (n : ℕ) :
    ‖physicalTranslation c (normalizedAffinePacket c n)-normalizedAffinePacket c n‖^2 =
      if c = 0 then 0 else 4-2/((n : ℝ)+1) := by
  by_cases hc : c = 0
  · simp [hc, normalizedAffinePacket_zero]
  · rw [if_neg hc]
    have hci : |c⁻¹| ≠ 0 := abs_ne_zero.mpr (inv_ne_zero hc)
    have hN : (n : ℝ)+1 ≠ 0 := by positivity
    have hk : 0 < |c⁻¹| * ((n : ℝ)+1) :=
      mul_pos (abs_pos.mpr (inv_ne_zero hc)) (by positivity)
    rw [normalizedAffinePacket, map_smul, ← smul_sub, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hk.le,
      scaledAlternatingPacket_shift_energy]
    field_simp

def physicalAffineProducer (a b : ℝ) (n : ℕ) : Velocity :=
  normalizedAffinePacket (b*(a-1)) n

theorem physicalAffineProducer_norm (a b : ℝ) (n : ℕ) :
    ‖physicalAffineProducer a b n‖ = if b*(a-1) = 0 then 0 else 1 :=
  normalizedAffinePacket_norm _ n

theorem physicalAffineProducer_norm_sq (a b : ℝ) (n : ℕ) :
    ‖physicalAffineProducer a b n‖^2 = if b*(a-1) = 0 then 0 else 1 :=
  normalizedAffinePacket_energy _ n

theorem physicalAffineProducer_energy (a b : ℝ) (n : ℕ) :
    ‖physicalAffineCommutator a b (physicalAffineProducer a b n)‖^2 =
      if b*(a-1) = 0 then 0 else |a| * (4-2/((n : ℝ)+1)) := by
  rw [physicalAffineCommutator_energy, physicalAffineProducer, normalizedAffinePacket_shift_energy]
  split_ifs <;> simp

theorem physicalAffineProducer_defect (a b : ℝ) (n : ℕ) :
    4*|a| * ‖physicalAffineProducer a b n‖^2-
      ‖physicalAffineCommutator a b (physicalAffineProducer a b n)‖^2 =
        if b*(a-1) = 0 then 0 else 2*|a|/((n : ℝ)+1) := by
  rw [physicalAffineProducer_norm_sq, physicalAffineProducer_energy]
  split_ifs <;> ring

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
