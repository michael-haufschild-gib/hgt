/-
# Chen--Gupta--Li smooth fourth-moment finite absorption

This module closes the finite packet version of the absorption step in
Chen--Gupta--Li, Lemma 9.2.  Diagonal configurations force the literal
additive-multiplicative energy to be at least the square of packet size.  At a
certified smoothing scale dominating that size, fourth-order Fourier decay
therefore absorbs the explicit far `R^(4 : ℕ)` configuration count into the energy
scale.

No RH, GRH, smoothness, energy, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketSmoothIntegral

open Complex MeasureTheory Set Filter

noncomputable section

namespace RHTower

/-- A certified large smoothing scale that dominates the finite packet size. -/
def CGLCharacterPacketAbsorptionScale (R : ℕ) :=
  {X : CGLCharacterPacketLargeScale // (R : ℝ) ≤ (X.1 : ℝ)}

/-- Every ordered row-pair contributes its diagonal configuration to CGL's
literal additive-multiplicative energy. -/
theorem cglCharacterPacketEnergy_lower_square {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) :
    R ^ (2 : ℕ) ≤ cglCharacterPacketEnergy w := by
  let f : CGLCharacterPacketPairIndex R →
      {pq // pq ∈ cglCharacterPacketEnergyIndexSet w} := fun p =>
    ⟨(p, p), by
      simp [cglCharacterPacketEnergyIndexSet, cglCharacterPacketPairCharacter,
        cglCharacterPacketPairOrdinate]⟩
  have hf : Function.Injective f := by
    intro p p' h
    simpa [f] using congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  simpa [cglCharacterPacketEnergy, pow_two] using hcard

/-- At a certified packet-dominating scale, a fourth-order far Fourier tail
is bounded by the CGL energy scale. -/
theorem cglCharacterPacket_fourthTail_le_energyScale
    {q R : ℕ} (w : Fin R → CGLCharacterDyadicRowData (q + 1))
    (X : CGLCharacterPacketAbsorptionScale R) (C : ℝ) (hC : 0 ≤ C) :
    ((q + 1).totient : ℝ) * (R ^ (4 : ℕ) : ℝ) *
        ((X.1.1 : ℝ) * C / (1 + (X.1.1 : ℝ)) ^ (4 : ℕ)) ≤
      ((q + 1).totient : ℝ) * (cglCharacterPacketEnergy w : ℝ) *
        ((X.1.1 : ℝ) * C) := by
  have hR0 : (0 : ℝ) ≤ R := by positivity
  have hX0 : (0 : ℝ) ≤ (X.1.1 : ℝ) := X.1.1.2
  have hRle : (R : ℝ) ≤ 1 + (X.1.1 : ℝ) := by linarith [X.2]
  have hRsq : (R : ℝ) ^ (2 : ℕ) ≤ (1 + (X.1.1 : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hR0 hRle 2
  have hb2 : 1 ≤ (1 + (X.1.1 : ℝ)) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (1 + (X.1.1 : ℝ))]
  have hb4 : (1 + (X.1.1 : ℝ)) ^ (2 : ℕ) ≤ (1 + (X.1.1 : ℝ)) ^ (4 : ℕ) := by
    calc
      (1 + (X.1.1 : ℝ)) ^ (2 : ℕ) = 1 * (1 + (X.1.1 : ℝ)) ^ (2 : ℕ) := by ring
      _ ≤ (1 + (X.1.1 : ℝ)) ^ (2 : ℕ) * (1 + (X.1.1 : ℝ)) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hb2 (sq_nonneg (1 + (X.1.1 : ℝ)))
      _ = (1 + (X.1.1 : ℝ)) ^ (4 : ℕ) := by ring
  have hRsqle : (R : ℝ) ^ (2 : ℕ) ≤ (1 + (X.1.1 : ℝ)) ^ (4 : ℕ) := hRsq.trans hb4
  have hRfourth : (R : ℝ) ^ (4 : ℕ) ≤
      (R : ℝ) ^ (2 : ℕ) * (1 + (X.1.1 : ℝ)) ^ (4 : ℕ) := by
    calc
      (R : ℝ) ^ (4 : ℕ) = (R : ℝ) ^ (2 : ℕ) * (R : ℝ) ^ (2 : ℕ) := by ring
      _ ≤ (R : ℝ) ^ (2 : ℕ) * (1 + (X.1.1 : ℝ)) ^ (4 : ℕ) :=
        mul_le_mul_of_nonneg_left hRsqle (sq_nonneg (R : ℝ))
  have hden : 0 < (1 + (X.1.1 : ℝ)) ^ (4 : ℕ) := by positivity
  have htail : (R ^ (4 : ℕ) : ℝ) *
      ((X.1.1 : ℝ) * C / (1 + (X.1.1 : ℝ)) ^ (4 : ℕ)) ≤
      (R ^ (2 : ℕ) : ℝ) * ((X.1.1 : ℝ) * C) := by
    rw [show (R : ℝ) ^ (4 : ℕ) * ((X.1.1 : ℝ) * C / (1 + (X.1.1 : ℝ)) ^ (4 : ℕ)) =
      ((R : ℝ) ^ (4 : ℕ) * ((X.1.1 : ℝ) * C)) / (1 + (X.1.1 : ℝ)) ^ (4 : ℕ) by ring]
    apply (div_le_iff₀ hden).2
    calc
      (R : ℝ) ^ (4 : ℕ) * ((X.1.1 : ℝ) * C) ≤
          ((R : ℝ) ^ (2 : ℕ) * (1 + (X.1.1 : ℝ)) ^ (4 : ℕ)) * ((X.1.1 : ℝ) * C) :=
        mul_le_mul_of_nonneg_right hRfourth (mul_nonneg hX0 hC)
      _ = ((R : ℝ) ^ (2 : ℕ) * ((X.1.1 : ℝ) * C)) * (1 + (X.1.1 : ℝ)) ^ (4 : ℕ) := by ring
  have henergy : (R ^ (2 : ℕ) : ℝ) ≤ (cglCharacterPacketEnergy w : ℝ) := by
    exact_mod_cast cglCharacterPacketEnergy_lower_square w
  calc
    ((q + 1).totient : ℝ) * (R ^ (4 : ℕ) : ℝ) *
        ((X.1.1 : ℝ) * C / (1 + (X.1.1 : ℝ)) ^ (4 : ℕ)) =
      ((q + 1).totient : ℝ) * ((R ^ (4 : ℕ) : ℝ) *
        ((X.1.1 : ℝ) * C / (1 + (X.1.1 : ℝ)) ^ (4 : ℕ))) := by ring
    _ ≤ ((q + 1).totient : ℝ) * ((R ^ (2 : ℕ) : ℝ) * ((X.1.1 : ℝ) * C)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ ((q + 1).totient : ℝ) *
        ((cglCharacterPacketEnergy w : ℝ) * ((X.1.1 : ℝ) * C)) := by
      gcongr
    _ = ((q + 1).totient : ℝ) * (cglCharacterPacketEnergy w : ℝ) *
        ((X.1.1 : ℝ) * C) := by ring

/-- A closed finite CGL Lemma 9.2 estimate: under a certified smoothing scale
that dominates packet size, the literal smoothed quartic integral is bounded
by its additive-multiplicative energy times the scale. -/
theorem exists_norm_cglCharacterPacketSmoothQuarticIntegral_le_energyScale :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q R : ℕ)
      (w : Fin R → CGLCharacterDyadicRowData (q + 1))
      (X : CGLCharacterPacketAbsorptionScale R),
      ‖cglCharacterPacketSmoothQuarticIntegral w X.1‖ ≤
        ((q + 1).totient : ℝ) * (cglCharacterPacketEnergy w : ℝ) *
          ((X.1.1 : ℝ) * C) := by
  obtain ⟨Cnear, hCnear, hnear⟩ :=
    exists_norm_cglCharacterPacketSmoothNearContribution_le
  obtain ⟨Cfar, hCfar, hfar⟩ :=
    exists_norm_cglCharacterPacketSmoothFarContribution_le 4
  refine ⟨Cnear + Cfar, add_nonneg hCnear hCfar, fun q R w X => ?_⟩
  rw [cglCharacterPacketSmoothQuarticIntegral_eq_smoothFourthMomentContribution,
    cglCharacterPacketSmoothFourthMomentContribution_eq_near_add_far]
  calc
    ‖cglCharacterPacketSmoothNearContribution w X.1.1 +
        cglCharacterPacketSmoothFarContribution w X.1.1‖ ≤
      ‖cglCharacterPacketSmoothNearContribution w X.1.1‖ +
        ‖cglCharacterPacketSmoothFarContribution w X.1.1‖ := norm_add_le _ _
    _ ≤ ((q + 1).totient : ℝ) * (cglCharacterPacketEnergy w : ℝ) *
        ((X.1.1 : ℝ) * Cnear) +
        ((q + 1).totient : ℝ) * (cglCharacterPacketEnergy w : ℝ) *
          ((X.1.1 : ℝ) * Cfar) := by
      apply add_le_add
      · exact hnear q R w X.1.1
      · exact (hfar q R w X.1).trans
          (cglCharacterPacket_fourthTail_le_energyScale w X Cfar hCfar)
    _ = ((q + 1).totient : ℝ) * (cglCharacterPacketEnergy w : ℝ) *
        ((X.1.1 : ℝ) * (Cnear + Cfar)) := by ring

end RHTower
