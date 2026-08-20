/-
# Chen--Gupta--Li quartic character packet

Chen--Gupta--Li Lemma 9.2 controls a fourth packet moment by additive-
multiplicative energy.  This module supplies its exact algebraic starting
point: square the finite packet, regard it as a packet indexed by row pairs,
and identify its Hermitian mass with the literal fourth norm moment.

No RH, GRH, smoothness, large-value, energy, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketSecondMoment

open Complex

noncomputable section

namespace RHTower

/-- The square of a CGL packet, represented as a character packet indexed by
ordered pairs of source rows. -/
noncomputable def cglCharacterPacketSquare (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (τ : ℝ) (a : ZMod (q + 1)) : ℂ :=
  ∑ rs : Fin R × Fin R,
    cglCharacterPacketWave ((w rs.1).time + (w rs.2).time) τ *
      ((w rs.1).character * (w rs.2).character) a

/-- Source waves multiply by adding their ordinates. -/
theorem cglCharacterPacketWave_mul (t u τ : ℝ) :
    cglCharacterPacketWave t τ * cglCharacterPacketWave u τ =
      cglCharacterPacketWave (t + u) τ := by
  unfold cglCharacterPacketWave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The pair-indexed packet is exactly the square of the original CGL packet. -/
theorem cglCharacterPacketSquare_eq_sq (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (τ : ℝ) (a : ZMod (q + 1)) :
    cglCharacterPacketSquare q R w τ a = cglCharacterPacket q R w τ a ^ 2 := by
  unfold cglCharacterPacketSquare cglCharacterPacket
  rw [pow_two, Finset.sum_mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  change cglCharacterPacketWave ((w r).time + (w s).time) τ *
      ((w r).character a * (w s).character a) =
    cglCharacterPacketWave (w r).time τ * (w r).character a *
      (cglCharacterPacketWave (w s).time τ * (w s).character a)
  rw [← cglCharacterPacketWave_mul]
  ring

/-- Hermitian mass of the pair-indexed square packet. -/
noncomputable def cglCharacterPacketQuarticHermitianMass (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (τ : ℝ) : ℂ :=
  ∑ a : ZMod (q + 1),
    cglCharacterPacketSquare q R w τ a * star (cglCharacterPacketSquare q R w τ a)

/-- The square packet's Hermitian mass is exactly the fourth norm moment of
the original finite CGL packet. -/
theorem cglCharacterPacketQuarticHermitianMass_eq_normPowFour (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (τ : ℝ) :
    cglCharacterPacketQuarticHermitianMass q R w τ =
      ∑ a : ZMod (q + 1), ((‖cglCharacterPacket q R w τ a‖ ^ 4 : ℝ) : ℂ) := by
  unfold cglCharacterPacketQuarticHermitianMass
  apply Finset.sum_congr rfl
  intro a ha
  rw [cglCharacterPacketSquare_eq_sq]
  change cglCharacterPacket q R w τ a ^ 2 *
    (starRingEnd ℂ) (cglCharacterPacket q R w τ a ^ 2) = _
  rw [map_pow]
  calc
    cglCharacterPacket q R w τ a ^ 2 * star (cglCharacterPacket q R w τ a) ^ 2 =
        (cglCharacterPacket q R w τ a * star (cglCharacterPacket q R w τ a)) ^ 2 := by ring
    _ = (((‖cglCharacterPacket q R w τ a‖ ^ 2 : ℝ) : ℂ)) ^ 2 := by
      congr 1
      rw [Complex.sq_norm]
      exact Complex.mul_conj _
    _ = ((‖cglCharacterPacket q R w τ a‖ ^ 4 : ℝ) : ℂ) := by
      norm_cast
      ring

end RHTower
