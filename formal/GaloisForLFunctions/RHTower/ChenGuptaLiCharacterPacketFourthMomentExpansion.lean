/-
# Chen--Gupta--Li quartic character-product expansion

The fourth CGL packet moment is expanded exactly into pair labels. Character
orthogonality leaves precisely the source relation `χ₁χ₂ = χ₃χ₄`, the
multiplicative part of the additive-multiplicative energy in Lemma 9.2.

No RH, GRH, smoothness, large-value, energy, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketFourthMoment

open Complex

noncomputable section

namespace RHTower

/-- Exact character-product expansion of the CGL fourth packet moment. -/
theorem cglCharacterPacketQuarticHermitianMass_expand (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (τ : ℝ) :
    cglCharacterPacketQuarticHermitianMass q R w τ =
      ∑ p : Fin R × Fin R, ∑ q' : Fin R × Fin R,
        cglCharacterPacketWave ((w p.1).time + (w p.2).time) τ *
          star (cglCharacterPacketWave ((w q'.1).time + (w q'.2).time) τ) *
          (if (w p.1).character * (w p.2).character =
              (w q'.1).character * (w q'.2).character then ((q + 1).totient : ℂ) else 0) := by
  unfold cglCharacterPacketQuarticHermitianMass cglCharacterPacketSquare
  have hstar : ∀ a : ZMod (q + 1),
      star (∑ p : Fin R × Fin R,
        cglCharacterPacketWave ((w p.1).time + (w p.2).time) τ *
          ((w p.1).character * (w p.2).character) a) =
        ∑ p : Fin R × Fin R,
          star (cglCharacterPacketWave ((w p.1).time + (w p.2).time) τ *
            ((w p.1).character * (w p.2).character) a) := by
    intro a
    exact map_sum (starRingEnd ℂ) _ _
  simp_rw [hstar]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q' hq
  calc
    _ = cglCharacterPacketWave ((w p.1).time + (w p.2).time) τ *
        star (cglCharacterPacketWave ((w q'.1).time + (w q'.2).time) τ) *
        ∑ a : ZMod (q + 1),
          ((w p.1).character * (w p.2).character) a *
            star (((w q'.1).character * (w q'.2).character) a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      change cglCharacterPacketWave ((w p.1).time + (w p.2).time) τ *
          ((w p.1).character * (w p.2).character) a *
          (starRingEnd ℂ) (cglCharacterPacketWave ((w q'.1).time + (w q'.2).time) τ *
            ((w q'.1).character * (w q'.2).character) a) = _
      rw [map_mul]
      simp only [starRingEnd_apply]
      ring
    _ = _ := by
      change cglCharacterPacketWave ((w p.1).time + (w p.2).time) τ *
          star (cglCharacterPacketWave ((w q'.1).time + (w q'.2).time) τ) *
          ∑ a : ZMod (q + 1), ((w p.1).character * (w p.2).character) a *
            (starRingEnd ℂ) (((w q'.1).character * (w q'.2).character) a) = _
      rw [cgl_sum_character_mul_conj_character]

end RHTower
