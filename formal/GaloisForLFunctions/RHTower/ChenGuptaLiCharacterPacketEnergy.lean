/-
# Chen--Gupta--Li additive-multiplicative packet energy

Chen--Gupta--Li define `E(W)` by quadruples whose pairwise character products
agree and whose pairwise ordinate sums differ by at most one.  This module
provides that exact finite carrier using pair indices; it is the precise energy
relation that the fourth-moment Fourier argument must control.

No RH, GRH, smoothness, large-value, energy, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketFourthMomentExpansion

noncomputable section

namespace RHTower

/-- An ordered pair of CGL packet rows. -/
abbrev CGLCharacterPacketPairIndex (R : ℕ) := Fin R × Fin R

/-- The ordinate sum attached to a pair label. -/
def cglCharacterPacketPairOrdinate {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1))
    (p : CGLCharacterPacketPairIndex R) : ℝ :=
  (w p.1).time + (w p.2).time

/-- The Dirichlet-character product attached to a pair label. -/
def cglCharacterPacketPairCharacter {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1))
    (p : CGLCharacterPacketPairIndex R) : DirichletCharacter ℂ (q + 1) :=
  (w p.1).character * (w p.2).character

/-- The literal source energy configurations: equal character products and
ordinate-pair sums within one unit. -/
def cglCharacterPacketEnergyIndexSet {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) :
    Finset (CGLCharacterPacketPairIndex R × CGLCharacterPacketPairIndex R) :=
  Finset.univ.filter fun pq =>
    cglCharacterPacketPairCharacter w pq.1 = cglCharacterPacketPairCharacter w pq.2 ∧
      |cglCharacterPacketPairOrdinate w pq.1 - cglCharacterPacketPairOrdinate w pq.2| ≤ 1

/-- Chen--Gupta--Li's finite additive-multiplicative packet energy. -/
def cglCharacterPacketEnergy {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) : ℕ :=
  (cglCharacterPacketEnergyIndexSet w).card

/-- The source energy is a literal subcount of the four-row label space. -/
theorem cglCharacterPacketEnergy_le_fourthPower {q R : ℕ}
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) :
    cglCharacterPacketEnergy w ≤ R ^ 4 := by
  unfold cglCharacterPacketEnergy cglCharacterPacketEnergyIndexSet
  calc
    (Finset.univ.filter fun pq : CGLCharacterPacketPairIndex R × CGLCharacterPacketPairIndex R =>
        cglCharacterPacketPairCharacter w pq.1 = cglCharacterPacketPairCharacter w pq.2 ∧
          |cglCharacterPacketPairOrdinate w pq.1 - cglCharacterPacketPairOrdinate w pq.2| ≤ 1).card ≤
        (Finset.univ : Finset (CGLCharacterPacketPairIndex R × CGLCharacterPacketPairIndex R)).card :=
      Finset.card_filter_le _ _
    _ = R ^ 4 := by
      simp only [Fintype.card_prod, Fintype.card_fin, Finset.card_univ]
      ring

end RHTower
