/-
# Chen--Gupta--Li character-packet orthogonality

Chen--Gupta--Li, Lemma 9.1, begins with the packet

`R(v, a) = Σ_{(t, χ) ∈ W} v^{it} χ(a)`

and sums its squared norm over residues coprime to the modulus.  This module
formalizes the exact finite character-orthogonality kernel and expands that
packet energy into its same-character correlations.  It is the finite algebra
before the source applies separation in the ordinate and integrates over `v`.

No RH, GRH, zero-density, smoothness, separation, or growth premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterLargeValues
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.MulChar.Lemmas

open Complex

noncomputable section

namespace RHTower

/-- Exact orthogonality of two complex Dirichlet characters at the concrete
positive modulus `q + 1`.  Summing over all residue classes is the same as
summing over units because each Dirichlet character vanishes on nonunits. -/
theorem cgl_sum_character_mul_conj_character (q : ℕ)
    (χ ψ : DirichletCharacter ℂ (q + 1)) :
    ∑ a : ZMod (q + 1), χ a * (starRingEnd ℂ) (ψ a) =
      if χ = ψ then ((q + 1).totient : ℂ) else 0 := by
  change ∑ a : ZMod (q + 1), χ a * star (ψ a) = _
  simp_rw [MulChar.star_apply']
  have hterm : ∀ a : ZMod (q + 1), χ a * ψ⁻¹ a = (χ * ψ⁻¹) a := by
    intro a
    rw [MulChar.mul_apply]
  rw [show (∑ a : ZMod (q + 1), χ a * ψ⁻¹ a) = ∑ a : ZMod (q + 1), (χ * ψ⁻¹) a by
    exact Finset.sum_congr rfl fun a _ => hterm a]
  by_cases h : χ = ψ
  · subst ψ
    simp only [mul_inv_cancel, MulChar.sum_one_eq_card_units]
    exact_mod_cast ZMod.card_units_eq_totient (q + 1)
  · rw [if_neg h]
    apply MulChar.sum_eq_zero_of_ne_one
    intro hprod
    apply h
    exact mul_inv_eq_one.mp hprod

/-- The source wave `v^{it}` after the substitution `v = exp τ`. -/
noncomputable def cglCharacterPacketWave (t τ : ℝ) : ℂ :=
  Complex.exp (((t * τ : ℝ) : ℂ) * Complex.I)

/-- The literal finite packet `R(exp τ, a)` from CGL Lemma 9.1, at a positive
modulus encoded as `q + 1`. -/
noncomputable def cglCharacterPacket (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (τ : ℝ) (a : ZMod (q + 1)) : ℂ :=
  ∑ r, cglCharacterPacketWave (w r).time τ * (w r).character a

/-- The finite Hermitian packet mass which the source subsequently integrates
over a compact logarithmic ordinate interval. -/
noncomputable def cglCharacterPacketHermitianMass (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (τ : ℝ) : ℂ :=
  ∑ a : ZMod (q + 1),
    cglCharacterPacket q R w τ a * star (cglCharacterPacket q R w τ a)

/-- The Hermitian mass is the exact finite sum of squared packet norms. -/
theorem cglCharacterPacketHermitianMass_eq_normSq (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (τ : ℝ) :
    cglCharacterPacketHermitianMass q R w τ =
      ∑ a : ZMod (q + 1), ((‖cglCharacterPacket q R w τ a‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  unfold cglCharacterPacketHermitianMass
  apply Finset.sum_congr rfl
  intro a ha
  rw [Complex.sq_norm]
  exact Complex.mul_conj _

/-- Exact CGL packet-energy expansion.  Different character labels cancel;
the surviving terms are precisely the same-character correlations which the
source controls using ordinate separation in Lemma 9.1. -/
theorem cglCharacterPacketHermitianMass_expand (q R : ℕ)
    (w : Fin R → CGLCharacterDyadicRowData (q + 1)) (τ : ℝ) :
    cglCharacterPacketHermitianMass q R w τ =
      ∑ r, ∑ s,
        cglCharacterPacketWave (w r).time τ * star (cglCharacterPacketWave (w s).time τ) *
          (if (w r).character = (w s).character then ((q + 1).totient : ℂ) else 0) := by
  unfold cglCharacterPacketHermitianMass cglCharacterPacket
  have hstar : ∀ a : ZMod (q + 1),
      star (∑ r, cglCharacterPacketWave (w r).time τ * (w r).character a) =
        ∑ r, star (cglCharacterPacketWave (w r).time τ * (w r).character a) := by
    intro a
    exact map_sum (starRingEnd ℂ) _ _
  simp_rw [hstar]
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  calc
    _ = cglCharacterPacketWave (w r).time τ * star (cglCharacterPacketWave (w s).time τ) *
        ∑ a : ZMod (q + 1), (w r).character a * star ((w s).character a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      change cglCharacterPacketWave (w r).time τ * (w r).character a *
          (starRingEnd ℂ) (cglCharacterPacketWave (w s).time τ * (w s).character a) =
        cglCharacterPacketWave (w r).time τ * (starRingEnd ℂ) (cglCharacterPacketWave (w s).time τ) *
          ((w r).character a * (starRingEnd ℂ) ((w s).character a))
      rw [map_mul]
      ring
    _ = _ := by
      change cglCharacterPacketWave (w r).time τ * star (cglCharacterPacketWave (w s).time τ) *
          ∑ a : ZMod (q + 1), (w r).character a * (starRingEnd ℂ) ((w s).character a) = _
      rw [cgl_sum_character_mul_conj_character]

end RHTower
