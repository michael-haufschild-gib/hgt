import GaloisForLFunctions.ArithmeticElectrostatics.TheTransverseEnergyOfTheZeroDivisor
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticHodgeIndexSignatureLaw
import GaloisForLFunctions.RHTower.CCM.CCMZetaWeilSmoothIdentity

/-!
# Transverse energy pays the arithmetic negative index

A packet of distinct zeros right of the critical line has a disjoint reflected packet.
Each member of their union carries one unit of angular energy. Thus the packet's
cardinality is bounded by the total transverse energy, including when that energy is
infinite. The Pontryagin bound then pays every negative square of a finite Weil Gram
with one unit of energy. The corresponding intersection form has one additional
positive square, supplied by its pole plane.
-/

open Finset RHTower Zeta23
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticElectrostatics
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

/-- A finite right-hand packet costs one transverse-energy unit per distinct zero. -/
theorem card_rightPacket_le_divisorTransverseEnergy (s : Finset XiDivisorSupport)
    (hs : ∀ j ∈ s, 1 / 2 < (j : ℂ).re) :
    (s.card : ℝ≥0∞) ≤ divisorTransverseEnergy := by
  classical
  have hd : Disjoint s (s.image supportPartner) := by
    refine Finset.disjoint_left.mpr fun j hj hjp => ?_
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hjp
    have hright := hs (supportPartner k) hj
    rw [supportPartner_re] at hright
    linarith [hs k hk]
  have hcard : (s ∪ s.image supportPartner).card = 2 * s.card := by
    rw [Finset.card_union_of_disjoint hd,
      Finset.card_image_of_injective s supportPartner.injective]
    omega
  have hquantum := card_le_two_mul_divisorTransverseEnergy
    (s := s ∪ s.image supportPartner) (by
      intro j hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (hs j hj).ne'
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
        rw [supportPartner_re]
        linarith [hs k hk])
  rw [hcard, Nat.cast_mul, Nat.cast_ofNat] at hquantum
  rw [two_mul_divisorTransverseEnergy] at hquantum
  rw [divisorTransverseEnergy, ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero)
    (Or.inl ENNReal.ofNat_ne_top)]
  simpa only [mul_comm] using hquantum

/-- The energy bound uses the actual zeta carrier, with distinct zeros counted once. -/
theorem card_rightZeros_le_divisorTransverseEnergy (s : Finset ℂ)
    (hs : ∀ ρ ∈ s, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 < ρ.re) :
    (s.card : ℝ≥0∞) ≤ divisorTransverseEnergy := by
  classical
  let j : s → XiDivisorSupport := fun ρ =>
    xiDivisorZetaCarrierEquiv.symm ⟨ρ, (hs ρ ρ.property).1⟩
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : XiDivisorSupport => (z : ℂ)) hab)
  have hbound := card_rightPacket_le_divisorTransverseEnergy (s.attach.image j) (by
    intro ρ hρ
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hρ
    exact (hs a a.property).2)
  simpa only [Finset.card_image_of_injective _ hj, Finset.card_attach] using hbound

/-- Every negative square of a finite smooth Weil Gram costs one unit of transverse energy. -/
theorem negIndex_weilGram_le_divisorTransverseEnergy {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ≥0∞)
      ≤ divisorTransverseEnergy := by
  classical
  let k := hermNegIndex (weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f)
  let R : Set ℂ := {ρ ∈ zetaZeroConfig.carrier | 1 / 2 < ρ.re}
  have hk : (k : ℕ∞) ≤ R.encard := negIndex_weilGram_le_offLineCount f hf hfc
  have hpacket : ∃ s : Finset ℂ, (↑s : Set ℂ) ⊆ R ∧ s.card = k := by
    rcases R.finite_or_infinite with hR | hR
    · rw [hR.encard_eq_coe_toFinset_card] at hk
      obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (ENat.coe_le_coe.mp hk)
      exact ⟨s, fun ρ hρ => hR.mem_toFinset.mp (hs hρ), hcard⟩
    · exact hR.exists_subset_card_eq k
  obtain ⟨s, hs, hcard⟩ := hpacket
  have hbound := card_rightZeros_le_divisorTransverseEnergy s (fun ρ hρ => hs hρ)
  simpa only [hcard] using hbound

/-- The pole plane contributes one positive square; transverse energy pays the excess. -/
theorem posIndex_intersectionGram_le_one_add_divisorTransverseEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i)) :
    (hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) : ℝ≥0∞)
      ≤ 1 + divisorTransverseEnergy := by
  rw [posIndex_intersectionGram, Nat.cast_add, Nat.cast_one]
  exact add_le_add le_rfl (negIndex_weilGram_le_divisorTransverseEnergy f hf hfc)

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.negIndex_weilGram_le_divisorTransverseEnergy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.posIndex_intersectionGram_le_one_add_divisorTransverseEnergy
