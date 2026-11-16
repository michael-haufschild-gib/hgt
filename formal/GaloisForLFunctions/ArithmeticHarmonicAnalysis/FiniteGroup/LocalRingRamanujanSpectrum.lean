import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.RingRamanujanRadicalMoments
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCountLawOverEveryFiniteRing

/-!
# The three values of a local-ring Ramanujan sum

Units are the complement of the maximal ideal. Subtracting their two character
sums gives the complete spectrum, including degenerate characters. The three
spectral masses determine every moment over local rings with nilpotents as
well as over fields.
-/

open Finset
open scoped BigOperators Classical

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
noncomputable section
variable {R : Type*} [CommRing R] [Fintype R] [IsLocalRing R]

/-- Frequencies that kill the maximal ideal under the character pairing. -/
def localCharacterAnnihilator (ψ : AddChar R ℂ) : Finset R :=
  univ.filter fun g => ∀ a : IsLocalRing.maximalIdeal R, ψ (g * (a : R)) = 1

private theorem sum_maximalIdeal_character (ψ : AddChar R ℂ) (g : R) :
    (∑ a : IsLocalRing.maximalIdeal R, ψ (g * (a : R))) =
      if g ∈ localCharacterAnnihilator ψ then
        (Fintype.card (IsLocalRing.maximalIdeal R) : ℂ) else 0 := by
  let χ : AddChar (IsLocalRing.maximalIdeal R) ℂ :=
    (ψ.mulShift g).compAddMonoidHom
      (IsLocalRing.maximalIdeal R).subtype.toAddMonoidHom
  have he : χ = 1 ↔ g ∈ localCharacterAnnihilator ψ := by
    simp only [localCharacterAnnihilator, mem_filter, mem_univ, true_and]
    exact DFunLike.ext_iff
  by_cases hg : g ∈ localCharacterAnnihilator ψ
  · rw [if_pos hg]
    exact AddChar.sum_eq_card_of_eq_one (he.mpr hg)
  · rw [if_neg hg]
    exact AddChar.sum_eq_zero_of_ne_one (fun h => hg (he.mp h))

/-- Local Ramanujan sums are the difference of two exact annihilator indicators. -/
theorem local_ringRamanujanSum_value (ψ : AddChar R ℂ) (g : R) :
    ringRamanujanSum ψ g =
      (if g ∈ characterRadical ψ then (Fintype.card R : ℂ) else 0) -
      (if g ∈ localCharacterAnnihilator ψ then
        (Fintype.card (IsLocalRing.maximalIdeal R) : ℂ) else 0) := by
  have hu : (∑ u : Rˣ, ψ (g * (u : R))) =
      ∑ u : {x : R // IsUnit x}, ψ (g * (u : R)) :=
    Fintype.sum_equiv (ArithmeticHodgeTheoryOfDegenerations.unitsEquivIsUnit R)
      _ _ (fun _ => rfl)
  have hm : (∑ a : IsLocalRing.maximalIdeal R, ψ (g * (a : R))) =
      ∑ a : {x : R // ¬IsUnit x}, ψ (g * (a : R)) :=
    Fintype.sum_equiv
      (Equiv.subtypeEquivRight (p := fun x : R => x ∈ IsLocalRing.maximalIdeal R)
        (q := fun x => ¬IsUnit x) (fun x => IsLocalRing.mem_maximalIdeal x))
      (fun a => ψ (g * (a : R))) (fun a => ψ (g * (a : R))) (fun _ => rfl)
  have hs := Fintype.sum_subtype_add_sum_subtype (fun x : R => IsUnit x)
    (fun x => ψ (g * x))
  rw [← hu, ← hm, sum_maximalIdeal_character] at hs
  have hr := sum_character_mul_eq_radical ψ g
  simp_rw [mul_comm _ g] at hr
  rw [hr] at hs
  exact eq_sub_of_add_eq hs

/-- The spectrum has at most three values, regardless of character primitivity. -/
theorem local_ringRamanujanSum_three_values (ψ : AddChar R ℂ) (g : R) :
    ringRamanujanSum ψ g =
      if g ∈ characterRadical ψ then
        (Fintype.card R : ℂ) - Fintype.card (IsLocalRing.maximalIdeal R)
      else if g ∈ localCharacterAnnihilator ψ then
        -(Fintype.card (IsLocalRing.maximalIdeal R) : ℂ) else 0 := by
  rw [local_ringRamanujanSum_value]
  by_cases hg : g ∈ characterRadical ψ
  · have hm : g ∈ localCharacterAnnihilator ψ := by
      simp only [localCharacterAnnihilator, mem_filter, mem_univ, true_and]
      intro a
      simpa only [mul_comm g] using hg (a : R)
    rw [if_pos hg, if_pos hm, if_pos hg]
  · rw [if_neg hg, if_neg hg]
    split_ifs <;> simp only [zero_sub, sub_zero]

/-- The three spectral masses give the exact distribution for every test function. -/
theorem sum_local_ringRamanujan_distribution (ψ : AddChar R ℂ) (F : ℂ → ℂ) :
    (∑ g : R, F (ringRamanujanSum ψ g)) =
      ((univ.filter fun g => g ∈ characterRadical ψ).card : ℂ) *
        F ((Fintype.card R : ℂ) - Fintype.card (IsLocalRing.maximalIdeal R)) +
      ((univ.filter fun g => g ∉ characterRadical ψ ∧
        g ∈ localCharacterAnnihilator ψ).card : ℂ) *
        F (-(Fintype.card (IsLocalRing.maximalIdeal R) : ℂ)) +
      ((univ.filter fun g => g ∉ localCharacterAnnihilator ψ).card : ℂ) * F 0 := by
  have hterm (g : R) : F (ringRamanujanSum ψ g) =
      (if g ∈ characterRadical ψ then
        F ((Fintype.card R : ℂ) - Fintype.card (IsLocalRing.maximalIdeal R)) else 0) +
      (if g ∉ characterRadical ψ ∧ g ∈ localCharacterAnnihilator ψ then
        F (-(Fintype.card (IsLocalRing.maximalIdeal R) : ℂ)) else 0) +
      (if g ∉ localCharacterAnnihilator ψ then F 0 else 0) := by
    rw [local_ringRamanujanSum_three_values]
    by_cases hg : g ∈ characterRadical ψ
    · have hm : g ∈ localCharacterAnnihilator ψ := by
        simp only [localCharacterAnnihilator, mem_filter, mem_univ, true_and]
        intro a
        simpa only [mul_comm g] using hg (a : R)
      simp only [hg, hm, if_true, not_true_eq_false, false_and, if_false, add_zero]
    · by_cases hm : g ∈ localCharacterAnnihilator ψ <;> simp [hg, hm]
  simp_rw [hterm]
  rw [sum_add_distrib, sum_add_distrib]
  simp only [← sum_filter, sum_const, nsmul_eq_mul]

/-- All local-ring moments, including degree zero, follow from the exact three-point measure. -/
theorem sum_local_ringRamanujan_pow (ψ : AddChar R ℂ) (k : ℕ) :
    (∑ g : R, ringRamanujanSum ψ g ^ k) =
      ((univ.filter fun g => g ∈ characterRadical ψ).card : ℂ) *
        ((Fintype.card R : ℂ) - Fintype.card (IsLocalRing.maximalIdeal R)) ^ k +
      ((univ.filter fun g => g ∉ characterRadical ψ ∧
        g ∈ localCharacterAnnihilator ψ).card : ℂ) *
        (-(Fintype.card (IsLocalRing.maximalIdeal R) : ℂ)) ^ k +
      ((univ.filter fun g => g ∉ localCharacterAnnihilator ψ).card : ℂ) * (0 : ℂ) ^ k :=
  sum_local_ringRamanujan_distribution ψ (fun z => z ^ k)

#print axioms local_ringRamanujanSum_value
#print axioms local_ringRamanujanSum_three_values
#print axioms sum_local_ringRamanujan_distribution
#print axioms sum_local_ringRamanujan_pow

end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
