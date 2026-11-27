import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Orientation
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Partial.Threshold.Width

/-! # Complete temperature identifiability from an unlabeled outgoing loss spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold

open Peak.Ranks.Capped _root_.HTGeometry

variable {S : Finset Nat.Primes} (c : S → ℕ) (m : ℕ)

theorem opposite_spectra_iff (t : ℝ) :
    thermalLosses c m t = thermalLosses c m (-t) ↔ t = 0 ∨ candidates c m = ∅ := by
  classical
  constructor
  · intro he
    rcases (candidates c m).eq_empty_or_nonempty with h | h
    · exact Or.inr h
    · left
      have hh := thermal_orientation c m h t
      rw [he,oriented,if_pos rfl] at hh
      exact hh.symm
  · rintro (rfl | h)
    · rw [neg_zero]
    · by_cases hw : Nonempty (State c m)
      · obtain ⟨w⟩ := hw
        have same := (no_candidates_iff c m).mp h
        rcases le_total 0 t with pos | neg
        · obtain ⟨hl,hu⟩ := thermal_edges c m w t pos
          rw [hl,hu,same]
        · obtain ⟨hl,hu⟩ := thermal_edges c m w (-t) (neg_nonneg.mpr neg)
          rw [neg_neg] at hu
          rw [hl,hu,same]
      · rw [thermal_empty c m hw,thermal_empty c m hw]

private theorem single_spectrum (hs : Subsingleton (State c m)) (t b : ℝ) :
    thermalLosses c m t = thermalLosses c m b := by
  by_cases hw : Nonempty (State c m)
  · obtain ⟨w⟩ := hw
    have all_eq (y : State c m) : energy (level y) = energy (level w) :=
      congrArg (fun z : State c m => energy (level z)) (hs.elim y w)
    have one (p : ℝ) : thermalLosses c m p = Set.range (fun _ : State c m => (0 : ℝ)) := by
      rw [thermalLosses,gibbs_losses _ p w (fun y => by rw [all_eq y])]
      apply congrArg Set.range
      funext y
      rw [all_eq y,sub_self,mul_zero]
    rw [one,one]
  · rw [thermal_empty c m hw,thermal_empty c m hw]

/-- For arbitrary capacities and particle counts, the only ambiguities of a peak-relative
spectrum are sectors with at most one state and sign reversal in a reflecting sector. -/
theorem equal_losses_iff (t b : ℝ) :
    thermalLosses c m t = thermalLosses c m b ↔
      Subsingleton (State c m) ∨ t=b ∨ (t = -b ∧ candidates c m = ∅) := by
  constructor
  · intro he
    by_cases hs : Subsingleton (State c m)
    · exact Or.inl hs
    right
    have hw : width c m ≠ 0 := fun h => hs ((width_zero_iff c m).mp h)
    have hh := congrArg sSup he
    rw [max_loss,max_loss] at hh
    have hab := (mul_left_injective₀ hw) hh
    rcases abs_eq_abs.mp hab with eq | eq
    · exact Or.inl eq
    · have rev : thermalLosses c m b = thermalLosses c m (-b) := eq ▸ he.symm
      rcases (opposite_spectra_iff c m b).mp rev with hb | h
      · left; linarith only [eq,hb]
      · exact Or.inr ⟨eq,h⟩
  · rintro (hs | rfl | ⟨rfl,h⟩)
    · exact single_spectrum c m hs t b
    · rfl
    · exact ((opposite_spectra_iff c m _).mpr (Or.inr h)).symm

theorem outgoing_identifiability (s w : ℂ) :
    outputSpectrum c m s = outputSpectrum c m w ↔
      Subsingleton (State c m) ∨ s.re = w.re ∨ (s.re+w.re = 1 ∧ candidates c m = ∅) := by
  rw [spectrum_eq,spectrum_eq,equal_losses_iff]
  have h₁ : 2*s.re-1 = 2*w.re-1 ↔ s.re=w.re := by constructor <;> intro h <;> linarith only [h]
  have h₂ : 2*s.re-1 = -(2*w.re-1) ↔ s.re+w.re=1 := by constructor <;> intro h <;> linarith only [h]
  rw [h₁,h₂]

#print axioms opposite_spectra_iff
#print axioms equal_losses_iff
#print axioms outgoing_identifiability

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Partial.Threshold
