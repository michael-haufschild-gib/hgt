import GaloisForLFunctions.BiScaleUncertainty.MultiChainToeplitzGramCoupling
import GaloisForLFunctions.HilbertMetric.Correlation.CompactSourceDeletion

/-!
# Stability of translation correlations under exceptional deletions

A translated source packet is a genuine compact source. Removing arbitrary
translations therefore obeys the square-integral deletion law, while all
cross-chain interactions remain present in the original Gram energy.
-/

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty
open HilbertMetric
noncomputable section
variable {ι : Type*}

/-- The compact source representing the complete translation Gram. -/
def translationPacket (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => ∑ i ∈ s, w i * f (u + t i),
    continuous_finsetSum _ fun i _ =>
      continuous_const.mul (f.continuous.comp (continuous_add_const _))⟩, by
    have hs := HasCompactSupport.finset_sum (s := s)
      (f := fun i u => w i * f (u + t i))
      (fun i _ => (f.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (t i))).mul_left)
    convert hs using 1
    ext u
    simp only [Finset.sum_apply]⟩

theorem compactEnergy_translationPacket (f : C_c(ℝ, ℝ)) (s : Finset ι) (w t : ι → ℝ) :
    compactEnergy (translationPacket f s w t) = translationGramEnergy f s w t :=
  (translationGramEnergy_eq_integral f s w t).symm

/-- Deleting translations is subtraction of their actual compact source. -/
theorem translationPacket_sdiff [DecidableEq ι] (f : C_c(ℝ, ℝ))
    (s e : Finset ι) (w t : ι → ℝ) :
    translationPacket f (s \ e) w t =
      translationPacket f s w t - translationPacket f (s ∩ e) w t := by
  ext u
  change (∑ i ∈ s \ e, w i * f (u + t i)) =
    (∑ i ∈ s, w i * f (u + t i)) - ∑ i ∈ s ∩ e, w i * f (u + t i)
  have h := Finset.sum_inter_add_sum_sdiff s e (fun i => w i * f (u + t i))
  linarith only [h]

/-- Centered error for the complete Toeplitz Gram after any finite deletion. -/
theorem translationGramEnergy_deletion_centered [DecidableEq ι]
    (f : C_c(ℝ, ℝ)) (s e : Finset ι) (w t : ι → ℝ) :
    (translationGramEnergy f (s \ e) w t - translationGramEnergy f s w t -
      translationGramEnergy f (s ∩ e) w t) ^ 2 ≤
      4 * translationGramEnergy f s w t * translationGramEnergy f (s ∩ e) w t := by
  have h := compactEnergy_deletion_centered (translationPacket f s w t)
    (translationPacket f (s ∩ e) w t)
  rw [← translationPacket_sdiff, compactEnergy_translationPacket,
    compactEnergy_translationPacket, compactEnergy_translationPacket] at h
  exact h

/-- The exceptional Gram and its geometric-mean interaction pay the entire error. -/
theorem translationGramEnergy_deletion_error [DecidableEq ι]
    (f : C_c(ℝ, ℝ)) (s e : Finset ι) (w t : ι → ℝ) :
    |translationGramEnergy f (s \ e) w t - translationGramEnergy f s w t| ≤
      translationGramEnergy f (s ∩ e) w t +
        2 * Real.sqrt (translationGramEnergy f s w t * translationGramEnergy f (s ∩ e) w t) := by
  have h := compactEnergy_deletion_error (translationPacket f s w t)
    (translationPacket f (s ∩ e) w t)
  rw [← translationPacket_sdiff, compactEnergy_translationPacket,
    compactEnergy_translationPacket, compactEnergy_translationPacket] at h
  exact h

end
end GaloisForLFunctions.BiScaleUncertainty

#print axioms GaloisForLFunctions.BiScaleUncertainty.translationGramEnergy_deletion_centered
#print axioms GaloisForLFunctions.BiScaleUncertainty.translationGramEnergy_deletion_error
