import GaloisForLFunctions.HTGeometry.BorelGrowthMonotone
import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction

/-!
# Good radii for the Borel growth lemma

The Borel lemma applies to a majorant that is monotone on all of `ℝ` and bounded below by one; the
Nevanlinna characteristic is only monotone on the positive reals and may dip below one.  Replacing it
by `max (T (max r 1)) 1` fixes both defects without changing the asymptotics.

Since the exceptional set has finite measure and every half-line has infinite measure, good radii —
those at which the majorant does not double across the step `1/T(r)` — exist beyond every bound.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

/-- The monotone majorant of the characteristic used by the Borel lemma. -/
noncomputable def charMajorant (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  max (ValueDistribution.characteristic f ⊤ (max r 1)) 1

theorem one_le_charMajorant (f : ℂ → ℂ) (r : ℝ) : 1 ≤ charMajorant f r := le_max_right _ _

theorem monotone_charMajorant {f : ℂ → ℂ} (hf : Meromorphic f) : Monotone (charMajorant f) := by
  intro a b hab
  refine max_le_max ?_ (le_refl 1)
  refine ValueDistribution.characteristic_monotoneOn hf ?_ ?_ (max_le_max hab (le_refl 1))
  · exact mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (le_max_right a 1))
  · exact mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one (le_max_right b 1))

/-- For `r ≥ 1` the majorant dominates the characteristic. -/
theorem characteristic_le_charMajorant {f : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r) :
    ValueDistribution.characteristic f ⊤ r ≤ charMajorant f r := by
  rw [charMajorant, max_eq_left hr]
  exact le_max_left _ _

/-- **Good radii exist beyond every bound.**  The Borel exceptional set has finite measure, while
every half-line has infinite measure. -/
theorem exists_good_radius {T : ℝ → ℝ} (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r) (a : ℝ) :
    ∃ r : ℝ, a ≤ r ∧ T (r + (T r)⁻¹) < 2 * T r := by
  by_contra hcon
  push_neg at hcon
  have hsub : Ici a ⊆ {r : ℝ | a ≤ r ∧ 2 * T r ≤ T (r + (T r)⁻¹)} := by
    intro r hr
    exact ⟨hr, hcon r hr⟩
  have hmeas := GaloisForLFunctions.Nevanlinna.borel_growth_monotone hmono hT1 a
  have hmono' := measure_mono (μ := volume) hsub
  rw [Real.volume_Ici] at hmono'
  have htop : (⊤ : ENNReal) ≤ 2 := le_trans hmono' hmeas
  simp at htop

/-- **A sequence of good radii tending to infinity.** -/
theorem exists_good_radius_seq {T : ℝ → ℝ} (hmono : Monotone T) (hT1 : ∀ r, 1 ≤ T r) :
    ∃ rn : ℕ → ℝ, Filter.Tendsto rn Filter.atTop Filter.atTop ∧
      ∀ n : ℕ, (n : ℝ) ≤ rn n ∧ T (rn n + (T (rn n))⁻¹) < 2 * T (rn n) := by
  choose g hg using fun n : ℕ => exists_good_radius hmono hT1 (n : ℝ)
  refine ⟨g, ?_, fun n => hg n⟩
  refine Filter.tendsto_atTop_mono (fun n : ℕ => (hg n).1) ?_
  exact tendsto_natCast_atTop_atTop

end GaloisForLFunctions.HTGeometry
