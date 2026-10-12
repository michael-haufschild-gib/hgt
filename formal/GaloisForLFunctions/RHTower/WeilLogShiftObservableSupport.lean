import GaloisForLFunctions.RHTower.WeilLogShiftObservableLaw

/-! Positive canonical edge masses turn almost-everywhere predicates into finite pointwise tests. -/

open MeasureTheory
open scoped BigOperators ENNReal

namespace RHTower

theorem finiteWeilCanonicalObservableLaw_ae_iff {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (r k : ℕ) (f : Fin (r + 1) → β) (p : β → Prop) :
    (∀ᵐ x ∂(finiteWeilCanonicalObservableLaw r k f : Measure β), p x) ↔
      ∀ i, p (f i) := by
  change (∀ᵐ x ∂(∑ i, ENNReal.ofReal (finiteWeilCanonicalEdgeMass r k i) •
    Measure.dirac (f i)), p x) ↔ _
  simp only [ae_finsetSum_measure_iff, Finset.mem_univ, true_implies]
  apply forall_congr'
  intro i
  have hmass : ENNReal.ofReal (finiteWeilCanonicalEdgeMass r k i) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (finiteWeilCanonicalEdgeMass_pos r k i)).ne'
  simp only [Measure.ae_ennreal_smul_measure_iff hmass, ae_dirac_eq, Filter.eventually_pure]

end RHTower
