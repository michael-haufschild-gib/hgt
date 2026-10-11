import GaloisForLFunctions.RHTower.WeilLogShiftObservableLaw
import GaloisForLFunctions.HTGeometry.KantorovichRubinsteinDuality

/-! Shared finite edge weights supply actual couplings on arbitrary measurable targets. -/

open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped BigOperators

noncomputable section
namespace RHTower

theorem finiteWeilCanonicalObservableLaw_map {β γ : Type*}
    [MeasurableSpace β] [MeasurableSpace γ] (r k : ℕ)
    (f : Fin (r + 1) → β) (g : β → γ) (hg : Measurable g) :
    Measure.map g (finiteWeilCanonicalObservableLaw r k f : Measure β) =
      (finiteWeilCanonicalObservableLaw r k (g ∘ f) : Measure γ) := by
  change Measure.map g (∑ i, ENNReal.ofReal (finiteWeilCanonicalEdgeMass r k i) •
    Measure.dirac (f i)) =
      ∑ i, ENNReal.ofReal (finiteWeilCanonicalEdgeMass r k i) • Measure.dirac (g (f i))
  rw [Measure.map_finset_sum hg.aemeasurable]
  simp_rw [Measure.map_smul, Measure.map_dirac' hg]

def finiteWeilCanonicalObservableCoupling {β : Type*} [MeasurableSpace β]
    (r k : ℕ) (f g : Fin (r + 1) → β) : ProbabilityMeasure (β × β) :=
  finiteWeilCanonicalObservableLaw r k (fun i => (f i, g i))

theorem finiteWeilCanonicalObservableCoupling_fst {β : Type*} [MeasurableSpace β]
    (r k : ℕ) (f g : Fin (r + 1) → β) :
    Measure.map Prod.fst (finiteWeilCanonicalObservableCoupling r k f g : Measure (β × β)) =
      (finiteWeilCanonicalObservableLaw r k f : Measure β) :=
  finiteWeilCanonicalObservableLaw_map r k (fun i => (f i, g i)) Prod.fst measurable_fst

theorem finiteWeilCanonicalObservableCoupling_snd {β : Type*} [MeasurableSpace β]
    (r k : ℕ) (f g : Fin (r + 1) → β) :
    Measure.map Prod.snd (finiteWeilCanonicalObservableCoupling r k f g : Measure (β × β)) =
      (finiteWeilCanonicalObservableLaw r k g : Measure β) :=
  finiteWeilCanonicalObservableLaw_map r k (fun i => (f i, g i)) Prod.snd measurable_snd

theorem finiteWeilCanonicalObservableCoupling_isCoupling {β : Type*} [MeasurableSpace β]
    (r k : ℕ) (f g : Fin (r + 1) → β) :
    IsCoupling (finiteWeilCanonicalObservableLaw r k f : Measure β)
      (finiteWeilCanonicalObservableLaw r k g : Measure β)
      (finiteWeilCanonicalObservableCoupling r k f g : Measure (β × β)) :=
  ⟨finiteWeilCanonicalObservableCoupling_fst r k f g,
    finiteWeilCanonicalObservableCoupling_snd r k f g⟩

theorem finiteWeilCanonicalObservableCoupling_cost {β : Type*}
    [MetricSpace β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (r k : ℕ) (f g : Fin (r + 1) → β) :
    (∫ p, dist p.1 p.2 ∂(finiteWeilCanonicalObservableCoupling r k f g : Measure (β × β))) =
      ∑ i, finiteWeilCanonicalEdgeMass r k i * dist (f i) (g i) :=
  finiteWeilCanonicalObservableLaw_integral_real r k (fun i => (f i, g i))
    (fun p => dist p.1 p.2)

end RHTower
