import GaloisForLFunctions.RHTower.WeilLogShiftJointCharacteristic
import GaloisForLFunctions.HTGeometry.PaperFourierLawMeasure

/-! Canonical edge weights define genuine finite probability laws on every measurable target. -/

open MeasureTheory
open GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped BigOperators

noncomputable section
namespace RHTower

def finiteWeilCanonicalEdgeLaw (r k : ℕ) : Law (Fin (r + 1)) :=
  ⟨finiteWeilCanonicalEdgeMass r k,
    ⟨fun i => (finiteWeilCanonicalEdgeMass_pos r k i).le, finiteWeilCanonicalEdgeMass_sum r k⟩⟩

def finiteWeilCanonicalObservableLaw {β : Type*} [MeasurableSpace β]
    (r k : ℕ) (f : Fin (r + 1) → β) : ProbabilityMeasure β :=
  (finiteWeilCanonicalEdgeLaw r k).atomicProbability f

theorem finiteWeilCanonicalObservableLaw_integrable {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β] (r k : ℕ) (f : Fin (r + 1) → β) (g : β → ℝ) :
    Integrable g (finiteWeilCanonicalObservableLaw r k f : Measure β) :=
  Law.integrable_atomicProbability (finiteWeilCanonicalEdgeLaw r k) f g

theorem finiteWeilCanonicalObservableLaw_integral_real {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β] (r k : ℕ) (f : Fin (r + 1) → β) (g : β → ℝ) :
    (∫ x, g x ∂(finiteWeilCanonicalObservableLaw r k f : Measure β)) =
      ∑ i, finiteWeilCanonicalEdgeMass r k i * g (f i) :=
  Law.integral_atomicProbability (finiteWeilCanonicalEdgeLaw r k) f g

theorem finiteWeilCanonicalObservableLaw_integral_complex {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β] (r k : ℕ) (f : Fin (r + 1) → β) (g : β → ℂ) :
    (∫ x, g x ∂(finiteWeilCanonicalObservableLaw r k f : Measure β)) =
      ∑ i, (finiteWeilCanonicalEdgeMass r k i : ℂ) * g (f i) := by
  change (∫ x, g x ∂(∑ i, ENNReal.ofReal (finiteWeilCanonicalEdgeMass r k i) • Measure.dirac (f i))) = _
  rw [integral_finsetSum_measure (fun _ _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  simp_rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (finiteWeilCanonicalEdgeMass_pos r k _).le, Complex.real_smul]

end RHTower
