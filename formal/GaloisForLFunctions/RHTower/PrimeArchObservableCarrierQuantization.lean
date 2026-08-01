import GaloisForLFunctions.HTGeometry.ObservablePushforwardHankelStrict
import GaloisForLFunctions.RHTower.PrimeArchMomentRepresentationRigidity
import GaloisForLFunctions.RHTower.PrimeArchThetaAtomMoments

/-!
# Quantization of observable Route D carriers

Any positive hidden-space observable that represents every normalized prime--archimedean moment
has a completely prescribed pushforward: the canonical compact atomic Xi-divisor measure.  Thus a
reporter with null level sets cannot be a Route D producer.  In particular, no injective reporter
on the literal atomless theta-cusp density can represent the complete moment tower.

The result is unconditional.  A supplied observable witness first implies RH through the existing
moment-representation theorem; only then does unrestricted moment determinacy identify its law.
-/

open MeasureTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- A positive hidden-space measure and one measurable real reporter represent every canonical
prime--archimedean moment. -/
def IsPrimeArchObservableWitness
    (mu : Measure X) (node : X → ℝ) : Prop :=
  Measurable node ∧
    (∀ k, normalizedPrimeArchMoment k = ∫ x, node x ^ k ∂mu) ∧
    ∀ k, Integrable (fun x => node x ^ k) mu

/-- Observable moments and their integrability turn the reporter's pushforward into an
unrestricted Route D moment witness. -/
theorem IsPrimeArchObservableWitness.pushforward_isMomentWitness
    {mu : Measure X} {node : X → ℝ}
    (h : IsPrimeArchObservableWitness mu node) :
    IsPrimeArchMomentWitness
      (HTGeometry.observablePushforwardMeasure mu node) := by
  refine ⟨?_, ?_⟩
  · intro k
    rw [HTGeometry.integral_pow_observablePushforwardMeasure mu h.1 k]
    exact h.2.1 k
  · intro k
    exact HTGeometry.integrable_pow_observablePushforwardMeasure mu h.1 (h.2.2 k)

/-- **Observable-law rigidity.** Every complete positive Route D reporter has exactly the
canonical compact atomic Xi-divisor pushforward, with no hidden-space or support hypothesis. -/
theorem IsPrimeArchObservableWitness.pushforward_eq_primeArchXiCompactMomentMeasure
    {mu : Measure X} {node : X → ℝ}
    (h : IsPrimeArchObservableWitness mu node) :
    HTGeometry.observablePushforwardMeasure mu node =
      primeArchXiCompactMomentMeasure :=
  h.pushforward_isMomentWitness.eq_primeArchXiCompactMomentMeasure

/-- **Exact fibre quantization.** Every Borel fibre packet of a successful reporter has the mass
prescribed by the canonical Xi-divisor moment measure. -/
theorem IsPrimeArchObservableWitness.measure_preimage_eq_primeArchXiCompactMomentMeasure
    {mu : Measure X} {node : X → ℝ}
    (h : IsPrimeArchObservableWitness mu node)
    {A : Set ℝ} (hA : MeasurableSet A) :
    mu (node ⁻¹' A) = primeArchXiCompactMomentMeasure A := by
  calc
    mu (node ⁻¹' A) = HTGeometry.observablePushforwardMeasure mu node A := by
      rw [HTGeometry.observablePushforwardMeasure, Measure.map_apply h.1 hA]
    _ = primeArchXiCompactMomentMeasure A := by
      rw [h.pushforward_eq_primeArchXiCompactMomentMeasure]

/-- Every enumerated canonical Xi thermal node carries strictly positive singleton mass.  Node
collisions can only increase this mass. -/
theorem primeArchXiCompactMomentMeasure_singleton_pos (j : ℕ) :
    0 < primeArchXiCompactMomentMeasure
      {xiThermalNode (xiThermalEnumeration j)} := by
  let family : ℕ → Measure ℝ := fun k =>
    ENNReal.ofReal (xiThermalNode (xiThermalEnumeration k)) •
      Measure.dirac (xiThermalNode (xiThermalEnumeration k))
  have hmass :
      0 < family j {xiThermalNode (xiThermalEnumeration j)} := by
    simp [family, ENNReal.ofReal_pos.mpr (xiThermalNode_pos _)]
  exact hmass.trans_le
    ((Measure.le_sum family j) {xiThermalNode (xiThermalEnumeration j)})

/-- Every successful reporter has a positive-measure level set above every enumerated canonical
Xi thermal node.  This is the source-side quantization forced by the complete moment tower. -/
theorem IsPrimeArchObservableWitness.measure_levelSet_xiThermalNode_pos
    {mu : Measure X} {node : X → ℝ}
    (h : IsPrimeArchObservableWitness mu node) (j : ℕ) :
    0 < mu (node ⁻¹' {xiThermalNode (xiThermalEnumeration j)}) := by
  rw [h.measure_preimage_eq_primeArchXiCompactMomentMeasure
    (measurableSet_singleton (xiThermalNode (xiThermalEnumeration j)))]
  exact primeArchXiCompactMomentMeasure_singleton_pos j

/-- The canonical compact Xi moment carrier is genuinely atomic. -/
theorem not_nullSingletonClass_primeArchXiCompactMomentMeasure :
    ¬ NullSingletonClass primeArchXiCompactMomentMeasure := by
  intro hno
  letI : NullSingletonClass primeArchXiCompactMomentMeasure := hno
  exact (ne_of_gt (primeArchXiCompactMomentMeasure_singleton_pos 0))
    (measure_singleton (xiThermalNode (xiThermalEnumeration 0)))

/-- **Diffuse-reporter no-go.** A reporter all of whose level sets are null cannot represent the
complete Route D moment tower. -/
theorem not_isPrimeArchObservableWitness_of_forall_measure_levelSet_eq_zero
    {mu : Measure X} {node : X → ℝ}
    (hlevel : ∀ y, mu (node ⁻¹' {y}) = 0) :
    ¬ IsPrimeArchObservableWitness mu node := by
  intro h
  have heq := h.measure_preimage_eq_primeArchXiCompactMomentMeasure
    (measurableSet_singleton (xiThermalNode (xiThermalEnumeration 0)))
  rw [hlevel] at heq
  exact (ne_of_gt (primeArchXiCompactMomentMeasure_singleton_pos 0)) heq.symm

/-- **Countable-fibre no-go.** On an atomless hidden source, a reporter with countable fibres
cannot represent the complete Route D moment tower.  Thus every successful reporter has an
uncountable positive-measure fibre above every canonical thermal node. -/
theorem not_isPrimeArchObservableWitness_of_countable_levelSets
    {mu : Measure X} [NullSingletonClass mu] {node : X → ℝ}
    (hcountable : ∀ y, (node ⁻¹' {y}).Countable) :
    ¬ IsPrimeArchObservableWitness mu node :=
  not_isPrimeArchObservableWitness_of_forall_measure_levelSet_eq_zero fun y =>
    (hcountable y).measure_zero mu

/-- An injective reporter on an atomless hidden source has null level sets, so it cannot represent
the complete Route D tower. -/
theorem not_isPrimeArchObservableWitness_of_injective_of_nullSingleton
    {mu : Measure X} [NullSingletonClass mu] {node : X → ℝ}
    (hinj : Function.Injective node) :
    ¬ IsPrimeArchObservableWitness mu node := by
  apply not_isPrimeArchObservableWitness_of_forall_measure_levelSet_eq_zero
  intro y
  by_cases hy : y ∈ Set.range node
  · obtain ⟨x, rfl⟩ := hy
    have hpre : node ⁻¹' {node x} = {x} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact hinj.eq_iff
    rw [hpre, measure_singleton]
  · have hpre : node ⁻¹' {y} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro hx
      exact hy ⟨x, hx⟩
    rw [hpre, measure_empty]

/-- Literal positive theta-cusp density, viewed as a measure on the positive half-line. -/
def thetaCuspContinuousSourceMeasure : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun x => ENNReal.ofReal (2 * thetaCuspFullSource x))

/-- The theta-cusp source measure is absolutely continuous with respect to Lebesgue measure. -/
theorem thetaCuspContinuousSourceMeasure_absolutelyContinuous_volume :
    thetaCuspContinuousSourceMeasure ≪ (volume : Measure ℝ) := by
  unfold thetaCuspContinuousSourceMeasure
  exact (withDensity_absolutelyContinuous _ _).trans
    Measure.restrict_le_self.absolutelyContinuous

/-- The theta-cusp density is atomless because it is absolutely continuous with respect to
restricted Lebesgue measure. -/
instance thetaCuspContinuousSourceMeasure_nullSingleton :
    NullSingletonClass thetaCuspContinuousSourceMeasure := by
  unfold thetaCuspContinuousSourceMeasure
  infer_instance

/-- **Theta-fibre plateau law.** Every successful deterministic theta reporter has a
positive-Lebesgue-measure level set above every enumerated canonical thermal node. -/
theorem IsPrimeArchObservableWitness.volume_levelSet_xiThermalNode_pos
    {node : ℝ → ℝ} (h : IsPrimeArchObservableWitness thetaCuspContinuousSourceMeasure node)
    (j : ℕ) :
    0 < volume (node ⁻¹' {xiThermalNode (xiThermalEnumeration j)}) := by
  have hsource := h.measure_levelSet_xiThermalNode_pos j
  apply lt_of_not_ge
  intro hle
  have hvol : volume (node ⁻¹' {xiThermalNode (xiThermalEnumeration j)}) = 0 :=
    bot_unique hle
  exact (ne_of_gt hsource)
    (thetaCuspContinuousSourceMeasure_absolutelyContinuous_volume hvol)

/-- No reporter whose level sets are all Lebesgue-null can produce the complete moment carrier
from the literal theta-cusp density. -/
theorem not_isPrimeArchObservableWitness_thetaCusp_of_forall_volume_levelSet_eq_zero
    {node : ℝ → ℝ} (hlevel : ∀ y, volume (node ⁻¹' {y}) = 0) :
    ¬ IsPrimeArchObservableWitness thetaCuspContinuousSourceMeasure node := by
  intro h
  exact (ne_of_gt (h.volume_levelSet_xiThermalNode_pos 0))
    (hlevel (xiThermalNode (xiThermalEnumeration 0)))

/-- No countable-to-one deterministic observable of the literal positive theta-cusp density
produces the complete prime--archimedean moment carrier. -/
theorem not_isPrimeArchObservableWitness_thetaCusp_of_countable_levelSets
    {node : ℝ → ℝ} (hcountable : ∀ y, (node ⁻¹' {y}).Countable) :
    ¬ IsPrimeArchObservableWitness thetaCuspContinuousSourceMeasure node :=
  not_isPrimeArchObservableWitness_of_countable_levelSets hcountable

/-- **Theta-source specialization.** No injective deterministic observable of the literal
positive theta-cusp density produces the complete prime--archimedean moment carrier. -/
theorem not_isPrimeArchObservableWitness_thetaCusp_of_injective
    {node : ℝ → ℝ} (hinj : Function.Injective node) :
    ¬ IsPrimeArchObservableWitness thetaCuspContinuousSourceMeasure node :=
  not_isPrimeArchObservableWitness_of_injective_of_nullSingleton hinj

end

end RHTower
