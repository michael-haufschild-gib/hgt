import GaloisForLFunctions.HTGeometry.FiniteResponseLiouvillian
import GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH
import GaloisForLFunctions.RHTower.PrimeArchReflectionPositiveHankelRH
import GaloisForLFunctions.RHTower.TraceHankelSequenceCone

/-!
# Thermal Krylov moment values as source-Hankel producers

This file applies the finite Wightman transition-value identities from
`HTGeometry.ThermalKrylovMoments` to the trace-Hankel cone used by the prime--archimedean source
criterion.  It supplies two interfaces:

* an exact squared-energy-gap moment representation;
* a pointwise limit of finite thermal Krylov moment sequences.

The second interface is the physically useful thermodynamic/Krylov-limit form.  System sizes may
vary because every approximating sequence carries its own finite dimension.  Closedness of the
trace-Hankel cone then transports finite thermal positivity to the limiting source sequence.
-/

open Filter Topology

namespace RHTower

noncomputable section

open Polynomial

/-- A sequence realized by the even Liouvillian moments of a finite nonnegative transition
spectrum.  The finite dimension is part of the witness, so a family of such sequences may have
growing system size. -/
def FiniteThermalKrylovMomentSequence (m : ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ intensity : Fin d → Fin d → ℝ, ∃ energy : Fin d → ℝ,
    (∀ a b, 0 ≤ intensity a b) ∧
    m = HTGeometry.thermalEvenGapMoment intensity energy

/-- Every finite thermal even-gap sequence belongs to the full trace-Hankel cone. -/
theorem sequenceTraceHankelNonnegative_of_thermalEvenGapMoments
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) :
    SequenceTraceHankelNonnegative
      (HTGeometry.thermalEvenGapMoment intensity energy) := by
  intro p
  have heq : sequenceTraceHankel (HTGeometry.thermalEvenGapMoment intensity energy) p =
      HTGeometry.momentFunctional
        (HTGeometry.thermalEvenGapMoment intensity energy) (p ^ 2) := by
    rw [sequenceTraceHankel, HTGeometry.momentFunctional_eq_support_sum, pow_two]
  rw [heq]
  exact HTGeometry.momentFunctional_thermalEvenGapMoment_sq_nonneg
    intensity energy hintensity p

/-- The packaged finite thermal realization is a reusable producer for any trace-Hankel
consumer. -/
theorem finiteThermalKrylovMomentSequence_traceHankelNonnegative
    {m : ℕ → ℝ} (hm : FiniteThermalKrylovMomentSequence m) :
    SequenceTraceHankelNonnegative m := by
  obtain ⟨d, intensity, energy, hnonneg, rfl⟩ := hm
  exact sequenceTraceHankelNonnegative_of_thermalEvenGapMoments
    intensity energy hnonneg

/-- A pointwise/product-topology limit of finite thermal Krylov sequences remains in the complete
trace-Hankel cone.  This directly applies the closed-cone theorem to thermodynamic or growing
finite-section approximants. -/
theorem sequenceTraceHankelNonnegative_of_finiteThermalKrylov_tendsto
    (m : ℕ → ℕ → ℝ) (target : ℕ → ℝ)
    (hm : ∀ N, FiniteThermalKrylovMomentSequence (m N))
    (hconv : Tendsto m atTop (nhds target)) :
    SequenceTraceHankelNonnegative target := by
  apply isClosed_sequenceTraceHankelNonnegative.mem_of_tendsto hconv
  exact Filter.Eventually.of_forall fun N =>
    finiteThermalKrylovMomentSequence_traceHankelNonnegative (hm N)

/-- Exact equality of the source moments with nonnegative thermal squared-gap moments discharges
the source trace-Hankel hypothesis. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_thermalEvenGapMoments
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      HTGeometry.thermalEvenGapMoment intensity energy n) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  rw [show HTGeometry.momentFunctional normalizedPrimeArchMoment (p ^ 2) =
      HTGeometry.momentFunctional
        (HTGeometry.thermalEvenGapMoment intensity energy) (p ^ 2) by
    apply HTGeometry.momentFunctional_congr
    exact hmom]
  exact HTGeometry.momentFunctional_thermalEvenGapMoment_sq_nonneg
    intensity energy hintensity p

/-- **Exact thermal-value RH capstone.** -/
theorem riemannHypothesis_of_primeArchThermalEvenGapMoments
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      HTGeometry.thermalEvenGapMoment intensity energy n) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_thermalEvenGapMoments
      intensity energy hintensity hmom)

/-- The response-theory squared Liouvillian automatically supplies the self-adjoint observable and
its vacuum moments to the existing complex-observable source consumer. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_squaredTransitionLiouvillian
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      HTGeometry.thermalEvenGapMoment intensity energy n) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  apply primeArchSourceTraceHankelIntNonnegative_of_complexSelfAdjointObservable
    ((HTGeometry.transitionGapLiouvillian energy) ^ 2)
    (HTGeometry.thermalTransitionVector intensity)
    ((HTGeometry.transitionGapLiouvillian_isSelfAdjoint energy).pow 2)
  intro n
  rw [HTGeometry.inner_transitionVector_pow_squaredGapLiouvillian
    intensity energy hintensity]
  exact_mod_cast (hmom n).symm

/-- **Finite response-Liouvillian RH capstone.** -/
theorem riemannHypothesis_of_primeArchSquaredTransitionLiouvillian
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      HTGeometry.thermalEvenGapMoment intensity energy n) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_squaredTransitionLiouvillian
      intensity energy hintensity hmom)

/-- Pointwise convergence of growing finite thermal Krylov systems to the normalized source
moments discharges the source trace-Hankel hypothesis. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_finiteThermalKrylov_tendsto
    (m : ℕ → ℕ → ℝ)
    (hm : ∀ N, FiniteThermalKrylovMomentSequence (m N))
    (hconv : Tendsto m atTop (nhds normalizedPrimeArchMoment)) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  have hseq : SequenceTraceHankelNonnegative normalizedPrimeArchMoment :=
    sequenceTraceHankelNonnegative_of_finiteThermalKrylov_tendsto m _ hm hconv
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  exact hseq p

/-- **Thermodynamic-limit thermal Krylov RH capstone.**  The remaining input is the source-defined
pointwise value convergence, not a separate positivity hypothesis. -/
theorem riemannHypothesis_of_primeArchFiniteThermalKrylov_tendsto
    (m : ℕ → ℕ → ℝ)
    (hm : ∀ N, FiniteThermalKrylovMomentSequence (m N))
    (hconv : Tendsto m atTop (nhds normalizedPrimeArchMoment)) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_finiteThermalKrylov_tendsto m hm hconv)

end

end RHTower
