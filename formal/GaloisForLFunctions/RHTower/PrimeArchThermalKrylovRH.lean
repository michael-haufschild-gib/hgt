import GaloisForLFunctions.HTGeometry.FiniteResponseLiouvillian
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman
import GaloisForLFunctions.HTGeometry.ThermalKrylovDeterminant
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

/-- A moment sequence realized by canonical finite-temperature Wightman values.  Writing the
dimension as `d + 1` makes nonemptiness, and hence partition-function positivity, structural. -/
def FiniteKMSWightmanMomentSequence (m : ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ β : ℝ, ∃ energy : Fin (d + 1) → ℝ,
    ∃ amplitude : Fin (d + 1) → Fin (d + 1) → ℂ,
      m = HTGeometry.thermalEvenGapMoment
        (HTGeometry.finiteKMSWightmanTransitionIntensity β energy amplitude) energy

/-- Canonical finite Wightman realization discharges the arbitrary nonnegative-intensity witness
in the generic finite thermal interface. -/
theorem finiteKMSWightmanMomentSequence_finiteThermalKrylov
    {m : ℕ → ℝ} (hm : FiniteKMSWightmanMomentSequence m) :
    FiniteThermalKrylovMomentSequence m := by
  obtain ⟨d, β, energy, amplitude, rfl⟩ := hm
  exact ⟨d + 1, _, _,
    HTGeometry.finiteKMSWightmanTransitionIntensity_nonneg β energy amplitude, rfl⟩

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
  rw [show HTGeometry.momentFunctional normalizedPrimeArchMoment
        ((p.map (Int.castRingHom ℝ)) ^ 2) =
      HTGeometry.momentFunctional
        (HTGeometry.thermalEvenGapMoment intensity energy)
          ((p.map (Int.castRingHom ℝ)) ^ 2) by
    exact HTGeometry.momentFunctional_congr hmom _]
  exact HTGeometry.momentFunctional_thermalEvenGapMoment_sq_nonneg
    intensity energy hintensity (p.map (Int.castRingHom ℝ))

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

/-- **No fixed finite thermal system can realize the complete source moment tower.**  Its Krylov
Gram determinant vanishes above the finite transition-space dimension.  Exact equality with every
source moment would imply the existing strict source determinant hierarchy, a contradiction.

Thus the physically live thermal route is necessarily a growing-system/thermodynamic limit, not
one fixed finite KMS model. -/
theorem not_primeArchExactFiniteThermalEvenGapMoments
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) :
    ¬ (∀ n, normalizedPrimeArchMoment n =
      HTGeometry.thermalEvenGapMoment intensity energy n) := by
  intro hmom
  let N := Fintype.card α * Fintype.card α + 1
  have hN : Fintype.card α * Fintype.card α < N := by
    dsimp only [N]
    exact Nat.lt_succ_self _
  have hzero :
      (HTGeometry.momentHankelMatrix
        (HTGeometry.thermalEvenGapMoment intensity energy) N).det = 0 :=
    HTGeometry.det_thermalEvenGapMoment_eq_zero_of_card_sq_lt
      intensity energy hintensity N hN
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_primeArchThermalEvenGapMoments
      intensity energy hintensity hmom
  have hstrict : PrimeArchSourceMomentHankelDeterminantsPositive :=
    primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mpr hRH
  have hmatrix : primeArchSourceMomentHankelMatrix N =
      HTGeometry.momentHankelMatrix
        (HTGeometry.thermalEvenGapMoment intensity energy) N := by
    ext i j
    exact hmom ((i : ℕ) + (j : ℕ))
  have hpos := hstrict N
  rw [hmatrix, hzero] at hpos
  exact (lt_irrefl 0) hpos

/-- Canonical KMS/Wightman weights remove the separate transition-intensity positivity hypothesis
from the exact source-moment bridge. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_finiteKMSWightmanMoments
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      HTGeometry.thermalEvenGapMoment
        (HTGeometry.finiteKMSWightmanTransitionIntensity β energy amplitude) energy n) :
    PrimeArchSourceTraceHankelIntNonnegative :=
  primeArchSourceTraceHankelIntNonnegative_of_thermalEvenGapMoments
    _ energy
    (HTGeometry.finiteKMSWightmanTransitionIntensity_nonneg β energy amplitude) hmom

/-- **Canonical finite-temperature Wightman RH capstone.**  Its only mathematical input beyond the
finite quantum data is the exact comparison with the normalized source values. -/
theorem riemannHypothesis_of_primeArchFiniteKMSWightmanMoments
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      HTGeometry.thermalEvenGapMoment
        (HTGeometry.finiteKMSWightmanTransitionIntensity β energy amplitude) energy n) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_finiteKMSWightmanMoments
      β energy amplitude hmom)

/-- Canonical finite KMS/Wightman data inherit the same finite-rank obstruction: no fixed finite
Hamiltonian and amplitude can match the complete source moment tower in every degree. -/
theorem not_primeArchExactFiniteKMSWightmanMoments
    {α : Type*} [Fintype α] [Nonempty α]
    (β : ℝ) (energy : α → ℝ) (amplitude : α → α → ℂ) :
    ¬ (∀ n, normalizedPrimeArchMoment n =
      HTGeometry.thermalEvenGapMoment
        (HTGeometry.finiteKMSWightmanTransitionIntensity β energy amplitude) energy n) :=
  not_primeArchExactFiniteThermalEvenGapMoments
    (HTGeometry.finiteKMSWightmanTransitionIntensity β energy amplitude) energy
    (HTGeometry.finiteKMSWightmanTransitionIntensity_nonneg β energy amplitude)

/-- The normalized source sequence is not one packaged fixed finite thermal Krylov sequence. -/
theorem not_finiteThermalKrylovMomentSequence_normalizedPrimeArchMoment :
    ¬ FiniteThermalKrylovMomentSequence normalizedPrimeArchMoment := by
  rintro ⟨d, intensity, energy, hintensity, hmoment⟩
  exact not_primeArchExactFiniteThermalEvenGapMoments intensity energy hintensity
    (fun n => congrFun hmoment n)

/-- The normalized source sequence is likewise not one packaged fixed finite KMS/Wightman
sequence.  Only a limit of growing such sequences can remain a live producer. -/
theorem not_finiteKMSWightmanMomentSequence_normalizedPrimeArchMoment :
    ¬ FiniteKMSWightmanMomentSequence normalizedPrimeArchMoment := by
  rintro ⟨d, β, energy, amplitude, hmoment⟩
  exact not_primeArchExactFiniteKMSWightmanMoments β energy amplitude
    (fun n => congrFun hmoment n)

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
  rw [← sequenceTraceHankel_eq_momentFunctional]
  exact hseq (p.map (Int.castRingHom ℝ))

/-- **Thermodynamic-limit thermal Krylov RH capstone.**  The remaining input is the source-defined
pointwise value convergence, not a separate positivity hypothesis. -/
theorem riemannHypothesis_of_primeArchFiniteThermalKrylov_tendsto
    (m : ℕ → ℕ → ℝ)
    (hm : ∀ N, FiniteThermalKrylovMomentSequence (m N))
    (hconv : Tendsto m atTop (nhds normalizedPrimeArchMoment)) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_finiteThermalKrylov_tendsto m hm hconv)

/-- **Canonical Wightman thermodynamic-limit RH capstone.**  Canonical finite KMS systems
automatically meet every finite positivity hypothesis; only pointwise convergence to the source
values remains. -/
theorem riemannHypothesis_of_primeArchFiniteKMSWightman_tendsto
    (m : ℕ → ℕ → ℝ)
    (hm : ∀ N, FiniteKMSWightmanMomentSequence (m N))
    (hconv : Tendsto m atTop (nhds normalizedPrimeArchMoment)) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchFiniteThermalKrylov_tendsto m
    (fun N => finiteKMSWightmanMomentSequence_finiteThermalKrylov (hm N)) hconv

end

end RHTower
