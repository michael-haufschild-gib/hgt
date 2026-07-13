import GaloisForLFunctions.HTGeometry.ReflectionPositiveHankel
import GaloisForLFunctions.RHTower.PrimeArchMomentMeasureRH
import GaloisForLFunctions.RHTower.TraceHankelSequenceCone

/-!
# Reflection-positive quantum moment criteria for RH

The normalized prime--archimedean moments already determine every Xi trace-Hankel test through
the fixed prime--Gamma source germ.  This file supplies the quantum/operator-facing producer for
that consumer: a real or complex reflection-positive Gram orbit makes the trace-Hankel value a
squared norm.  Equivalently, it is enough to realize the moments as vacuum moments of a bounded
self-adjoint observable.

These are static value-relation criteria.  They do not posit a Hamiltonian evolution, and they do
not require the representing measure or monomial-integrability hypotheses of
`PrimeArchMomentMeasureRH`.
-/

namespace RHTower

noncomputable section

/-! ## Abstract sequence cone -/

/-- A real reflection-positive Gram realization places a sequence in the full trace-Hankel cone. -/
theorem sequenceTraceHankelNonnegative_of_reflectionPositiveGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : ℕ → ℝ) (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) = m (i + j)) :
    SequenceTraceHankelNonnegative m := by
  intro p
  have heq : sequenceTraceHankel m p =
      HTGeometry.momentFunctional m (p ^ 2) := by
    rw [sequenceTraceHankel, HTGeometry.momentFunctional_eq_support_sum, pow_two]
  rw [heq]
  exact HTGeometry.momentFunctional_pow_two_nonneg_of_reflectionPositiveGram
    m v hgram p

/-- A complex reflection-positive Gram realization also places the underlying real sequence in
the full trace-Hankel cone. -/
theorem sequenceTraceHankelNonnegative_of_complexReflectionPositiveGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (m : ℕ → ℝ) (v : ℕ → E)
    (hgram : ∀ i j, inner ℂ (v i) (v j) = (m (i + j) : ℂ)) :
    SequenceTraceHankelNonnegative m := by
  intro p
  have heq : sequenceTraceHankel m p =
      HTGeometry.momentFunctional m (p ^ 2) := by
    rw [sequenceTraceHankel, HTGeometry.momentFunctional_eq_support_sum, pow_two]
  rw [heq]
  exact HTGeometry.momentFunctional_pow_two_nonneg_of_complexReflectionPositiveGram
    m v hgram p

/-! ## Reflection-positive prime--archimedean Gram criteria -/

/-- A real reflected Gram orbit for the canonical source moments discharges the sole source
trace-Hankel positivity hypothesis. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_reflectionPositiveGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) =
      normalizedPrimeArchMoment (i + j)) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  exact HTGeometry.momentFunctional_pow_two_nonneg_of_reflectionPositiveGram
    normalizedPrimeArchMoment v hgram _

/-- **Real reflection-positive RH capstone.** -/
theorem riemannHypothesis_of_primeArchReflectionPositiveGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) =
      normalizedPrimeArchMoment (i + j)) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_reflectionPositiveGram v hgram)

/-- A complex reflected Gram orbit for the canonical source moments discharges source
trace-Hankel positivity.  This is the interface native to the complex Sonin spaces. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_complexReflectionPositiveGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ℕ → E)
    (hgram : ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ)) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  exact HTGeometry.momentFunctional_pow_two_nonneg_of_complexReflectionPositiveGram
    normalizedPrimeArchMoment v hgram _

/-- **Complex reflection-positive RH capstone.** -/
theorem riemannHypothesis_of_primeArchComplexReflectionPositiveGram
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : ℕ → E)
    (hgram : ∀ i j, inner ℂ (v i) (v j) =
      (normalizedPrimeArchMoment (i + j) : ℂ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_complexReflectionPositiveGram v hgram)

/-! ## Strict reflected Gram criteria -/

/-- Finite linear independence of the reflected source packets discharges the stronger leading
Hankel-determinant hierarchy, without constructing a representing measure or proving that its
support is infinite. -/
theorem primeArchSourceMomentHankelDeterminantsPositive_of_reflectionPositiveGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) =
      normalizedPrimeArchMoment (i + j))
    (hli : ∀ n, LinearIndependent ℝ (fun i : Fin n => v (i : ℕ))) :
    PrimeArchSourceMomentHankelDeterminantsPositive := by
  intro n
  have hmatrix : primeArchSourceMomentHankelMatrix n =
      HTGeometry.momentHankelMatrix normalizedPrimeArchMoment n := by
    ext i j
    rfl
  rw [hmatrix]
  exact HTGeometry.det_momentHankelMatrix_pos_of_reflectionPositiveGram
    normalizedPrimeArchMoment v hgram n (hli n)

/-- The linearly independent reflected-orbit interface also proves RH through the strict source
determinant criterion. -/
theorem riemannHypothesis_of_primeArchStrictReflectionPositiveGram
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℕ → E)
    (hgram : ∀ i j, inner ℝ (v i) (v j) =
      normalizedPrimeArchMoment (i + j))
    (hli : ∀ n, LinearIndependent ℝ (fun i : Fin n => v (i : ℕ))) :
    RiemannHypothesis :=
  primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mp
    (primeArchSourceMomentHankelDeterminantsPositive_of_reflectionPositiveGram v hgram hli)

/-- A bounded self-adjoint observable whose finite Krylov packets at `omega` are linearly
independent supplies every strict source Hankel determinant.  The independence hypothesis is the
finite-degree statement that no nonzero polynomial annihilates the state orbit. -/
theorem primeArchSourceMomentHankelDeterminantsPositive_of_selfAdjointObservableOrbit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (omega : E) (hA : IsSelfAdjoint A)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      inner ℝ omega ((A ^ n) omega))
    (hli : ∀ n, LinearIndependent ℝ
      (fun i : Fin n => (A ^ (i : ℕ)) omega)) :
    PrimeArchSourceMomentHankelDeterminantsPositive := by
  apply primeArchSourceMomentHankelDeterminantsPositive_of_reflectionPositiveGram
    (fun n => (A ^ n) omega) _ hli
  intro i j
  rw [HTGeometry.inner_selfAdjointObservableOrbit A omega hA]
  exact (hmom (i + j)).symm

/-- **Strict real observable RH capstone.** -/
theorem riemannHypothesis_of_primeArchSelfAdjointObservableOrbit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (omega : E) (hA : IsSelfAdjoint A)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      inner ℝ omega ((A ^ n) omega))
    (hli : ∀ n, LinearIndependent ℝ
      (fun i : Fin n => (A ^ (i : ℕ)) omega)) :
    RiemannHypothesis :=
  primeArchSourceMomentHankelDeterminantsPositive_iff_riemannHypothesis.mp
    (primeArchSourceMomentHankelDeterminantsPositive_of_selfAdjointObservableOrbit
      A omega hA hmom hli)

/-! ## Bounded self-adjoint observable criteria -/

/-- Exact real vacuum moments of a bounded self-adjoint observable discharge source positivity. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_selfAdjointObservable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (omega : E) (hA : IsSelfAdjoint A)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      inner ℝ omega ((A ^ n) omega)) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  exact HTGeometry.momentFunctional_pow_two_nonneg_of_selfAdjointObservable
    normalizedPrimeArchMoment A omega hA hmom _

/-- **Real bounded-observable RH capstone.**  The mathematical obligation is the all-order static
vacuum value relation, not a time evolution. -/
theorem riemannHypothesis_of_primeArchSelfAdjointObservable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (omega : E) (hA : IsSelfAdjoint A)
    (hmom : ∀ n, normalizedPrimeArchMoment n =
      inner ℝ omega ((A ^ n) omega)) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_selfAdjointObservable A omega hA hmom)

/-- Exact complex vacuum moments of a bounded self-adjoint observable discharge source
positivity. -/
theorem primeArchSourceTraceHankelIntNonnegative_of_complexSelfAdjointObservable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (omega : E) (hA : IsSelfAdjoint A)
    (hmom : ∀ n, inner ℂ omega ((A ^ n) omega) =
      (normalizedPrimeArchMoment n : ℂ)) :
    PrimeArchSourceTraceHankelIntNonnegative := by
  intro p
  rw [re_primeArchSourceTraceHankel_eq_momentFunctional_sq]
  exact HTGeometry.momentFunctional_pow_two_nonneg_of_complexSelfAdjointObservable
    normalizedPrimeArchMoment A omega hA hmom _

/-- **Complex bounded-observable RH capstone.** -/
theorem riemannHypothesis_of_primeArchComplexSelfAdjointObservable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (A : E →L[ℂ] E) (omega : E) (hA : IsSelfAdjoint A)
    (hmom : ∀ n, inner ℂ omega ((A ^ n) omega) =
      (normalizedPrimeArchMoment n : ℂ)) :
    RiemannHypothesis :=
  riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative
    (primeArchSourceTraceHankelIntNonnegative_of_complexSelfAdjointObservable A omega hA hmom)

end

end RHTower
