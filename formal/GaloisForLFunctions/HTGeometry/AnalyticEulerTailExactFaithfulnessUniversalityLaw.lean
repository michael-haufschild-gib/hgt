import GaloisForLFunctions.HTGeometry.AnalyticEulerTailQuotientRealization
import GaloisForLFunctions.HTGeometry.FinitePrimeCoefficientField

/-!
# Analytic Euler-tail exact faithfulness universality

The exact finite-prime tail matroid is transferred through faithful finite-abscissa fraction
realization and genuine-coordinate disjointness. The resulting analytic field contains the
Euler-exponential base, so an infinite prime tail cannot disappear modulo that base.

Consequently the order-zero Euler-tail realization is injective. The entire all-jet realization
is then injective by projection to order zero, discharging the kernel obstruction isolated by the
continuum analytic Euler-tail law.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Set
open scoped Differential

noncomputable section

set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 600000

/-- Faithful comparison of finite-abscissa fractions with unrestricted arithmetic fractions. -/
noncomputable def finiteAbscissaFractionToArithmeticFraction :
    finiteAbscissaDirichletFractionField →+* arithmeticFunctionFractionField :=
  IsFractionRing.lift
    (A := finiteAbscissaArithmeticSubalgebra)
    (K := finiteAbscissaDirichletFractionField)
    (g := (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField).comp
      finiteAbscissaArithmeticSubalgebra.val.toRingHom)
    (by
      intro f g h
      apply Subtype.ext
      apply (FaithfulSMul.algebraMap_injective
        (ArithmeticFunction ℂ) arithmeticFunctionFractionField)
      exact h)

theorem finiteAbscissaFractionToArithmeticFraction_injective :
    Function.Injective finiteAbscissaFractionToArithmeticFraction :=
  finiteAbscissaFractionToArithmeticFraction.injective

@[simp]
theorem finiteAbscissaFractionToArithmeticFraction_algebraMap
    (f : finiteAbscissaArithmeticSubalgebra) :
    finiteAbscissaFractionToArithmeticFraction
        (algebraMap finiteAbscissaArithmeticSubalgebra
          finiteAbscissaDirichletFractionField f) =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f.1 := by
  apply IsFractionRing.lift_algebraMap

/-- Finite-abscissa fractions whose arithmetic image has finite prime activity. -/
def finiteAbscissaFinitePrimeCoefficientField :
    Subfield finiteAbscissaDirichletFractionField :=
  finitePrimeCoefficientField.comap finiteAbscissaFractionToArithmeticFraction

def finiteAbscissaFinitePrimeToFinitePrimeCoefficient :
    finiteAbscissaFinitePrimeCoefficientField →+* finitePrimeCoefficientField :=
  (finiteAbscissaFractionToArithmeticFraction.comp
    finiteAbscissaFinitePrimeCoefficientField.subtype).codRestrict
      finitePrimeCoefficientField fun x => x.2

theorem finiteAbscissaFinitePrimeToFinitePrimeCoefficient_injective :
    Function.Injective finiteAbscissaFinitePrimeToFinitePrimeCoefficient := by
  intro x y h
  apply Subtype.ext
  exact finiteAbscissaFractionToArithmeticFraction_injective
    (congrArg Subtype.val h)

theorem algebraicIndependent_finiteAbscissaPrimeColumns_over_pulledFinitePrime
    {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → finiteAbscissaArithmeticSubalgebra)
    (c : I → Nat.Primes → ℂ)
    (hf : ∀ i, (f i).1 = arithmeticOfPrimeColumn (c i))
    (htail : TailCoefficientIndependent c) :
    AlgebraicIndependent finiteAbscissaFinitePrimeCoefficientField
      (fun i => algebraMap finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField (f i)) := by
  let kToF := finiteAbscissaFinitePrimeToFinitePrimeCoefficient
  letI : Algebra finiteAbscissaFinitePrimeCoefficientField
      finitePrimeCoefficientField := kToF.toAlgebra
  let kToA : finiteAbscissaFinitePrimeCoefficientField →+*
      arithmeticFunctionFractionField :=
    finiteAbscissaFractionToArithmeticFraction.comp
      finiteAbscissaFinitePrimeCoefficientField.subtype
  letI : Algebra finiteAbscissaFinitePrimeCoefficientField
      arithmeticFunctionFractionField := kToA.toAlgebra
  letI : IsScalarTower finiteAbscissaFinitePrimeCoefficientField
      finitePrimeCoefficientField arithmeticFunctionFractionField :=
    .of_algebraMap_eq fun x => rfl
  let h : finiteAbscissaDirichletFractionField →ₐ[
      finiteAbscissaFinitePrimeCoefficientField]
      arithmeticFunctionFractionField :=
    { __ := finiteAbscissaFractionToArithmeticFraction
      commutes' := fun x => rfl }
  have hA : AlgebraicIndependent finitePrimeCoefficientField
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (arithmeticOfPrimeColumn (c i))) :=
    algebraicIndependent_fractionPrimeColumns_over_finitePrimeCoefficientField c htail
  have hAK : AlgebraicIndependent finiteAbscissaFinitePrimeCoefficientField
      (fun i => algebraMap (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField (arithmeticOfPrimeColumn (c i))) :=
    hA.restrictScalars finiteAbscissaFinitePrimeToFinitePrimeCoefficient_injective
  apply (AlgHom.algebraicIndependent_iff h
    finiteAbscissaFractionToArithmeticFraction_injective).mp
  convert hAK using 1
  funext i
  change finiteAbscissaFractionToArithmeticFraction
      (algebraMap finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField (f i)) =
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
      (arithmeticOfPrimeColumn (c i))
  rw [finiteAbscissaFractionToArithmeticFraction_algebraMap, hf i]

/-- Analytic realization of the pulled finite-prime field. -/
noncomputable def finiteAbscissaFinitePrimeToUpperEndMero :
    finiteAbscissaFinitePrimeCoefficientField →+* upperEndMeroField :=
  finiteAbscissaFractionToUpperEndMero.comp
    finiteAbscissaFinitePrimeCoefficientField.subtype

noncomputable instance finiteAbscissaFinitePrimeUpperEndAlgebra :
    Algebra finiteAbscissaFinitePrimeCoefficientField upperEndMeroField :=
  finiteAbscissaFinitePrimeToUpperEndMero.toAlgebra

attribute [local instance]
  analyticObservableUpperEndAnalyticDomain
  analyticObservableUpperEndMeroComplexAlgebra
  analyticObservableUpperEndMeroDifferential

local instance finiteAbscissaFinitePrimeFractionUpperEndScalarTower :
    IsScalarTower finiteAbscissaFinitePrimeCoefficientField
      finiteAbscissaDirichletFractionField upperEndMeroField :=
  IsScalarTower.of_algebraMap_eq'
    (R := finiteAbscissaFinitePrimeCoefficientField)
    (S := finiteAbscissaDirichletFractionField)
    (A := upperEndMeroField) rfl

/-- The analytic coordinate field over the pulled finite-prime coefficient field. -/
def analyticPulledFinitePrimeCoordinateField :
    IntermediateField finiteAbscissaFinitePrimeCoefficientField upperEndMeroField :=
  IntermediateField.adjoin finiteAbscissaFinitePrimeCoefficientField
    ({upperEndCoordinateMero} : Set upperEndMeroField)

theorem algebraicIndependent_finiteAbscissaLSeries_over_pulledFinitePrimeCoordinate
    {I : Type*} (f : I → finiteAbscissaArithmeticSubalgebra)
    (hf : AlgebraicIndependent finiteAbscissaFinitePrimeCoefficientField
      (fun i => algebraMap finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField (f i))) :
    AlgebraicIndependent analyticPulledFinitePrimeCoordinateField
      (fun i => finiteAbscissaLSeriesToUpperEndMero (f i)) := by
  let xF : I → finiteAbscissaDirichletFractionField := fun i =>
    algebraMap finiteAbscissaArithmeticSubalgebra
      finiteAbscissaDirichletFractionField (f i)
  let xM : I → upperEndMeroField := fun i =>
    algebraMap finiteAbscissaDirichletFractionField upperEndMeroField (xF i)
  let t : Unit → upperEndMeroField := fun _ => upperEndCoordinateMero
  have ht : AlgebraicIndependent finiteAbscissaDirichletFractionField t := by
    rw [algebraicIndependent_unique_type_iff]
    exact upperEndCoordinateMero_transcendental_over_finiteAbscissaFraction
  have hjoint₀ : AlgebraicIndependent finiteAbscissaFinitePrimeCoefficientField
      (Sum.elim t
        (algebraMap finiteAbscissaDirichletFractionField upperEndMeroField ∘ xF)) :=
    (@AlgebraicIndependent.sumElim_comp
      I finiteAbscissaFinitePrimeCoefficientField
      finiteAbscissaDirichletFractionField upperEndMeroField
      _ _ _ _ finiteAbscissaFinitePrimeUpperEndAlgebra
      finiteAbscissaFractionUpperEndAlgebra
      finiteAbscissaFinitePrimeFractionUpperEndScalarTower
      Unit xF t hf ht)
  have hjoint : AlgebraicIndependent finiteAbscissaFinitePrimeCoefficientField
      (Sum.elim xM t) := by
    let e : I ⊕ Unit ≃ Unit ⊕ I := Equiv.sumComm I Unit
    have hcomp := hjoint₀.comp e e.injective
    have heq :
        (Sum.elim t
          (algebraMap finiteAbscissaDirichletFractionField upperEndMeroField ∘ xF)) ∘ e =
            Sum.elim xM t := by
      funext z
      rcases z with i | u <;> rfl
    rwa [heq] at hcomp
  have hAlg : AlgebraicIndependent
      (Algebra.adjoin finiteAbscissaFinitePrimeCoefficientField (Set.range t)) xM :=
    (AlgebraicIndependent.sumElim_iff.mp hjoint).2
  have hrange : Set.range t =
      ({upperEndCoordinateMero} : Set upperEndMeroField) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      rfl
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      exact ⟨(), hz.symm⟩
  rw [hrange] at hAlg
  have hField : AlgebraicIndependent analyticPulledFinitePrimeCoordinateField xM :=
    IntermediateField.algebraicIndependent_adjoin_iff.mpr hAlg
  have hxM : xM = fun i => finiteAbscissaLSeriesToUpperEndMero (f i) := by
    funext i
    exact finiteAbscissaFractionToUpperEndMero_algebraMap (f i)
  rwa [hxM] at hField

theorem finiteAbscissaFractionToArithmeticFraction_algebraMap_complex
    (z : ℂ) :
    finiteAbscissaFractionToArithmeticFraction
        (algebraMap ℂ finiteAbscissaDirichletFractionField z) =
      algebraMap ℂ arithmeticFunctionFractionField z := by
  rw [show algebraMap ℂ finiteAbscissaDirichletFractionField z =
      algebraMap finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField
          (algebraMap ℂ finiteAbscissaArithmeticSubalgebra z) from
      (IsScalarTower.algebraMap_apply ℂ finiteAbscissaArithmeticSubalgebra
        finiteAbscissaDirichletFractionField z).symm,
    finiteAbscissaFractionToArithmeticFraction_algebraMap]
  rfl

/-- Complex constants inside the pulled finite-prime field. -/
noncomputable def complexToFiniteAbscissaFinitePrime :
    ℂ →+* finiteAbscissaFinitePrimeCoefficientField :=
  (algebraMap ℂ finiteAbscissaDirichletFractionField).codRestrict
    finiteAbscissaFinitePrimeCoefficientField (by
      intro z
      change finiteAbscissaFractionToArithmeticFraction
          (algebraMap ℂ finiteAbscissaDirichletFractionField z) ∈
        finitePrimeCoefficientField
      rw [finiteAbscissaFractionToArithmeticFraction_algebraMap_complex,
        mem_finitePrimeCoefficientField_iff,
        finitePrimeActivity_algebraMap_complex]
      exact Set.finite_empty)

noncomputable instance finiteAbscissaFinitePrimeAlgebraComplex :
    Algebra ℂ finiteAbscissaFinitePrimeCoefficientField :=
  complexToFiniteAbscissaFinitePrime.toAlgebra

local instance complexFiniteAbscissaFinitePrimeUpperEndScalarTower :
    IsScalarTower ℂ finiteAbscissaFinitePrimeCoefficientField upperEndMeroField :=
  IsScalarTower.of_algebraMap_eq'
    (R := ℂ) (S := finiteAbscissaFinitePrimeCoefficientField)
    (A := upperEndMeroField) (by
      apply RingHom.ext
      intro z
      change algebraMap ℂ upperEndMeroField z =
        finiteAbscissaFractionToUpperEndMero
          (algebraMap ℂ finiteAbscissaDirichletFractionField z)
      symm
      rw [show algebraMap ℂ finiteAbscissaDirichletFractionField z =
          algebraMap finiteAbscissaArithmeticSubalgebra
            finiteAbscissaDirichletFractionField
              (algebraMap ℂ finiteAbscissaArithmeticSubalgebra z) from
          (IsScalarTower.algebraMap_apply ℂ finiteAbscissaArithmeticSubalgebra
            finiteAbscissaDirichletFractionField z).symm,
        finiteAbscissaFractionToUpperEndMero_algebraMap]
      exact finiteAbscissaLSeriesToUpperEndMero.commutes z)

/-- The same pulled coordinate field, regarded as a complex intermediate field. -/
def analyticPulledFinitePrimeCoordinateComplexField :
    IntermediateField ℂ upperEndMeroField where
  __ := analyticPulledFinitePrimeCoordinateField.toSubfield
  algebraMap_mem' := by
    intro z
    have hz := IntermediateField.algebraMap_mem
      analyticPulledFinitePrimeCoordinateField
      (algebraMap ℂ finiteAbscissaFinitePrimeCoefficientField z)
    change finiteAbscissaFractionToUpperEndMero
        (algebraMap ℂ finiteAbscissaDirichletFractionField z) ∈
      analyticPulledFinitePrimeCoordinateField at hz
    convert hz using 1
    change algebraMap ℂ upperEndMeroField z =
      finiteAbscissaFractionToUpperEndMero
        (algebraMap ℂ finiteAbscissaDirichletFractionField z)
    symm
    rw [show algebraMap ℂ finiteAbscissaDirichletFractionField z =
        algebraMap finiteAbscissaArithmeticSubalgebra
          finiteAbscissaDirichletFractionField
            (algebraMap ℂ finiteAbscissaArithmeticSubalgebra z) from
        (IsScalarTower.algebraMap_apply ℂ finiteAbscissaArithmeticSubalgebra
          finiteAbscissaDirichletFractionField z).symm,
      finiteAbscissaFractionToUpperEndMero_algebraMap]
    exact finiteAbscissaLSeriesToUpperEndMero.commutes z

theorem upperEndRationalCoordinateField_le_pulledFinitePrimeCoordinate :
    upperEndRationalCoordinateField ≤
      analyticPulledFinitePrimeCoordinateComplexField := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst z
  exact IntermediateField.subset_adjoin
    finiteAbscissaFinitePrimeCoefficientField
    ({upperEndCoordinateMero} : Set upperEndMeroField) rfl

/-- The pulled coordinate field as an extension of the actual rational coordinate field. -/
def analyticPulledFinitePrimeCoordinateOverRational :
    IntermediateField upperEndRationalCoordinateField upperEndMeroField where
  __ := analyticPulledFinitePrimeCoordinateField.toSubfield
  algebraMap_mem' := fun z =>
    upperEndRationalCoordinateField_le_pulledFinitePrimeCoordinate z.2

/-- A finite-abscissa source with finite prime activity realizes inside the pulled coordinate
field. -/
theorem finiteAbscissaLSeries_mem_pulledFinitePrimeCoordinate
    (f : finiteAbscissaArithmeticSubalgebra)
    (hf : algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f.1 ∈
      finitePrimeCoefficientField) :
    finiteAbscissaLSeriesToUpperEndMero f ∈
      analyticPulledFinitePrimeCoordinateField := by
  let y : finiteAbscissaFinitePrimeCoefficientField :=
    ⟨algebraMap finiteAbscissaArithmeticSubalgebra
      finiteAbscissaDirichletFractionField f, by
        change finiteAbscissaFractionToArithmeticFraction
            (algebraMap finiteAbscissaArithmeticSubalgebra
              finiteAbscissaDirichletFractionField f) ∈
          finitePrimeCoefficientField
        rw [finiteAbscissaFractionToArithmeticFraction_algebraMap]
        exact hf⟩
  have hy := IntermediateField.algebraMap_mem
    analyticPulledFinitePrimeCoordinateField y
  change finiteAbscissaFractionToUpperEndMero y.1 ∈
    analyticPulledFinitePrimeCoordinateField at hy
  rw [show y.1 = algebraMap finiteAbscissaArithmeticSubalgebra
    finiteAbscissaDirichletFractionField f from rfl,
    finiteAbscissaFractionToUpperEndMero_algebraMap] at hy
  exact hy

theorem differentialJet_analyticSinglePrimeShiftCarrier_mem_pulledFinitePrimeCoordinate
    (a : ℂ) (q : Nat.Primes) (k : ℕ) :
    GaloisForLFunctions.differentialJet k
        (analyticSinglePrimeShiftCarrier a q) ∈
      analyticPulledFinitePrimeCoordinateField := by
  let f :=
    (finiteAbscissaRotatedDeriv^[k])
      (finiteAbscissaDirichletShift a
        (uniformlyBoundedPrimeFiniteAbscissa
          (primeKroneckerCoefficient q) 1
          (primeKroneckerCoefficient_norm_le_one q)))
  have hfsource : f.1 = arithmeticOfPrimeColumn
      (fun p => primeKroneckerCoefficient q p * primeShiftFactor a p *
        rotatedPrimeLogClock p ^ k) := by
    exact analyticPrimeObservableShiftJetSource_eq_arithmeticOfPrimeColumn
      (primeKroneckerCoefficient q) 1
      (primeKroneckerCoefficient_norm_le_one q) a k
  have hfinite :
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f.1 ∈
        finitePrimeCoefficientField := by
    rw [hfsource, arithmeticOfPrimeColumn_mem_finitePrimeCoefficientField_iff]
    apply (Set.finite_singleton q).subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    by_contra hpq
    have hpne : p ≠ q := by simpa using hpq
    apply hp
    simp [primeKroneckerCoefficient, hpne]
  have hmem := finiteAbscissaLSeries_mem_pulledFinitePrimeCoordinate f hfinite
  change GaloisForLFunctions.differentialJet k
      (finiteAbscissaLSeriesToUpperEndMero
        (finiteAbscissaDirichletShift a
          (uniformlyBoundedPrimeFiniteAbscissa
            (primeKroneckerCoefficient q) 1
            (primeKroneckerCoefficient_norm_le_one q)))) ∈ _
  rw [differentialJet_finiteAbscissaLSeriesToUpperEndMero]
  exact hmem

/-- The analytic Euler-exponential base is contained in the coordinate extension of the pulled
finite-prime field. -/
theorem analyticEulerExponentialBase_le_pulledFinitePrimeCoordinate (a : ℂ) :
    analyticEulerExponentialBase a ≤
      analyticPulledFinitePrimeCoordinateOverRational := by
  unfold analyticEulerExponentialBase GaloisForLFunctions.differentialAdjoin
  apply IntermediateField.adjoin_le_iff.mpr
  rintro y ⟨x, ⟨q, rfl⟩, k, rfl⟩
  exact differentialJet_analyticSinglePrimeShiftCarrier_mem_pulledFinitePrimeCoordinate
    a q k

/-- Inclusion of the analytic Euler base into the pulled finite-prime coordinate field. -/
noncomputable def analyticEulerBaseToPulledFinitePrimeCoordinate (a : ℂ) :
    analyticEulerExponentialBase a →+*
      analyticPulledFinitePrimeCoordinateField where
  toFun x := ⟨x.1,
    analyticEulerExponentialBase_le_pulledFinitePrimeCoordinate a x.2⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem analyticEulerBaseToPulledFinitePrimeCoordinate_injective (a : ℂ) :
    Function.Injective (analyticEulerBaseToPulledFinitePrimeCoordinate a) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  change (⟨x, _⟩ : analyticPulledFinitePrimeCoordinateField) =
    ⟨y, _⟩ at h
  have hxy : x = y := congrArg
    (fun z : analyticPulledFinitePrimeCoordinateField => z.1) h
  subst y
  rfl

noncomputable instance analyticEulerBasePulledFinitePrimeCoordinateAlgebra (a : ℂ) :
    Algebra (analyticEulerExponentialBase a)
      analyticPulledFinitePrimeCoordinateField :=
  (analyticEulerBaseToPulledFinitePrimeCoordinate a).toAlgebra

local instance analyticEulerBasePulledFinitePrimeCoordinateUpperEndScalarTower (a : ℂ) :
    IsScalarTower (analyticEulerExponentialBase a)
      analyticPulledFinitePrimeCoordinateField upperEndMeroField :=
  IsScalarTower.of_algebraMap_eq'
    (R := analyticEulerExponentialBase a)
    (S := analyticPulledFinitePrimeCoordinateField)
    (A := upperEndMeroField) rfl

/-- Tail-independent bounded prime columns remain algebraically independent as actual analytic
Dirichlet carriers over the full Euler-exponential base. -/
theorem analyticPrimeObservableShiftCarrier_algebraicIndependent_over_eulerBase
    {I : Type*} [Fintype I] [DecidableEq I]
    (c : I → Nat.Primes → ℂ) (M : I → ℝ)
    (hM : ∀ i p, ‖c i p‖ ≤ M i) (a : ℂ)
    (htail : TailCoefficientIndependent c) :
    AlgebraicIndependent (analyticEulerExponentialBase a)
      (fun i => analyticPrimeObservableShiftCarrier (c i) (M i) (hM i) a) := by
  let f : I → finiteAbscissaArithmeticSubalgebra := fun i =>
    finiteAbscissaDirichletShift a
      (uniformlyBoundedPrimeFiniteAbscissa (c i) (M i) (hM i))
  let d : I → Nat.Primes → ℂ := fun i p =>
    c i p * primeShiftFactor a p
  have hf : ∀ i, (f i).1 = arithmeticOfPrimeColumn (d i) := by
    intro i
    simpa only [f, d, pow_zero, mul_one] using
      (analyticPrimeObservableShiftJetSource_eq_arithmeticOfPrimeColumn
        (c i) (M i) (hM i) a 0)
  have hdtail : TailCoefficientIndependent d := by
    have hweighted :=
      (tailCoefficientIndependent_commonWeight_iff c
        (primeShiftFactor a) (primeShiftFactor_ne_zero a)).mpr htail
    simpa only [d, mul_comm] using hweighted
  have hsource :=
    algebraicIndependent_finiteAbscissaPrimeColumns_over_pulledFinitePrime
      f d hf hdtail
  have hpulled :=
    algebraicIndependent_finiteAbscissaLSeries_over_pulledFinitePrimeCoordinate
      f hsource
  have heuler : AlgebraicIndependent (analyticEulerExponentialBase a)
      (fun i => finiteAbscissaLSeriesToUpperEndMero (f i)) :=
    (@AlgebraicIndependent.restrictScalars
      I (analyticEulerExponentialBase a) upperEndMeroField
      (fun i => finiteAbscissaLSeriesToUpperEndMero (f i))
      _ _ _ analyticPulledFinitePrimeCoordinateField _
      (analyticEulerBasePulledFinitePrimeCoordinateAlgebra a)
      _ (analyticEulerBasePulledFinitePrimeCoordinateUpperEndScalarTower a)
      (analyticEulerBaseToPulledFinitePrimeCoordinate_injective a) hpulled)
  simpa only [f, analyticPrimeObservableShiftCarrier] using heuler

/-- An infinite-support bounded prime carrier is transcendental over the full analytic Euler
base. -/
theorem analyticBoundedPrimeShiftCarrier_transcendental_over_eulerBase
    (a : ℂ) (c : BoundedPrimeSource)
    (hc : ¬(Function.support (c : Nat.Primes → ℂ)).Finite) :
    Transcendental (analyticEulerExponentialBase a)
      (analyticBoundedPrimeShiftCarrier a c) := by
  have htail : TailCoefficientIndependent
      (fun _ : Unit => (c : Nat.Primes → ℂ)) := by
    apply (tailCoefficientIndependent_unit_iff
      (c : Nat.Primes → ℂ)).mpr
    simpa only [PrimeCoefficientTailZero, Function.support] using hc
  have hAI :=
    analyticPrimeObservableShiftCarrier_algebraicIndependent_over_eulerBase
      (fun _ : Unit => (c : Nat.Primes → ℂ))
      (fun _ : Unit => boundedPrimeSourceBound c)
      (fun _ p => boundedPrimeSourceBound_spec c p) a htail
  exact hAI.transcendental ()

/-- Exact kernel of the order-zero bounded-source quotient map: analytic membership in the
Euler base occurs precisely for finitely supported prime sources. -/
theorem analyticBoundedPrimeJetQuotientMap_zero_iff_finiteSupport
    (a : ℂ) (c : BoundedPrimeSource) :
    analyticBoundedPrimeJetQuotientMap a 0 c = 0 ↔
      (Function.support (c : Nat.Primes → ℂ)).Finite := by
  constructor
  · intro hzero
    change Submodule.Quotient.mk
        (GaloisForLFunctions.differentialJet 0
          (analyticBoundedPrimeShiftCarrier a c)) = 0 at hzero
    rw [Submodule.Quotient.mk_eq_zero,
      GaloisForLFunctions.differentialJet_zero] at hzero
    by_contra hfinite
    have ht :=
      analyticBoundedPrimeShiftCarrier_transcendental_over_eulerBase
        a c hfinite
    apply ht
    let b : analyticEulerExponentialBase a :=
      ⟨analyticBoundedPrimeShiftCarrier a c, hzero⟩
    change IsAlgebraic (analyticEulerExponentialBase a)
      (b : upperEndMeroField)
    exact isAlgebraic_algebraMap b
  · intro hfinite
    have hc : c ∈ boundedPrimeFiniteSupportSubmodule := hfinite
    have hker :=
      boundedPrimeFiniteSupport_le_analyticBoundedPrimeJetQuotientMap_ker
        a 0 hc
    exact LinearMap.mem_ker.mp hker

/-- The descended order-zero Euler-tail realization is injective. -/
theorem analyticEulerTailJetRealization_zero_injective (a : ℂ) :
    Function.Injective (analyticEulerTailJetRealization a 0) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro q hq
    induction q using Submodule.Quotient.induction_on with
    | _ c =>
        have hzero := LinearMap.mem_ker.mp hq
        change analyticBoundedPrimeJetQuotientMap a 0 c = 0 at hzero
        have hfinite :=
          (analyticBoundedPrimeJetQuotientMap_zero_iff_finiteSupport
            a c).mp hzero
        rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
        exact hfinite
  · exact bot_le

/-- The canonical all-jet Euler-tail realization is injective because its order-zero coordinate
already is. -/
theorem analyticEulerTailAllJetRealization_injective (a : ℂ) :
    Function.Injective (analyticEulerTailAllJetRealization a) := by
  intro q r hqr
  apply analyticEulerTailJetRealization_zero_injective a
  exact congrFun hqr 0

/-- Every linearly independent bounded tail-source family stays linearly independent after the
canonical analytic all-jet realization. -/
theorem linearIndependent_analyticEulerTailAllJetRealization
    {I : Type*} (a : ℂ) (v : I → BoundedPrimeTailSpace)
    (hv : LinearIndependent ℂ v) :
    LinearIndependent ℂ
      (fun i => analyticEulerTailAllJetRealization a (v i)) := by
  have hmap := hv.map' (analyticEulerTailAllJetRealization a)
    (LinearMap.ker_eq_bot.mpr
      (analyticEulerTailAllJetRealization_injective a))
  simpa only [Function.comp_apply] using hmap

/-- **Analytic Euler-tail exact faithfulness universality law.**  The order-zero kernel on
bounded sources is exactly finite support; after descent, both order zero and the entire all-jet
tower are injective, so every independent source frame remains analytically independent. -/
theorem analyticEulerTail_exactFaithfulnessUniversality (a : ℂ) :
    (∀ c : BoundedPrimeSource,
      analyticBoundedPrimeJetQuotientMap a 0 c = 0 ↔
        (Function.support (c : Nat.Primes → ℂ)).Finite) ∧
    Function.Injective (analyticEulerTailJetRealization a 0) ∧
    Function.Injective (analyticEulerTailAllJetRealization a) ∧
    ∀ {I : Type*} (v : I → BoundedPrimeTailSpace),
      LinearIndependent ℂ v →
        LinearIndependent ℂ
          (fun i => analyticEulerTailAllJetRealization a (v i)) := by
  exact ⟨
    analyticBoundedPrimeJetQuotientMap_zero_iff_finiteSupport a,
    analyticEulerTailJetRealization_zero_injective a,
    analyticEulerTailAllJetRealization_injective a,
    linearIndependent_analyticEulerTailAllJetRealization a⟩

end
end GaloisForLFunctions.HTGeometry
