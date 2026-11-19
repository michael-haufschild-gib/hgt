import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Function fields of curves: the two Dedekind charts

Let `F` be a field and `K` a finite separable extension of `F(x)`. The places of `K` are seen
through two Dedekind domains:

* the finite chart `A = FunctionField.ringOfIntegers F K`, the integral closure of `F[x]`;
* the infinite chart `O∞ = integralClosure (infRing F) K`, the integral closure of the
  valuation ring `infRing F` of `F(x)` at infinity, which is a discrete valuation ring
  (`instIsDiscreteValuationRingInfRing`).

A place is a height-one prime of one of the two charts (`Place`); its degree is the dimension
over `F` of its residue ring.
-/

noncomputable section

open Polynomial IsDedekindDomain

namespace GaloisForLFunctions.CurvesOverFiniteFields

variable (F : Type*) [Field F] [DecidableEq (RatFunc F)]

/-- The valuation ring of `F(x)` at infinity. -/
abbrev infRing : ValuationSubring (RatFunc F) := (RatFunc.inftyValuation F).valuationSubring

instance : IsCyclic (WithZero (Multiplicative ℤ))ˣ :=
  isCyclic_of_surjective (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).symm.toMonoidHom
    (WithZero.unitsWithZeroEquiv (α := Multiplicative ℤ)).symm.surjective

instance : IsCyclic (MonoidWithZeroHom.ofClass (RatFunc.inftyValuation F)).valueGroup :=
  Subgroup.isCyclic _

instance : Nontrivial (MonoidWithZeroHom.ofClass (RatFunc.inftyValuation F)).valueGroup := by
  refine ⟨⟨1, ⟨Units.mk0 (RatFunc.inftyValuation F RatFunc.X) ?_, ?_⟩, ?_⟩⟩
  · rw [RatFunc.inftyValuation.X]; exact WithZero.coe_ne_zero
  · exact MonoidWithZeroHom.mem_valueGroup _ ⟨RatFunc.X, rfl⟩
  · intro h
    have h1 := congrArg (fun u : (MonoidWithZeroHom.ofClass (RatFunc.inftyValuation F)).valueGroup =>
      ((u : (WithZero (Multiplicative ℤ))ˣ) : WithZero (Multiplicative ℤ))) h
    simp only [OneMemClass.coe_one, Units.val_one, Units.val_mk0] at h1
    rw [RatFunc.inftyValuation.X] at h1
    exact absurd h1.symm (by decide)

instance instIsDiscreteValuationRingInfRing : IsDiscreteValuationRing (infRing F) :=
  Valuation.valuationSubring_isDiscreteValuationRing _

example : IsFractionRing (infRing F) (RatFunc F) := inferInstance

variable (K : Type*) [Field K] [Algebra F[X] K] [Algebra (RatFunc F) K]
  [IsScalarTower F[X] (RatFunc F) K]

/-- `K` as an algebra over the valuation ring at infinity, through `F(x)`. -/
instance (priority := 10) algebraInfRingField : Algebra (infRing F) K :=
  ((algebraMap (RatFunc F) K).comp (infRing F).subtype).toAlgebra

instance : IsScalarTower (infRing F) (RatFunc F) K :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The finite chart: the integral closure of `F[x]` in `K`. -/
abbrev finChart : Subalgebra F[X] K := FunctionField.ringOfIntegers F K

/-- The infinite chart: the integral closure of the valuation ring at infinity in `K`. -/
abbrev infChart : Subalgebra (infRing F) K := integralClosure (infRing F) K

variable [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K]

example : IsDedekindDomain (finChart F K) := inferInstance

instance : IsDedekindDomain (infChart F K) :=
  integralClosure.isDedekindDomain (infRing F) (RatFunc F) K

example : IsFractionRing (finChart F K) K := inferInstance

instance : IsFractionRing (infChart F K) K :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc F) K

/-- Finite places: height-one primes of the finite chart. -/
abbrev FinPlace := HeightOneSpectrum (finChart F K)

/-- Infinite places: height-one primes of the infinite chart. -/
abbrev InfPlace := HeightOneSpectrum (infChart F K)

/-- A place of `K`: a finite or an infinite place. -/
abbrev Place := FinPlace F K ⊕ InfPlace F K

/-- The valuation of a place. -/
def Place.valuation : Place F K → Valuation K (WithZero (Multiplicative ℤ))
  | Sum.inl P => P.valuation K
  | Sum.inr Q => Q.valuation K

end GaloisForLFunctions.CurvesOverFiniteFields
