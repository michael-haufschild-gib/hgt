import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticCharts
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Jacobson.Ring

/-!
# The elliptic function field as a finite global function field

The coordinate basis `(1,y)` remains a basis over the rational function field.
Its degree is two, hence its trace is nonzero in characteristic three and the
extension is separable. The integral closure and its finite adeles are therefore
constructed from the actual curve, with no assumed arithmetic field structure.
-/

open Polynomial
open scoped nonZeroDivisors

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

noncomputable section

/-- The rational subfield defined by the existing `x` coordinate. -/
instance ratFuncAlgebra : Algebra (RatFunc Constants) FunctionField :=
  RatFunc.liftAlgebra Constants FunctionField

instance ratFuncScalarTower :
    IsScalarTower Constants[X] (RatFunc Constants) FunctionField :=
  RatFunc.isScalarTower_liftAlgebra Constants FunctionField

private def coordinateBasis : Module.Basis (Fin 2) Constants[X] CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.basis curve.toAffine

private def rationalBasisFamily (i : Fin 2) : FunctionField :=
  algebraMap CoordinateRing FunctionField (coordinateBasis i)

private lemma rationalBasisFamily_independent :
    LinearIndependent (RatFunc Constants) rationalBasisFamily := by
  have hlin : LinearIndependent Constants[X] rationalBasisFamily :=
    coordinateBasis.linearIndependent.map'
      (IsScalarTower.toAlgHom Constants[X] CoordinateRing FunctionField).toLinearMap
      (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective CoordinateRing FunctionField))
  exact hlin.localization (RatFunc Constants) Constants[X]⁰

private lemma rationalBasisFamily_span :
    Submodule.span (RatFunc Constants) (Set.range rationalBasisFamily) = ⊤ := by
  apply top_unique
  intro z _
  have hspan : (Ideal.span ({(1 : CoordinateRing)} : Set CoordinateRing) : Set CoordinateRing) ⊆
      Submodule.span Constants[X] (Set.range coordinateBasis) := by
    rw [coordinateBasis.span_eq]
    exact Set.subset_univ _
  have h := IsFractionRing.ideal_span_singleton_map_subset Constants[X]
    (K := RatFunc Constants) (S := CoordinateRing) (L := FunctionField)
    (FaithfulSMul.algebraMap_injective Constants[X] FunctionField) hspan
    (show z ∈ Ideal.span ({algebraMap CoordinateRing FunctionField 1} : Set FunctionField) by simp)
  rw [← Set.range_comp] at h
  exact h

/-- The actual function field has rational-function basis `(1,y)`. -/
def rationalFunctionBasis : Module.Basis (Fin 2) (RatFunc Constants) FunctionField :=
  Module.Basis.mk rationalBasisFamily_independent (by rw [rationalBasisFamily_span])

instance : _root_.FunctionField Constants FunctionField :=
  Module.Finite.of_basis rationalFunctionBasis

theorem functionField_finrank : Module.finrank (RatFunc Constants) FunctionField = 2 := by
  rw [Module.finrank_eq_card_basis rationalFunctionBasis]
  exact Fintype.card_fin 2

/-- The quadratic extension is separable because its trace of one is nonzero. -/
instance functionField_isSeparable : Algebra.IsSeparable (RatFunc Constants) FunctionField := by
  have htwo : (2 : RatFunc Constants) ≠ 0 := by
    have hc : (2 : Constants) ≠ 0 := by decide
    simpa only [map_ofNat, map_zero] using (algebraMap Constants (RatFunc Constants)).injective.ne hc
  have htrace : Algebra.trace (RatFunc Constants) FunctionField 1 = 2 := by
    simpa using Algebra.trace_algebraMap_of_basis rationalFunctionBasis (1 : RatFunc Constants)
  by_contra hn
  have hz := congrArg (fun f : FunctionField →ₗ[RatFunc Constants] RatFunc Constants => f 1)
    (Algebra.trace_eq_zero_of_not_isSeparable hn)
  rw [htrace, LinearMap.zero_apply] at hz
  exact htwo hz

/-- The integral closure of the rational-coordinate polynomial ring in the actual curve field. -/
abbrev RingOfIntegers := _root_.FunctionField.ringOfIntegers Constants FunctionField

instance : IsDedekindDomain RingOfIntegers := inferInstance

instance : IsFractionRing RingOfIntegers FunctionField := inferInstance

/-- Finite places are actual height-one primes of the integral closure. -/
abbrev FinitePlace := IsDedekindDomain.HeightOneSpectrum RingOfIntegers

instance finitePlace_nonempty : Nonempty FinitePlace := by
  obtain ⟨v, _⟩ := (IsDedekindDomain.HeightOneSpectrum.ideal_ne_top_iff_exists
    (_root_.FunctionField.ringOfIntegers.not_isField Constants FunctionField)
    (⊥ : Ideal RingOfIntegers)).mp bot_ne_top
  exact ⟨v⟩

/-- Residue fields of all finite places are finite extensions of the actual constant field. -/
instance finitePlace_quotient_finite (v : FinitePlace) :
    Finite (RingOfIntegers ⧸ v.asIdeal) := by
  letI : Module.Finite Constants[X] RingOfIntegers := inferInstance
  letI : Algebra.FiniteType Constants RingOfIntegers :=
    Algebra.FiniteType.trans (R := Constants) (S := Constants[X]) (A := RingOfIntegers)
      inferInstance inferInstance
  letI : Field (RingOfIntegers ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  letI : Module.Finite Constants (RingOfIntegers ⧸ v.asIdeal) :=
    finite_of_finite_type_of_isJacobsonRing Constants (RingOfIntegers ⧸ v.asIdeal)
  exact Module.finite_of_finite Constants

/-- Restricted product of the actual nonarchimedean completions at finite places. -/
abbrev FiniteAdeles := IsDedekindDomain.FiniteAdeleRing RingOfIntegers FunctionField

instance finiteAdeles_nontrivial : Nontrivial FiniteAdeles := by
  obtain ⟨v⟩ := finitePlace_nonempty
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have he := congrArg (fun a : FiniteAdeles => a v) h
  exact zero_ne_one he

/-- The diagonal field map into finite adeles, with finite denominator support proved by construction. -/
def finiteAdeleEmbedding : FunctionField →+* FiniteAdeles := algebraMap FunctionField FiniteAdeles

theorem finiteAdeleEmbedding_injective : Function.Injective finiteAdeleEmbedding :=
  finiteAdeleEmbedding.injective

@[simp] lemma finiteAdeleEmbedding_apply (z : FunctionField) (v : FinitePlace) :
    finiteAdeleEmbedding z v = z := rfl

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
