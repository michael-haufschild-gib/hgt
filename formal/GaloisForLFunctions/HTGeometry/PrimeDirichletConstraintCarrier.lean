import GaloisForLFunctions.HTGeometry.PrimeDirichletDifferentialField
import GaloisForLFunctions.HTGeometry.LocalizedStanleyReisnerDifferentialMatroid

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction
open GaloisForLFunctions MvPolynomial Polynomial
open scoped Differential

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

theorem arithmeticFunctionRationalCoordinateField_deriv_complexConstant (c : ℂ) :
    (algebraMap ℂ arithmeticFunctionRationalCoordinateField c)′ = 0 := by
  rw [show algebraMap ℂ arithmeticFunctionRationalCoordinateField c =
      algebraMap arithmeticFunctionFractionField
        arithmeticFunctionRationalCoordinateField
        (algebraMap ℂ arithmeticFunctionFractionField c) by rfl]
  rw [arithmeticFunctionRationalCoordinateField_deriv_algebraMap]
  rw [show algebraMap ℂ arithmeticFunctionFractionField c =
      algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField
        (algebraMap ℂ (ArithmeticFunction ℂ) c) by rfl]
  rw [arithmeticFunctionFractionField_deriv_apply,
    rotatedLogFractionDerivation_algebraMap]
  have hlog : logWeight (algebraMap ℂ (ArithmeticFunction ℂ) c) = 0 := by
    ext n
    by_cases hn : n = 1
    · subst n
      simp [logWeight_apply]
    · simp [logWeight_apply, Algebra.algebraMap_eq_smul_one,
        ArithmeticFunction.smul_map, hn]
  rw [hlog, smul_zero,
    (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField).map_zero,
    (algebraMap arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField).map_zero]

local instance complexFinitePrimeRationalAmbientScalarTower :
    IsScalarTower ℂ finitePrimeRationalCoefficientField
      arithmeticFunctionRationalCoordinateField :=
  .of_algebraMap_eq fun c => by
    change algebraMap ℂ arithmeticFunctionRationalCoordinateField c =
      finitePrimeRationalCoefficientFieldToFormalRatFunc
        (algebraMap ℂ finitePrimeRationalCoefficientField c)
    rw [IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      finitePrimeRationalCoefficientField]
    rw [finitePrimeRationalCoefficientFieldToFormalRatFunc_algebraMap]
    rw [← IsScalarTower.algebraMap_apply ℂ finitePrimeCoefficientField
      arithmeticFunctionFractionField]
    rw [IsScalarTower.algebraMap_apply ℂ arithmeticFunctionFractionField
      arithmeticFunctionRationalCoordinateField]

theorem primeOrientation_singleton_tailIndependent (epsilon : Nat.Primes → Bool) :
    PrimeOrientationTailIndependent (fun _ : Unit => epsilon) := by
  intro c hfin
  funext u
  have hu : u = () := Subsingleton.elim _ _
  subst u
  change c () = (0 : ℂ)
  by_contra hc
  have hset :
      {p : Nat.Primes |
        ∑ i : Unit, c i * primeDirichletSign ((fun _ : Unit => epsilon) i p) ≠ 0} =
        Set.univ := by
    ext p
    simp [hc, primeDirichletSign_ne_zero]
  rw [hset] at hfin
  exact Set.infinite_univ hfin

theorem signedPrimeNaturalShiftPalette_differentialIndependent_complex
    (epsilon : Nat.Primes → Bool) :
    DifferentialIndependent ℂ (signedPrimeNaturalShiftPalette epsilon) := by
  have hfull :=
    (signedPrimeNaturalShiftPalette_differentialIndependent_iff
      (fun _ : Unit => epsilon)).mpr
        (primeOrientation_singleton_tailIndependent epsilon)
  have hpalette := hfull.comp (fun n : ℕ => ((), n)) (by
    intro m n h
    exact congrArg Prod.snd h)
  unfold DifferentialIndependent at hpalette ⊢
  exact AlgebraicIndependent.restrictScalars
    (FaithfulSMul.algebraMap_injective ℂ finitePrimeRationalCoefficientField) hpalette

/-- Canonical injection of any finite constraint-row index into the natural shift palette. -/
def finiteConstraintIndexNatEmbedding (I : Type*) [Fintype I] : I ↪ ℕ :=
  (Fintype.equivFin I).toEmbedding.trans Fin.valEmbedding

/-- **Signed-prime complete Stanley--Reisner constraint carrier.** Every orientation's canonical
nonnegative-integer shift palette realizes every finite localized Stanley--Reisner differential
matroid. The source is explicit: enumerate the finite operator rows into the natural shifts. -/
theorem signedPrimeNaturalShiftPalette_stanleyReisnerLaurentDifferentialMatroid
    {alpha iota : Type*}
    [Fintype alpha] [Fintype iota] [DecidableEq alpha] [DecidableEq iota]
    (epsilon : Nat.Primes → Bool)
    (d : translationSubmonoid (Polynomial ℂ) alpha)
    (facets : Finset (Finset alpha))
    (N : iota → MvPolynomial alpha (Polynomial ℂ) ⧸
      stanleyReisnerIdeal (Polynomial ℂ) facets) :
    let source : FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N) →
        arithmeticFunctionRationalCoordinateField := fun q =>
      signedPrimeNaturalShiftPalette epsilon
        (finiteConstraintIndexNatEmbedding
          (FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N)) q)
    DifferentialIndependent ℂ
        (differentialOperatorRowApply
          (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
      LinearIndependent (Polynomial ℂ) N := by
  classical
  let rowIndex := FiniteFinsuppRowIndex (stanleyReisnerLaurentRows d facets N)
  let e : rowIndex ↪ ℕ := finiteConstraintIndexNatEmbedding rowIndex
  let source : rowIndex → arithmeticFunctionRationalCoordinateField := fun q =>
    signedPrimeNaturalShiftPalette epsilon (e q)
  have hsource : DifferentialIndependent ℂ source := by
    exact (signedPrimeNaturalShiftPalette_differentialIndependent_complex epsilon).comp
      e e.injective
  change DifferentialIndependent ℂ
      (differentialOperatorRowApply
        (finiteFinsuppOperatorRows (stanleyReisnerLaurentRows d facets N)) source) ↔
    LinearIndependent (Polynomial ℂ) N
  exact differentialIndependent_stanleyReisnerLaurentRows_iff
    (C := ℂ) (K := arithmeticFunctionRationalCoordinateField)
    arithmeticFunctionRationalCoordinateField_deriv_complexConstant
      d facets N source hsource

end
end GaloisForLFunctions.HTGeometry
