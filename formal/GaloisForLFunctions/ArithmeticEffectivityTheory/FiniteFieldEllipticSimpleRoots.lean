import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLoopCarrier
import GaloisForLFunctions.HTGeometry.LoopEisenstein.AffineSimpleIwasawaValues

/-!
# Actual adelic simple roots and their Iwasawa valuations

An integral scalar gives an integral simple-root loop. Thus every adele
supplies a restricted finite or affine negative root. Evaluating actual
adelic Iwasawa factors at each place gives the exact radial torus values.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein Filter
open scoped WithZero WithZeroMulInt
noncomputable section

private theorem lower_integral {F : Type*} [Field F]
    (v : Valuation F ℤᵐ⁰) (x : F) (hx : v x ≤ 1) :
    sl2Lower x ∈ valuationIntegralSL2 v := by
  intro i j
  fin_cases i <;> fin_cases j
  · change v 1 ≤ 1
    rw [map_one]
  · change v 0 ≤ 1
    rw [map_zero]
    exact zero_le_one
  · exact hx
  · change v 1 ≤ 1
    rw [map_one]

private theorem finiteNegativeRoot_integral {F : Type*} [Field F]
    (v : Valuation F ℤᵐ⁰) (x : F) (hx : v x ≤ 1) :
    LoopSL2.finiteSL2Embedding F (sl2Lower x) ∈ LoopSL2.integralLoop v :=
  LoopSL2.integralSimpleLoop_le_integralLoop v
    ((show LoopSL2.finiteIntegralSimple v ≤ LoopSL2.integralSimpleLoop v from le_sup_left)
      ⟨sl2Lower x, lower_integral v x hx, rfl⟩)

private theorem affineNegativeRoot_integral {F : Type*} [Field F]
    (v : Valuation F ℤᵐ⁰) (x : F) (hx : v x ≤ 1) :
    LoopSL2.affineSimpleSL2Embedding F (sl2Lower x) ∈ LoopSL2.integralLoop v :=
  LoopSL2.integralSimpleLoop_le_integralLoop v
    ((show LoopSL2.affineIntegralSimple v ≤ LoopSL2.integralSimpleLoop v from le_sup_right)
      ⟨sl2Lower x, lower_integral v x hx, rfl⟩)

/-- The finite negative simple root with an actual adele as parameter. -/
def adelicFiniteNegativeRoot (a : Adeles) : AdelicLoop :=
  (⟨fun v => LoopSL2.finiteSL2Embedding (v.adicCompletion K) (sl2Lower (a.1 v)), by
    filter_upwards [a.1.property] with v hv
    exact finiteNegativeRoot_integral Valued.v (a.1 v) hv⟩,
    LoopSL2.finiteSL2Embedding InfinityCompletion (sl2Lower a.2))

/-- The affine negative simple root with an actual adele as parameter. -/
def adelicAffineNegativeRoot (a : Adeles) : AdelicLoop :=
  (⟨fun v => LoopSL2.affineSimpleSL2Embedding (v.adicCompletion K) (sl2Lower (a.1 v)), by
    filter_upwards [a.1.property] with v hv
    exact affineNegativeRoot_integral Valued.v (a.1 v) hv⟩,
    LoopSL2.affineSimpleSL2Embedding InfinityCompletion (sl2Lower a.2))

/-- Every actual finite-root factorization has the radial value at every finite place. -/
theorem adelicFiniteNegativeRoot_finite_values (a : Adeles)
    (k : adelicIntegralLoop) (b : adelicPositiveBorel)
    (he : (k : AdelicLoop) * b = adelicFiniteNegativeRoot a) (v : FinitePlace) :
    LoopSL2.borelValuationHom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (finiteBorelEvaluation v b) = (1, max 1 (Valued.v (a.1 v))) :=
  LoopSL2.finiteLowerRoot_iwasawa_values Valued.v (a.1 v)
    ⟨k.1.1 v, k.property.1 v⟩ (finiteBorelEvaluation v b)
    (congrArg (fun g : AdelicLoop => g.1 v) he)

/-- The same finite-root value holds at the actual infinity completion. -/
theorem adelicFiniteNegativeRoot_infinity_values (a : Adeles)
    (k : adelicIntegralLoop) (b : adelicPositiveBorel)
    (he : (k : AdelicLoop) * b = adelicFiniteNegativeRoot a) :
    LoopSL2.borelValuationHom (Valued.v : Valuation InfinityCompletion ℤᵐ⁰)
      (infinityBorelEvaluation b) = (1, max 1 (Valued.v a.2)) :=
  LoopSL2.finiteLowerRoot_iwasawa_values Valued.v a.2
    ⟨k.1.2, k.property.2⟩ (infinityBorelEvaluation b) (congrArg Prod.snd he)

/-- Every actual affine-root factorization has radial central value and inverse finite value. -/
theorem adelicAffineNegativeRoot_finite_values (a : Adeles)
    (k : adelicIntegralLoop) (b : adelicPositiveBorel)
    (he : (k : AdelicLoop) * b = adelicAffineNegativeRoot a) (v : FinitePlace) :
    LoopSL2.borelValuationHom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (finiteBorelEvaluation v b) =
        (max 1 (Valued.v (a.1 v)), (max 1 (Valued.v (a.1 v)))⁻¹) :=
  LoopSL2.affineLowerRoot_iwasawa_values Valued.v (a.1 v)
    ⟨k.1.1 v, k.property.1 v⟩ (finiteBorelEvaluation v b)
    (congrArg (fun g : AdelicLoop => g.1 v) he)

/-- The affine-root radial pair also holds at the actual infinity completion. -/
theorem adelicAffineNegativeRoot_infinity_values (a : Adeles)
    (k : adelicIntegralLoop) (b : adelicPositiveBorel)
    (he : (k : AdelicLoop) * b = adelicAffineNegativeRoot a) :
    LoopSL2.borelValuationHom (Valued.v : Valuation InfinityCompletion ℤᵐ⁰)
      (infinityBorelEvaluation b) = (max 1 (Valued.v a.2), (max 1 (Valued.v a.2))⁻¹) :=
  LoopSL2.affineLowerRoot_iwasawa_values Valued.v a.2
    ⟨k.1.2, k.property.2⟩ (infinityBorelEvaluation b) (congrArg Prod.snd he)

/-- Actual finite-root factors exist and have all their local torus valuations simultaneously. -/
theorem exists_adelicFiniteNegativeRoot_iwasawa_values (a : Adeles) :
    ∃ k : adelicIntegralLoop, ∃ b : adelicPositiveBorel,
      (k : AdelicLoop) * b = adelicFiniteNegativeRoot a ∧
        (∀ v : FinitePlace,
          LoopSL2.borelValuationHom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
            (finiteBorelEvaluation v b) = (1, max 1 (Valued.v (a.1 v)))) ∧
        LoopSL2.borelValuationHom (Valued.v : Valuation InfinityCompletion ℤᵐ⁰)
          (infinityBorelEvaluation b) = (1, max 1 (Valued.v a.2)) := by
  obtain ⟨k, b, he⟩ := exists_adelic_integral_borel (adelicFiniteNegativeRoot a)
  exact ⟨k, b, he, adelicFiniteNegativeRoot_finite_values a k b he,
    adelicFiniteNegativeRoot_infinity_values a k b he⟩

/-- Actual affine-root factors exist and have all their local torus valuations simultaneously. -/
theorem exists_adelicAffineNegativeRoot_iwasawa_values (a : Adeles) :
    ∃ k : adelicIntegralLoop, ∃ b : adelicPositiveBorel,
      (k : AdelicLoop) * b = adelicAffineNegativeRoot a ∧
        (∀ v : FinitePlace,
          LoopSL2.borelValuationHom (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
            (finiteBorelEvaluation v b) =
              (max 1 (Valued.v (a.1 v)), (max 1 (Valued.v (a.1 v)))⁻¹)) ∧
        LoopSL2.borelValuationHom (Valued.v : Valuation InfinityCompletion ℤᵐ⁰)
          (infinityBorelEvaluation b) = (max 1 (Valued.v a.2), (max 1 (Valued.v a.2))⁻¹) := by
  obtain ⟨k, b, he⟩ := exists_adelic_integral_borel (adelicAffineNegativeRoot a)
  exact ⟨k, b, he, adelicAffineNegativeRoot_finite_values a k b he,
    adelicAffineNegativeRoot_infinity_values a k b he⟩

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.exists_adelicFiniteNegativeRoot_iwasawa_values
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.exists_adelicAffineNegativeRoot_iwasawa_values
