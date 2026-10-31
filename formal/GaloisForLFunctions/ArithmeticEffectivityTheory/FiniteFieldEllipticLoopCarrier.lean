import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLocalFields
import GaloisForLFunctions.HTGeometry.LoopEisenstein.IntegralLoopBorelIntersection
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2FieldMap

/-!
# The actual restricted central loop group of the elliptic curve

Finite components are restricted by the coefficient-integral completed
loop subgroup. The arithmetic group is the preimage of this restriction
under diagonal coefficient-field maps, so no unrestricted rational loop
is silently admitted into the adelic carrier.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein
open Filter
open scoped RestrictedProduct WithZero WithZeroMulInt
noncomputable section

/-- Full product of all finite completed central loop groups. -/
abbrev FiniteLoopProduct := ∀ v : FinitePlace, LoopSL2 (v.adicCompletion K)

/-- Actual coefficient-integral subgroup at a finite place. -/
def finiteIntegralLoop (v : FinitePlace) : Subgroup (LoopSL2 (v.adicCompletion K)) :=
  LoopSL2.integralLoop (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

/-- Actual coefficient-integral subgroup at infinity. -/
def infinityIntegralLoop : Subgroup (LoopSL2 InfinityCompletion) :=
  LoopSL2.integralLoop (Valued.v : Valuation InfinityCompletion ℤᵐ⁰)

/-- The actual restricted finite central loop group. -/
abbrev FiniteAdelicLoop := Πʳ v : FinitePlace,
  [LoopSL2 (v.adicCompletion K), finiteIntegralLoop v]

/-- Include the actual infinity completion. -/
abbrev AdelicLoop := FiniteAdelicLoop × LoopSL2 InfinityCompletion

/-- Diagonal central loops in the unrestricted finite product. -/
def diagonalFiniteLoop : LoopSL2 K →* FiniteLoopProduct where
  toFun g v := LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)) g
  map_one' := by funext v; exact map_one _
  map_mul' g h := by funext v; exact map_mul _ g h

/-- Rational completed loops satisfying the genuine finite-place restriction. -/
def restrictedRationalLoop : Subgroup (LoopSL2 K) where
  carrier := {g | ∀ᶠ v : FinitePlace in cofinite, diagonalFiniteLoop g v ∈ finiteIntegralLoop v}
  one_mem' := by
    change ∀ᶠ v : FinitePlace in cofinite, diagonalFiniteLoop 1 v ∈ finiteIntegralLoop v
    filter_upwards [] with v
    change LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)) 1 ∈ finiteIntegralLoop v
    rw [map_one]
    exact (finiteIntegralLoop v).one_mem
  mul_mem' := by
    intro g h hg hh
    change ∀ᶠ v : FinitePlace in cofinite, diagonalFiniteLoop g v ∈ finiteIntegralLoop v at hg
    change ∀ᶠ v : FinitePlace in cofinite, diagonalFiniteLoop h v ∈ finiteIntegralLoop v at hh
    change ∀ᶠ v : FinitePlace in cofinite, diagonalFiniteLoop (g * h) v ∈ finiteIntegralLoop v
    filter_upwards [hg, hh] with v hv hw
    change LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)) (g * h) ∈ finiteIntegralLoop v
    rw [map_mul]
    exact (finiteIntegralLoop v).mul_mem hv hw
  inv_mem' := by
    intro g hg
    change ∀ᶠ v : FinitePlace in cofinite, diagonalFiniteLoop g v ∈ finiteIntegralLoop v at hg
    change ∀ᶠ v : FinitePlace in cofinite, diagonalFiniteLoop g⁻¹ v ∈ finiteIntegralLoop v
    filter_upwards [hg] with v hv
    change LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)) g⁻¹ ∈ finiteIntegralLoop v
    rw [map_inv]
    exact (finiteIntegralLoop v).inv_mem hv

/-- The diagonal arithmetic embedding, defined exactly on restricted rational loops. -/
def arithmeticLoopEmbedding : restrictedRationalLoop →* AdelicLoop where
  toFun g := (⟨diagonalFiniteLoop g, g.property⟩, LoopSL2.fieldMap infinityEmbedding g)
  map_one' := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      change LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)) 1 = 1
      exact map_one (LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)))
    · change LoopSL2.fieldMap infinityEmbedding 1 = 1
      exact map_one (LoopSL2.fieldMap infinityEmbedding)
  map_mul' g h := by
    apply Prod.ext
    · apply RestrictedProduct.ext
      intro v
      change LoopSL2.fieldMap (algebraMap K (v.adicCompletion K))
        ((g : LoopSL2 K) * (h : LoopSL2 K)) =
          LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)) (g : LoopSL2 K) *
            LoopSL2.fieldMap (algebraMap K (v.adicCompletion K)) (h : LoopSL2 K)
      exact (LoopSL2.fieldMap (algebraMap K (v.adicCompletion K))).map_mul _ _
    · change LoopSL2.fieldMap infinityEmbedding ((g : LoopSL2 K) * (h : LoopSL2 K)) =
        LoopSL2.fieldMap infinityEmbedding (g : LoopSL2 K) * LoopSL2.fieldMap infinityEmbedding (h : LoopSL2 K)
      exact (LoopSL2.fieldMap infinityEmbedding).map_mul _ _

theorem arithmeticLoopEmbedding_injective : Function.Injective arithmeticLoopEmbedding := by
  intro g h he
  apply Subtype.ext
  exact LoopSL2.fieldMap_injective infinityEmbedding (congrArg Prod.snd he)

/-- The literal arithmetic subgroup of the actual restricted adelic central loop group. -/
def arithmeticLoopGroup : Subgroup AdelicLoop := arithmeticLoopEmbedding.range

/-- The adelic integral subgroup, integral at every place. -/
def adelicIntegralLoop : Subgroup AdelicLoop where
  carrier := {g | (∀ v : FinitePlace, g.1 v ∈ finiteIntegralLoop v) ∧ g.2 ∈ infinityIntegralLoop}
  one_mem' := ⟨fun v => (finiteIntegralLoop v).one_mem, infinityIntegralLoop.one_mem⟩
  mul_mem' := by
    intro g h hg hh
    exact ⟨fun v => (finiteIntegralLoop v).mul_mem (hg.1 v) (hh.1 v),
      infinityIntegralLoop.mul_mem hg.2 hh.2⟩
  inv_mem' := by
    intro g hg
    exact ⟨fun v => (finiteIntegralLoop v).inv_mem (hg.1 v),
      infinityIntegralLoop.inv_mem hg.2⟩

/-- Positive Borel inside the actual restricted carrier. -/
def adelicPositiveBorel : Subgroup AdelicLoop where
  carrier := {g | (∀ v : FinitePlace, g.1 v ∈ LoopSL2.positiveBorel (v.adicCompletion K)) ∧
    g.2 ∈ LoopSL2.positiveBorel InfinityCompletion}
  one_mem' := ⟨fun v => (LoopSL2.positiveBorel (v.adicCompletion K)).one_mem,
    (LoopSL2.positiveBorel InfinityCompletion).one_mem⟩
  mul_mem' := by
    intro g h hg hh
    exact ⟨fun v => (LoopSL2.positiveBorel (v.adicCompletion K)).mul_mem (hg.1 v) (hh.1 v),
      (LoopSL2.positiveBorel InfinityCompletion).mul_mem hg.2 hh.2⟩
  inv_mem' := by
    intro g hg
    exact ⟨fun v => (LoopSL2.positiveBorel (v.adicCompletion K)).inv_mem (hg.1 v),
      (LoopSL2.positiveBorel InfinityCompletion).inv_mem hg.2⟩

/-- Evaluation of an adelic Borel element at a finite place. -/
def finiteBorelEvaluation (v : FinitePlace) :
    adelicPositiveBorel →* LoopSL2.positiveBorel (v.adicCompletion K) where
  toFun b := ⟨b.1.1 v, b.property.1 v⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Evaluation of an adelic Borel element at infinity. -/
def infinityBorelEvaluation : adelicPositiveBorel →* LoopSL2.positiveBorel InfinityCompletion where
  toFun b := ⟨b.1.2, b.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Both local Borel torus coordinates are valuation units outside one finite set. -/
theorem adelicBorel_torus_eventually_integral (b : adelicPositiveBorel) :
    ∀ᶠ v : FinitePlace in cofinite,
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
        (((LoopSL2.borelTorusHom _ (finiteBorelEvaluation v b)).1 : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) = 1 ∧
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
        (((LoopSL2.borelTorusHom _ (finiteBorelEvaluation v b)).2 : (v.adicCompletion K)ˣ) :
          v.adicCompletion K) = 1 := by
  filter_upwards [b.1.1.property] with v hv
  have h := LoopSL2.borelValuationHom_integralLoop
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (finiteBorelEvaluation v b) hv
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩


private theorem local_normalized_iwasawa {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰)
    (g : LoopSL2 F) :
    ∃ k ∈ LoopSL2.integralLoop v, ∃ b ∈ LoopSL2.positiveBorel F,
      k * b = g ∧ (g ∈ LoopSL2.integralLoop v → b = 1) := by
  classical
  by_cases hg : g ∈ LoopSL2.integralLoop v
  · exact ⟨g, hg, 1, (LoopSL2.positiveBorel F).one_mem, mul_one g, fun _ => rfl⟩
  · obtain ⟨k, b, he⟩ := LoopSL2.exists_integralLoop_borel v g
    exact ⟨k, k.property, b, b.property, he, fun h => (hg h).elim⟩

/-- Actual adelic Iwasawa factors stay inside one restricted product. -/
theorem exists_adelic_integral_borel (g : AdelicLoop) :
    ∃ k : adelicIntegralLoop, ∃ b : adelicPositiveBorel, (k : AdelicLoop) * b = g := by
  classical
  choose k hk b hb he hn using fun v : FinitePlace =>
    local_normalized_iwasawa (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (g.1 v)
  obtain ⟨ki, hki, bi, hbi, hei, _⟩ :=
    local_normalized_iwasawa (Valued.v : Valuation InfinityCompletion ℤᵐ⁰) g.2
  have hbr : ∀ᶠ v : FinitePlace in cofinite, b v ∈ finiteIntegralLoop v := by
    filter_upwards [g.1.property] with v hv
    rw [hn v hv]
    exact (finiteIntegralLoop v).one_mem
  let ka : AdelicLoop := (⟨k, Filter.Eventually.of_forall hk⟩, ki)
  let ba : AdelicLoop := (⟨b, hbr⟩, bi)
  refine ⟨⟨ka, hk, hki⟩, ⟨ba, hb, hbi⟩, ?_⟩
  apply Prod.ext
  · apply RestrictedProduct.ext
    exact he
  · exact hei

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.arithmeticLoopEmbedding_injective
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicBorel_torus_eventually_integral

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.exists_adelic_integral_borel
