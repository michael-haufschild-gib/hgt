import GaloisForLFunctions.GaloisTheoryOfZeros.TheDescentOfTheGlobalWidthSquareClass
import Mathlib.RingTheory.Norm.Basic

/-!
# Source norms of squared zero widths

The source norm of a nonzero squared width represents the global width class
raised to its source degree. Odd source degree therefore splits the entire
width restriction, not merely the Galois group of a finite truncation.
-/

noncomputable section
set_option autoImplicit false
open scoped IntermediateField
namespace GaloisForLFunctions.GaloisTheoryOfZeros

/-- The norm of a unit from the simple field it generates over the source. -/
def sourceSimpleNormUnit (K : Type*) {E : Type*} [Field K] [Field E] [Algebra K E]
    (a : Eˣ) : Kˣ :=
  Units.map (Algebra.norm K)
    (Units.mk0 (IntermediateField.AdjoinSimple.gen K (a : E)) (by
      intro h
      exact a.ne_zero (congrArg (algebraMap K⟮(a : E)⟯ E) h)))

/-- The norm of an invariant square class is its source-degree power. -/
theorem sourceSimpleNorm_squareClass {K E : Type*} [Field K] [Field E] [Algebra K E]
    [IsGalois K E] (a : Eˣ)
    (hinv : ∀ σ : E ≃ₐ[K] E,
      sourceSquareClassMap σ.toRingHom (sourceSquareClassProjection E a) =
        sourceSquareClassProjection E a) :
    sourceSquareClassMap (algebraMap K E)
      (sourceSquareClassProjection K (sourceSimpleNormUnit K a)) =
        (sourceSquareClassProjection E a) ^ (minpoly K (a : E)).natDegree := by
  classical
  let D : IntermediateField K E := K⟮(a : E)⟯
  have ha : IsIntegral K (a : E) := Algebra.IsIntegral.isIntegral (a : E)
  let pb : PowerBasis K D := IntermediateField.adjoin.powerBasis ha
  letI : FiniteDimensional K D := pb.finite
  letI : Fintype (D →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  let u : Dˣ := Units.mk0 pb.gen (by
    intro h
    exact a.ne_zero (congrArg (algebraMap D E) h))
  have hsep : IsSeparable K pb.gen := Algebra.IsSeparable.isSeparable K pb.gen
  have hsplit : ((minpoly K pb.gen).map (algebraMap K E)).Splits := by
    rw [← minpoly.algebraMap_eq (algebraMap D E).injective pb.gen]
    exact (inferInstance : Normal K E).splits (a : E)
  have hnorm : Units.map (algebraMap K E).toMonoidHom (sourceSimpleNormUnit K a) =
      ∏ φ : D →ₐ[K] E, Units.map φ.toMonoidHom u := by
    apply Units.ext
    change algebraMap K E (Algebra.norm K pb.gen) =
      ((∏ φ : D →ₐ[K] E, Units.map φ.toMonoidHom u : Eˣ) : E)
    calc
      algebraMap K E (Algebra.norm K pb.gen) = ∏ φ : D →ₐ[K] E, φ pb.gen :=
        Algebra.norm_eq_prod_embeddings_gen E pb hsplit hsep
      _ = ((∏ φ : D →ₐ[K] E, Units.map φ.toMonoidHom u : Eˣ) : E) :=
        (map_prod (show Eˣ →* E from
          { toFun := fun v => (v : E), map_one' := rfl, map_mul' := fun _ _ => rfl })
          (fun φ : D →ₐ[K] E => Units.map φ.toMonoidHom u) Finset.univ).symm
  have hfactor (φ : D →ₐ[K] E) :
      sourceSquareClassProjection E (Units.map φ.toMonoidHom u) =
        sourceSquareClassProjection E a := by
    let τ : E ≃ₐ[K] E :=
      AlgEquiv.ofBijective (φ.liftNormal E) (AlgHom.normal_bijective K E E _)
    have he : Units.map τ.toRingHom.toMonoidHom a = Units.map φ.toMonoidHom u := by
      apply Units.ext
      exact φ.liftNormal_commutes E pb.gen
    rw [← he,← sourceSquareClassMap_projection]
    exact hinv τ
  rw [sourceSquareClassMap_projection,hnorm,map_prod]
  calc
    ∏ φ : D →ₐ[K] E, sourceSquareClassProjection E (Units.map φ.toMonoidHom u) =
        ∏ _φ : D →ₐ[K] E, sourceSquareClassProjection E a :=
      Finset.prod_congr rfl (fun φ _ => hfactor φ)
    _ = (sourceSquareClassProjection E a) ^ (minpoly K (a : E)).natDegree := by
      rw [Finset.prod_const,Finset.card_univ,AlgHom.card_of_powerBasis pb hsep hsplit]
      rfl

/-- Every square class has exponent two. -/
theorem sourceSquareClass_sq {A : Type*} [Field A] (v : SourceSquareClass A) : v^2 = 1 := by
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (powMonoidHom (α := Aˣ) 2).range v
  change (sourceSquareClassProjection A a)^2 = 1
  rw [← map_pow]
  exact (sourceSquareClass_eq_one_iff _).mpr ⟨a,rfl⟩

/-- An invariant square class represented by an element of odd source degree descends. -/
theorem sourceSquareClass_descends_of_odd_degree {K E : Type*} [Field K] [Field E] [Algebra K E]
    [IsGalois K E] (a : Eˣ)
    (hinv : ∀ σ : E ≃ₐ[K] E,
      sourceSquareClassMap σ.toRingHom (sourceSquareClassProjection E a) =
        sourceSquareClassProjection E a)
    (hodd : Odd (minpoly K (a : E)).natDegree) :
    sourceSquareClassProjection E a ∈ Set.range (sourceSquareClassMap (algebraMap K E)) := by
  refine ⟨sourceSquareClassProjection K (sourceSimpleNormUnit K a),?_⟩
  rw [sourceSimpleNorm_squareClass a hinv]
  obtain ⟨k,hk⟩ := hodd
  have hn : (minpoly K (a : E)).natDegree = 2*k+1 := by omega
  rw [hn,pow_add,pow_mul,sourceSquareClass_sq,one_pow,one_mul,pow_one]

/-- The degree of the actual squared-width equation over the complete-fibre source. -/
def widthSquareSourceDegree (q : RHTower.XiZeroCopy) : ℕ :=
  (minpoly fullFibreSourceField (widthSquareInEven q)).natDegree

/-- The norm of a squared width represents the global class to its actual source degree. -/
theorem widthSquare_source_norm_class (q : RHTower.XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    sourceSquareClassMap (algebraMap fullFibreSourceField evenWidthInReal)
      (sourceSquareClassProjection fullFibreSourceField
        (sourceSimpleNormUnit fullFibreSourceField (widthSquareUnit q hq))) =
      globalWidthSquareClass ^ widthSquareSourceDegree q := by
  letI : IsGalois fullFibreSourceField evenWidthInReal := ⟨⟩
  rw [globalWidthSquareClass_eq q hq]
  exact sourceSimpleNorm_squareClass (widthSquareUnit q hq) (widthSquareClass_invariant q hq)

/-- Any nonzero squared width of odd source degree splits the full infinite restriction. -/
theorem widthRestrictionSplits_of_odd_square_degree
    (q : RHTower.XiZeroCopy) (hq : zeroWidth q ≠ 0) (hodd : Odd (widthSquareSourceDegree q)) :
    WidthRestrictionSplits := by
  letI : IsGalois fullFibreSourceField evenWidthInReal := ⟨⟩
  apply globalWidthSquareClass_descent_iff.mpr
  rw [globalWidthSquareClass_eq q hq]
  exact sourceSquareClass_descends_of_odd_degree (widthSquareUnit q hq)
    (widthSquareClass_invariant q hq) hodd

/-- Failure of source descent forces every nonzero squared-width equation to have even degree. -/
theorem width_square_degree_dichotomy :
    WidthRestrictionSplits ∨ ∀ q : RHTower.XiZeroCopy,
      zeroWidth q ≠ 0 → 2 ∣ widthSquareSourceDegree q := by
  classical
  by_cases hs : WidthRestrictionSplits
  · exact Or.inl hs
  · right
    intro q hq
    refine ⟨widthSquareSourceDegree q/2,?_⟩
    by_contra hn
    apply hs
    apply widthRestrictionSplits_of_odd_square_degree q hq
    exact ⟨widthSquareSourceDegree q/2,by omega⟩

private theorem square_root_source_degree {K E : Type*} [Field K] [Field E] [Algebra K E]
    (x : E) (hi : IsIntegral K x) (hx : x ∉ K⟮x^2⟯) :
    (minpoly K x).natDegree = 2*(minpoly K (x^2)).natDegree := by
  let D : IntermediateField K E := K⟮x^2⟯
  let H : IntermediateField D E := D⟮x⟯
  have hDle : D ≤ K⟮x⟯ :=
    IntermediateField.adjoin_simple_le_iff.mpr (by
      rw [pow_two]
      exact (K⟮x⟯).mul_mem (IntermediateField.mem_adjoin_simple_self K x)
        (IntermediateField.mem_adjoin_simple_self K x))
  have hH : H.restrictScalars K = K⟮x⟯ := by
    change (D⟮x⟯).restrictScalars K = K⟮x⟯
    rw [IntermediateField.restrictScalars_adjoin_eq_sup,sup_eq_right.mpr hDle]
  have hD : Module.finrank K D = (minpoly K (x^2)).natDegree :=
    IntermediateField.adjoin.finrank (hi.pow 2)
  have hquad : Module.finrank D H = 2 := by
    apply HTGeometry.finrank_adjoin_eq_two
      (c := ⟨x^2,IntermediateField.mem_adjoin_simple_self K (x^2)⟩)
      (show x*x = algebraMap D E (⟨x^2,IntermediateField.mem_adjoin_simple_self K (x^2)⟩ : D)
        by change x*x = x^2; rw [pow_two])
    rintro ⟨d,hd⟩
    change (d : E) = x at hd
    have hm : x ∈ D := (congrArg (fun y : E => y ∈ D) hd).mp d.property
    exact hx hm
  calc
    (minpoly K x).natDegree = Module.finrank K K⟮x⟯ :=
      (IntermediateField.adjoin.finrank hi).symm
    _ = Module.finrank K H :=
      (congrArg (fun T : IntermediateField K E => Module.finrank K T) hH).symm
    _ = Module.finrank K D * Module.finrank D H :=
      (Module.finrank_mul_finrank K D H).symm
    _ = 2*(minpoly K (x^2)).natDegree := by rw [hD,hquad,Nat.mul_comm]

/-- The degree of a signed width over the complete-fibre source. -/
def widthSourceDegree (q : RHTower.XiZeroCopy) : ℕ :=
  (minpoly fullFibreSourceField (zeroWidthInField q)).natDegree

/-- In the nonsplit regime, each nonzero width has twice its squared-width source degree. -/
theorem widthSourceDegree_eq_twice_of_not_split (hs : ¬ WidthRestrictionSplits)
    (q : RHTower.XiZeroCopy) (hq : zeroWidth q ≠ 0) :
    widthSourceDegree q = 2*widthSquareSourceDegree q := by
  have hqE : zeroWidth q ∉ evenWidthField := by
    intro h
    exact hs (widthRestrictionSplits_of_eq ((realWidthField_eq_even_iff q hq).mpr h))
  have hD : fullFibreSourceField⟮(zeroWidthInField q)^2⟯ ≤ evenWidthInReal :=
    IntermediateField.adjoin_simple_le_iff.mpr (widthSquareInEven q).property
  have hn : zeroWidthInField q ∉ fullFibreSourceField⟮(zeroWidthInField q)^2⟯ :=
    fun h => hqE (hD h)
  have hdeg := square_root_source_degree (zeroWidthInField q)
    (Algebra.IsIntegral.isIntegral (zeroWidthInField q)) hn
  have he : minpoly fullFibreSourceField ((zeroWidthInField q)^2) =
      minpoly fullFibreSourceField (widthSquareInEven q) :=
    minpoly.algebraMap_eq (algebraMap evenWidthInReal realWidthField).injective (widthSquareInEven q)
  rw [he] at hdeg
  exact hdeg

/-- Failure of continuous splitting forces every nonzero signed width to have source degree divisible by four. -/
theorem width_source_degree_dichotomy :
    WidthRestrictionSplits ∨ ∀ q : RHTower.XiZeroCopy,
      zeroWidth q ≠ 0 → 4 ∣ widthSourceDegree q := by
  classical
  by_cases hs : WidthRestrictionSplits
  · exact Or.inl hs
  · right
    intro q hq
    obtain ⟨k,hk⟩ := (width_square_degree_dichotomy.resolve_left hs) q hq
    refine ⟨k,?_⟩
    rw [widthSourceDegree_eq_twice_of_not_split hs q hq,hk]
    omega

end GaloisForLFunctions.GaloisTheoryOfZeros
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.sourceSimpleNorm_squareClass
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthSquare_source_norm_class
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.widthRestrictionSplits_of_odd_square_degree
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.width_square_degree_dichotomy
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.width_source_degree_dichotomy
