import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerFinitePlaceCenters
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalConstantPlaces

/-!
# Intrinsic finite places of a polynomial normalization

A proper constant-field valuation ring in which the coordinate is
integral has a unique height-one center on the actual polynomial
normalization. This identifies rational finite primes with intrinsic
rational places where the coordinate has no pole.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
open GaloisForLFunctions.HTGeometry.ValuationInertia
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra K[X] L]
    [IsScalarTower K K[X] L]
local notation "B" => integralClosure K[X] L
variable [IsDedekindDomain (integralClosure K[X] L)]
    [IsFractionRing (integralClosure K[X] L) L]

/-- Every proper constant valuation ring containing the coordinate comes from its normalization center. -/
theorem polynomialNormalization_finitePlace_of_coordinate_mem
    (W : ValuationSubring L) (hW : W ≠ ⊤)
    (hK : ∀ a : K, algebraMap K L a ∈ W) (hX : algebraMap K[X] L X ∈ W) :
    ∃ w : HeightOneSpectrum B, (w.valuation L).valuationSubring = W := by
  have hA := polynomial_algebraMap_mem_valuationSubring W hK hX
  have hB : ∀ z : B, algebraMap B L z ∈ W := integralClosure_mem_of_base_mem W hA
  refine ⟨centerHeightOne W hB hW, ?_⟩
  have h := valuationSubringAtPrime_eq W hB hW
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h
  exact h

/-- A height-one normalization prime defines an intrinsic constant-field place. -/
def polynomialNormalizationFiniteConstantPlace (w : HeightOneSpectrum B) : ConstantFieldPlaces K L :=
  ⟨(w.valuation L).valuationSubring, heightOne_valuationSubring_ne_top w, heightOne_constants_mem w⟩

/-- The coordinate is integral at every finite normalization place. -/
theorem polynomialNormalizationFiniteConstantPlace_coordinate_mem (w : HeightOneSpectrum B) :
    algebraMap K[X] L X ∈ (polynomialNormalizationFiniteConstantPlace (K := K) w).val := by
  rw [IsScalarTower.algebraMap_apply K[X] B L]
  exact GaloisForLFunctions.HTGeometry.algebraMap_mem_valuationSubringAtPlace _ w _

/-- Distinct height-one centers give distinct intrinsic finite places. -/
theorem polynomialNormalizationFiniteConstantPlace_injective :
    Function.Injective (polynomialNormalizationFiniteConstantPlace (K := K) (L := L)) := by
  intro v w h
  exact heightOne_valuationSubring_injective (congrArg Subtype.val h)

/-- A rational normalization prime defines an intrinsic rational place. -/
def polynomialNormalizationRationalFinitePlace (w : HeightOneSpectrum B)
    (hw : Function.Surjective (algebraMap K (B ⧸ w.asIdeal))) : RationalConstantFieldPlaces K L :=
  ⟨polynomialNormalizationFiniteConstantPlace (K := K) w,
    (heightOne_constant_residue_surjective_iff w).mpr hw⟩

/-- Rational finite normalization primes are exactly intrinsic rational places with integral coordinate. -/
def polynomialNormalizationRationalFiniteEquiv :
    {w : HeightOneSpectrum B // Function.Surjective (algebraMap K (B ⧸ w.asIdeal))} ≃
      {W : RationalConstantFieldPlaces K L // algebraMap K[X] L X ∈ W.val.val} := by
  let f : {w : HeightOneSpectrum B // Function.Surjective (algebraMap K (B ⧸ w.asIdeal))} →
      {W : RationalConstantFieldPlaces K L // algebraMap K[X] L X ∈ W.val.val} :=
    fun w => ⟨polynomialNormalizationRationalFinitePlace w.val w.property,
      polynomialNormalizationFiniteConstantPlace_coordinate_mem w.val⟩
  apply Equiv.ofBijective f
  constructor
  · intro v w h
    apply Subtype.ext
    exact heightOne_valuationSubring_injective
      (congrArg (fun W : {W : RationalConstantFieldPlaces K L //
        algebraMap K[X] L X ∈ W.val.val} => W.val.val.val) h)
  · intro W
    obtain ⟨w, hw⟩ := polynomialNormalization_finitePlace_of_coordinate_mem
      W.val.val.val W.val.val.property.1 W.val.val.property.2 W.property
    have he : polynomialNormalizationFiniteConstantPlace (K := K) w = W.val.val := Subtype.ext hw
    have hres : Function.Surjective (valuationConstantResidue
        (polynomialNormalizationFiniteConstantPlace (K := K) w).val
        (polynomialNormalizationFiniteConstantPlace (K := K) w).property.2) :=
      he.symm ▸ W.val.property
    refine ⟨⟨w, (heightOne_constant_residue_surjective_iff w).mp hres⟩, ?_⟩
    exact Subtype.ext (Subtype.ext he)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
