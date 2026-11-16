import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionInfinityOrders
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialNormalizationPlaces
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.IntrinsicPlaceEquivalences

/-!
# Intrinsic places of the three-point field over extended constants

The reciprocal normalization supplies an actual rational infinity
place. Every constant valuation ring where the coordinate has a pole
has that unique center. All remaining places come from the finite
normalization, and the classification preserves residue rationality.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
open GaloisForLFunctions.HTGeometry.ValuationInertia
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] (η : Eˣ)
local notation "q" => p ^ (d + 1)
local notation "a" => (q - 1) * kummerExponent q r
local notation "c" => (η⁻¹) ^ a
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "L∞" => PrimePowerThreePointExtensionInfinityField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a
local notation "B∞" => PrimePowerThreePointExtensionInfinityNormalization p d n E c a

local instance finitePlaceNormalizationAlgebra : Algebra B L :=
  inferInstanceAs (Algebra (integralClosure E[X] L) L)

local instance finitePlaceNormalizationFractionRing : IsFractionRing B L :=
  primePowerThreePointExtensionNormalization_fractionRing p d n E c a

local instance infinityPlaceNormalizationAlgebra : Algebra B∞ L∞ :=
  inferInstanceAs (Algebra (integralClosure E[X] L∞) L∞)

local instance infinityPlaceNormalizationFractionRing : IsFractionRing B∞ L∞ :=
  primePowerThreePointExtensionInfinityNormalization_fractionRing p d n E c a

/-- The actual intrinsic rational infinity place, transported from the reciprocal normalization. -/
def primePowerKummerExtensionRationalInfinityPlace : RationalConstantFieldPlaces E L :=
  rationalConstantFieldPlaceComap (kummerInfinityFieldEquiv c 0 a (M - 1))
    (polynomialNormalizationRationalFinitePlace (K := E) («L» := L∞)
      (primePowerKummerExtensionInfinityPlace p d n r E η)
      (primePowerKummerExtensionInfinityPlace_residue_surjective p d n r E η))

/-- The original coordinate has a pole at the intrinsic infinity place. -/
theorem primePowerKummerExtensionInfinity_coordinate_notMem :
    algebraMap E[X] L X ∉ (primePowerKummerExtensionRationalInfinityPlace p d n r E η).val.val := by
  intro h
  change primePowerKummerExtensionInfinityValuation p d n r E η (algebraMap E[X] L X) ≤ 1 at h
  rw [primePowerKummerExtensionInfinityValuation_coordinate,
    ← WithZero.exp_zero, WithZero.exp_le_exp] at h
  have hM := primePowerKummerCyclicDegree_pos p d n
  omega

/-- A coordinate pole identifies a proper constant valuation ring with the unique infinity place. -/
theorem primePowerKummerExtension_infinityPlace_of_coordinate_notMem
    (W : ValuationSubring L) (hW : W ≠ ⊤) (hE : ∀ t : E, algebraMap E L t ∈ W)
    (hX : algebraMap E[X] L X ∉ W) :
    W = (primePowerKummerExtensionRationalInfinityPlace p d n r E η).val.val := by
  let e := kummerInfinityFieldEquiv c 0 a (M - 1)
  let W' := W.comap e.symm.toRingHom
  have hW' : W' ≠ ⊤ := by
    intro h
    apply hW
    apply top_unique
    intro x _
    have hx : e x ∈ W' := by rw [h]; trivial
    change e.symm (e x) ∈ W at hx
    simpa only [e.symm_apply_apply] using hx
  have hE' : ∀ t : E, algebraMap E L∞ t ∈ W' := by
    intro t
    change e.symm (algebraMap E L∞ t) ∈ W
    rw [e.symm.commutes]
    exact hE t
  have hX' : algebraMap E[X] L∞ X ∈ W' := by
    change e.symm (algebraMap E[X] L∞ X) ∈ W
    rw [kummerInfinityFieldEquiv_symm_coordinate]
    exact (W.mem_or_inv_mem _).resolve_left hX
  have hA := polynomial_algebraMap_mem_valuationSubring W' hE' hX'
  have hB : ∀ z : B∞, algebraMap B∞ L∞ z ∈ W' := integralClosure_mem_of_base_mem W' hA
  let P := centerPrime W' hB
  have hxP : algebraMap E[X] B∞ X ∈ P := by
    by_contra hx
    have hi := inv_mem_of_notMem_centerPrime W' hB hx
    rw [← IsScalarTower.algebraMap_apply E[X] B∞ L∞] at hi
    change e.symm ((algebraMap E[X] L∞ X)⁻¹) ∈ W at hi
    rw [map_inv₀, kummerInfinityFieldEquiv_symm_coordinate, inv_inv] at hi
    exact hX hi
  have hmax : (Ideal.span {(X : E[X])}).IsMaximal :=
    (kummerInfinityBasePlace (K := E)).isPrime.isMaximal (kummerInfinityBasePlace (K := E)).ne_bot
  have hproper : P.under E[X] ≠ ⊤ := by
    intro h
    have h1 : (1 : E[X]) ∈ P.under E[X] := by rw [h]; trivial
    change algebraMap E[X] B∞ 1 ∈ P at h1
    rw [map_one] at h1
    exact (show P.IsPrime from inferInstance).ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  have hover : P.LiesOver (Ideal.span {(X : E[X])}) := by
    apply (Ideal.liesOver_iff P _).mpr
    apply hmax.eq_of_le hproper
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hxP
  letI := hover
  have hP := primePowerKummerExtensionInfinityPlace_unique p d n r E η P
  have hw : centerHeightOne W' hB hW' = primePowerKummerExtensionInfinityPlace p d n r E η :=
    HeightOneSpectrum.ext hP
  have hval := valuationSubringAtPrime_eq W' hB hW'
  rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring, hw] at hval
  change W = ((primePowerKummerExtensionInfinityPlace p d n r E η).valuation L∞).valuationSubring.comap
    e.toRingHom
  rw [hval]
  ext x
  change x ∈ W ↔ e.symm (e x) ∈ W
  rw [e.symm_apply_apply]

/-- Every intrinsic rational place comes from a rational finite normalization prime or the unique infinity place. -/
theorem primePowerKummerExtension_rationalPlace_cases (W : RationalConstantFieldPlaces E L) :
    (∃ w : HeightOneSpectrum B,
      ∃ hw : Function.Surjective (algebraMap E (B ⧸ w.asIdeal)),
        polynomialNormalizationRationalFinitePlace (K := E) («L» := L) w hw = W) ∨
      primePowerKummerExtensionRationalInfinityPlace p d n r E η = W := by
  by_cases hX : algebraMap E[X] L X ∈ W.val.val
  · obtain ⟨w, hw⟩ := polynomialNormalization_finitePlace_of_coordinate_mem
      W.val.val W.val.property.1 W.val.property.2 hX
    have he : polynomialNormalizationFiniteConstantPlace (K := E) («L» := L) w = W.val := Subtype.ext hw
    have hres : Function.Surjective (valuationConstantResidue
        (polynomialNormalizationFiniteConstantPlace (K := E) («L» := L) w).val
        (polynomialNormalizationFiniteConstantPlace (K := E) («L» := L) w).property.2) :=
      he.symm ▸ W.property
    exact Or.inl ⟨w, (heightOne_constant_residue_surjective_iff w).mp hres, Subtype.ext he⟩
  · exact Or.inr (Subtype.ext (Subtype.ext
      (primePowerKummerExtension_infinityPlace_of_coordinate_notMem p d n r E η
        W.val.val W.val.property.1 W.val.property.2 hX).symm))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
