import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerThreePointArithmetic
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionInfinityRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialNormalizationResidues

/-!
# The actual infinity place over extended constants

The prime-power pole degree is coprime to the fixed covering degree.
The reciprocal normalization therefore has one prime above its origin,
with residue degree one. This supplies its actual height-one place and
surjectivity of the constant map to its residue field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] (η : Eˣ)
local notation "q" => p ^ (d + 1)
local notation "a" => (q - 1) * kummerExponent q r
local notation "c" => (η⁻¹) ^ a
local notation "L" => PrimePowerThreePointExtensionInfinityField p d n E c a
local notation "B" => PrimePowerThreePointExtensionInfinityNormalization p d n E c a

local instance infinityPolynomialTorsionFree : Module.IsTorsionFree E[X] L :=
  kummerInfinityField_torsionFree c 0 a (primePowerKummerCyclicDegree p d n - 1)

local instance infinityNormalizationTorsionFree : Module.IsTorsionFree E[X] B :=
  inferInstanceAs (Module.IsTorsionFree E[X] (integralClosure E[X] L))

local instance infinityNormalizationDedekind : IsDedekindDomain B :=
  primePowerThreePointExtensionInfinityNormalization_dedekind p d n E c a

local instance infinityNormalizationFinite : Module.Finite E[X] B :=
  primePowerThreePointExtensionInfinityNormalization_finite p d n E c a

local instance infinityNormalizationAlgebra : Algebra B L :=
  inferInstanceAs (Algebra (integralClosure E[X] L) L)

local instance infinityNormalizationFractionRing : IsFractionRing B L :=
  primePowerThreePointExtensionInfinityNormalization_fractionRing p d n E c a

private def infinityPrimeData : {P : Ideal B // P.IsPrime ∧
    P.LiesOver (Ideal.span {(X : E[X])}) ∧
    (Ideal.span {(X : E[X])}).inertiaDeg' P = 1 ∧
    IsDedekindDomain.primesOverFinset (Ideal.span {(X : E[X])}) B = {P}} := by
  classical
  let v := kummerInfinityBasePlace (K := E)
  letI : (Ideal.span {(X : E[X])}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {(X : E[X])}) ≠ ⊥ := v.ne_bot
  let h := primePowerThreePointExtensionInfinity_singleton p d n E c a
    (primePowerThreePointExponent_pole_coprime p d n r)
  let P : Ideal B := h.choose
  have hP : IsDedekindDomain.primesOverFinset (Ideal.span {(X : E[X])}) B = {P} :=
    h.choose_spec.1
  have hf : (Ideal.span {(X : E[X])}).inertiaDeg' P = 1 := h.choose_spec.2
  have hm : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(X : E[X])}) B := by
    rw [hP]
    exact Finset.mem_singleton_self _
  obtain ⟨hp, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp hm
  exact ⟨P, hp, hover, hf, hP⟩

/-- The unique actual height-one infinity prime of the fixed-degree family over extended constants. -/
def primePowerKummerExtensionInfinityPlace : HeightOneSpectrum B := by
  let P := infinityPrimeData p d n r E η
  letI := P.property.2.1
  have hv0 : (Ideal.span {(X : E[X])}) ≠ ⊥ :=
    (kummerInfinityBasePlace (K := E)).ne_bot
  exact ⟨P.val, P.property.1,
    Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P.val⟩

/-- The canonical infinity prime lies over the reciprocal origin. -/
instance primePowerKummerExtensionInfinityPlace_liesOver :
    (primePowerKummerExtensionInfinityPlace p d n r E η).asIdeal.LiesOver
      (Ideal.span {(X : E[X])}) :=
  (infinityPrimeData p d n r E η).property.2.1

/-- The full reciprocal-origin fiber consists of the canonical infinity prime. -/
theorem primePowerKummerExtensionInfinityPlace_fiber :
    IsDedekindDomain.primesOverFinset (Ideal.span {(X : E[X])}) B =
      {(primePowerKummerExtensionInfinityPlace p d n r E η).asIdeal} :=
  (infinityPrimeData p d n r E η).property.2.2.2

/-- The actual infinity prime has constant residue degree one. -/
theorem primePowerKummerExtensionInfinityPlace_inertia :
    (Ideal.span {(X : E[X])}).inertiaDeg'
      (primePowerKummerExtensionInfinityPlace p d n r E η).asIdeal = 1 :=
  (infinityPrimeData p d n r E η).property.2.2.1

/-- The actual infinity prime is totally ramified with the fixed covering degree. -/
theorem primePowerKummerExtensionInfinityPlace_ramification :
    (Ideal.span {(X : E[X])}).ramificationIdx'
      (primePowerKummerExtensionInfinityPlace p d n r E η).asIdeal =
        primePowerKummerCyclicDegree p d n :=
  primePowerThreePointExtensionInfinity_ramification_eq_degree p d n E c a
    (primePowerThreePointExponent_pole_coprime p d n r) _

/-- Every prime of the reciprocal normalization above the origin is the canonical infinity prime. -/
theorem primePowerKummerExtensionInfinityPlace_unique
    (P : Ideal B) [hP : P.IsPrime] [P.LiesOver (Ideal.span {(X : E[X])})] :
    P = (primePowerKummerExtensionInfinityPlace p d n r E η).asIdeal := by
  classical
  let v := kummerInfinityBasePlace (K := E)
  letI : (Ideal.span {(X : E[X])}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {(X : E[X])}) ≠ ⊥ := v.ne_bot
  have hm := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mpr ⟨hP, inferInstance⟩
  rwa [primePowerKummerExtensionInfinityPlace_fiber, Finset.mem_singleton] at hm

/-- Constants surject onto the actual residue field at infinity over every extension of constants. -/
theorem primePowerKummerExtensionInfinityPlace_residue_surjective :
    Function.Surjective (algebraMap E
      (B ⧸ (primePowerKummerExtensionInfinityPlace p d n r E η).asIdeal)) := by
  let w := primePowerKummerExtensionInfinityPlace p d n r E η
  letI : w.asIdeal.LiesOver (Ideal.span {X - C (0 : E)}) := by
    simpa only [map_zero, sub_zero] using
      (primePowerKummerExtensionInfinityPlace_liesOver p d n r E η)
  have hf : (Ideal.span {X - C (0 : E)}).inertiaDeg' w.asIdeal = 1 := by
    simpa only [map_zero, sub_zero] using
      primePowerKummerExtensionInfinityPlace_inertia p d n r E η
  exact heightOne_linearPrime_constant_residue_surjective w 0 hf

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
