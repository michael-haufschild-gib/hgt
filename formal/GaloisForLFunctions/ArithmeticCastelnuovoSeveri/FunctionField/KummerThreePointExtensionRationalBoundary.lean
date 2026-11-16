import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionBoundary
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionRationalFibers

/-!
# Rationality of both finite boundary fibers

The singleton origin fiber has constant residue field. Every prime of
the gcd-sized fiber above one also has constant residue field. Thus the
full boundary prime counts are already rational-prime counts, including
the zero-exponent case.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (E : Type*) [Field E] [Finite E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] (η : Eˣ)
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "a" => (q - 1) * R
local notation "c" => (η⁻¹) ^ a
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a

local instance boundaryPolynomialTorsionFree : Module.IsTorsionFree E[X] L :=
  kummerBranchField_torsionFree c 0 a (primePowerKummerCyclicDegree p d n - 1)

local instance boundaryNormalizationTorsionFree : Module.IsTorsionFree E[X] B :=
  inferInstanceAs (Module.IsTorsionFree E[X] (integralClosure E[X] L))

local instance boundaryNormalizationAlgebra : Algebra B L :=
  inferInstanceAs (Algebra (integralClosure E[X] L) L)

local instance boundaryNormalizationFractionRing : IsFractionRing B L :=
  primePowerThreePointExtensionNormalization_fractionRing p d n E c a

/-- The rational part of the normalized origin fiber consists of its unique prime. -/
theorem primePowerKummerExtension_origin_rational_fiber_card :
    Nat.card (RationalPolynomialPrimeFiber E B 0) = 1 := by
  classical
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (0 : E))
  letI : (Ideal.span {X - C (0 : E)}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C (0 : E)}) ≠ ⊥ := v.ne_bot
  obtain ⟨P₀, hP₀, hf⟩ := primePowerThreePointExtension_origin_singleton p d n E c a
  have hall : ∀ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {X - C (0 : E)}) B,
      Function.Surjective (algebraMap E (B ⧸ P)) := by
    intro P hP
    obtain ⟨hp, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp hP
    letI := hp
    letI := hover
    let w : HeightOneSpectrum B := ⟨P, hp, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P⟩
    have hEq : P = P₀ := by rwa [hP₀, Finset.mem_singleton] at hP
    have hfP : (Ideal.span {X - C (0 : E)}).inertiaDeg' P = 1 := by
      rw [hEq]
      exact hf
    exact heightOne_linearPrime_constant_residue_surjective w 0 hfP
  rw [rationalPolynomialPrimeFiber_card_of_all E B 0 hall, hP₀, Finset.card_singleton]

/-- Every prime above one is rational, so the rational fiber has the full branch-gcd cardinality. -/
theorem primePowerKummerExtension_one_rational_fiber_card :
    Nat.card (RationalPolynomialPrimeFiber E B 1) =
      (q - 1) * Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1) R := by
  classical
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (1 : E))
  letI : (Ideal.span {X - C (1 : E)}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C (1 : E)}) ≠ ⊥ := v.ne_bot
  have hall : ∀ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {X - C (1 : E)}) B,
      Function.Surjective (algebraMap E (B ⧸ P)) := by
    intro P hP
    obtain ⟨hp, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp hP
    letI := hp
    letI := hover
    let w : HeightOneSpectrum B := ⟨P, hp, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P⟩
    exact heightOne_linearPrime_constant_residue_surjective w 1
      (primePowerKummerExtension_branch_indices p d n r E η w).2
  rw [rationalPolynomialPrimeFiber_card_of_all E B 1 hall,
    primePowerThreePointExtension_inversePower_branch_primes_card,
    primePowerThreePointExponent_gcd]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

