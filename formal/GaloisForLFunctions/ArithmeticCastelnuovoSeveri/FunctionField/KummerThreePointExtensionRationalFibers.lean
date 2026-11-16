import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionSplitting
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPolynomialPrimeFibers
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerPowerFibers
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FiniteFieldPowerCharacterCounts

/-!
# Literal roots and normalized rational fibers

Away from a zero of the defining function, a soluble fiber splits
completely in the actual normalization. Its rational prime count is
therefore exactly the literal radical root count. An insoluble fiber
has no rational prime, because reduction of the integral radical
would produce a root in the constants.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
    (E : Type*) [Field E] [Finite E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
    (c : Eˣ) (a : ℕ)
local notation "K" => SquareConstantField p (kummerSquareIndex d n)
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "N" => M - 1 + 1
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a

/-- Every soluble nonzero radical fiber has exactly the unchanged covering degree many roots. -/
theorem primePowerThreePointExtension_root_fiber_card
    (x : E) (hx : (kummerBranch c 0 a).eval x ≠ 0)
    (hsol : ∃ β : E, β ^ N = (kummerBranch c 0 a).eval x) :
    Nat.card {β : E | β ^ N = (kummerBranch c 0 a).eval x} = M := by
  have hdiv : M ∣ Nat.card E - 1 :=
    (primePowerKummerCyclicDegree_dvd p d n).trans (finiteField_unit_card_dvd_extension K E)
  rw [finiteField_nonzero_power_fiber_card_of_soluble (M - 1) _ hx hsol,
    primePowerThreePointExtension_index, Nat.gcd_eq_right hdiv]

/-- A nonzero defining value has exactly as many rational normalization primes as literal radical roots. -/
theorem primePowerThreePointExtension_rational_fiber_card
    (x : E) (hx : (kummerBranch c 0 a).eval x ≠ 0) :
    Nat.card (RationalPolynomialPrimeFiber E B x) =
      Nat.card {β : E | β ^ N = (kummerBranch c 0 a).eval x} := by
  classical
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C x)
  letI : (Ideal.span {X - C x}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C x}) ≠ ⊥ := v.ne_bot
  by_cases hsol : ∃ β : E, β ^ N = (kummerBranch c 0 a).eval x
  · rw [primePowerThreePointExtension_root_fiber_card p d n E c a x hx hsol]
    obtain ⟨β, hpow⟩ := hsol
    have hβ : β ≠ 0 := by
      intro h
      rw [h, zero_pow (Nat.succ_ne_zero _)] at hpow
      exact hx hpow.symm
    have hall : ∀ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {X - C x}) B,
        Function.Surjective (algebraMap E (B ⧸ P)) := by
      intro P hP
      obtain ⟨hp, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp hP
      letI := hp
      letI := hover
      let w : HeightOneSpectrum B := ⟨P, hp, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P⟩
      exact primePowerThreePointExtension_rational_residue_surjective p d n E c a x w
        (primePowerThreePointExtension_split_indices p d n E c a x β hβ hpow w).2
    rw [rationalPolynomialPrimeFiber_card_of_all E B x hall]
    exact primePowerThreePointExtension_split_primes_card p d n E c a x β hβ hpow
  · rw [finiteField_nonzero_power_fiber_card (M - 1) _ hx, if_neg hsol]
    apply Nat.card_eq_zero.mpr
    left
    refine ⟨fun P => ?_⟩
    obtain ⟨hp, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp P.val.property
    letI := hp
    letI := hover
    exact hsol (primePowerThreePointExtension_rationalPrime_root p d n E c a x P.val.val P.property)

/-- On the chart omitting zero and one, normalization preserves the literal point count fiber by fiber. -/
theorem primePowerThreePointExtension_punctured_rational_fiber_card
    (x : E) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    Nat.card (RationalPolynomialPrimeFiber E B x) =
      Nat.card {β : E | β ^ N = (c : E) * x * (1 - x) ^ a} := by
  have hx : (kummerBranch c 0 a).eval x ≠ 0 := by
    simp only [kummerBranch, eval_mul, eval_C, eval_X, eval_pow, eval_sub, eval_one,
      Nat.zero_add, pow_one]
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero c) hx0)
      (pow_ne_zero a (sub_ne_zero.mpr (Ne.symm hx1)))
  simpa only [kummerBranch, eval_mul, eval_C, eval_X, eval_pow, eval_sub, eval_one,
    Nat.zero_add, pow_one] using
    primePowerThreePointExtension_rational_fiber_card p d n E c a x hx

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

