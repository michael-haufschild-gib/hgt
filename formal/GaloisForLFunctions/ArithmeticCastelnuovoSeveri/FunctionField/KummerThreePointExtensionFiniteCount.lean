import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionRationalBoundary
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerPuncturedJacobiCount

/-!
# From the punctured equation to all finite rational primes

On the punctured chart the literal root count equals the normalized
rational-prime count. The origin contributes one and the fiber above
one contributes the branch gcd. Summing the disjoint coordinate fibers
therefore gives the complete finite normalization count.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain ArithmeticHarmonicAnalysis
open scoped Classical

private theorem sum_zero_one_punctured (K : Type*) [Field K] [Fintype K] (f : K → ℕ) :
    (∑ x : K, f x) = f 0 + f 1 +
      ∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0 ∧ x ≠ 1), f x := by
  classical
  have h0 : (∑ x : K, if x = 0 then f 0 else 0) = f 0 := by
    rw [Finset.sum_eq_single 0]
    · rw [if_pos rfl]
    · intro x _ hx
      rw [if_neg hx]
    · intro h
      exact (h (Finset.mem_univ 0)).elim
  have h1 : (∑ x : K, if x = 1 then f 1 else 0) = f 1 := by
    rw [Finset.sum_eq_single 1]
    · rw [if_pos rfl]
    · intro x _ hx
      rw [if_neg hx]
    · intro h
      exact (h (Finset.mem_univ 1)).elim
  rw [Finset.sum_filter, ← h0, ← h1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx0 : x = 0
  · subst x
    simp
  · by_cases hx1 : x = 1
    · subst x
      simp
    · have hx : x ≠ 0 ∧ x ≠ 1 := ⟨hx0, hx1⟩
      simp only [if_neg hx0, if_neg hx1, if_pos hx, zero_add]

variable (p : ℕ) [Fact p.Prime] (d n r : ℕ)
    (E : Type*) [Field E] [Fintype E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E] (η : Eˣ)
local notation "q" => p ^ (d + 1)
local notation "R" => kummerExponent q r
local notation "a" => (q - 1) * R
local notation "c" => (η⁻¹) ^ a
local notation "M" => primePowerKummerCyclicDegree p d n
local notation "δ" => Nat.gcd (p ^ (kummerSquareIndex d n + 1) + 1) R
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a

local instance finiteCountPolynomialTorsionFree : Module.IsTorsionFree E[X] L :=
  kummerBranchField_torsionFree c 0 a (M - 1)

local instance finiteCountNormalizationTorsionFree : Module.IsTorsionFree E[X] B :=
  inferInstanceAs (Module.IsTorsionFree E[X] (integralClosure E[X] L))

/-- The complete finite rational-prime count equals the punctured literal count plus the two resolved boundary fibers. -/
theorem primePowerKummerExtension_finiteRationalPrimes_card :
    Nat.card (RationalPolynomialPrimes E B) =
      Nat.card (PuncturedKummerPoints (M - 1) a c) + 1 + (q - 1) * δ := by
  classical
  let f : E → ℕ := fun x => Nat.card (RationalPolynomialPrimeFiber E B x)
  have h0 : f 0 = 1 := primePowerKummerExtension_origin_rational_fiber_card p d n r E η
  have h1 : f 1 = (q - 1) * δ := primePowerKummerExtension_one_rational_fiber_card p d n r E η
  have hpunct :
      (∑ x ∈ Finset.univ.filter (fun x : E => x ≠ 0 ∧ x ≠ 1), f x) =
        Nat.card (PuncturedKummerPoints (M - 1) a c) := by
    rw [puncturedKummerPoints_card]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    exact primePowerThreePointExtension_punctured_rational_fiber_card p d n E c a x hx'.1 hx'.2
  calc
    Nat.card (RationalPolynomialPrimes E B) = ∑ x : E, f x := rationalPolynomialPrimes_card E B
    _ = f 0 + f 1 + ∑ x ∈ Finset.univ.filter (fun x : E => x ≠ 0 ∧ x ≠ 1), f x :=
      sum_zero_one_punctured E f
    _ = Nat.card (PuncturedKummerPoints (M - 1) a c) + 1 + (q - 1) * δ := by
      rw [h0, h1, hpunct]
      omega

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

