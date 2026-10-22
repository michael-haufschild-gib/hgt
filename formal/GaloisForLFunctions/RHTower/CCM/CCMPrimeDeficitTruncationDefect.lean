import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitCoefficientAction
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitDivisorSourceEntry
import GaloisForLFunctions.RHTower.LogarithmicCausalPair

/-!
# The exact signed defect of an arbitrary coefficient cutoff

The error of a shorter Möbius prefix is the complete quadratic tail
pairing. Its square expansion uses the actual causal divisor source;
terms beyond the multiplicative horizon vanish rather than being omitted.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmPrimeDeficitTruncatedAction (U : ℕ) (T : ℝ) : ℝ :=
  ccmPrimeDeficitCoefficientAction T (logarithmicMobiusHeadExtension U (fun _ => 0))

theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction (U : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction U T =
      logarithmicWeightedDilation (logarithmicLongTail U moebiusCoeff)
        (logarithmicWeightedDilation (logarithmicLongTail U moebiusCoeff)
          ccmPrimeDeficitDivisorSource) T := by
  have hc : logarithmicMobiusHeadExtension U (fun _ => 0) =
      fun n => (ArithmeticFunction.moebius n : ℝ) + (-1) * logarithmicLongTail U moebiusCoeff n := by
    funext n
    by_cases hn : n ≤ U
    · simp [logarithmicMobiusHeadExtension, logarithmicLongTail, hn, not_lt.mpr hn]
    · simp [logarithmicMobiusHeadExtension, logarithmicLongTail, hn, Nat.lt_of_not_ge hn,
        moebiusCoeff]
  rw [ccmPrimeDeficitTruncatedAction, hc,
    ccmPrimeDeficitCoefficientAction_mobius_line _ hT (-1)]
  ring

theorem ccmLogChebyshevDeficitPrimitive_sub_truncatedAction_eq_square (U : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T - ccmPrimeDeficitTruncatedAction U T =
      ∑ a ∈ Finset.Icc 1 ⌊Real.exp T⌋₊, ∑ b ∈ Finset.Icc 1 ⌊Real.exp T⌋₊,
        logarithmicLongTail U moebiusCoeff a * logarithmicLongTail U moebiusCoeff b *
          ccmPrimeDeficitDivisorSource (T - Real.log (a * b : ℕ)) := by
  rw [ccmLogChebyshevDeficitPrimitive_sub_truncatedAction U hT]
  exact logarithmicWeightedDilation_pair_eq_square _ _ _
    (fun _ ht => ccmPrimeDeficitDivisorSource_of_nonpos ht.le) T

theorem abs_logarithmicLongTail_moebiusCoeff_le_one (U n : ℕ) :
    |logarithmicLongTail U moebiusCoeff n| ≤ 1 := by
  by_cases hn : U < n
  · simpa only [logarithmicLongTail, if_pos hn] using abs_moebiusCoeff_le_one n
  · simp [logarithmicLongTail, hn]

end RHTower
