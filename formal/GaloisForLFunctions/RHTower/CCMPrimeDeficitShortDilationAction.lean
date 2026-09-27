import GaloisForLFunctions.RHTower.CCMPrimeDeficitShortReflection
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# First variation of the actual short arithmetic correlation

A real Mellin parameter acts on each coefficient through its centered
logarithmic delay. The first variation of the finite quadratic action
is twice the signed pairing in the prime-deficit conservation identity.
The coefficient group law and the first variation are exact; invariance
of a completed action remains a separate mathematical question.
-/

noncomputable section
open MeasureTheory ArithmeticFunction
open scoped BigOperators

namespace RHTower

def logarithmicDilationTwist (T z : ℝ) (n : ℕ) : ℝ :=
  Real.exp (z * (T / 2 - 1 - Real.log n))

theorem logarithmicDilationTwist_add (T z u : ℝ) (n : ℕ) :
    logarithmicDilationTwist T (z + u) n =
      logarithmicDilationTwist T z n * logarithmicDilationTwist T u n := by
  simp only [logarithmicDilationTwist, add_mul, Real.exp_add]

@[simp] theorem logarithmicDilationTwist_zero (T : ℝ) (n : ℕ) :
    logarithmicDilationTwist T 0 n = 1 := by
  simp [logarithmicDilationTwist]

def ccmPrimeDeficitShortCorrelationAction (T z : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
    ∑ b ∈ Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊,
      (moebius a : ℝ) * (moebius b : ℝ) *
        Real.exp (z * (T - Real.log (a * b : ℕ) - 2)) *
          logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ))

/-- The main and error terms complete the first variation without using
the prime deficit itself in the action's definition. -/
def ccmPrimeDeficitShortCompletedDilationAction (T z : ℝ) : ℝ :=
  ccmPrimeDeficitShortCorrelationAction T z +
    2 * z * (ccmPrimeDeficitShortReflectedMainWork T + ccmPrimeDeficitShortReciprocalErrorWork T)

theorem ccmPrimeDeficitShortCorrelationAction_eq_profile_integral (T z : ℝ) :
    ccmPrimeDeficitShortCorrelationAction T z =
      ∫ s in (0 : ℝ)..T,
        logarithmicFiniteEntryProfile (fun n => (moebius n : ℝ) * logarithmicDilationTwist T z n)
          ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth s *
            logarithmicFiniteEntryProfile (fun n => (moebius n : ℝ) * logarithmicDilationTwist T z n)
              ⌊Real.exp (T / 2)⌋₊ logarithmicCenteredSawtooth (T - s) := by
  rw [integral_logarithmicFiniteEntryProfile_pair]
  unfold ccmPrimeDeficitShortCorrelationAction
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hap : (0 : ℝ) < a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
  have hbp : (0 : ℝ) < b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
  have he : Real.exp (z * (T - Real.log (a * b : ℕ) - 2)) =
      logarithmicDilationTwist T z a * logarithmicDilationTwist T z b := by
    rw [logarithmicDilationTwist, logarithmicDilationTwist, ← Real.exp_add,
      Nat.cast_mul, Real.log_mul hap.ne' hbp.ne']
    congr 1
    ring
  rw [he]
  ring

theorem hasDerivAt_ccmPrimeDeficitShortCorrelationAction_zero (T : ℝ) :
    HasDerivAt (ccmPrimeDeficitShortCorrelationAction T)
      (2 * ccmPrimeDeficitShortReciprocalPairing T) 0 := by
  let S := Finset.Icc 1 ⌊Real.exp (T / 2)⌋₊
  let term := fun (a b : ℕ) (z : ℝ) =>
    (moebius a : ℝ) * (moebius b : ℝ) *
      Real.exp (z * (T - Real.log (a * b : ℕ) - 2)) *
        logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ))
  let d := fun a b : ℕ => (moebius a : ℝ) * (moebius b : ℝ) *
    (T - Real.log (a * b : ℕ) - 2) *
      logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ))
  have hd (a b : ℕ) : HasDerivAt (term a b) (d a b) 0 := by
    convert! (((((hasDerivAt_id (0 : ℝ)).mul_const
      (T - Real.log (a * b : ℕ) - 2)).exp).const_mul
        ((moebius a : ℝ) * (moebius b : ℝ))).mul_const
          (logarithmicReciprocalSawtoothCorrelation (T - Real.log (a * b : ℕ)))) using 1
    simp only [d, id_eq, zero_mul, Real.exp_zero, one_mul]
  have hs := HasDerivAt.fun_sum (u := S)
    (fun a _ => HasDerivAt.fun_sum (u := S) (fun b _ => hd a b))
  have he : (∑ a ∈ S, ∑ b ∈ S, d a b) =
      2 * ccmPrimeDeficitShortReciprocalPairing T := by
    rw [ccmPrimeDeficitShortReciprocalPairing_eq_square]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [d]
    ring
  rw [he] at hs
  exact hs

theorem ccmLogChebyshevDeficitPrimitive_dilation_first_variation_conservation
    {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T = ccmPrimeDeficitShortReflectedMainWork T +
      deriv (ccmPrimeDeficitShortCorrelationAction T) 0 / 2 +
        ccmPrimeDeficitShortReciprocalErrorWork T +
          2 * logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ ccmPrimeDeficitDilationRemainder T := by
  rw [(hasDerivAt_ccmPrimeDeficitShortCorrelationAction_zero T).deriv]
  have h := ccmLogChebyshevDeficitPrimitive_reflected_pairing_conservation hT
  linarith only [h]

theorem hasDerivAt_ccmPrimeDeficitShortCompletedDilationAction_zero
    {T : ℝ} (hT : 0 ≤ T) :
    HasDerivAt (ccmPrimeDeficitShortCompletedDilationAction T)
      (2 * ccmPrimeDeficitShortQuadraticWork T) 0 := by
  have h := (hasDerivAt_ccmPrimeDeficitShortCorrelationAction_zero T).add
    (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const
      (ccmPrimeDeficitShortReflectedMainWork T + ccmPrimeDeficitShortReciprocalErrorWork T))
  convert! h using 1
  rw [ccmPrimeDeficitShortQuadraticWork_eq_reflected_pairing hT]
  ring

theorem ccmLogChebyshevDeficitPrimitive_completed_dilation_conservation
    {T : ℝ} (hT : 0 ≤ T) :
    ccmLogChebyshevDeficitPrimitive T =
      deriv (ccmPrimeDeficitShortCompletedDilationAction T) 0 / 2 +
        2 * logarithmicShortMobiusInverse ⌊Real.exp (T / 2)⌋₊ ccmPrimeDeficitDilationRemainder T := by
  rw [(hasDerivAt_ccmPrimeDeficitShortCompletedDilationAction_zero hT).deriv]
  have h := ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork hT
  linarith only [h]

theorem abs_ccmLogChebyshevDeficitPrimitive_sub_completed_dilation_deriv_le
    {T : ℝ} (hT : 0 ≤ T) :
    |ccmLogChebyshevDeficitPrimitive T -
      deriv (ccmPrimeDeficitShortCompletedDilationAction T) 0 / 2| ≤ 7 * Real.exp (T / 2) := by
  rw [(hasDerivAt_ccmPrimeDeficitShortCompletedDilationAction_zero hT).deriv,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  exact abs_ccmLogChebyshevDeficitPrimitive_sub_shortQuadraticWork_le hT

end RHTower
