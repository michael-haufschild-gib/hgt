import GaloisForLFunctions.RHTower.CCMFUSuzukiMobiusDivisorDilationChannels

/-!
# Source-faithful Möbius--Riesz tail duality

The literal transported tail can be read in either source coordinate without an estimate:
pairing any finite source with the signed Riesz tail is exactly the same finite hyperbola action
with the Möbius coefficient exposed first.  This retains the moving square-root endpoint,
all Möbius signs, and every source coefficient.  In particular, it does not replace the completed
prime--polar source by an absolute or positive surrogate.
-/

noncomputable section

namespace RHTower

open Finset

/-- **Finite source--tail duality.**  The literal pairing with the transported signed
Möbius--Riesz tail equals its Möbius-first finite hyperbola form. -/
theorem sum_mul_mobiusDilationRieszTail_eq_dilationDual
    (M : ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 (M - 1), a n * mobiusDilationRieszTail M n) =
      ∑ d ∈ Icc 1 (M - 1), ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ∑ n ∈ Icc 1 ((M - 1) / d),
          a n * (Real.sqrt M - Real.sqrt (n * d : ℕ)) := by
  rw [show (∑ n ∈ Icc 1 (M - 1), a n * mobiusDilationRieszTail M n) =
      ∑ n ∈ Icc 1 (M - 1), ∑ d ∈ Icc 1 ((M - 1) / n),
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          (a n * (Real.sqrt M - Real.sqrt (n * d : ℕ))) by
    simp only [mobiusDilationRieszTail]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring]
  rw [← sum_hyperbola_swap_real (M - 1)
    (fun d n => ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
      (a n * (Real.sqrt M - Real.sqrt (n * d : ℕ))))]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]

end RHTower
