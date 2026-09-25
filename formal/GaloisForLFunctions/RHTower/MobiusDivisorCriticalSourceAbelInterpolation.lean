import GaloisForLFunctions.RHTower.MobiusDivisorTerminalCriticalSourceTransform
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic

/-!
# Exact Abel source inside the clipped terminal prime child

The terminal child source is a continuous square-root-clock interpolation of
the complete Chebyshev defect source. This removes the finite Möbius channel
sum from each terminal prime sample while retaining the exact clipped block.
It is an identity, not a bound on its prime sampling or terminal energy.
-/

noncomputable section
open Finset
namespace RHTower

/-- At every nonempty quotient cutoff, the terminal child is the complete
Chebyshev-defect Abel prefix plus its literal clipped final block. -/
theorem mobiusDivisorCriticalChildSource_eq_psiAbel
    (M p : ℕ) (hqp : 1 ≤ M / p) :
    mobiusDivisorCriticalChildSource M p =
      (∑ k ∈ Ico 1 (M / p),
        (Real.sqrt (k + 1 : ℕ) - Real.sqrt k) * psiDefect k) +
      divisorPrimeClipWeight M p *
        (Real.sqrt (M / p + 1 : ℕ) - Real.sqrt (M / p : ℕ)) *
        psiDefect (M / p) := by
  unfold mobiusDivisorCriticalChildSource
  rw [sum_mobiusDivisorDilationChannel_eq_psiDefect_abel,
    sum_mobiusDivisorDilationChannel_eq_psiDefect_abel]
  rw [sum_Ico_succ_top hqp]
  ring

end RHTower
