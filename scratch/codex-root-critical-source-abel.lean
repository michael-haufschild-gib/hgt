import GaloisForLFunctions.RHTower.MobiusDivisorTerminalCriticalSourceTransform
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic

noncomputable section
open Finset
namespace RHTower

theorem criticalChildSource_eq_psiAbel (M p : ℕ) (hqp : 1 ≤ M / p) :
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
