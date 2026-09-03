import GaloisForLFunctions.RHTower.PrimeHodgeHistoryIntegralNuclearHomotopyDefect
import GaloisForLFunctions.RHTower.ThetaSurvivalRelativeCurvaturePrimeLift

/-!
# Prime--Hodge first-exit transgression

The additive relative curvature of the forced theta-survival shift determines its cumulative
survival ratios.  Their ordered product determines the surviving history mass, and its next
boundary loss determines the integral--nuclear defect.  This file lifts that nonlinear
first-exit law through the common prime-mixed Stokes kernel.

No zero, divisor copy, ordinate, or RH premise enters the construction.
-/

open Filter Topology BigOperators

namespace PrimeHodgeHistory

noncomputable section

/-- Nonlinear first-exit transgression of the additive relative-curvature increments. -/
def curvatureFirstExitWeight (n : ℕ) : ℝ :=
  (∏ j ∈ Finset.range n,
      ∑ k ∈ Finset.range (j + 1), relativeCurvatureWeight k) *
    (1 - ∑ k ∈ Finset.range (n + 1), relativeCurvatureWeight k)

/-- Additive curvature, cumulative survival, multiplicative history, and emitted nuclear flux
are one exact formation law. -/
theorem curvatureFirstExitWeight_eq_w (n : ℕ) :
    curvatureFirstExitWeight n = w n := by
  rw [curvatureFirstExitWeight]
  simp_rw [← survivalRatio_eq_sum_range_relativeCurvatureWeight]
  rw [← m_eq_prod_survivalRatio]
  exact (w_eq_m_mul_one_sub_survivalRatio n).symm

theorem curvatureFirstExitWeight_nonneg (n : ℕ) :
    0 ≤ curvatureFirstExitWeight n := by
  rw [curvatureFirstExitWeight_eq_w]
  exact (w_pos n).le

theorem summable_sq_curvatureFirstExitWeight :
    Summable fun n => curvatureFirstExitWeight n ^ 2 := by
  have hw2 : Summable fun n => w n ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) ?_
      (summable_w.mul_left (2 / 3))
    intro n
    nlinarith [w_pos n, w_le_two_thirds n]
  simpa only [curvatureFirstExitWeight_eq_w] using hw2

end


end PrimeHodgeHistory

namespace RHTower

open ContinuousLinearMap

noncomputable section

/-- Prime-mixed lift of the nonlinear first-exit transgression at positive aperture. -/
def primeHodgeHistoryCurvatureFirstExitOperator {d : ℝ} (hd : 0 < d) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  historyStokesOperator PrimeHodgeHistory.curvatureFirstExitWeight
    PrimeHodgeHistory.curvatureFirstExitWeight_nonneg
    PrimeHodgeHistory.summable_sq_curvatureFirstExitWeight hd

/-- The curvature-generated first-exit operator is exactly the pre-divisor integral--nuclear
defect, not merely trace-equivalent to it. -/
theorem primeHodgeHistoryCurvatureFirstExitOperator_eq_defectOperator
    {d : ℝ} (hd : 0 < d) :
    primeHodgeHistoryCurvatureFirstExitOperator hd =
      primeHodgeHistoryDefectOperator hd := by
  unfold primeHodgeHistoryCurvatureFirstExitOperator
    historyStokesOperator primeHodgeHistoryDefectOperator
  apply HilbertSchmidt.toOperator_congr
  funext ab
  simp only [historyStokesKernel, primeHodgeHistoryDefectKernel,
    PrimeHodgeHistory.curvatureFirstExitWeight_eq_w]

/-- One signed two-sided wall family, now constructed from additive relative curvature followed by
multiplicative first-exit formation. -/
def primeHodgeHistoryCurvatureFirstExitHomotopyDefect (t : ℝ) :
    PrimeHodgeHistoryHilbert →L[ℂ] PrimeHodgeHistoryHilbert :=
  if ht : t = 0 then 0 else
    (Real.sign t : ℂ) •
      primeHodgeHistoryCurvatureFirstExitOperator (abs_pos.mpr ht)

/-- The first-exit construction recovers the literal signed pre-divisor defect at every wall
parameter. -/
theorem primeHodgeHistoryCurvatureFirstExitHomotopyDefect_eq (t : ℝ) :
    primeHodgeHistoryCurvatureFirstExitHomotopyDefect t =
      primeHodgeHistoryIntegralNuclearHomotopyDefect t := by
  by_cases ht : t = 0
  · subst t
    simp [primeHodgeHistoryCurvatureFirstExitHomotopyDefect]
  · rw [primeHodgeHistoryCurvatureFirstExitHomotopyDefect,
      primeHodgeHistoryIntegralNuclearHomotopyDefect, dif_neg ht, dif_neg ht,
      primeHodgeHistoryCurvatureFirstExitOperator_eq_defectOperator]

/-- Exact same-boundary conservation on every history grade and every ordered prime pair. -/
theorem primeHodgeHistory_firstExit_curvature_kernel_conservation
    (n : ℕ) (p q : Nat.Primes) :
    (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ) *
        primeHodgeHistoryDefectKernel 1 ((n, p), (n, q)) =
      (PrimeHodgeHistory.w n : ℂ) *
        historyStokesKernel PrimeHodgeHistory.relativeCurvatureWeight 1
          ((n, p), (n, q)) := by
  rw [primeHodgeHistoryDefectKernel, historyStokesKernel, if_pos rfl, if_pos rfl]
  ring

/-- Closed certificate: the nonlinear additive-to-multiplicative transgression constructs the
same integral, nuclear, prime-mixed homotopy defect and preserves the full ordered-prime
boundary, not only its scalar trace. -/
theorem primeHodgeHistoryCurvatureFirstExitHomotopyDefect_closed (t : ℝ) :
    primeHodgeHistoryCurvatureFirstExitHomotopyDefect t =
        primeHodgeHistoryIntegralNuclearHomotopyDefect t ∧
      MemSchattenClass 1
        (primeHodgeHistoryCurvatureFirstExitHomotopyDefect t) ∧
      ContinuousLinearMap.opTrace
          (primeHodgeHistoryCurvatureFirstExitHomotopyDefect t) =
        (Real.sign t : ℂ) ∧
      traceNorm PrimeHodgeHistoryHilbert
          (primeHodgeHistoryCurvatureFirstExitHomotopyDefect t) =
        |Real.sign t| ∧
      (∀ n,
        PrimeHodgeHistory.curvatureFirstExitWeight n = PrimeHodgeHistory.w n) ∧
      (∀ n p q,
        (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ) *
            primeHodgeHistoryDefectKernel 1 ((n, p), (n, q)) =
          (PrimeHodgeHistory.w n : ℂ) *
            historyStokesKernel PrimeHodgeHistory.relativeCurvatureWeight 1
              ((n, p), (n, q))) := by
  rw [primeHodgeHistoryCurvatureFirstExitHomotopyDefect_eq]
  exact ⟨rfl,
    primeHodgeHistoryIntegralNuclearHomotopyDefect_memSchattenClass_one t,
    opTrace_primeHodgeHistoryIntegralNuclearHomotopyDefect t,
    traceNorm_primeHodgeHistoryIntegralNuclearHomotopyDefect t,
    PrimeHodgeHistory.curvatureFirstExitWeight_eq_w,
    primeHodgeHistory_firstExit_curvature_kernel_conservation⟩

end
end RHTower
