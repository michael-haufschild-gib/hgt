import GaloisForLFunctions.RHTower.RoutePJuliaKreinHistoryPort
import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarCovarianceHardCore

/-!
# SP-E/P diagonal clock-transport no-go

The physical P-G186 incidence is a Burnol window Gram.  For one retained label,
retuning its ordinate clock cannot alter its diagonal Gram entry: the exact Cauchy
kernel sees only the self-difference `kappa i - kappa i = 0`.  In contrast, the
literal SP-E first adjacent-gap covariance coefficient grows strictly when the head
passes from cutoff `2` to `3`.

Hence a source-to-P transport cannot retain one label and encode this live SP-E
coefficient in a P-G186 diagonal while trying to absorb all cutoff dynamics by clock
retuning.  The survivor is necessarily off-diagonal and history-cocyclic; this does
not construct that transport or bound its cofinal limit.
-/

namespace RHTower

noncomputable section

/-- A P-G186 window Gram diagonal depends on a label but not on its clock. -/
theorem routePPrimitiveBurnolWindowGramMatrix_diagonal_clock_invariant {N : ℕ}
    (pe : Fin N → Nat.Primes × ℕ) (kappa nu : Fin N → ℝ) (i : Fin N) :
    routePPrimitiveBurnolWindowGramMatrix pe kappa i i =
      routePPrimitiveBurnolWindowGramMatrix pe nu i i := by
  rw [routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy,
    routePPrimitiveBurnolWindowGramMatrix_eq_baseCauchy,
    routePPrimitiveBaseCauchyCubicKernelMatrix_apply,
    routePPrimitiveBaseCauchyCubicKernelMatrix_apply]
  simp

/-- **Clock-diagonal no-go.** No fixed one-label P-G186 packet, even with arbitrary
cutoff-dependent clock retuning, can represent both literal SP-E first-gap coefficients at
cutoffs `2` and `3` on its diagonal. -/
theorem not_exists_speQuantileRieszCovarianceGap_two_three_as_routePWindowDiagonal :
    ¬ ∃ (pe : Fin 1 → Nat.Primes × ℕ) (kappa : ℕ → Fin 1 → ℝ),
      (routePPrimitiveBurnolWindowGramMatrix pe (kappa 2) 0 0).re =
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel 2 0 ∧
        (routePPrimitiveBurnolWindowGramMatrix pe (kappa 3) 0 0).re =
          ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel 3 0 := by
  rintro ⟨pe, kappa, htwo, hthree⟩
  have hdiag := routePPrimitiveBurnolWindowGramMatrix_diagonal_clock_invariant
    pe (kappa 2) (kappa 3) 0
  have hdiagRe := congrArg Complex.re hdiag
  rw [htwo, hthree] at hdiagRe
  exact (ne_of_lt ccmActualHeadMatchedQuantileParabolicCovarianceGapKernel_two_lt_three) hdiagRe

end

end RHTower
