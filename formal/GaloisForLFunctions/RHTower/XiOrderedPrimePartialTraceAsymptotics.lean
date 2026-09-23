import GaloisForLFunctions.RHTower.XiOrderedPrimeApproximationAsymptotics
import GaloisForLFunctions.HTGeometry.LogHarmonicResidueTransfer

/-!
# Squared-log partial trace law for the reciprocal-Xi operator

Pointwise approximation numbers asymptotic to `log(n+1)/(π(n+1))` have partial sums asymptotic to
`log²(N+1)/(2π)`.  This is the exact non-trace-class growth asserted by the determinant card.
-/

open Filter

namespace RHTower

noncomputable section

/-- Partial sums of reciprocal-Xi approximation numbers have residue `1 / (2π)`. -/
theorem tendsto_xiOrderedSignedPrimeOperator_approxNumber_partialSum_div_logSq :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N, approxNumber xiOrderedSignedPrimeOperator n) /
        Real.log ((N : ℝ) + 1) ^ (2 : ℕ)) atTop
      (nhds (1 / (2 * Real.pi))) := by
  have hscaled :=
    tendsto_xiOrderedSignedPrimeOperator_approxNumber_div_model.div_const Real.pi
  have hratio : Tendsto (fun n : ℕ =>
      approxNumber xiOrderedSignedPrimeOperator n /
        GaloisForLFunctions.logHarmonicWeight n) atTop
      (nhds (1 / Real.pi)) := by
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hlog : Real.log ((n : ℝ) + 1) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast Nat.succ_lt_succ hn
    rw [GaloisForLFunctions.logHarmonicWeight]
    field_simp [hlog, Real.pi_ne_zero]
  have h :=
    GaloisForLFunctions.tendsto_logSquaredResidue_of_div_logHarmonicWeight_tendsto
      hratio
  convert h using 1 <;> field_simp [Real.pi_ne_zero]

end

end RHTower
