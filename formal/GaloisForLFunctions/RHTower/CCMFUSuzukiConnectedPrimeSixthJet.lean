import GaloisForLFunctions.RHTower.CCMFUSuzukiConnectedCompletedAbel

/-!
# Six spectral derivatives of the literal connected Suzuki prime channel

The sixth logarithmic derivative removes the connected inverse-cubic weight
on each actual prime atom. The result is the endpoint exponential jet, with
the active critical-Mellin atom retained. This is the prime half of the
completed sixth-jet identity; it gives no bound on the signed window.
-/

open Complex Filter Set Topology MeasureTheory
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

private theorem connected_logMul_six (f : ℕ → ℂ) (n : ℕ) :
    ((LSeries.logMul^[6]) f) n = Complex.log n ^ (6 : ℕ) * f n := by
  simp [Function.iterate_succ_apply, LSeries.logMul]
  ring

theorem ccmSuzukiConnectedPrime_sixth_coeff
    {b ω : ℝ} (hb : 0 < b) (n : ℕ) :
    ((LSeries.logMul^[6]) (ccmSuzukiConnectedPrimeDirichletCoeff b ω)) n =
      ((96 / ω ^ (3 : ℕ) : ℝ) *
        (Real.exp (ω * Real.log n) - Real.exp (-(ω * Real.log n)) -
          2 * ω * Real.log n) : ℂ) *
        ccmGuinandWeilActiveCriticalMellinAtomCoeff b n := by
  rw [connected_logMul_six]
  by_cases hbn : b < Real.log n
  · have hn1 : 1 < n :=
      Nat.one_lt_cast.mp ((Real.log_pos_iff (by positivity)).mp (hb.trans hbn))
    have hlogEq : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast]
      exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
    rw [hlogEq]
    simp only [ccmSuzukiConnectedPrimeDirichletCoeff,
      ccmGuinandWeilThirdGradePrimeDirichletCoeff,
      ccmGuinandWeilActiveCriticalMellinAtomCoeff, if_pos hbn]
    rw [← criticalMellinAtomWeight_mul_ccmGuinandWeilThirdGradeWeight_eq_scale]
    have hjet := ccmSuzukiConnectedThirdGradeWeight_sixthJet ω (Real.log n)
    have hreal := congrArg (fun t : ℝ => t * criticalMellinAtomWeight n) hjet
    have hcomplex := congrArg (fun t : ℝ => (t : ℂ)) hreal
    convert hcomplex using 1
    · rw [ccmSuzukiConnectedThirdGradeWeight]
      push_cast
      ring
    · push_cast
      ring
  · simp [ccmSuzukiConnectedPrimeDirichletCoeff,
      ccmGuinandWeilThirdGradePrimeDirichletCoeff,
      ccmGuinandWeilActiveCriticalMellinAtomCoeff, hbn]

theorem ccmSuzukiConnectedPrime_sixth_deriv
    {b ω : ℝ} (hb : 0 < b) (hω : 0 < ω)
    {u : ℂ} (hu : 1 + ω < u.re) :
    iteratedDeriv 6 (LSeries (ccmSuzukiConnectedPrimeDirichletCoeff b ω)) u =
      LSeries (fun n =>
        ((96 / ω ^ (3 : ℕ) : ℝ) *
          (Real.exp (ω * Real.log n) - Real.exp (-(ω * Real.log n)) -
            2 * ω * Real.log n) : ℂ) *
          ccmGuinandWeilActiveCriticalMellinAtomCoeff b n) u := by
  have habs : LSeries.abscissaOfAbsConv
      (ccmSuzukiConnectedPrimeDirichletCoeff b ω) < u.re :=
    (abscissa_ccmSuzukiConnectedPrimeDirichletCoeff_le hb hω).trans_lt
      (by exact_mod_cast (show ω + 1 < u.re by linarith [hu]))
  rw [LSeries_iteratedDeriv 6 habs]
  rw [show (-1 : ℂ) ^ (6 : ℕ) = 1 by norm_num, one_mul]
  congr 1
  funext n
  exact ccmSuzukiConnectedPrime_sixth_coeff (ω := ω) hb n

end
end RHTower
