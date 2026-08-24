import GaloisForLFunctions.RHTower.TransverseRelocationCarrier
import GaloisForLFunctions.RHTower.ReciprocalGammaExactOrderOne
import GaloisForLFunctions.RHTower.LiReflectedGammaCarrier
import GaloisForLFunctions.HTGeometry.BesselOrderPhysicalScan
import GaloisForLFunctions.HTGeometry.MovingCanonicalSurgery
import GaloisForLFunctions.HTGeometry.LocalInverseHypertranscendence

/-!
# Analytic completion of the transverse relocation carrier

This leaf closes the global analytic claims for the reflected-Gamma/Cosh relocation family.  The
Cosh factor is a nonzero differentially algebraic entire function of order at most one.  Therefore
it preserves reflected-Gamma hypertranscendence, while the inherited Gamma arithmetic-progression
divisor proves exact entire order one for both centered and critical-line coordinates.
-/

open Complex Set
open scoped Differential

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

theorem coshQuartetEnvelope_analyticOnNhd (a : ℝ) :
    AnalyticOnNhd ℂ (coshQuartetEnvelope a) Set.univ :=
  fun z _ => coshQuartetEnvelope_analyticAt a z

theorem coshQuartetEnvelope_orderOneEnvelope (a : ℝ) :
    OrderOneEnvelope (coshQuartetEnvelope a) := by
  have hplus := orderOneEnvelope_exp_linear (2 : ℂ)
  have hminus := orderOneEnvelope_exp_linear (-2 : ℂ)
  have hcosh : OrderOneEnvelope (fun z : ℂ => Complex.cosh (2 * z)) := by
    have h := (hplus.add hminus).const_mul (1 / 2 : ℂ)
    exact h.congr fun z => by
      rw [Complex.cosh]
      ring_nf
  have h := (hcosh.add
    (orderOneEnvelope_const (Complex.cosh (2 * (a : ℂ))))).const_mul (1 / 2 : ℂ)
  exact h.congr fun z => by
    have htwo := two_mul_coshQuartetEnvelope a z
    rw [← htwo]
    ring

theorem coshQuartetEnvelope_differentiallyAlgebraic (a : ℝ) :
    DifferentiallyAlgebraic (coshQuartetEnvelope a) := by
  have hplusDA := differentiallyAlgebraic_cexp_linear (2 : ℂ)
  have hminusDA := differentiallyAlgebraic_cexp_linear (-2 : ℂ)
  have hplusAn : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (2 * z)) Set.univ := by
    exact (analyticOnNhd_const.mul analyticOnNhd_id).cexp
  have hminusAn : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (-2 * z)) Set.univ := by
    exact (analyticOnNhd_const.mul analyticOnNhd_id).cexp
  have hsumDA : DifferentiallyAlgebraic
      (fun z : ℂ => Complex.exp (2 * z) + Complex.exp (-2 * z)) :=
    differentiallyAlgebraic_add hplusAn hminusAn hplusDA hminusDA
  have hcoshDA : DifferentiallyAlgebraic (fun z : ℂ => Complex.cosh (2 * z)) := by
    have h := hsumDA.const_mul (by norm_num : (1 / 2 : ℂ) ≠ 0)
    convert h using 1
    funext z
    rw [Complex.cosh]
    ring_nf
  have hcoshAn : AnalyticOnNhd ℂ (fun z : ℂ => Complex.cosh (2 * z)) Set.univ := by
    intro z _
    exact Complex.analyticAt_cosh.comp (analyticAt_const.mul analyticAt_id)
  have hconstAn : AnalyticOnNhd ℂ
      (fun _ : ℂ => Complex.cosh (2 * (a : ℂ))) Set.univ := analyticOnNhd_const
  have hadd := differentiallyAlgebraic_add hcoshAn hconstAn hcoshDA
    (differentiallyAlgebraic_const (Complex.cosh (2 * (a : ℂ))))
  have hscaled := hadd.const_mul (by norm_num : (1 / 2 : ℂ) ≠ 0)
  convert hscaled using 1
  funext z
  have htwo := two_mul_coshQuartetEnvelope a z
  rw [← htwo]
  ring

theorem coshQuartetEnvelope_ne_zero_zero (a : ℝ) :
    coshQuartetEnvelope a 0 ≠ 0 := by
  by_cases ha : a = 0
  · simp [ha, coshQuartetEnvelope]
  · obtain ⟨r, hr, hvalue⟩ :=
      coshQuartetEnvelope_mul_I_pos_real (a := a) (y := 0) ha
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hr)
    simpa using hvalue.trans_ne hr0

theorem coshQuartetEnvelope_analyticMeroElement_ne_zero (a : ℝ) :
    analyticMeroElement (coshQuartetEnvelope a)
      (coshQuartetEnvelope_analyticOnNhd a) ≠ 0 := by
  exact analyticMeroElement_ne_zero isOpen_univ isPreconnected_univ Set.univ_nonempty
    (coshQuartetEnvelope_analyticOnNhd a) (Set.mem_univ 0)
    (coshQuartetEnvelope_ne_zero_zero a)

theorem reflectedGammaQuartetCarrier_orderOneEnvelope (beta a : ℝ) :
    OrderOneEnvelope (reflectedGammaQuartetCarrier beta a) := by
  exact ((reflectedGammaCarrier_orderOneEnvelope beta).mul
    (coshQuartetEnvelope_orderOneEnvelope a)).congr fun z => rfl

theorem reflectedGammaQuartetCarrier_ne_zero_zero
    {beta : ℝ} (hbeta : 0 < beta) (a : ℝ) :
    reflectedGammaQuartetCarrier beta a 0 ≠ 0 := by
  exact mul_ne_zero (reflectedGammaCarrier_ne_zero_zero hbeta)
    (coshQuartetEnvelope_ne_zero_zero a)

theorem reflectedGammaQuartetCarrier_zero_arithmeticProgression
    (beta a : ℝ) (n : ℕ) :
    reflectedGammaQuartetCarrier beta a
      (Complex.I * (beta : ℂ) + n • Complex.I) = 0 := by
  rw [reflectedGammaQuartetCarrier,
    reflectedGammaCarrier_zero_arithmeticProgression, zero_mul]

theorem reflectedGammaQuartetCarrier_hasExactEntireOrderOne
    {beta : ℝ} (hbeta : 0 < beta) (a : ℝ) :
    HasExactEntireOrderOne (reflectedGammaQuartetCarrier beta a) := by
  refine ⟨Complex.analyticOnNhd_univ_iff_differentiable.mp
      (reflectedGammaQuartetCarrier_analyticOnNhd beta a),
    reflectedGammaQuartetCarrier_orderOneEnvelope beta a, ?_⟩
  intro hmin
  exact hmin.no_arithmeticProgression_zeros
    (reflectedGammaQuartetCarrier_ne_zero_zero hbeta a) I_ne_zero
    (reflectedGammaQuartetCarrier_zero_arithmeticProgression beta a)

theorem reflectedGammaQuartetCarrier_hypertranscendental
    {beta a : ℝ}
    (hsep : ∀ k : ℤ, (2 * beta : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (reflectedGammaQuartetCarrier beta a) := by
  have h := hypertranscendental_mul_entire_differentiallyAlgebraic
      (reflectedGammaCarrier_analyticOnNhd beta)
      (coshQuartetEnvelope_analyticOnNhd a)
      (coshQuartetEnvelope_differentiallyAlgebraic a)
      (coshQuartetEnvelope_analyticMeroElement_ne_zero a)
      (reflectedGammaCarrier_hypertranscendental hsep)
  change Hypertranscendental
    (fun z => reflectedGammaCarrier beta z * coshQuartetEnvelope a z)
  simpa only [mul_comm] using h

theorem reflectedGammaQuartetCarrier_hypertranscendental_of_two_mul_sub_one
    {beta a : ℝ}
    (hsep : ∀ k : ℤ, (2 * beta - 1 : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (reflectedGammaQuartetCarrier beta a) := by
  apply reflectedGammaQuartetCarrier_hypertranscendental
  intro k hk
  apply hsep (k - 1)
  push_cast
  linear_combination hk

theorem transverseRelocationCarrier_orderOneEnvelope (beta a : ℝ) :
    OrderOneEnvelope (transverseRelocationCarrier beta a) := by
  have h := (reflectedGammaQuartetCarrier_orderOneEnvelope beta a).comp_affine
    1 (-(1 / 2 : ℂ))
  exact h.congr fun s => by
    unfold transverseRelocationCarrier
    congr 1
    ring

theorem transverseRelocationCarrier_ne_zero_half
    {beta : ℝ} (hbeta : 0 < beta) (a : ℝ) :
    transverseRelocationCarrier beta a (1 / 2 : ℂ) ≠ 0 := by
  simpa [transverseRelocationCarrier] using
    reflectedGammaQuartetCarrier_ne_zero_zero hbeta a

theorem transverseRelocationCarrier_zero_arithmeticProgression
    (beta a : ℝ) (n : ℕ) :
    transverseRelocationCarrier beta a
      ((1 / 2 : ℂ) + Complex.I * (beta : ℂ) + n • Complex.I) = 0 := by
  unfold transverseRelocationCarrier
  convert reflectedGammaQuartetCarrier_zero_arithmeticProgression beta a n using 1
  ring

theorem transverseRelocationCarrier_hasExactEntireOrderOne
    {beta : ℝ} (hbeta : 0 < beta) (a : ℝ) :
    HasExactEntireOrderOne (transverseRelocationCarrier beta a) := by
  refine ⟨Complex.analyticOnNhd_univ_iff_differentiable.mp
      (transverseRelocationCarrier_analyticOnNhd beta a),
    transverseRelocationCarrier_orderOneEnvelope beta a, ?_⟩
  intro hmin
  exact hmin.no_arithmeticProgression_zeros
    (transverseRelocationCarrier_ne_zero_half hbeta a) I_ne_zero
    (transverseRelocationCarrier_zero_arithmeticProgression beta a)

theorem transverseRelocationCarrier_hypertranscendental_of_two_mul_sub_one
    {beta a : ℝ}
    (hsep : ∀ k : ℤ, (2 * beta - 1 : ℂ) ≠ (k : ℂ)) :
    Hypertranscendental (transverseRelocationCarrier beta a) := by
  have h := (hypertranscendental_comp_add_const_iff
      (f := reflectedGammaQuartetCarrier beta a) (-(1 / 2 : ℂ))).2
    (reflectedGammaQuartetCarrier_hypertranscendental_of_two_mul_sub_one hsep)
  change Hypertranscendental
    (fun z => reflectedGammaQuartetCarrier beta a (z - (1 / 2 : ℂ)))
  simpa only [sub_eq_add_neg] using h

end
end RHTower
