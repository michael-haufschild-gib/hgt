import GaloisForLFunctions.RHTower.SuzukiScrewPointwiseNonnegativityCriterion
import GaloisForLFunctions.RHTower.SuzukiTitchmarshUniqueness

noncomputable section

/-!
# Strict positivity of Suzuki's screw function under RH

This file closes the strict clause of Suzuki (2022), Theorem 1.7.  If the exact critical-zero
screw series vanishes at `t`, positivity of every reciprocal-square summand makes every zero phase
equal to one.  Suzuki's Lemma 2.1, supplied unconditionally by
`SuzukiTitchmarshUniqueness.lean`, then forces `z ↦ exp (I * t * z)` to be constant.  Evaluation at
`-I` gives `exp t = 1`, hence `t = 0`.
-/

open Complex Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Vanishing of the RH-side critical screw series forces every critical-zero phase to be one. -/
theorem xiCriticalScrewPhase_eq_one_of_series_eq_zero
    (hRH : RiemannHypothesis) {t : ℝ} (hzero : xiCriticalScrewSeries t = 0)
    (q : XiZeroCopy) :
    Complex.exp (Complex.I * ((xiRealSpectralPoint q * t : ℝ) : ℂ)) = 1 := by
  have hsum :
      Summable (fun r : XiZeroCopy =>
        xiCriticalScrewWeight r * (1 - Real.cos (xiRealSpectralPoint r * t))) :=
    summable_xiCriticalScrewTerm_of_rh hRH t
  have hnonneg : ∀ r : XiZeroCopy,
      0 ≤ xiCriticalScrewWeight r * (1 - Real.cos (xiRealSpectralPoint r * t)) := by
    intro r
    exact mul_nonneg (xiCriticalScrewWeight_nonneg r)
      (sub_nonneg.mpr (Real.cos_le_one _))
  have htermle := hsum.le_tsum q (fun r _ => hnonneg r)
  have htsum :
      (∑' r : XiZeroCopy,
        xiCriticalScrewWeight r * (1 - Real.cos (xiRealSpectralPoint r * t))) = 0 := by
    simpa [xiCriticalScrewSeries, screwSeries] using hzero
  have htermzero :
      xiCriticalScrewWeight q * (1 - Real.cos (xiRealSpectralPoint q * t)) = 0 := by
    rw [htsum] at htermle
    exact le_antisymm htermle (hnonneg q)
  have hcos : Real.cos (xiRealSpectralPoint q * t) = 1 := by
    rcases mul_eq_zero.mp htermzero with hweight | hphase
    · exact False.elim ((xiCriticalScrewWeight_pos_of_rh hRH q).ne' hweight)
    · linarith
  have hsin : Real.sin (xiRealSpectralPoint q * t) = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq (xiRealSpectralPoint q * t)]
  rw [show Complex.I * ((xiRealSpectralPoint q * t : ℝ) : ℂ) =
      ((xiRealSpectralPoint q * t : ℝ) : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I, hcos, hsin]
  norm_num

/-- Every zero in Suzuki's centered coordinate has phase one when the critical screw series
vanishes. -/
theorem suzukiCenteredZero_phase_eq_one_of_series_eq_zero
    (hRH : RiemannHypothesis) {t : ℝ} (hzero : xiCriticalScrewSeries t = 0)
    {z : ℂ} (hz : xi (1 / 2 - Complex.I * z) = 0) :
    Complex.exp (Complex.I * (t : ℂ) * z) = 1 := by
  have hXi : XiC (-z) = 0 := by
    rw [XiC]
    rw [show (1 / 2 : ℂ) + -z * Complex.I = 1 / 2 - Complex.I * z by ring]
    exact hz
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (-z)).mp hXi
  have hreal := xiSpectralPoint_eq_ofReal_of_rh hRH q
  have hzcoord : z = -((xiRealSpectralPoint q : ℝ) : ℂ) := by
    rw [hq] at hreal
    linear_combination -hreal
  have hphase := xiCriticalScrewPhase_eq_one_of_series_eq_zero hRH hzero q
  have hphase' :
      Complex.exp (Complex.I * (t : ℂ) * (xiRealSpectralPoint q : ℂ)) = 1 := by
    rw [show Complex.I * (t : ℂ) * (xiRealSpectralPoint q : ℂ) =
        Complex.I * ((xiRealSpectralPoint q * t : ℝ) : ℂ) by
      push_cast
      ring]
    exact hphase
  rw [hzcoord]
  rw [show Complex.I * (t : ℂ) * -((xiRealSpectralPoint q : ℝ) : ℂ) =
      -(Complex.I * (t : ℂ) * (xiRealSpectralPoint q : ℂ)) by ring,
    Complex.exp_neg, hphase']
  simp

/-- The critical-zero screw series is strictly positive away from the origin under RH. -/
theorem xiCriticalScrewSeries_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) {t : ℝ} (ht : t ≠ 0) :
    0 < xiCriticalScrewSeries t := by
  have hnonneg : 0 ≤ xiCriticalScrewSeries t :=
    screwSeries_nonneg xiCriticalScrewWeight_nonneg t
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have hexponentialType :
      ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧
        ∀ z : ℂ, ‖Complex.exp (Complex.I * (t : ℂ) * z)‖ ≤
          C * Real.exp (A * ‖z‖) := by
    refine ⟨|t|, 1, abs_nonneg t, le_rfl, ?_⟩
    intro z
    simp only [one_mul]
    calc
      ‖Complex.exp (Complex.I * (t : ℂ) * z)‖
          ≤ Real.exp ‖Complex.I * (t : ℂ) * z‖ :=
        Complex.norm_exp_le_exp_norm _
      _ = Real.exp (|t| * ‖z‖) := by
        congr 1
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul,
          Complex.norm_real, Real.norm_eq_abs]
  have hconstant := suzuki_lemma_two_one
    (F := fun z : ℂ => Complex.exp (Complex.I * (t : ℂ) * z))
    (by fun_prop) 1 hexponentialType
    (fun z hz => suzukiCenteredZero_phase_eq_one_of_series_eq_zero hRH hzero.symm hz)
  have heval := congrFun hconstant (-Complex.I)
  have hexp : Complex.exp (t : ℂ) = 1 := by
    rw [show Complex.I * (t : ℂ) * -Complex.I = (t : ℂ) by
      rw [mul_neg, mul_assoc, mul_comm (t : ℂ) Complex.I,
        ← mul_assoc, Complex.I_mul_I]
      ring] at heval
    exact heval
  have hnorm := congrArg norm hexp
  rw [Complex.norm_exp, Complex.ofReal_re, norm_one, Real.exp_eq_one_iff] at hnorm
  exact ht hnorm

/-- **Suzuki 2022, Theorem 1.7 (strict clause).**  Under RH, the paper's literal `Psi` is
strictly positive at every nonzero point of its source half-line. -/
theorem suzukiPsi_pos_of_riemannHypothesis
    (hRH : RiemannHypothesis) {t : ℝ} (ht : 0 < t) :
    0 < suzukiPsi t := by
  rw [suzukiPsi_eq_xiScrewDivisor_re ht.le,
    xiScrewDivisor_re_eq_xiCriticalScrewSeries_of_rh hRH]
  exact xiCriticalScrewSeries_pos_of_riemannHypothesis hRH ht.ne'

end RHTower
