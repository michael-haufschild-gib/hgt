import GaloisForLFunctions.RHTower.DeningerArithmeticLocalDivision

/-!
# Taylor approximation of local Xi quotients

After local Xi jets vanish, the normalized quotient is holomorphic on the corresponding disk.
Its Cauchy--Taylor partial sums are genuine entire functions and converge uniformly on every
strictly smaller disk.  Multiplying back by Xi gives locally uniform representatives of the zero
cohomology class.

This is the approximation half of `[DAC_LOCAL_QUOTIENT_OPENNESS]`.  It uses only local analytic
division and Cauchy power-series convergence; no global jet interpolation is assumed.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/-- Cauchy--Taylor partial sum of the locally normalized Xi quotient at the origin. -/
def deningerLocalXiQuotientTaylorApprox
    (F : DeningerCompactOpenEntire) (R : ℝ≥0)
    (n : ℕ) (z : ℂ) : ℂ :=
  (cauchyPowerSeries
    (deningerNormalizedXiQuotient F) 0 R).partialSum n z

/-- Every local quotient Taylor partial sum is an entire function. -/
theorem deningerLocalXiQuotientTaylorApprox_differentiable
    (F : DeningerCompactOpenEntire) (R : ℝ≥0) (n : ℕ) :
    Differentiable ℂ
      (deningerLocalXiQuotientTaylorApprox F R n) := by
  unfold deningerLocalXiQuotientTaylorApprox
    FormalMultilinearSeries.partialSum
  apply Differentiable.fun_sum
  intro k hk
  exact fun z =>
    (HasFDerivAt.multilinear_comp
      (f := cauchyPowerSeries
        (deningerNormalizedXiQuotient F) 0 R k)
      (fun _ => hasFDerivAt_id z)).differentiableAt

/-- Taylor partial sum as a compact-open entire source. -/
def deningerCompactOpenLocalXiQuotientTaylorApprox
    (F : DeningerCompactOpenEntire) (R : ℝ≥0)
    (n : ℕ) : DeningerCompactOpenEntire :=
  let hdiff :=
    deningerLocalXiQuotientTaylorApprox_differentiable
      F R n
  ⟨⟨deningerLocalXiQuotientTaylorApprox F R n,
      hdiff.continuous⟩,
    hdiff⟩

@[simp]
theorem deningerCompactOpenLocalXiQuotientTaylorApprox_apply
    (F : DeningerCompactOpenEntire) (R : ℝ≥0)
    (n : ℕ) (z : ℂ) :
    deningerCompactOpenLocalXiQuotientTaylorApprox
        F R n z =
      deningerLocalXiQuotientTaylorApprox F R n z :=
  rfl

/--
Local Xi division followed by Cauchy--Taylor approximation converges uniformly on every strictly
smaller disk.
-/
theorem deningerLocalXiQuotientTaylorApprox_tendstoUniformlyOn
    (F : DeningerCompactOpenEntire)
    {r R S : ℝ≥0} (hrR : r < R) (hRS : R < S)
    (hjets :
      ∀ (rho : XiDivisorSupport),
        ‖xiSpectralPointSupport rho‖ < S →
          ∀ k : DeningerArithmeticJetIndex rho,
            deningerCompactOpenJet
                (xiSpectralPointSupport rho) k F = 0) :
    TendstoUniformlyOn
      (fun n =>
        deningerLocalXiQuotientTaylorApprox F R n)
      (deningerNormalizedXiQuotient F)
      atTop (Metric.ball 0 r) := by
  have hQanalytic :
      AnalyticOnNhd ℂ
        (deningerNormalizedXiQuotient F)
        (Metric.ball 0 S) := by
    apply
      deningerNormalizedXiQuotient_analyticOnNhd_of_localJets
        F (Metric.ball 0 S)
    intro rho hrho
    exact hjets rho (by simpa [Metric.mem_ball] using hrho)
  have hRSreal : (R : ℝ) < (S : ℝ) := by
    exact_mod_cast hRS
  have hQdiff :
      DifferentiableOn ℂ
        (deningerNormalizedXiQuotient F)
        (Metric.closedBall 0 R) := by
    intro z hz
    exact
      (hQanalytic z
        (Metric.closedBall_subset_ball hRSreal hz))
        |>.differentiableAt.differentiableWithinAt
  have hR0 : 0 < R :=
    lt_of_le_of_lt (zero_le r) hrR
  have hpow :=
    hQdiff.hasFPowerSeriesOnBall hR0
  have hconv :=
    hpow.tendstoUniformlyOn' (by
      exact_mod_cast hrR)
  simpa only [
    deningerLocalXiQuotientTaylorApprox,
    sub_zero] using hconv

/--
Multiplying the Taylor approximants back by Xi gives locally uniform zero representatives.
-/
theorem deningerLocalXiTaylorCoboundaryError_tendstoLocallyUniformlyOn
    (F : DeningerCompactOpenEntire)
    {r R S : ℝ≥0} (hrR : r < R) (hRS : R < S)
    (hjets :
      ∀ (rho : XiDivisorSupport),
        ‖xiSpectralPointSupport rho‖ < S →
          ∀ k : DeningerArithmeticJetIndex rho,
            deningerCompactOpenJet
                (xiSpectralPointSupport rho) k F = 0) :
    TendstoLocallyUniformlyOn
      (fun n z =>
        F z - XiC z *
          deningerLocalXiQuotientTaylorApprox F R n z)
      (fun _ => 0)
      atTop (Metric.ball 0 r) := by
  have happrox :=
    (deningerLocalXiQuotientTaylorApprox_tendstoUniformlyOn
      F hrR hRS hjets).tendstoLocallyUniformlyOn
  have hQanalytic :
      AnalyticOnNhd ℂ
        (deningerNormalizedXiQuotient F)
        (Metric.ball 0 S) := by
    apply
      deningerNormalizedXiQuotient_analyticOnNhd_of_localJets
        F (Metric.ball 0 S)
    intro rho hrho
    exact hjets rho (by simpa [Metric.mem_ball] using hrho)
  have hQcontinuous :
      ContinuousOn
        (deningerNormalizedXiQuotient F)
        (Metric.ball 0 r) := by
    intro z hz
    exact
      (hQanalytic z
        (Metric.ball_subset_ball
          (show (r : ℝ) ≤ (S : ℝ) by
            exact_mod_cast (hrR.le.trans hRS.le))
          hz)).continuousAt.continuousWithinAt
  have hXi :
      TendstoLocallyUniformlyOn
        (fun _ : ℕ => XiC) XiC atTop
        (Metric.ball 0 r) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    filter_upwards [] with n z hz
    simpa using hepsilon
  have hF :
      TendstoLocallyUniformlyOn
        (fun _ : ℕ => (F : ℂ → ℂ))
        (F : ℂ → ℂ) atTop
        (Metric.ball 0 r) := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    filter_upwards [] with n z hz
    simpa using hepsilon
  have hmul :=
    hXi.mul₀ happrox
      (XiC_differentiable.continuous.continuousOn)
      hQcontinuous
  have hsub := hF.sub hmul
  have hdiv :=
    deningerNormalizedXiQuotient_mul_XiC_eqOn_ball
      F
      (show 0 < (S : ℝ) by
        exact_mod_cast
          (lt_of_le_of_lt (zero_le r)
            (hrR.trans hRS)))
      hjets
  apply hsub.congr_right
  intro z hz
  have hzS :
      z ∈ Metric.ball (0 : ℂ) (S : ℝ) :=
    Metric.ball_subset_ball
      (show (r : ℝ) ≤ (S : ℝ) by
        exact_mod_cast (hrR.le.trans hRS.le))
      hz
  have hpoint := hdiv hzS
  simp only [Pi.sub_apply, Pi.mul_apply,
    Pi.zero_apply]
  rw [mul_comm, hpoint, sub_self]

end

end RHTower
