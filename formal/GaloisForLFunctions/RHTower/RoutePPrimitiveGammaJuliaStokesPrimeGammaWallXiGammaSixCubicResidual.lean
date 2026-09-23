import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallColdAllOrderFredholmCollapse
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock

/-!
# Prime/Gamma wall cubic Malgrange residual

The cold irregular prime wall collapses all fixed Fredholm coefficients above order one. This
module converts that source-side statement into the exact third logarithmic jet of its tau germ.
After the forced Xi first-jet scaling, the wall contributes
`normalizedPrimeArchMoment 0 ^ 3 / 4`; the even source-horizontal Gamma-six correction contributes
no cubic jet. Therefore the remaining odd Stokes/Malgrange datum is exactly
`normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4`.

No target-fit correction is introduced, and no limit is interchanged with a Fredholm series.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace RHTower

noncomputable section

private def cubicWallCoeff (d : ℝ) (n : ℕ) : ℂ :=
  routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
    (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n

private theorem entireCoeffs_cubicWallCoeff (d : ℝ) :
    GaloisForLFunctions.HTGeometry.EntireCoeffs (cubicWallCoeff d) := by
  intro r hr
  have hmajorant :=
    summable_routePPrimitiveGammaJuliaStokesWallFredholmMajorant hr.le
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le n))
    (fun n => ?_) hmajorant.tendsto_atTop_zero
  rw [routePPrimitiveGammaJuliaStokesWallFredholmMajorant]
  calc
    ‖cubicWallCoeff d n‖ * r ^ n ≤
        ((Real.sqrt n) ^ n / (n.factorial : ℝ)) * r ^ n := by
      gcongr
      exact norm_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_le
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
        (wallHalfLineLaw_Iio_zero d) n
    _ = (Real.sqrt n * r) ^ n / (n.factorial : ℝ) := by ring

private theorem cubicWallDet_eq_coeffFun (d : ℝ) (z : ℂ) :
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z =
      GaloisForLFunctions.HTGeometry.coeffFun (cubicWallCoeff d) z := by
  rw [routePPrimitiveGammaJuliaStokesWallFredholmEntireDet,
    GaloisForLFunctions.HTGeometry.coeffFun_eq_tsum]
  apply tsum_congr
  intro n
  dsimp [cubicWallCoeff]
  ring

private theorem iteratedDeriv_cubicWallDet (d : ℝ) (n : ℕ) :
    iteratedDeriv n
        (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)) 0 =
      ((Nat.factorial n : ℕ) : ℂ) * cubicWallCoeff d n := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (cubicWallCoeff d)
  have hrad : 0 < p.radius := by
    dsimp [p]
    rw [GaloisForLFunctions.HTGeometry.ofScalars_radius_eq_top
      (entireCoeffs_cubicWallCoeff d)]
    simp
  have hp := p.hasFPowerSeriesOnBall hrad
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq,
    one_pow, smul_eq_mul, mul_one] at hfac
  rw [show routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) =
      GaloisForLFunctions.HTGeometry.coeffFun (cubicWallCoeff d) by
    funext z
    exact cubicWallDet_eq_coeffFun d z]
  simpa only [GaloisForLFunctions.HTGeometry.coeffFun, nsmul_eq_mul] using hfac.symm

/-- Every positive scaled wall tau jet is its same-order complete Fredholm coefficient. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_of_pos
    (d : ℝ) (c : ℂ) (n : ℕ) (hn : 0 < n) :
    iteratedDeriv n
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0 =
      ((n.factorial : ℕ) : ℂ) * c ^ n *
        routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n := by
  by_cases hc : c = 0
  · subst c
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hconst : routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d 0 =
        fun _ => 1 := by
      funext z
      simp [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau,
        routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero]
    simp [hconst, iteratedDeriv_succ']
  · change iteratedDeriv n
      (fun z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) (c * z)) 0 = _
    rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_mul_of_ne
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)) n hc 0]
    simp only [mul_zero]
    rw [iteratedDeriv_cubicWallDet]
    dsimp [cubicWallCoeff]
    ring

theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_three
    (d : ℝ) (c : ℂ) :
    iteratedDeriv 3
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0 =
      6 * c ^ 3 *
        routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 3 := by
  rw [iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_of_pos
    d c 3 (by norm_num)]
  norm_num

private theorem iteratedDeriv_clog_three_of_differentiable
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hzero : F 0 = 1) (a b c : ℂ)
    (ha : iteratedDeriv 1 F 0 = a)
    (hb : iteratedDeriv 2 F 0 = b)
    (hc : iteratedDeriv 3 F 0 = c) :
    iteratedDeriv 3 (fun z => Complex.log (F z)) 0 =
      c - 3 * a * b + 2 * a ^ 3 := by
  have hFzero : F 0 ≠ 0 := by rw [hzero]; norm_num
  have hFfirst : HasDerivAt F a 0 := by
    have ha' : deriv F 0 = a := by
      simpa [iteratedDeriv_succ'] using ha
    rw [← ha']
    exact (hF 0).hasDerivAt
  have hFsecond : HasDerivAt (deriv F) b 0 := by
    have hb' : deriv (deriv F) 0 = b := by
      simpa [iteratedDeriv_succ'] using hb
    rw [← hb']
    exact (hF.analyticAt 0).deriv.differentiableAt.hasDerivAt
  have hFthird : HasDerivAt (deriv (deriv F)) c 0 := by
    have hc' : deriv (deriv (deriv F)) 0 = c := by
      simpa [iteratedDeriv_succ'] using hc
    rw [← hc']
    exact (hF.analyticAt 0).deriv.deriv.differentiableAt.hasDerivAt
  let U : Set ℂ := F ⁻¹' Complex.slitPlane
  let Q : ℂ → ℂ := deriv F / F
  let R : ℂ → ℂ := fun z =>
    (deriv (deriv F) z * F z - deriv F z * deriv F z) / F z ^ 2
  have hUopen : IsOpen U := Complex.isOpen_slitPlane.preimage hF.continuous
  have hzeroU : (0 : ℂ) ∈ U := by
    change F 0 ∈ Complex.slitPlane
    rw [hzero]
    exact Complex.one_mem_slitPlane
  have hderivLog : EqOn (deriv (fun z => Complex.log (F z))) Q U := by
    intro z hz
    have h := (hF z).hasDerivAt.clog hz
    simpa only [Q, Pi.div_apply] using h.deriv
  have hderivQ : EqOn (deriv Q) R U := by
    intro z hz
    have hFz : HasDerivAt F (deriv F z) z := (hF z).hasDerivAt
    have hFderivz : HasDerivAt (deriv F) (deriv (deriv F) z) z :=
      (hF.analyticAt z).deriv.differentiableAt.hasDerivAt
    have hquot := hFderivz.div hFz (Complex.slitPlane_ne_zero hz)
    dsimp only [Q, R]
    simpa only [Pi.div_apply, pow_two] using hquot.deriv
  have hsecondLocal :
      deriv (deriv (fun z => Complex.log (F z))) =ᶠ[𝓝 0] R := by
    refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds hzeroU) fun z hz => ?_
    have hlocal : deriv (fun w => Complex.log (F w)) =ᶠ[𝓝 z] Q :=
      Filter.eventuallyEq_of_mem (hUopen.mem_nhds hz) hderivLog
    rw [hlocal.deriv_eq]
    exact hderivQ hz
  have hnum : HasDerivAt
      (fun z => deriv (deriv F) z * F z - deriv F z * deriv F z)
      (c - a * b) 0 := by
    change HasDerivAt
      ((deriv (deriv F) * F) - (deriv F * deriv F)) (c - a * b) 0
    have hraw := (hFthird.mul hFfirst).sub (hFsecond.mul hFsecond)
    rw [hzero, hFsecond.deriv, hFfirst.deriv] at hraw
    apply hraw.congr_deriv
    ring
  have hden : HasDerivAt (fun z => F z ^ 2) (2 * a) 0 := by
    change HasDerivAt (F ^ 2) (2 * a) 0
    have hraw := hFfirst.pow 2
    rw [hzero] at hraw
    simpa using hraw
  have hR : HasDerivAt R (c - 3 * a * b + 2 * a ^ 3) 0 := by
    have hquot := hnum.div hden (by rw [hzero]; norm_num)
    change HasDerivAt R _ 0 at hquot
    have hvalue :
        (((c - a * b) * F 0 ^ 2 -
              (deriv (deriv F) 0 * F 0 - deriv F 0 * deriv F 0) * (2 * a)) /
            (F 0 ^ 2) ^ 2) = c - 3 * a * b + 2 * a ^ 3 := by
      rw [hzero, hFsecond.deriv, hFfirst.deriv]
      ring
    rw [hvalue] at hquot
    exact hquot
  have hthree : iteratedDeriv 3 (fun z => Complex.log (F z)) =
      deriv (deriv (deriv (fun z => Complex.log (F z)))) := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hthree, hsecondLocal.deriv_eq]
  exact hR.deriv

/-- Third logarithmic jet of the finite prime/Gamma wall in terms of its first three complete
Fredholm coefficients. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_three
    (d : ℝ) (c : ℂ) :
    iteratedDeriv 3
        (fun z => Complex.log
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) 0 =
      c ^ 3 *
        (6 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 3 -
          6 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
              (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 *
            routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
              (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 2 +
          2 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
              (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 ^ 3) := by
  rw [iteratedDeriv_clog_three_of_differentiable
    (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c)
    (differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c)
    (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero d c)
    (c * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1)
    (2 * c ^ 2 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 2)
    (6 * c ^ 3 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 3)
    (iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_one d c)
    (iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_two d c)
    (iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_three d c)]
  ring

private theorem iteratedDeriv_primeGammaWallScaledTauLog_three_of_pos
    {d : ℝ} (hd : 0 < d) (c : ℂ) :
    iteratedDeriv 3
        (fun z => Complex.log
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) 0 =
      c ^ 3 *
        (6 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 3 -
          6 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 2 + 2) := by
  rw [iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_three,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_one hd]
  ring

/-- Cold prime-2 condensation fixes the scaled wall's cubic logarithmic jet. -/
theorem tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_three_atTop
    (c : ℂ) :
    Tendsto (fun d : ℝ => iteratedDeriv 3
      (fun z => Complex.log
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) 0)
      atTop (𝓝 (2 * c ^ 3)) := by
  have h2 :=
    tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_atTop_of_two_le
      (n := 2) (by norm_num)
  have h3 :=
    tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_atTop_of_two_le
      (n := 3) (by norm_num)
  have hinside : Tendsto (fun d : ℝ =>
      6 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 3 -
        6 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 2 + 2)
      atTop (𝓝 (2 : ℂ)) := by
    simpa using ((tendsto_const_nhds.mul h3).sub
      (tendsto_const_nhds.mul h2)).add tendsto_const_nhds
  have hscaled : Tendsto (fun d : ℝ => c ^ 3 *
      (6 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 3 -
        6 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 2 + 2))
      atTop (𝓝 (2 * c ^ 3)) := by
    have hc : Tendsto (fun _ : ℝ => c ^ 3) atTop (𝓝 (c ^ 3)) := tendsto_const_nhds
    simpa [mul_comm] using hc.mul hinside
  refine hscaled.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
  exact (iteratedDeriv_primeGammaWallScaledTauLog_three_of_pos hd c).symm

/-- Canonical completed-Xi seam third jet is its second prime--archimedean source moment. -/
theorem iteratedDeriv_canonicalXiSeamLog_three :
    iteratedDeriv 3 canonicalXiSeamLog 0 =
      (normalizedPrimeArchMoment 2 : ℂ) := by
  have h := canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment 2
  norm_num [canonicalXiSeamLogMoment, canonicalXiSeamLogCoeff, seamLogCoeff] at h
  linear_combination h

/-- Even Gamma-six correction carries no cubic Stokes jet. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_three
    (d : ℝ) :
    iteratedDeriv 3
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 = 0 := by
  let k : ℂ :=
    (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionClock d : ℂ)
  have hfirst :
      deriv (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) =
        fun z : ℂ => 2 * k * Complex.sinh (k * z) := by
    funext z
    have hlinear : HasDerivAt (fun w : ℂ => k * w) k z := hasDerivAt_const_mul k
    have hcosh := (Complex.hasDerivAt_cosh (k * z)).comp z hlinear
    have hscaled := (hcosh.sub_const 1).const_mul 2
    change deriv (fun w : ℂ => 2 * (Complex.cosh (k * w) - 1)) z = _
    simpa only [Function.comp_apply, mul_comm, mul_left_comm, mul_assoc] using hscaled.deriv
  have hsecond : deriv (fun z : ℂ => 2 * k * Complex.sinh (k * z)) =
      fun z : ℂ => 2 * k ^ 2 * Complex.cosh (k * z) := by
    funext z
    have hlinear : HasDerivAt (fun w : ℂ => k * w) k z := hasDerivAt_const_mul k
    have hsinh := (Complex.hasDerivAt_sinh (k * z)).comp z hlinear
    have hscaled := hsinh.const_mul (2 * k)
    calc
      deriv (fun w : ℂ => 2 * k * Complex.sinh (k * w)) z =
          2 * k * (Complex.cosh (k * z) * k) := by
            simpa only [Function.comp_apply] using hscaled.deriv
      _ = 2 * k ^ 2 * Complex.cosh (k * z) := by ring
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
    show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one,
    hfirst, hsecond]
  have hlinear : HasDerivAt (fun w : ℂ => k * w) k 0 := hasDerivAt_const_mul k
  have hcosh := (Complex.hasDerivAt_cosh (k * 0)).comp 0 hlinear
  have hscaled := hcosh.const_mul (2 * k ^ 2)
  simpa [Function.comp_def] using hscaled.deriv

/-- The Gamma-six-corrected wall retains the cold cubic jet `2 c_Xi^(3 : ℕ)`. -/
theorem tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog_three_atTop :
    Tendsto (fun d : ℝ => iteratedDeriv 3
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog d) 0)
      atTop (𝓝 (((normalizedPrimeArchMoment 0 ^ 3 / 4 : ℝ) : ℂ))) := by
  have hwall :=
    tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_three_atTop
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale
  have hsum : Tendsto (fun d : ℝ =>
      iteratedDeriv 3
        (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 + 0)
      atTop (𝓝 (2 * routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ^ 3)) := by
    simpa using hwall
  have hcorrected : Tendsto (fun d : ℝ => iteratedDeriv 3
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectedWallLog d) 0)
      atTop (𝓝 (2 * routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ^ 3)) := by
    refine hsum.congr' ?_
    filter_upwards with d
    have hwallDiff : ContDiffAt ℂ 3
        (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 := by
      have hanalytic : AnalyticAt ℂ
          (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
            routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 := by
        apply ((differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale).analyticAt 0).clog
        rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero]
        exact Complex.one_mem_slitPlane
      exact hanalytic.contDiffAt
    have hcorrDiff : ContDiffAt ℂ 3
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 :=
      (analyticAt_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d 0).contDiffAt
    symm
    change iteratedDeriv 3
      ((fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) +
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog d) 0 = _
    rw [iteratedDeriv_add hwallDiff hcorrDiff,
      iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiGammaSixCorrectionLog_three,
      add_zero]
  convert hcorrected using 1
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale]
  push_cast
  ring

/-- Exact cold cubic datum still required of the wall--Xi Malgrange correction after first-jet
normalization. -/
theorem tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_three_atTop :
    Tendsto (fun d : ℝ => iteratedDeriv 3
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0)
      atTop (𝓝 (((normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 0 ^ 3 / 4 : ℝ) : ℂ))) := by
  have hwall :=
    tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_three_atTop
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale
  have hraw := (tendsto_const_nhds : Tendsto (fun _ : ℝ =>
      (normalizedPrimeArchMoment 2 : ℂ)) atTop
      (𝓝 (normalizedPrimeArchMoment 2 : ℂ))).sub hwall
  have hcorrection : Tendsto (fun d : ℝ => iteratedDeriv 3
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0)
      atTop (𝓝 ((normalizedPrimeArchMoment 2 : ℂ) -
        2 * routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ^ 3)) := by
    refine hraw.congr' ?_
    filter_upwards with d
    have hXi : ContDiffAt ℂ 3 canonicalXiSeamLog 0 :=
      analyticAt_canonicalXiSeamLog.contDiffAt
    have hwallDiff : ContDiffAt ℂ 3
        (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 := by
      have hanalytic : AnalyticAt ℂ
          (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
            routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 := by
        apply ((differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale).analyticAt 0).clog
        rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero]
        exact Complex.one_mem_slitPlane
      exact hanalytic.contDiffAt
    symm
    change iteratedDeriv 3
      (canonicalXiSeamLog - fun z => Complex.log
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 = _
    rw [iteratedDeriv_sub hXi hwallDiff, iteratedDeriv_canonicalXiSeamLog_three]
  convert hcorrection using 1
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale]
  push_cast
  ring

end

end RHTower
