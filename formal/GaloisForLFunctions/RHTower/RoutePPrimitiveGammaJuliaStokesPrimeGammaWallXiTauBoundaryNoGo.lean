import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesExpWallXiTauProjectiveJetNoGo
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallFredholmCoefficientLimit

/-!
# Prime/Gamma Stokes-wall Xi tau boundary-neighborhood no-go

The finite-aperture laws in this file are the literal discrete prime/Gamma Stokes-wall laws, not
the limiting exponential model.  Their first two Fredholm coefficients converge to `1` and
`19 / 70`, so their scale-free logarithmic two-jet converges to `8 / 35`.  The strict source-side
Xi bound is below `9 / 80`.  Continuity therefore excludes every sufficiently small positive
aperture, even after an aperture-dependent complex rescaling of irregular time.

This proves that the existing non-scalar finite-aperture Stokes deformation cannot repair the Xi
tau mismatch near the wild wall.  Any viable irregular Riemann--Hilbert bridge must add a new even
Stokes/monodromy channel or leave this boundary neighborhood.  No RH assumption or target-fed
parameter enters the result.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace RHTower

noncomputable section

private def primeGammaWallCoeff (d : ℝ) (n : ℕ) : ℂ :=
  routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
    (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n

private theorem entireCoeffs_primeGammaWallCoeff (d : ℝ) :
    GaloisForLFunctions.HTGeometry.EntireCoeffs (primeGammaWallCoeff d) := by
  intro r hr
  have hmajorant :=
    summable_routePPrimitiveGammaJuliaStokesWallFredholmMajorant hr.le
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le n))
    (fun n => ?_) hmajorant.tendsto_atTop_zero
  rw [routePPrimitiveGammaJuliaStokesWallFredholmMajorant]
  calc
    ‖primeGammaWallCoeff d n‖ * r ^ n ≤
        ((Real.sqrt n) ^ n / (n.factorial : ℝ)) * r ^ n := by
      gcongr
      exact norm_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_le
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
        (wallHalfLineLaw_Iio_zero d) n
    _ = (Real.sqrt n * r) ^ n / (n.factorial : ℝ) := by ring

private theorem primeGammaWallDet_eq_coeffFun (d : ℝ) (z : ℂ) :
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z =
      GaloisForLFunctions.HTGeometry.coeffFun (primeGammaWallCoeff d) z := by
  rw [routePPrimitiveGammaJuliaStokesWallFredholmEntireDet,
    GaloisForLFunctions.HTGeometry.coeffFun_eq_tsum]
  apply tsum_congr
  intro n
  dsimp [primeGammaWallCoeff]
  ring

private theorem iteratedDeriv_primeGammaWallDet (d : ℝ) (n : ℕ) :
    iteratedDeriv n
        (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)) 0 =
      ((Nat.factorial n : ℕ) : ℂ) * primeGammaWallCoeff d n := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ (primeGammaWallCoeff d)
  have hrad : 0 < p.radius := by
    dsimp [p]
    rw [GaloisForLFunctions.HTGeometry.ofScalars_radius_eq_top
      (entireCoeffs_primeGammaWallCoeff d)]
    simp
  have hp := p.hasFPowerSeriesOnBall hrad
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq,
    one_pow, smul_eq_mul, mul_one] at hfac
  rw [show routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) =
      GaloisForLFunctions.HTGeometry.coeffFun (primeGammaWallCoeff d) by
    funext z
    exact primeGammaWallDet_eq_coeffFun d z]
  simpa only [GaloisForLFunctions.HTGeometry.coeffFun, nsmul_eq_mul] using hfac.symm

/-- Finite-aperture prime/Gamma wall tau after scalar rescaling of irregular time. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau
    (d : ℝ) (c z : ℂ) : ℂ :=
  routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
    (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) (c * z)

theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero
    (d : ℝ) (c : ℂ) :
    routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c 0 = 1 := by
  simp [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau,
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero]

theorem differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau
    (d : ℝ) (c : ℂ) :
    Differentiable ℂ (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) := by
  exact (differentiable_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
    (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
    (wallHalfLineLaw_Iio_zero d)).comp (by fun_prop)

theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_one
    (d : ℝ) (c : ℂ) :
    iteratedDeriv 1
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0 =
      c * primeGammaWallCoeff d 1 := by
  by_cases hc : c = 0
  · subst c
    have hconst : routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d 0 =
        fun _ => 1 := by
      funext z
      simp [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau,
        routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero]
    rw [hconst]
    simp [iteratedDeriv_succ']
  · change iteratedDeriv 1
      (fun z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) (c * z)) 0 = _
    rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_mul_of_ne
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)) 1 hc 0]
    simp only [mul_zero]
    rw [iteratedDeriv_primeGammaWallDet]
    norm_num

theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_two
    (d : ℝ) (c : ℂ) :
    iteratedDeriv 2
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0 =
      2 * c ^ 2 * primeGammaWallCoeff d 2 := by
  by_cases hc : c = 0
  · subst c
    have hconst : routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d 0 =
        fun _ => 1 := by
      funext z
      simp [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau,
        routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero]
    rw [hconst]
    simp [iteratedDeriv_succ']
  · change iteratedDeriv 2
      (fun z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) (c * z)) 0 = _
    rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_mul_of_ne
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)) 2 hc 0]
    simp only [mul_zero]
    rw [iteratedDeriv_primeGammaWallDet]
    norm_num
    ring

private theorem iteratedDeriv_clog_two_of_differentiable_primeGamma
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hzero : F 0 = 1) (a b : ℂ)
    (ha : iteratedDeriv 1 F 0 = a)
    (hb : iteratedDeriv 2 F 0 = b) :
    iteratedDeriv 2 (fun z => Complex.log (F z)) 0 = b - a ^ 2 := by
  have hFone : F 0 ≠ 0 := by rw [hzero]; norm_num
  have hFoneSlit : F 0 ∈ Complex.slitPlane := by
    rw [hzero]
    exact Complex.one_mem_slitPlane
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
  have hquot := hFsecond.div hFfirst hFone
  have hslit : ∀ᶠ z in 𝓝 0, F z ∈ Complex.slitPlane :=
    hF.continuous.continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds hFoneSlit)
  have hlocal :
      (fun z => deriv (fun w => Complex.log (F w)) z) =ᶠ[𝓝 0]
        (deriv F / F) := by
    filter_upwards [hslit] with z hz
    simpa only [Pi.div_apply] using ((hF z).hasDerivAt.clog hz).deriv
  have hderivEq := hlocal.deriv_eq
  rw [show 2 = 1 + 1 by norm_num, congrFun iteratedDeriv_succ' 0]
  simp only [iteratedDeriv_one]
  rw [hderivEq, hquot.deriv, hzero, hFfirst.deriv]
  ring

theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_one
    (d : ℝ) (c : ℂ) :
    iteratedDeriv 1
        (fun z => Complex.log
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) 0 =
      c * primeGammaWallCoeff d 1 := by
  have hfirst : HasDerivAt
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c)
      (c * primeGammaWallCoeff d 1) 0 := by
    have hc : deriv
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c) 0 =
        c * primeGammaWallCoeff d 1 := by
      simpa [iteratedDeriv_succ'] using
        iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_one d c
    have h :=
      (differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c 0).hasDerivAt
    simpa only [hc] using h
  have hlog := hfirst.clog (by
    rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero]
    exact Complex.one_mem_slitPlane)
  simpa [iteratedDeriv_succ',
    routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero] using hlog.deriv

theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_two
    (d : ℝ) (c : ℂ) :
    iteratedDeriv 2
        (fun z => Complex.log
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) 0 =
      c ^ 2 * (2 * primeGammaWallCoeff d 2 - primeGammaWallCoeff d 1 ^ 2) := by
  rw [iteratedDeriv_clog_two_of_differentiable_primeGamma
    (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c)
    (differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c)
    (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero d c)
    (c * primeGammaWallCoeff d 1)
    (2 * c ^ 2 * primeGammaWallCoeff d 2)
    (iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_one d c)
    (iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_two d c)]
  ring

/-- Scale-free projective logarithmic two-jet of the finite prime/Gamma Stokes wall. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet (d : ℝ) : ℂ :=
  (primeGammaWallCoeff d 1 ^ 2 - 2 * primeGammaWallCoeff d 2) /
    (2 * primeGammaWallCoeff d 1 ^ 2)

/-- The finite-aperture projective wall invariant tends to the exponential-wall value `8/35`. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_nhdsGT_zero :
    Tendsto routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet
      (𝓝[>] (0 : ℝ)) (𝓝 (8 / 35 : ℂ)) := by
  have h1 : Tendsto (fun d : ℝ => primeGammaWallCoeff d 1)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa [primeGammaWallCoeff,
      routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_one] using
      (tendsto_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_nhdsGT_zero 1)
  have h2 : Tendsto (fun d : ℝ => primeGammaWallCoeff d 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (19 / 70 : ℂ)) := by
    simpa [primeGammaWallCoeff,
      routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_two] using
      (tendsto_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_nhdsGT_zero 2)
  have hsq : Tendsto (fun d : ℝ => primeGammaWallCoeff d 1 * primeGammaWallCoeff d 1)
      (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℂ) * 1)) := h1.mul h1
  have htwo : Tendsto (fun d : ℝ => (2 : ℂ) * primeGammaWallCoeff d 2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℂ) * (19 / 70))) :=
    tendsto_const_nhds.mul h2
  have hden : Tendsto (fun d : ℝ => (2 : ℂ) *
      (primeGammaWallCoeff d 1 * primeGammaWallCoeff d 1))
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℂ) * ((1 : ℂ) * 1))) :=
    tendsto_const_nhds.mul hsq
  have hraw := (htwo.sub hsq).neg.div hden (by norm_num)
  norm_num at hraw
  rw [show routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet =
      (fun d : ℝ =>
        (primeGammaWallCoeff d 1 * primeGammaWallCoeff d 1 -
            2 * primeGammaWallCoeff d 2) /
          (2 * (primeGammaWallCoeff d 1 * primeGammaWallCoeff d 1))) by
    funext d
    simp [routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet, pow_two]]
  refine hraw.congr' ?_
  exact Filter.Eventually.of_forall fun d => rfl

/-- Real part of the finite-aperture wall invariant retains the endpoint gap near zero. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_nhdsGT_zero :
    Tendsto (fun d : ℝ =>
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re)
      (𝓝[>] (0 : ℝ)) (𝓝 (8 / 35 : ℝ)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_nhdsGT_zero
  norm_num at h
  simpa only [Function.comp_def] using h

/-- Eventually the genuine prime/Gamma wall remains above Xi's unconditional projective bound. -/
theorem eventually_nine_div_eighty_lt_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re :
    ∀ᶠ d : ℝ in 𝓝[>] 0,
      (9 / 80 : ℝ) <
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re := by
  exact (tendsto_order.1
    tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_nhdsGT_zero).1
      (9 / 80 : ℝ) (by norm_num)

/-- Scalar irregular-time rescaling leaves each nondegenerate finite-wall projective jet fixed. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_projectiveTwoJet
    {d : ℝ} {c : ℂ} (hc : c ≠ 0) (ha : primeGammaWallCoeff d 1 ≠ 0) :
    routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet
        (fun z => Complex.log
          (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) =
      routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d := by
  rw [routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_one,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_two,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet]
  field_simp [hc, ha]
  ring

/-- Germ-level claim that some scalar rescaling identifies a finite prime/Gamma wall tau with Xi. -/
def RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt
    (d : ℝ) : Prop :=
  ∃ c : ℂ, canonicalXiSeamLog =ᶠ[𝓝 0]
    fun z => Complex.log
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)

/-- No scalar time rescaling works throughout a punctured right neighborhood of the wild wall. -/
theorem eventually_not_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt :
    ∀ᶠ d : ℝ in 𝓝[>] 0,
      ¬ RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt d := by
  filter_upwards
    [eventually_nine_div_eighty_lt_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re]
      with d hgap
  rintro ⟨c, hgerm⟩
  have hfirst := hgerm.iteratedDeriv_eq 1
  rw [iteratedDeriv_canonicalXiSeamLog_one,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_one] at hfirst
  have hca : c * primeGammaWallCoeff d 1 ≠ 0 := by
    rw [← hfirst]
    exact div_ne_zero
      (Complex.ofReal_ne_zero.mpr normalizedPrimeArchMoment_zero_pos.ne') (by norm_num)
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hca).1
  have ha : primeGammaWallCoeff d 1 ≠ 0 := (mul_ne_zero_iff.mp hca).2
  have hprojective :
      routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet canonicalXiSeamLog =
        routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet
          (fun z => Complex.log
            (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) := by
    unfold routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet
    rw [
      hgerm.iteratedDeriv_eq 1, hgerm.iteratedDeriv_eq 2]
  rw [routePPrimitiveGammaJuliaStokes_canonicalXiSeamLog_projectiveTwoJet,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_projectiveTwoJet hc ha]
      at hprojective
  have hre : normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 =
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hprojective
  have hlt := normalizedPrimeArchMoment_projectiveTauJet_lt_nine_div_eighty
  rw [hre] at hlt
  linarith

end
end RHTower
