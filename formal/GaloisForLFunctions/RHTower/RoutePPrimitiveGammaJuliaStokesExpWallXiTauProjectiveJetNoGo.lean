import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallFirstJetInvariant
import GaloisForLFunctions.RHTower.CanonicalXiSeamLogEquivalence
import GaloisForLFunctions.RHTower.ThetaCuspCalibratedPowerReciprocalSecondMomentLaw
import GaloisForLFunctions.HTGeometry.MaximumTermLogarithmicDerivative

/-!
# Route P exponential-wall/Xi tau projective-jet no-go

Irregular Riemann--Hilbert theory permits multiplication of a tau function by a constant, and a
one-time model also permits rescaling its irregular time. The logarithmic two-jet

```text
J(L) = -L''(0) / (2 L'(0)^2)
```

removes both freedoms. This file extracts that invariant from the literal exponential SP-E wall
Fredholm determinant and compares it with the canonical Xi seam logarithm.

The wall coefficients `1, 1, 19/70` force `J = 8/35` for every nonzero time scale. Existing
source-only Xi estimates instead force `J_Xi < 9/80 < 8/35`. Consequently no scalar rescaling of
the exponential-wall Fredholm tau germ can be the Xi tau germ. Any viable irregular-RH repair must
change even Stokes/monodromy data, not only normalize tau or rescale time.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace RHTower

noncomputable section

private def expWallCoeff (n : ℕ) : ℂ :=
  routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) n

private theorem entireCoeffs_expWallCoeff :
    GaloisForLFunctions.HTGeometry.EntireCoeffs expWallCoeff := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  intro r hr
  have hmajorant :=
    summable_routePPrimitiveGammaJuliaStokesWallFredholmMajorant hr.le
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr.le n))
    (fun n => ?_) hmajorant.tendsto_atTop_zero
  rw [routePPrimitiveGammaJuliaStokesWallFredholmMajorant]
  calc
    ‖expWallCoeff n‖ * r ^ n ≤
        ((Real.sqrt n) ^ n / (n.factorial : ℝ)) * r ^ n := by
      gcongr
      exact norm_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_le
        (expMeasure 1) GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero n
    _ = (Real.sqrt n * r) ^ n / (n.factorial : ℝ) := by ring

private theorem expWallDet_eq_coeffFun (z : ℂ) :
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) z =
      GaloisForLFunctions.HTGeometry.coeffFun expWallCoeff z := by
  rw [routePPrimitiveGammaJuliaStokesWallFredholmEntireDet,
    GaloisForLFunctions.HTGeometry.coeffFun_eq_tsum]
  apply tsum_congr
  intro n
  dsimp [expWallCoeff]
  ring

private theorem iteratedDeriv_expWallDet (n : ℕ) :
    iteratedDeriv n
        (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1)) 0 =
      ((Nat.factorial n : ℕ) : ℂ) * expWallCoeff n := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ expWallCoeff
  have hrad : 0 < p.radius := by
    dsimp [p]
    rw [GaloisForLFunctions.HTGeometry.ofScalars_radius_eq_top entireCoeffs_expWallCoeff]
    simp
  have hp := p.hasFPowerSeriesOnBall hrad
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const_one, one_smul] at hfac
  simp only [p, FormalMultilinearSeries.ofScalars_apply_eq,
    one_pow, smul_eq_mul, mul_one] at hfac
  rw [show routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) =
      GaloisForLFunctions.HTGeometry.coeffFun expWallCoeff by
    funext z
    exact expWallDet_eq_coeffFun z]
  simpa only [GaloisForLFunctions.HTGeometry.coeffFun, nsmul_eq_mul] using hfac.symm

/-- First differential jet of the literal exponential-wall Fredholm determinant. -/
theorem iteratedDeriv_expWallDet_one :
    iteratedDeriv 1
        (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1)) 0 = 1 := by
  rw [iteratedDeriv_expWallDet]
  simp [expWallCoeff,
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_one]

/-- Second differential jet of the literal exponential-wall Fredholm determinant. -/
theorem iteratedDeriv_expWallDet_two :
    iteratedDeriv 2
        (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1)) 0 =
      (19 / 35 : ℂ) := by
  rw [iteratedDeriv_expWallDet]
  simp [expWallCoeff,
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_exp_two]
  norm_num

/-- Exponential-wall Fredholm tau after scalar rescaling of irregular time. -/
def routePPrimitiveGammaJuliaStokesExpWallScaledTau (c z : ℂ) : ℂ :=
  routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) (c * z)

/-- Every time-rescaled wall tau retains normalization one at the origin. -/
theorem routePPrimitiveGammaJuliaStokesExpWallScaledTau_zero (c : ℂ) :
    routePPrimitiveGammaJuliaStokesExpWallScaledTau c 0 = 1 := by
  simp [routePPrimitiveGammaJuliaStokesExpWallScaledTau,
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero]

theorem differentiable_routePPrimitiveGammaJuliaStokesExpWallScaledTau (c : ℂ) :
    Differentiable ℂ (routePPrimitiveGammaJuliaStokesExpWallScaledTau c) := by
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure one_pos
  exact (differentiable_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
    (expMeasure 1) GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero).comp (by fun_prop)

theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTau_one (c : ℂ) :
    iteratedDeriv 1 (routePPrimitiveGammaJuliaStokesExpWallScaledTau c) 0 = c := by
  by_cases hc : c = 0
  · subst c
    have hconst : routePPrimitiveGammaJuliaStokesExpWallScaledTau 0 = fun _ => 1 := by
      funext z
      simp [routePPrimitiveGammaJuliaStokesExpWallScaledTau,
        routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero]
    rw [hconst]
    simp [iteratedDeriv_succ']
  · change iteratedDeriv 1
      (fun z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (expMeasure 1) (c * z)) 0 = c
    rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_mul_of_ne
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1)) 1 hc 0]
    simp only [mul_zero]
    rw [iteratedDeriv_expWallDet_one]
    ring

theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTau_two (c : ℂ) :
    iteratedDeriv 2 (routePPrimitiveGammaJuliaStokesExpWallScaledTau c) 0 =
      (19 / 35 : ℂ) * c ^ 2 := by
  by_cases hc : c = 0
  · subst c
    have hconst : routePPrimitiveGammaJuliaStokesExpWallScaledTau 0 = fun _ => 1 := by
      funext z
      simp [routePPrimitiveGammaJuliaStokesExpWallScaledTau,
        routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero]
    rw [hconst]
    simp [iteratedDeriv_succ']
  · change iteratedDeriv 2
      (fun z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (expMeasure 1) (c * z)) 0 = (19 / 35 : ℂ) * c ^ 2
    rw [GaloisForLFunctions.HTGeometry.iteratedDeriv_comp_const_mul_of_ne
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1)) 2 hc 0]
    simp only [mul_zero]
    rw [iteratedDeriv_expWallDet_two]
    ring

private theorem iteratedDeriv_clog_two_of_differentiable
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

/-- First logarithmic wall jet is exactly the chosen time scale. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTauLog_one (c : ℂ) :
    iteratedDeriv 1
        (fun z => Complex.log (routePPrimitiveGammaJuliaStokesExpWallScaledTau c z)) 0 = c := by
  have hfirst : HasDerivAt (routePPrimitiveGammaJuliaStokesExpWallScaledTau c) c 0 := by
    have hc : deriv (routePPrimitiveGammaJuliaStokesExpWallScaledTau c) 0 = c := by
      simpa [iteratedDeriv_succ'] using
        iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTau_one c
    have h := (differentiable_routePPrimitiveGammaJuliaStokesExpWallScaledTau c 0).hasDerivAt
    simpa only [hc] using h
  have hlog := hfirst.clog (by
    rw [routePPrimitiveGammaJuliaStokesExpWallScaledTau_zero]
    exact Complex.one_mem_slitPlane)
  simpa [iteratedDeriv_succ',
    routePPrimitiveGammaJuliaStokesExpWallScaledTau_zero] using hlog.deriv

/-- Second logarithmic wall jet carries the fixed curvature `-16/35`. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTauLog_two (c : ℂ) :
    iteratedDeriv 2
        (fun z => Complex.log (routePPrimitiveGammaJuliaStokesExpWallScaledTau c z)) 0 =
      -(16 / 35 : ℂ) * c ^ 2 := by
  rw [iteratedDeriv_clog_two_of_differentiable
    (routePPrimitiveGammaJuliaStokesExpWallScaledTau c)
    (differentiable_routePPrimitiveGammaJuliaStokesExpWallScaledTau c)
    (routePPrimitiveGammaJuliaStokesExpWallScaledTau_zero c) c
    ((19 / 35 : ℂ) * c ^ 2)
    (iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTau_one c)
    (iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTau_two c)]
  ring

/-- Canonical Xi seam slope is half its zeroth completed source moment. -/
theorem iteratedDeriv_canonicalXiSeamLog_one :
    iteratedDeriv 1 canonicalXiSeamLog 0 =
      (normalizedPrimeArchMoment 0 : ℂ) / 2 := by
  have h := canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment 0
  have h' : 2 * iteratedDeriv 1 canonicalXiSeamLog 0 =
      (normalizedPrimeArchMoment 0 : ℂ) := by
    simpa [canonicalXiSeamLogMoment, canonicalXiSeamLogCoeff, seamLogCoeff] using h
  calc
    iteratedDeriv 1 canonicalXiSeamLog 0 =
        (2 * iteratedDeriv 1 canonicalXiSeamLog 0) / 2 := by ring
    _ = (normalizedPrimeArchMoment 0 : ℂ) / 2 := by rw [h']

/-- Canonical Xi seam curvature is minus half its first completed source moment. -/
theorem iteratedDeriv_canonicalXiSeamLog_two :
    iteratedDeriv 2 canonicalXiSeamLog 0 =
      -(normalizedPrimeArchMoment 1 : ℂ) / 2 := by
  have h := canonicalXiSeamLogMoment_succ_eq_normalizedPrimeArchMoment 1
  have h' : -2 * iteratedDeriv 2 canonicalXiSeamLog 0 =
      (normalizedPrimeArchMoment 1 : ℂ) := by
    norm_num [canonicalXiSeamLogMoment, canonicalXiSeamLogCoeff, seamLogCoeff] at h
    calc
      -2 * iteratedDeriv 2 canonicalXiSeamLog 0 =
          -(4 * (1 / 2 * iteratedDeriv 2 canonicalXiSeamLog 0)) := by ring
      _ = (normalizedPrimeArchMoment 1 : ℂ) := h
  calc
    iteratedDeriv 2 canonicalXiSeamLog 0 =
        -(-2 * iteratedDeriv 2 canonicalXiSeamLog 0) / 2 := by ring
    _ = -(normalizedPrimeArchMoment 1 : ℂ) / 2 := by rw [h']

/-- Scale-free two-jet of a normalized logarithmic tau germ. -/
def routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet (L : ℂ → ℂ) : ℂ :=
  -iteratedDeriv 2 L 0 / (2 * iteratedDeriv 1 L 0 ^ 2)

/-- Every nonzero scalar time rescaling has the same projective wall two-jet `8/35`. -/
theorem routePPrimitiveGammaJuliaStokesExpWallScaledTauLog_projectiveTwoJet
    {c : ℂ} (hc : c ≠ 0) :
    routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet
        (fun z => Complex.log (routePPrimitiveGammaJuliaStokesExpWallScaledTau c z)) =
      (8 / 35 : ℂ) := by
  rw [routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTauLog_one,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTauLog_two]
  field_simp [hc]
  ring

/-- Xi's projective logarithmic two-jet is its first-to-square-zeroth moment ratio. -/
theorem routePPrimitiveGammaJuliaStokes_canonicalXiSeamLog_projectiveTwoJet :
    routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet canonicalXiSeamLog =
      ((normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 : ℝ) : ℂ) := by
  have hzero : (normalizedPrimeArchMoment 0 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr normalizedPrimeArchMoment_zero_pos.ne'
  rw [routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet,
    iteratedDeriv_canonicalXiSeamLog_one,
    iteratedDeriv_canonicalXiSeamLog_two]
  push_cast
  field_simp [hzero]

/-- Unconditional source separation: Xi's projective tau jet is below `9/80`. -/
theorem normalizedPrimeArchMoment_projectiveTauJet_lt_nine_div_eighty :
    normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 <
      (9 / 80 : ℝ) := by
  have hzero := normalizedPrimeArchMoment_zero_pos
  have hratio := normalizedPrimeArchMoment_ratio_lt_nine_div_twoThousand
  have hfirst : normalizedPrimeArchMoment 1 <
      (9 / 2000 : ℝ) * normalizedPrimeArchMoment 0 :=
    (div_lt_iff₀ hzero).mp hratio
  apply (div_lt_iff₀ (sq_pos_of_pos hzero)).2
  have hscale : (9 / 2000 : ℝ) <
      (9 / 80 : ℝ) * normalizedPrimeArchMoment 0 := by
    nlinarith [one_div_twentyFive_lt_normalizedPrimeArchMoment_zero]
  nlinarith [mul_lt_mul_of_pos_right hscale hzero]

/-- Xi's projective tau jet is strictly smaller than the exponential-wall value. -/
theorem normalizedPrimeArchMoment_projectiveTauJet_lt_expWall :
    normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 <
      (8 / 35 : ℝ) := by
  exact normalizedPrimeArchMoment_projectiveTauJet_lt_nine_div_eighty.trans (by norm_num)

/-- Germ-level claim that scalar irregular-time rescaling identifies wall and Xi tau logarithms. -/
def RoutePPrimitiveGammaJuliaStokesExpWallXiTauScalarRescaling : Prop :=
  ∃ c : ℂ, canonicalXiSeamLog =ᶠ[𝓝 0]
    fun z => Complex.log (routePPrimitiveGammaJuliaStokesExpWallScaledTau c z)

/-- No scalar time rescaling identifies the exponential-wall and canonical Xi tau germs. -/
theorem not_routePPrimitiveGammaJuliaStokesExpWallXiTauScalarRescaling :
    ¬ RoutePPrimitiveGammaJuliaStokesExpWallXiTauScalarRescaling := by
  rintro ⟨c, hgerm⟩
  have hfirst := hgerm.iteratedDeriv_eq 1
  have hsecond := hgerm.iteratedDeriv_eq 2
  rw [iteratedDeriv_canonicalXiSeamLog_one,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTauLog_one] at hfirst
  rw [iteratedDeriv_canonicalXiSeamLog_two,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTauLog_two] at hsecond
  have heqC : (normalizedPrimeArchMoment 1 : ℂ) =
      (8 / 35 : ℂ) * (normalizedPrimeArchMoment 0 : ℂ) ^ 2 := by
    calc
      (normalizedPrimeArchMoment 1 : ℂ) =
          -2 * (-(normalizedPrimeArchMoment 1 : ℂ) / 2) := by ring
      _ = -2 * (-(16 / 35 : ℂ) * c ^ 2) := by rw [hsecond]
      _ = (8 / 35 : ℂ) * (normalizedPrimeArchMoment 0 : ℂ) ^ 2 := by
        rw [← hfirst]
        ring
  have heqR : normalizedPrimeArchMoment 1 =
      (8 / 35 : ℝ) * normalizedPrimeArchMoment 0 ^ 2 := by
    have hre := congrArg Complex.re heqC
    norm_num [pow_two, Complex.mul_re] at hre ⊢
    exact hre
  have hlt := normalizedPrimeArchMoment_projectiveTauJet_lt_expWall
  have hzero := normalizedPrimeArchMoment_zero_pos
  have hlt' : normalizedPrimeArchMoment 1 <
      (8 / 35 : ℝ) * normalizedPrimeArchMoment 0 ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hzero)).mp hlt
  exact (ne_of_lt hlt') heqR

/-- **P-G105 projective-jet capstone.** Wall time scaling is rigid at `8/35`, Xi lies strictly
below it, and scalar-rescaled local tau identification is impossible. -/
theorem routePPrimitive_GammaJulia_Stokes_expWallXiTau_projectiveJetNoGo :
    (∀ c : ℂ, c ≠ 0 →
      routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet
          (fun z => Complex.log (routePPrimitiveGammaJuliaStokesExpWallScaledTau c z)) =
        (8 / 35 : ℂ)) ∧
      routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet canonicalXiSeamLog =
        ((normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 : ℝ) : ℂ) ∧
      normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 <
        (9 / 80 : ℝ) ∧
      (9 / 80 : ℝ) < 8 / 35 ∧
      ¬ RoutePPrimitiveGammaJuliaStokesExpWallXiTauScalarRescaling :=
  ⟨fun _c hc => routePPrimitiveGammaJuliaStokesExpWallScaledTauLog_projectiveTwoJet hc,
    routePPrimitiveGammaJuliaStokes_canonicalXiSeamLog_projectiveTwoJet,
    normalizedPrimeArchMoment_projectiveTauJet_lt_nine_div_eighty,
    by norm_num,
    not_routePPrimitiveGammaJuliaStokesExpWallXiTauScalarRescaling⟩

end

end RHTower
