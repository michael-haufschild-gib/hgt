import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauExplicitColdNoGo

/-!
# Prime/Gamma Stokes-wall Xi Malgrange correction curvature

Normalize irregular time so the prime/Gamma wall and completed-Xi logarithmic tau germs have the
same first jet.  Their difference is then first-order flat, but its quadratic jet is exactly the
wall--Xi projective defect.  The already-proved source inequalities make this correction curvature
strictly positive on the explicit cold half-ray and throughout a punctured wild-wall collar.

This is the positive rigidity law exposed by the scalar-rescaling no-go: any viable irregular
Riemann--Hilbert realization must add genuine even Stokes data.  No RH assumption, target zero, or
global coherence monotonicity is used.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace RHTower

noncomputable section

/-- Unique scalar irregular-time normalization matching the first completed-Xi seam jet. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale : ℂ :=
  (normalizedPrimeArchMoment 0 : ℂ) / 2

/-- Canonical logarithmic correction left after first-jet-normalized prime/Gamma wall transport. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog
    (d : ℝ) (z : ℂ) : ℂ :=
  canonicalXiSeamLog z -
    Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
      routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)

private theorem analyticAt_primeGammaWallXiScaledTauLog (d : ℝ) :
    AnalyticAt ℂ
      (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 := by
  apply ((differentiable_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale).analyticAt 0).clog
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero]
  exact Complex.one_mem_slitPlane

/-- Both normalized logarithmic tau germs vanish at the central point. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_zero
    (d : ℝ) :
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d 0 = 0 := by
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog,
    canonicalXiSeamLog_zero,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau_zero]
  norm_num

/-- First-jet normalization makes the canonical Malgrange correction first-order flat. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_one
    {d : ℝ} (hd : 0 < d) :
    iteratedDeriv 1
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0 = 0 := by
  have hXi : ContDiffAt ℂ 1 canonicalXiSeamLog 0 :=
    analyticAt_canonicalXiSeamLog.contDiffAt
  have hWall : ContDiffAt ℂ 1
      (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 :=
    (analyticAt_primeGammaWallXiScaledTauLog d).contDiffAt
  change iteratedDeriv 1
    (canonicalXiSeamLog - fun z => Complex.log
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 = 0
  rw [iteratedDeriv_sub hXi hWall, iteratedDeriv_canonicalXiSeamLog_one,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_one]
  change (normalizedPrimeArchMoment 0 : ℂ) / 2 -
    routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale *
      routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 = 0
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_one hd]
  simp [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale]

/-- Exact quadratic Malgrange anomaly after the forced first-jet normalization. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two
    {d : ℝ} (hd : 0 < d) :
    iteratedDeriv 2
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0 =
      2 * routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ^ 2 *
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d -
          ((normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 : ℝ) : ℂ)) := by
  have hXi : ContDiffAt ℂ 2 canonicalXiSeamLog 0 :=
    analyticAt_canonicalXiSeamLog.contDiffAt
  have hWall : ContDiffAt ℂ 2
      (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 :=
    (analyticAt_primeGammaWallXiScaledTauLog d).contDiffAt
  have hscale : routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ≠ 0 := by
    rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale]
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr normalizedPrimeArchMoment_zero_pos.ne')
      (by norm_num)
  have hcoefficient :
      routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 ≠ 0 := by
    rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_one hd]
    norm_num
  have hprojective :=
    routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_projectiveTwoJet
      (d := d) (c := routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale)
      hscale (by
        change routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 ≠ 0
        exact hcoefficient)
  rw [routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_one]
    at hprojective
  change
    -iteratedDeriv 2
        (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
          routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 /
          (2 * (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale *
            routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
              (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1) ^ 2) =
      routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d at hprojective
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_one hd,
    mul_one] at hprojective
  have hwallCurvature :
      iteratedDeriv 2
          (fun z => Complex.log (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
            routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 =
        -2 * routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ^ 2 *
          routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hscale))).mp at hprojective
    linear_combination -hprojective
  change iteratedDeriv 2
    (canonicalXiSeamLog - fun z => Complex.log
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d
        routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale z)) 0 = _
  rw [iteratedDeriv_sub hXi hWall, iteratedDeriv_canonicalXiSeamLog_two,
    hwallCurvature]
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale]
  push_cast
  field_simp [normalizedPrimeArchMoment_zero_pos.ne']
  ring

private theorem re_two_mul_firstJetScale_sq_mul_projective_sub_eq
    (P : ℂ) :
    (2 * routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale ^ 2 *
      (P - ((normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 : ℝ) : ℂ))).re =
        2 * (normalizedPrimeArchMoment 0 / 2) ^ 2 *
          (P.re - normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2) := by
  change (2 * (Complex.ofReal (normalizedPrimeArchMoment 0) / 2) ^ 2 *
    (P - Complex.ofReal
      (normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2))).re = _
  norm_num [routePPrimitiveGammaJuliaStokesPrimeGammaWallXiFirstJetScale,
    Complex.mul_re, Complex.sub_re, Complex.div_re, Complex.div_im,
    Complex.normSq_apply, pow_two, normalizedPrimeArchMoment_zero_pos.ne']
  field_simp [normalizedPrimeArchMoment_zero_pos.ne']

/-- On every aperture `d ≥ 1`, required even Malgrange correction has positive curvature. -/
theorem zero_lt_re_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two_of_one_le
    {d : ℝ} (hd : 1 ≤ d) :
    0 < (iteratedDeriv 2
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0).re := by
  rw [iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two
    (lt_of_lt_of_le (by norm_num) hd)]
  have hwall :=
    nine_div_eighty_lt_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_of_one_le
      hd
  have hxi := normalizedPrimeArchMoment_projectiveTauJet_lt_nine_div_eighty
  rw [re_two_mul_firstJetScale_sq_mul_projective_sub_eq]
  have hscale : 0 < normalizedPrimeArchMoment 0 / 2 :=
    div_pos normalizedPrimeArchMoment_zero_pos (by norm_num)
  have hgap : 0 <
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re -
        normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 := by
    linarith
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hscale)) hgap

/-- The same forced positive curvature persists throughout a punctured wild-wall collar. -/
theorem eventually_zero_lt_re_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two :
    ∀ᶠ d : ℝ in 𝓝[>] 0,
      0 < (iteratedDeriv 2
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog d) 0).re := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_nine_div_eighty_lt_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re]
      with d hd hwall
  rw [iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_two hd]
  have hxi := normalizedPrimeArchMoment_projectiveTauJet_lt_nine_div_eighty
  rw [re_two_mul_firstJetScale_sq_mul_projective_sub_eq]
  have hscale : 0 < normalizedPrimeArchMoment 0 / 2 :=
    div_pos normalizedPrimeArchMoment_zero_pos (by norm_num)
  have hgap : 0 <
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re -
        normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 := by
    linarith
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hscale)) hgap

end

end RHTower
