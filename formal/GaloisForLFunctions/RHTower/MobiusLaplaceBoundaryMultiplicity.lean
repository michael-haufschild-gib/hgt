import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
import GaloisForLFunctions.RHTower.BoundedClockZeroTransfer
import GaloisForLFunctions.RHTower.HedenmalmLocalFrameObstruction
import GaloisForLFunctions.RHTower.XiHedenmalmEigenbasis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Boundary Abel growth and critical-line zeta multiplicity

Exact half-power control of the discrete Möbius--Laplace source gives more than zero-freeness to
the right of the critical line.  Its Mellin transform can grow at most like one inverse radial
power as the line is approached.  This file isolates the complex-analytic rigidity mechanism:
such a one-pole Abel bound forbids a double zero on the boundary.

The source-to-Abel estimate is kept as a separate theorem below.  The boundary theorem itself
applies to any independently obtained radial Mellin bound.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- The critical radial Mellin family is locally bounded after multiplication by its distance to
the critical line. -/
def MobiusLaplaceCriticalAbelBound (rho : ℂ) : Prop :=
  IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ))
    (norm ∘ fun r : ℝ =>
      (r : ℂ) * mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)))

/-- A local half-power bound and the unconditional `1/x` estimate combine into a uniform
half-power majorant on `(0, 1]`. -/
private theorem exists_halfPower_majorant_Ioc_one
    (hdecay : MobiusDiscreteLaplaceHalfDecay) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ D * x ^ (-(1 / 2 : ℝ)) := by
  rcases hdecay with ⟨C, delta, hC, hdelta, hsource⟩
  let d : ℝ := min delta 1
  have hd : 0 < d := lt_min hdelta zero_lt_one
  refine ⟨C + 1 / d, add_nonneg hC (one_div_nonneg.mpr hd.le), ?_⟩
  intro x hx hxOne
  have hxpow : 0 ≤ x ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
  by_cases hxd : x < d
  · have hlocal : ‖mobiusDiscreteLaplaceTransform x‖ ≤
        C * x ^ (-(1 / 2 : ℝ)) :=
      hsource x hx (hxd.trans_le (min_le_left delta 1))
    exact hlocal.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (one_div_nonneg.mpr hd.le)) hxpow)
  · have hdx : d ≤ x := le_of_not_gt hxd
    have hinv := norm_mobiusDiscreteLaplaceTransform_le_inv hx
    have hinvD : 1 / x ≤ 1 / d := one_div_le_one_div_of_le hd hdx
    have hpowOne : 1 ≤ x ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx hxOne (by norm_num)
    calc
      ‖mobiusDiscreteLaplaceTransform x‖ ≤ 1 / x := hinv
      _ ≤ 1 / d := hinvD
      _ ≤ (1 / d) * x ^ (-(1 / 2 : ℝ)) := by
        simpa using mul_le_mul_of_nonneg_left hpowOne (one_div_nonneg.mpr hd.le)
      _ ≤ (C + 1 / d) * x ^ (-(1 / 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) hxpow

/-- Positive real increments converge to zero as nonzero complex increments. -/
private theorem tendsto_ofReal_nhdsGT_zero_nhdsNE_zero :
    Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    simpa using hr.ne'

private theorem analyticAt_Gamma_of_re_pos_boundary {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ Complex.Gamma s := by
  have hinv : AnalyticAt ℂ (fun z => (Complex.Gamma z)⁻¹) s :=
    (Complex.differentiable_one_div_Gamma.differentiableOn.analyticOnNhd isOpen_univ)
      s (mem_univ s)
  have h := hinv.inv (inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos hs))
  change AnalyticAt ℂ (fun z => ((Complex.Gamma z)⁻¹)⁻¹) s at h
  simpa using h

private theorem analyticAt_zetaResidueUnit_boundary (s : ℂ) :
    AnalyticAt ℂ zetaResidueUnit s := by
  by_cases hs : s = 1
  · simpa [hs] using zetaResidueUnit_analyticAt
  · have hdiff : DifferentiableOn ℂ (fun z => (z - 1) * riemannZeta z) ({1}ᶜ) := by
      intro z hz
      exact (differentiableAt_id.sub_const 1).mul
        (differentiableAt_riemannZeta (by simpa using hz)) |>.differentiableWithinAt
    have han : AnalyticAt ℂ (fun z => (z - 1) * riemannZeta z) s :=
      (hdiff.analyticOnNhd isOpen_compl_singleton) s (by simpa using hs)
    exact han.congr (zetaResidueUnit_eventuallyEq hs).symm

/-- Local copy of the canonical identity-theorem output.  It is kept here so this module can be
checked directly with `lake env lean` before the final module build refreshes its parent `.olean`. -/
private theorem mellin_boundary_identity
    (hG : AnalyticOnNhd ℂ (mellin mobiusDiscreteLaplaceTransform) rightHalf) :
    ∀ s ∈ rightHalf,
      mellin mobiusDiscreteLaplaceTransform s * zetaResidueUnit s =
        Complex.Gamma s * (s - 1) := by
  let G : ℂ → ℂ := mellin mobiusDiscreteLaplaceTransform
  have hleft : AnalyticOnNhd ℂ
      (fun s => G s * zetaResidueUnit s) rightHalf := by
    intro s hs
    exact (hG s hs).mul (analyticAt_zetaResidueUnit_boundary s)
  have hright : AnalyticOnNhd ℂ
      (fun s => Complex.Gamma s * (s - 1)) rightHalf := by
    intro s hs
    have hspos : 0 < s.re := lt_trans (by norm_num) (mem_rightHalf.mp hs)
    exact (analyticAt_Gamma_of_re_pos_boundary hspos).mul
      (analyticAt_id.sub analyticAt_const)
  have hevent :
      (fun s => G s * zetaResidueUnit s) =ᶠ[𝓝 (2 : ℂ)]
        (fun s => Complex.Gamma s * (s - 1)) := by
    have hgt : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hgt] with s hs
    have hs1 : s ≠ 1 := by
      intro hsone
      subst s
      norm_num at hs
    have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
    rw [show G s = Complex.Gamma s * (riemannZeta s)⁻¹ by
      simpa [G] using mellin_mobiusDiscreteLaplaceTransform_eq_gamma_div_zeta hs]
    simp only [zetaResidueUnit, Function.update_of_ne hs1]
    field_simp
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright
    convex_rightHalf.isPreconnected two_mem_rightHalf hevent

/-- **Source-to-Abel boundary estimate.**  Exact half-power decay makes the critical radial
Mellin family bounded after multiplication by the radial distance.  The head contributes `D/r`;
the unconditional `1/x` tail contributes `1/(1/2-r)`, which remains bounded after multiplying by
`r`. -/
theorem mobiusLaplaceCriticalAbelBound_of_halfDecay
    (hdecay : MobiusDiscreteLaplaceHalfDecay) {rho : ℂ}
    (hrho : rho.re = 1 / 2) :
    MobiusLaplaceCriticalAbelBound rho := by
  obtain ⟨D, hD, hhead⟩ := exists_halfPower_majorant_Ioc_one hdecay
  rw [MobiusLaplaceCriticalAbelBound]
  apply isBoundedUnder_of_eventually_le (a := D + 1)
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 / 4 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with r hr hrSmall
  have hrPos : 0 < r := hr
  have hrHalf : r < 1 / 2 := by linarith
  let s : ℂ := rho + (r : ℂ)
  have hsRe : s.re = 1 / 2 + r := by
    dsimp only [s]
    rw [Complex.add_re, Complex.ofReal_re, hrho]
  have hsHalf : 1 / 2 < s.re := by rw [hsRe]; linarith
  have hconv : MellinConvergent mobiusDiscreteLaplaceTransform s :=
    mellinConvergent_of_isBigO_rpow_exp (a := 1) (b := 1 / 2) (by norm_num)
      mobiusDiscreteLaplaceTransform_locallyIntegrableOn
      mobiusDiscreteLaplaceTransform_isBigO_exp_neg hdecay.isBigO hsHalf
  let F : ℝ → ℂ := fun x =>
    (x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x
  have hFint : IntegrableOn F (Ioi 0) := by
    simpa only [MellinConvergent, F] using hconv
  have hFhead : IntegrableOn (fun x => ‖F x‖) (Ioc 0 1) :=
    (hFint.mono_set (by
      intro x hx
      exact hx.1)).norm
  have hFtail : IntegrableOn (fun x => ‖F x‖) (Ioi 1) :=
    (hFint.mono_set (Ioi_subset_Ioi zero_le_one)).norm
  have hheadMajorInt : IntegrableOn (fun x : ℝ => D * x ^ (r - 1)) (Ioc 0 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
    exact (intervalIntegral.intervalIntegrable_rpow'
      (by linarith : -1 < r - 1)).const_mul D
  have htailMajorInt : IntegrableOn (fun x : ℝ => x ^ (r - 3 / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  have hsplit : (∫ x : ℝ in Ioi 0, ‖F x‖) =
      (∫ x : ℝ in Ioc 0 1, ‖F x‖) + ∫ x : ℝ in Ioi 1, ‖F x‖ := by
    have hcover : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
      ext x
      simp only [mem_union, mem_Ioc, mem_Ioi]
      constructor
      · rintro (h | h) <;> linarith
      · intro hx
        by_cases hx1 : x ≤ 1
        · exact Or.inl ⟨hx, hx1⟩
        · exact Or.inr (lt_of_not_ge hx1)
    rw [← hcover]
    exact setIntegral_union (by
      rw [disjoint_left]
      intro x hx hxt
      exact (not_lt_of_ge hx.2) hxt) measurableSet_Ioi hFhead hFtail
  have hheadIntegral : (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤ D / r := by
    calc
      (∫ x : ℝ in Ioc 0 1, ‖F x‖) ≤
          ∫ x : ℝ in Ioc 0 1, D * x ^ (r - 1) := by
        apply MeasureTheory.integral_mono_ae hFhead hheadMajorInt
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
        have hxPos : 0 < x := hx.1
        change ‖(x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x‖ ≤ _
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hxPos,
          Complex.sub_re, Complex.one_re, hsRe]
        calc
          x ^ (1 / 2 + r - 1) * ‖mobiusDiscreteLaplaceTransform x‖
              ≤ x ^ (1 / 2 + r - 1) *
                  (D * x ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left (hhead x hxPos hx.2)
              (Real.rpow_nonneg hxPos.le _)
          _ = D * x ^ (r - 1) := by
            calc
              x ^ (1 / 2 + r - 1) * (D * x ^ (-(1 / 2 : ℝ))) =
                  D * (x ^ (1 / 2 + r - 1) * x ^ (-(1 / 2 : ℝ))) := by ring
              _ = D * x ^ ((1 / 2 + r - 1) + (-(1 / 2 : ℝ))) := by
                rw [Real.rpow_add hxPos]
              _ = D * x ^ (r - 1) := by
                congr 2
                ring
      _ = D / r := by
        rw [← intervalIntegral.integral_of_le zero_le_one,
          intervalIntegral.integral_const_mul,
          integral_rpow (Or.inl (by linarith : -1 < r - 1))]
        rw [show r - 1 + 1 = r by ring, Real.one_rpow, Real.zero_rpow hrPos.ne']
        field_simp
        ring
  have htailIntegral : (∫ x : ℝ in Ioi 1, ‖F x‖) ≤ 1 / (1 / 2 - r) := by
    calc
      (∫ x : ℝ in Ioi 1, ‖F x‖) ≤
          ∫ x : ℝ in Ioi 1, x ^ (r - 3 / 2) := by
        apply MeasureTheory.integral_mono_ae hFtail htailMajorInt
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hxPos : 0 < x := zero_lt_one.trans hx
        change ‖(x : ℂ) ^ (s - 1) • mobiusDiscreteLaplaceTransform x‖ ≤ _
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hxPos,
          Complex.sub_re, Complex.one_re, hsRe]
        calc
          x ^ (1 / 2 + r - 1) * ‖mobiusDiscreteLaplaceTransform x‖
              ≤ x ^ (1 / 2 + r - 1) * (1 / x) :=
            mul_le_mul_of_nonneg_left
              (norm_mobiusDiscreteLaplaceTransform_le_inv hxPos)
              (Real.rpow_nonneg hxPos.le _)
          _ = x ^ (r - 3 / 2) := by
            calc
              x ^ (1 / 2 + r - 1) * (1 / x) =
                  x ^ (1 / 2 + r - 1) * x ^ (-1 : ℝ) := by
                    simp only [one_div, Real.rpow_neg_one]
              _ = x ^ ((1 / 2 + r - 1) + (-1 : ℝ)) := by
                rw [Real.rpow_add hxPos]
              _ = x ^ (r - 3 / 2) := by
                congr 1
                ring
      _ = 1 / (1 / 2 - r) := by
        rw [integral_Ioi_rpow_of_lt (by linarith : r - 3 / 2 < -1) zero_lt_one,
          Real.one_rpow, show r - 3 / 2 + 1 = -(1 / 2 - r) by ring]
        field_simp
  have hmellinNorm : ‖mellin mobiusDiscreteLaplaceTransform s‖ ≤
      D / r + 1 / (1 / 2 - r) := by
    calc
      ‖mellin mobiusDiscreteLaplaceTransform s‖
          ≤ ∫ x : ℝ in Ioi 0, ‖F x‖ := by
        rw [mellin]
        exact norm_integral_le_integral_norm _
      _ = (∫ x : ℝ in Ioc 0 1, ‖F x‖) +
          ∫ x : ℝ in Ioi 1, ‖F x‖ := hsplit
      _ ≤ D / r + 1 / (1 / 2 - r) := add_le_add hheadIntegral htailIntegral
  have htailRatio : r / (1 / 2 - r) ≤ 1 := by
    apply (div_le_one (by linarith : 0 < 1 / 2 - r)).2
    linarith
  change ‖(r : ℂ) * mellin mobiusDiscreteLaplaceTransform s‖ ≤ D + 1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrPos]
  calc
    r * ‖mellin mobiusDiscreteLaplaceTransform s‖
        ≤ r * (D / r + 1 / (1 / 2 - r)) :=
      mul_le_mul_of_nonneg_left hmellinNorm hrPos.le
    _ = D + r / (1 / 2 - r) := by field_simp
    _ ≤ D + 1 := by gcongr

/-- **Boundary one-pole rigidity.**  If the canonical Möbius Mellin transform has at most one
radial pole at a critical-line zeta zero, that zero is simple.  The proof only uses the propagated
denominator-free Mellin identity and first-order differentiability of zeta. -/
theorem deriv_riemannZeta_ne_zero_of_mobiusLaplaceCriticalAbelBound
    (hdecay : MobiusDiscreteLaplaceHalfDecay) {rho : ℂ}
    (hrho : rho.re = 1 / 2) (hzero : riemannZeta rho = 0)
    (hAbel : MobiusLaplaceCriticalAbelBound rho) :
    deriv riemannZeta rho ≠ 0 := by
  intro hderivZero
  have hrhoPos : 0 < rho.re := by rw [hrho]; norm_num
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrho
  have hunitZero : zetaResidueUnit rho = 0 := by
    simp [zetaResidueUnit, hrhoOne, hzero]
  have hunitDeriv : HasDerivAt zetaResidueUnit 0 rho := by
    have hproduct : HasDerivAt (fun z : ℂ => (z - 1) * riemannZeta z) 0 rho := by
      convert ((hasDerivAt_id rho).sub_const 1).mul
        (differentiableAt_riemannZeta hrhoOne).hasDerivAt using 1
      all_goals simp [hzero, hderivZero]
    exact hproduct.congr_of_eventuallyEq (zetaResidueUnit_eventuallyEq hrhoOne)
  have hslopeComplex := hunitDeriv.tendsto_slope_zero
  have hslope : Tendsto
      (fun r : ℝ => (r : ℂ)⁻¹ * zetaResidueUnit (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
    have h := hslopeComplex.comp tendsto_ofReal_nhdsGT_zero_nhdsNE_zero
    simpa [hunitZero, smul_eq_mul] using h
  have hproductZero : Tendsto
      (fun r : ℝ =>
        ((r : ℂ) * mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ))) *
          ((r : ℂ)⁻¹ * zetaResidueUnit (rho + (r : ℂ))))
      (𝓝[>] 0) (𝓝 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero hAbel hslope
  have hmellinUnitZero : Tendsto
      (fun r : ℝ =>
        mellin mobiusDiscreteLaplaceTransform (rho + (r : ℂ)) *
          zetaResidueUnit (rho + (r : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by
    refine hproductZero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    field_simp
  have hcanonicalIdentity :=
    mellin_boundary_identity
      (analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform hdecay)
  have hrightZero : Tendsto
      (fun r : ℝ => Complex.Gamma (rho + (r : ℂ)) * (rho + (r : ℂ) - 1))
      (𝓝[>] 0) (𝓝 0) := by
    refine hmellinUnitZero.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    apply hcanonicalIdentity
    rw [mem_rightHalf]
    norm_num [Complex.add_re, hrho]
    exact hr
  have hnotGammaPole : ∀ m : ℕ, rho ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    simp only [neg_re, natCast_re] at hre
    rw [hrho] at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hray : Tendsto (fun r : ℝ => rho + (r : ℂ)) (𝓝[>] 0) (𝓝 rho) := by
    simpa using
      ((continuous_const.add Complex.continuous_ofReal).tendsto 0).mono_left
        nhdsWithin_le_nhds
  have hrightActual : Tendsto
      (fun r : ℝ => Complex.Gamma (rho + (r : ℂ)) * (rho + (r : ℂ) - 1))
      (𝓝[>] 0) (𝓝 (Complex.Gamma rho * (rho - 1))) := by
    exact ((Complex.continuousAt_Gamma rho hnotGammaPole).tendsto.comp hray).mul
      (((continuous_id.sub continuous_const).tendsto rho).comp hray)
  have hvanish : Complex.Gamma rho * (rho - 1) = 0 :=
    tendsto_nhds_unique hrightActual hrightZero
  exact (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hrhoPos)
    (sub_ne_zero.mpr hrhoOne)) hvanish

/-- Exact half-power decay forces every critical-line zeta zero to have nonzero derivative. -/
theorem deriv_riemannZeta_ne_zero_of_mobiusDiscreteLaplaceHalfDecay
    (hdecay : MobiusDiscreteLaplaceHalfDecay) {rho : ℂ}
    (hrho : rho.re = 1 / 2) (hzero : riemannZeta rho = 0) :
    deriv riemannZeta rho ≠ 0 :=
  deriv_riemannZeta_ne_zero_of_mobiusLaplaceCriticalAbelBound
    hdecay hrho hzero (mobiusLaplaceCriticalAbelBound_of_halfDecay hdecay hrho)

/-- Multiplicity form of the boundary theorem: every critical-line zeta zero has analytic order
exactly one under exact half-power Möbius--Laplace decay. -/
theorem analyticOrderAt_riemannZeta_eq_one_of_mobiusDiscreteLaplaceHalfDecay
    (hdecay : MobiusDiscreteLaplaceHalfDecay) {rho : ℂ}
    (hrho : rho.re = 1 / 2) (hzero : riemannZeta rho = 0) :
    analyticOrderAt riemannZeta rho = 1 := by
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    norm_num at hrho
  exact (analyticOn_riemannZeta rho hrhoOne).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    hzero (deriv_riemannZeta_ne_zero_of_mobiusDiscreteLaplaceHalfDecay hdecay hrho hzero)

/-- Strengthened exact-decay criterion: its conclusion is RH together with simplicity of every
critical-line zeta zero, not merely zero-freeness off that line. -/
theorem mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis_and_boundarySimplicity
    (hdecay : MobiusDiscreteLaplaceHalfDecay) :
    RiemannHypothesis ∧
      ∀ rho : ℂ, rho.re = 1 / 2 → riemannZeta rho = 0 →
        analyticOrderAt riemannZeta rho = 1 := by
  refine ⟨mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis hdecay, ?_⟩
  intro rho hrho hzero
  exact analyticOrderAt_riemannZeta_eq_one_of_mobiusDiscreteLaplaceHalfDecay
    hdecay hrho hzero

/-- **Möbius--Laplace/Hedenmalm simplicity transport.** Exact half-power decay forces RH and
global simplicity of the centered Xi divisor. The extra step from boundary zeta simplicity to
`XiZerosSimple` uses RH to place every centered Xi zero on the real axis, the nonvanishing
archimedean factor in the open strip, and the exact derivative change of coordinates. -/
theorem mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis_and_xiZerosSimple
    (hdecay : MobiusDiscreteLaplaceHalfDecay) :
    RiemannHypothesis ∧ XiZerosSimple := by
  have hRH : RiemannHypothesis :=
    mobiusDiscreteLaplaceHalfDecay_implies_riemannHypothesis hdecay
  refine ⟨hRH, ?_⟩
  intro alpha hXiC
  let rho : ℂ := 1 / 2 + alpha * I
  have halphaIm : alpha.im = 0 :=
    xiC_zero_im_eq_zero_of_riemannHypothesis hRH hXiC
  have hrho : rho.re = 1 / 2 := by
    dsimp only [rho]
    norm_num [Complex.div_re, Complex.normSq, halphaIm]
  have hstrip : 0 < rho.re ∧ rho.re < 1 := by
    rw [hrho]
    constructor <;> norm_num
  have hrhoZero : rho ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hrho] at this
    norm_num at this
  have hrhoOne : rho ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hrho] at this
    norm_num at this
  have hxi : xi rho = 0 := by
    simpa only [rho, XiC] using hXiC
  have hzeta : riemannZeta rho = 0 :=
    (xi_eq_zero_iff hstrip.1 hrhoOne).1 hxi
  have hzetaDeriv : deriv riemannZeta rho ≠ 0 :=
    deriv_riemannZeta_ne_zero_of_mobiusDiscreteLaplaceHalfDecay
      hdecay hrho hzeta
  have harchNe : archFactor rho ≠ 0 := archFactor_ne_zero_strip hstrip
  let U : Set ℂ := {z | 0 < z.re ∧ z.re < 1}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have heq : xi =ᶠ[nhds rho] fun z => archFactor z * riemannZeta z := by
    filter_upwards [hUopen.mem_nhds hstrip] with z hz
    exact xi_eq_archFactor_mul_zeta
      (by intro h; subst z; simpa using hz.1)
      (by intro h; subst z; simpa using hz.2)
      (Gammaℝ_ne_zero_of_re_pos hz.1)
  have harch : AnalyticAt ℂ archFactor rho := by
    have hpoly : AnalyticAt ℂ (fun z : ℂ => z * (z - 1) / 2) rho := by fun_prop
    exact hpoly.mul (Gammaℝ_analyticAt (Gammaℝ_ne_zero_of_re_pos hstrip.1))
  have hzetaAnalytic : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho hrhoOne
  have hproduct : HasDerivAt (fun z => archFactor z * riemannZeta z)
      (archFactor rho * deriv riemannZeta rho) rho := by
    convert harch.differentiableAt.hasDerivAt.mul
      hzetaAnalytic.differentiableAt.hasDerivAt using 1
    all_goals simp [hzeta]
  have hxiDeriv : deriv xi rho = archFactor rho * deriv riemannZeta rho :=
    (hproduct.congr_of_eventuallyEq heq).deriv
  rw [deriv_XiC_eq_deriv_xi_mul_I]
  change deriv xi rho * I ≠ 0
  rw [hxiDeriv]
  exact mul_ne_zero (mul_ne_zero harchNe hzetaDeriv) I_ne_zero

end

end RHTower
