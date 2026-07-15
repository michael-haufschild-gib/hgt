import GaloisForLFunctions.RHTower.BVPrimeWindowContinuation
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowCancellation
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Divisor tomography for bounded-variation prime windows

The continuation has one universal singular channel: the logarithmic derivative of the
pole-filled zeta. This file computes its residue and exact Mellin-censorship law.
-/

open Complex Filter Function Set Topology

noncomputable section

namespace RHTower

/-- The shifted logarithmic derivative has residue equal to the exact analytic multiplicity of
an arbitrary zero of the pole-filled zeta. -/
theorem tendsto_shiftedRegularizedZeta_logDeriv_residue_of_zero
    {rho : ℂ} (hzero : regularizedRiemannZeta rho = 0) :
    Tendsto
      (fun s : ℂ => (s - (rho + 1 / 2)) *
        logDeriv regularizedRiemannZeta (s - 1 / 2))
      (𝓝[≠] (rho + 1 / 2))
      (𝓝 ((analyticOrderAt regularizedRiemannZeta rho).toNat : ℂ)) := by
  have hreg : AnalyticAt ℂ regularizedRiemannZeta rho :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) rho (Set.mem_univ rho)
  have hbase := logDeriv_iteratedDeriv_residue_of_zero
    hreg (analyticOrderAt_regularizedRiemannZeta_ne_top rho) hzero 0
  have hbase' : Tendsto
      (fun t : ℂ => (t - rho) * logDeriv regularizedRiemannZeta t)
      (𝓝[≠] rho)
      (𝓝 ((analyticOrderAt regularizedRiemannZeta rho).toNat : ℂ)) := by
    simpa only [zero_add, pow_one, iteratedDeriv_zero, logDeriv_apply,
      pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one] using hbase
  have hshift : Tendsto (fun s : ℂ => s - 1 / 2)
      (𝓝[≠] (rho + 1 / 2)) (𝓝[≠] rho) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : ContinuousAt (fun s : ℂ => s - 1 / 2) (rho + 1 / 2) :=
        continuousAt_id.sub_const _
      have hle : 𝓝[≠] (rho + 1 / 2) ≤ 𝓝 (rho + 1 / 2) := inf_le_left
      simpa only [show rho + 1 / 2 - 1 / 2 = rho by ring] using
        hc.tendsto.mono_left hle
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s - 1 / 2 ≠ rho
      intro heq
      have hsp : s ≠ rho + 1 / 2 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
      apply hsp
      linear_combination heq
  have hcomposed := hbase'.comp hshift
  convert hcomposed using 1
  funext s
  rw [Function.comp_apply]
  congr 1
  ring

/-- The shifted logarithmic derivative has an exact simple pole at every zero of the pole-filled
zeta, independently of the zero multiplicity. -/
theorem meromorphicOrderAt_shiftedRegularizedZeta_logDeriv_eq_neg_one_of_zero
    {rho : ℂ} (hzero : regularizedRiemannZeta rho = 0) :
    meromorphicOrderAt
        (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
        (rho + 1 / 2) = ((-1 : ℤ) : WithTop ℤ) := by
  let shift : ℂ → ℂ := fun z => z - 1 / 2
  have hshiftAnalytic : AnalyticAt ℂ shift (rho + 1 / 2) := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift (rho + 1 / 2) ≠ 0 := by
    dsimp only [shift]
    rw [deriv_sub_const, deriv_id'']
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := logDeriv regularizedRiemannZeta) (g := shift) (x := rho + 1 / 2)
    hshiftAnalytic hshiftDeriv
  rw [show shift (rho + 1 / 2) = rho by dsimp only [shift]; ring,
    meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one hzero] at hcomp
  simpa only [shift, Function.comp_apply] using hcomp

/-- Away from `1`, pole filling does not change the analytic multiplicity of a zeta zero. -/
theorem analyticOrderAt_regularizedRiemannZeta_eq_riemannZeta
    {rho : ℂ} (hrho : rho ≠ 1) :
    analyticOrderAt regularizedRiemannZeta rho =
      analyticOrderAt riemannZeta rho := by
  have hev : regularizedRiemannZeta =ᶠ[nhds rho]
      fun z => (z - 1) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hrho] with z hz
    exact regularizedRiemannZeta_of_ne_one hz
  have hlin : AnalyticAt ℂ (fun z : ℂ => z - 1) rho := by fun_prop
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    analyticOn_riemannZeta rho hrho
  rw [analyticOrderAt_congr hev]
  change analyticOrderAt ((fun z : ℂ => z - 1) * riemannZeta) rho =
    analyticOrderAt riemannZeta rho
  rw [analyticOrderAt_mul hlin hzeta,
    hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hrho), zero_add]

end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- Exact residue law for the complete BV source at an arbitrary zero of the pole-filled zeta. -/
theorem tendsto_continuedSource_residue_of_regularizedZeta_zero
    (W : CompactBVPrimeWindow) {rho : ℂ} (hrho : 0 < rho.re)
    (hzero : regularizedRiemannZeta rho = 0) :
    Tendsto
      (fun s : ℂ => (s - (rho + 1 / 2)) * W.continuedSource s)
      (𝓝[≠] (rho + 1 / 2))
      (𝓝 (2 * W.mellinTransform (rho + 1 / 2) *
        (analyticOrderAt regularizedRiemannZeta rho).toNat)) := by
  let p : ℂ := rho + 1 / 2
  let shiftedLog : ℂ → ℂ := fun z =>
    logDeriv regularizedRiemannZeta (z - 1 / 2)
  let correction : ℂ → ℂ := fun z =>
    dslope W.poleNumerator (3 / 2) z - 2 * W.errorSeries z
  have hpHalf : 1 / 2 < p.re := by
    dsimp only [p]
    norm_num [Complex.add_re]
    linarith
  have hM : ContinuousAt (fun z => 2 * W.mellinTransform z) p :=
    (continuous_const.mul W.differentiable_mellinTransform.continuous).continuousAt
  have hlog : Tendsto
      (fun s : ℂ => (s - p) * shiftedLog s)
      (𝓝[≠] p)
      (𝓝 ((analyticOrderAt regularizedRiemannZeta rho).toNat : ℂ)) := by
    simpa only [p, shiftedLog] using
      tendsto_shiftedRegularizedZeta_logDeriv_residue_of_zero hzero
  have hsing : Tendsto
      (fun s : ℂ => (2 * W.mellinTransform s) * ((s - p) * shiftedLog s))
      (𝓝[≠] p)
      (𝓝 ((2 * W.mellinTransform p) *
        (analyticOrderAt regularizedRiemannZeta rho).toNat)) :=
    (hM.tendsto.mono_left nhdsWithin_le_nhds).mul hlog
  have hdiv : AnalyticAt ℂ (dslope W.poleNumerator (3 / 2)) p :=
    (W.differentiable_poleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have herr : AnalyticAt ℂ W.errorSeries p :=
    (W.differentiableOn_errorSeries_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) p hpHalf
  have hcorr : ContinuousAt correction p := by
    dsimp only [correction]
    exact (hdiv.sub (analyticAt_const.mul herr)).continuousAt
  have hlinear : Tendsto (fun s : ℂ => s - p) (𝓝[≠] p) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' p 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  have hcorrZero : Tendsto (fun s : ℂ => (s - p) * correction s)
      (𝓝[≠] p) (𝓝 0) :=
    by simpa using hlinear.mul (hcorr.tendsto.mono_left nhdsWithin_le_nhds)
  have htotal := hsing.add hcorrZero
  convert htotal using 1
  · funext s
    simp only [continuedSource, poleFilledMain, p, shiftedLog, correction]
    ring
  · congr 1
    dsimp only [p]
    ring

/-- In zeta language, the residue is `2 m(rho) I_W(rho+1/2)` with exact analytic
multiplicity. -/
theorem tendsto_continuedSource_residue_of_zeta_zero
    (W : CompactBVPrimeWindow) {rho : ℂ} (hrhoPos : 0 < rho.re)
    (hrhoOne : rho ≠ 1) (hzero : riemannZeta rho = 0) :
    Tendsto
      (fun s : ℂ => (s - (rho + 1 / 2)) * W.continuedSource s)
      (𝓝[≠] (rho + 1 / 2))
      (𝓝 (2 * W.mellinTransform (rho + 1 / 2) *
        (analyticOrderAt riemannZeta rho).toNat)) := by
  have hregZero : regularizedRiemannZeta rho = 0 := by
    rw [regularizedRiemannZeta_of_ne_one hrhoOne, hzero, mul_zero]
  have hres := W.tendsto_continuedSource_residue_of_regularizedZeta_zero
    hrhoPos hregZero
  rw [analyticOrderAt_regularizedRiemannZeta_eq_riemannZeta hrhoOne] at hres
  exact hres

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- A nonzero Mellin value leaves the universal logarithmic-derivative pole uncancelled. -/
theorem meromorphicOrderAt_continuedSource_eq_neg_one_of_mellin_ne_zero
    (W : CompactBVPrimeWindow) {rho : ℂ} (hrho : 0 < rho.re)
    (hzero : regularizedRiemannZeta rho = 0)
    (hMne : W.mellinTransform (rho + 1 / 2) ≠ 0) :
    meromorphicOrderAt W.continuedSource (rho + 1 / 2) =
      ((-1 : ℤ) : WithTop ℤ) := by
  let p : ℂ := rho + 1 / 2
  let shiftedLog : ℂ → ℂ := fun z =>
    logDeriv regularizedRiemannZeta (z - 1 / 2)
  let fac : ℂ → ℂ := fun z => 2 * W.mellinTransform z
  let singular : ℂ → ℂ := fun z => fac z * shiftedLog z
  let correction : ℂ → ℂ := fun z =>
    dslope W.poleNumerator (3 / 2) z - 2 * W.errorSeries z
  have hpHalf : 1 / 2 < p.re := by
    dsimp only [p]
    norm_num [Complex.add_re]
    linarith
  have hM : AnalyticAt ℂ W.mellinTransform p :=
    (W.differentiable_mellinTransform.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have hfac : AnalyticAt ℂ fac p := by
    dsimp only [fac]
    exact analyticAt_const.mul hM
  have hfac0 : fac p ≠ 0 := by
    dsimp only [fac, p]
    exact mul_ne_zero (by norm_num) hMne
  have hshiftedLog : MeromorphicAt shiftedLog p := by
    let shift : ℂ → ℂ := fun z => z - 1 / 2
    have hshiftAnalytic : AnalyticAt ℂ shift p := by
      dsimp only [shift]
      fun_prop
    have hbase : MeromorphicAt (logDeriv regularizedRiemannZeta) (shift p) :=
      meromorphicAt_logDeriv_regularizedRiemannZeta (shift p)
    have hcomp := MeromorphicAt.comp_analyticAt
      (f := logDeriv regularizedRiemannZeta) (g := shift)
      hbase hshiftAnalytic
    simpa only [shiftedLog, shift, Function.comp_apply] using hcomp
  have hshiftedLogOrder : meromorphicOrderAt shiftedLog p =
      ((-1 : ℤ) : WithTop ℤ) := by
    simpa only [shiftedLog, p] using
      meromorphicOrderAt_shiftedRegularizedZeta_logDeriv_eq_neg_one_of_zero hzero
  have hsingular : MeromorphicAt singular p := by
    dsimp only [singular]
    exact hfac.meromorphicAt.mul hshiftedLog
  have hfacOrder : meromorphicOrderAt fac p = 0 := by
    rw [hfac.meromorphicOrderAt_eq,
      hfac.analyticOrderAt_eq_zero.mpr hfac0]
    simp
  have hsingularOrder : meromorphicOrderAt singular p =
      ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [singular]
    rw [fun_meromorphicOrderAt_mul hfac.meromorphicAt hshiftedLog,
      hfacOrder, hshiftedLogOrder]
    norm_num
  have hdiv : AnalyticAt ℂ (dslope W.poleNumerator (3 / 2)) p :=
    (W.differentiable_poleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have herr : AnalyticAt ℂ W.errorSeries p :=
    (W.differentiableOn_errorSeries_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) p hpHalf
  have hcorr : AnalyticAt ℂ correction p := by
    dsimp only [correction]
    exact hdiv.sub (analyticAt_const.mul herr)
  have hlt : meromorphicOrderAt singular p <
      meromorphicOrderAt correction p := by
    rw [hsingularOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorr.meromorphicOrderAt_nonneg
  have hfun : W.continuedSource = singular + correction := by
    funext z
    simp only [continuedSource, poleFilledMain, singular, fac, shiftedLog,
      correction, Pi.add_apply]
    ring
  rw [hfun, meromorphicOrderAt_add_eq_left_of_lt hcorr.meromorphicAt hlt,
    hsingularOrder]

/-- **Exact Mellin-censorship law.** At every shifted zero in the BV continuation domain, the source
has a simple pole if and only if the Mellin transform does not vanish there. -/
theorem meromorphicOrderAt_continuedSource_eq_neg_one_iff_mellin_ne_zero
    (W : CompactBVPrimeWindow) {rho : ℂ} (hrho : 0 < rho.re)
    (hzero : regularizedRiemannZeta rho = 0) :
    meromorphicOrderAt W.continuedSource (rho + 1 / 2) =
        ((-1 : ℤ) : WithTop ℤ) ↔
      W.mellinTransform (rho + 1 / 2) ≠ 0 := by
  constructor
  · intro horder
    intro hMzero
    have hpHalf : 1 / 2 < (rho + 1 / 2).re := by
      norm_num [Complex.add_re]
      linarith
    have hmero : MeromorphicAt W.continuedSource (rho + 1 / 2) :=
      W.meromorphicOn_continuedSource_rightHalf (rho + 1 / 2) hpHalf
    have htrail := hmero.tendsto_nhds_meromorphicTrailingCoeffAt
    rw [horder] at htrail
    simp only [WithTop.untop₀_coe, neg_neg, zpow_one, smul_eq_mul] at htrail
    have hres := W.tendsto_continuedSource_residue_of_regularizedZeta_zero
      hrho hzero
    have hres0 : Tendsto
        (fun s : ℂ => (s - (rho + 1 / 2)) * W.continuedSource s)
        (𝓝[≠] (rho + 1 / 2)) (𝓝 0) := by
      rw [hMzero] at hres
      norm_num at hres
      exact hres
    have htrailZero : meromorphicTrailingCoeffAt W.continuedSource
        (rho + 1 / 2) = 0 :=
      tendsto_nhds_unique htrail hres0
    exact (hmero.meromorphicTrailingCoeffAt_ne_zero (by rw [horder]; simp))
      htrailZero
  · exact W.meromorphicOrderAt_continuedSource_eq_neg_one_of_mellin_ne_zero
      hrho hzero

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- Difference of two Mellin-normalized canonical BV sources. -/
def normalizedDifference (W V : CompactBVPrimeWindow) (s : ℂ) : ℂ :=
  W.continuedSource s / W.mellinTransform s -
    V.continuedSource s / V.mellinTransform s

/-- The kernel-normalized prime-source class is independent of the BV window modulo holomorphic
functions wherever both Mellin transforms are nonzero. -/
theorem analyticOnNhd_normalizedDifference
    (W V : CompactBVPrimeWindow) {U : Set ℂ} (hU : IsOpen U)
    (hWU : ∀ s ∈ U, W.mellinTransform s ≠ 0)
    (hVU : ∀ s ∈ U, V.mellinTransform s ≠ 0) :
    AnalyticOnNhd ℂ (W.normalizedDifference V)
      (U ∩ {s : ℂ | 1 / 2 < s.re}) := by
  intro s hs
  have hsU : s ∈ U := hs.1
  have hsHalf : 1 / 2 < s.re := hs.2
  have hMW : AnalyticAt ℂ W.mellinTransform s :=
    (W.differentiable_mellinTransform.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hMV : AnalyticAt ℂ V.mellinTransform s :=
    (V.differentiable_mellinTransform.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hdivW : AnalyticAt ℂ (dslope W.poleNumerator (3 / 2)) s :=
    (W.differentiable_poleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have hdivV : AnalyticAt ℂ (dslope V.poleNumerator (3 / 2)) s :=
    (V.differentiable_poleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  have herrW : AnalyticAt ℂ W.errorSeries s :=
    (W.differentiableOn_errorSeries_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) s hsHalf
  have herrV : AnalyticAt ℂ V.errorSeries s :=
    (V.differentiableOn_errorSeries_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) s hsHalf
  let regular : ℂ → ℂ := fun z =>
    dslope W.poleNumerator (3 / 2) z / W.mellinTransform z -
      dslope V.poleNumerator (3 / 2) z / V.mellinTransform z -
      (2 * W.errorSeries z) / W.mellinTransform z +
      (2 * V.errorSeries z) / V.mellinTransform z
  have hregular : AnalyticAt ℂ regular s := by
    dsimp only [regular]
    exact (((hdivW.div hMW (hWU s hsU)).sub
      (hdivV.div hMV (hVU s hsU))).sub
        ((analyticAt_const.mul herrW).div hMW (hWU s hsU))).add
      ((analyticAt_const.mul herrV).div hMV (hVU s hsU))
  have hev : regular =ᶠ[𝓝 s] W.normalizedDifference V := by
    filter_upwards [hU.mem_nhds hsU] with z hz
    have hWz := hWU z hz
    have hVz := hVU z hz
    dsimp only [regular, normalizedDifference, continuedSource, poleFilledMain]
    field_simp [hWz, hVz]
    ring
  exact hregular.congr hev

end CompactBVPrimeWindow
end RHTower

namespace RHTower
namespace CompactBVPrimeWindow

/-- A BV window whose Mellin transform is zero-free on `Re s > 1` detects every right
off-critical zero: RH is exactly holomorphy of its prime-defined canonical continuation there. -/
theorem riemannHypothesis_iff_continuedSource_analyticOn_rightOne
    (W : CompactBVPrimeWindow)
    (hM : ∀ s : ℂ, 1 < s.re → W.mellinTransform s ≠ 0) :
    RiemannHypothesis ↔
      AnalyticOnNhd ℂ W.continuedSource {s : ℂ | 1 < s.re} := by
  constructor
  · intro hRH
    have hxi := rh_iff_xi_ne_zero_right.mp hRH
    intro s hs
    change 1 < s.re at hs
    apply W.analyticAt_continuedSource_of_regularizedZeta_ne_zero
    · linarith
    · let t : ℂ := s - 1 / 2
      have htRight : t ∈ rightHalf := by
        rw [mem_rightHalf]
        dsimp only [t]
        norm_num [Complex.sub_re]
        linarith
      change regularizedRiemannZeta t ≠ 0
      by_cases ht : t = 1
      · rw [ht, regularizedRiemannZeta_one]
        norm_num
      · rw [regularizedRiemannZeta_of_ne_one ht]
        apply mul_ne_zero (sub_ne_zero.mpr ht)
        intro hzero
        have htpos : 0 < t.re := by
          rw [mem_rightHalf] at htRight
          linarith
        exact hxi t htRight ((xi_eq_zero_iff htpos ht).mpr hzero)
  · intro han
    by_contra hRH
    have hne : Nonempty XiRightZeroCopy :=
      nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
    let q : XiRightZeroCopy := Classical.choice hne
    let p : ℂ := xiRightShiftedPole q
    let rho : ℂ := p - 1 / 2
    have hp : 1 < p.re := by
      dsimp only [p]
      rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
      linarith [xiRightCenteredZero_re_pos q]
    have hrho : 0 < rho.re := by
      dsimp only [rho]
      norm_num [Complex.sub_re]
      linarith
    have hzero : regularizedRiemannZeta rho = 0 := by
      dsimp only [rho, p]
      exact regularizedRiemannZeta_shift_eq_zero_at_xiRightPole q
    have hpoint : rho + 1 / 2 = p := by
      dsimp only [rho]
      ring
    have horder := W.meromorphicOrderAt_continuedSource_eq_neg_one_of_mellin_ne_zero
      hrho hzero (by rw [hpoint]; exact hM p hp)
    rw [hpoint] at horder
    have hpAnalytic : AnalyticAt ℂ W.continuedSource p := han p hp
    have hnonneg : (0 : WithTop ℤ) ≤
        meromorphicOrderAt W.continuedSource p :=
      hpAnalytic.meromorphicOrderAt_nonneg
    rw [horder] at hnonneg
    have hnot : ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) := by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
    exact hnot hnonneg

end CompactBVPrimeWindow
end RHTower
