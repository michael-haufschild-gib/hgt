import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowDirichlet
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowCancellation
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowEnergySpectrum
import GaloisForLFunctions.RHTower.CCMShiftedXiPoleJet
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Multiplicity-exact divisor tomography from one dyadic prime window

The source coefficient

S(n) = 4 * (1 - 1 / sqrt 2) * sqrt n - 2 * sum_{n/2 < k <= n} Lambda(k) / sqrt k

contains no zero data. Its ordinary Dirichlet series has the canonical pole-filled continuation
dyadicSharpPrimeContinuedSource. The continuation already has a simple pole at every shifted
right Xi zero. This module computes the pole weights: the trailing coefficient is the analytic
zero multiplicity times the explicit nonvanishing sharp-window Mellin factor. Hence one fixed
source-defined dyadic statistic recovers the full right off-critical Xi divisor, including
multiplicity, and its holomorphy on Re s > 1 is equivalent to RH.
-/

open Complex Filter Function Set Topology

namespace RHTower

noncomputable section

/-- The shifted logarithmic derivative of the pole-filled zeta has residue equal to the exact
analytic multiplicity of the underlying Xi zero. -/
theorem tendsto_shiftedRegularizedZeta_logDeriv_residue
    (q : XiRightZeroCopy) :
    Tendsto
      (fun s : ℂ => (s - xiRightShiftedPole q) *
        logDeriv regularizedRiemannZeta (s - 1 / 2))
      (𝓝[≠] (xiRightShiftedPole q))
      (𝓝 (xiRightMultiplicity q : ℂ)) := by
  let p : ℂ := xiRightShiftedPole q
  let ρ : ℂ := (q.1.1 : ℂ)
  have hpρ : p - 1 / 2 = ρ := by
    simpa only [p, ρ] using xiRightShiftedPole_sub_half q
  have hreg : AnalyticAt ℂ regularizedRiemannZeta ρ :=
    (differentiable_regularizedRiemannZeta.differentiableOn.analyticOnNhd
      isOpen_univ) ρ (Set.mem_univ ρ)
  have hzero : regularizedRiemannZeta ρ = 0 := by
    simpa only [p, hpρ] using
      regularizedRiemannZeta_shift_eq_zero_at_xiRightPole q
  have hbase := logDeriv_iteratedDeriv_residue_of_zero
    hreg (analyticOrderAt_regularizedRiemannZeta_ne_top ρ) hzero 0
  have hbase' : Tendsto
      (fun t : ℂ => (t - ρ) * logDeriv regularizedRiemannZeta t)
      (𝓝[≠] ρ)
      (𝓝 ((analyticOrderAt regularizedRiemannZeta ρ).toNat : ℂ)) := by
    simpa only [zero_add, pow_one, iteratedDeriv_zero, logDeriv_apply,
      pow_zero, Nat.factorial_zero, Nat.cast_one, one_mul, mul_one] using hbase
  have hshift : Tendsto (fun s : ℂ => s - 1 / 2)
      (𝓝[≠] p) (𝓝[≠] ρ) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : ContinuousAt (fun s : ℂ => s - 1 / 2) p :=
        continuousAt_id.sub_const _
      have hle : 𝓝[≠] p ≤ 𝓝 p := inf_le_left
      simpa only [hpρ] using hc.tendsto.mono_left hle
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s - 1 / 2 ≠ ρ
      intro heq
      have hsp : s ≠ p := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
      apply hsp
      linear_combination heq - hpρ
  have hcomposed := hbase'.comp hshift
  have hbaseOrder : analyticOrderAt regularizedRiemannZeta ρ =
      analyticOrderAt xi (q.1.1 : ℂ) := by
    have hcenterRe := congrArg Complex.re
      (xiRightCenteredZero_eq_support_sub_half q)
    simp only [Complex.sub_re] at hcenterRe
    norm_num at hcenterRe
    have hcenterBounds := abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)
    have hρpos : 0 < ρ.re := by
      dsimp only [ρ]
      linarith
    have hρlt : ρ.re < 1 := by
      dsimp only [ρ]
      linarith
    have hρ1 : ρ ≠ 1 := by
      intro h
      rw [h, Complex.one_re] at hρlt
      exact (lt_irrefl 1 hρlt).elim
    have hregEqZeta :
        analyticOrderAt regularizedRiemannZeta ρ =
          analyticOrderAt riemannZeta ρ := by
      have hev : regularizedRiemannZeta =ᶠ[nhds ρ]
          fun z => (z - 1) * riemannZeta z := by
        filter_upwards [isOpen_ne.mem_nhds hρ1] with z hz
        exact regularizedRiemannZeta_of_ne_one hz
      have hlin : AnalyticAt ℂ (fun z : ℂ => z - 1) ρ := by fun_prop
      have hzeta : AnalyticAt ℂ riemannZeta ρ :=
        analyticOn_riemannZeta ρ hρ1
      rw [analyticOrderAt_congr hev]
      change analyticOrderAt ((fun z : ℂ => z - 1) * riemannZeta) ρ =
        analyticOrderAt riemannZeta ρ
      rw [analyticOrderAt_mul hlin hzeta,
        hlin.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hρ1), zero_add]
    calc
      analyticOrderAt regularizedRiemannZeta ρ =
          analyticOrderAt riemannZeta ρ := hregEqZeta
      _ = analyticOrderAt xi ρ :=
        (xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
          ⟨hρpos, hρlt⟩).symm
      _ = analyticOrderAt xi (q.1.1 : ℂ) := by rfl
  rw [hbaseOrder] at hcomposed
  change Tendsto _ _
    (𝓝 ((analyticOrderAt xi (q.1.1 : ℂ)).toNat : ℂ))
  convert hcomposed using 1
  funext s
  rw [Function.comp_apply]
  congr 1
  dsimp only [p, ρ] at hpρ ⊢
  rw [← hpρ]
  ring

/-- The shifted logarithmic derivative has a simple pole at every right Xi support point,
independently of the zero multiplicity. -/
theorem meromorphicOrderAt_shiftedRegularizedZeta_logDeriv_eq_neg_one
    (q : XiRightZeroCopy) :
    meromorphicOrderAt
        (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ) := by
  let p : ℂ := xiRightShiftedPole q
  let ρ : ℂ := (q.1.1 : ℂ)
  have hpρ : p - 1 / 2 = ρ := by
    simpa only [p, ρ] using xiRightShiftedPole_sub_half q
  have hzero : regularizedRiemannZeta ρ = 0 := by
    simpa only [p, hpρ] using
      regularizedRiemannZeta_shift_eq_zero_at_xiRightPole q
  let shift : ℂ → ℂ := fun z => z - 1 / 2
  have hshiftAnalytic : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hshiftDeriv : deriv shift p ≠ 0 := by
    dsimp only [shift]
    rw [deriv_sub_const, deriv_id'']
    norm_num
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := logDeriv regularizedRiemannZeta) (g := shift) (x := p)
    hshiftAnalytic hshiftDeriv
  rw [show shift p = ρ by simpa only [shift] using hpρ,
    meromorphicOrderAt_logDeriv_regularizedRiemannZeta_eq_neg_one hzero] at hcomp
  simpa only [shift, Function.comp_apply] using hcomp

/-- The trailing coefficient of the shifted logarithmic derivative is the full analytic
multiplicity, not merely a nonzero pole marker. -/
theorem meromorphicTrailingCoeffAt_shiftedRegularizedZeta_logDeriv
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt
        (fun s : ℂ => logDeriv regularizedRiemannZeta (s - 1 / 2))
        (xiRightShiftedPole q) = (xiRightMultiplicity q : ℂ) := by
  let p : ℂ := xiRightShiftedPole q
  let f : ℂ → ℂ := fun s =>
    logDeriv regularizedRiemannZeta (s - 1 / 2)
  let shift : ℂ → ℂ := fun s => s - 1 / 2
  have hshiftAnalytic : AnalyticAt ℂ shift p := by
    dsimp only [shift]
    fun_prop
  have hbase : MeromorphicAt (logDeriv regularizedRiemannZeta) (shift p) :=
    meromorphicAt_logDeriv_regularizedRiemannZeta (shift p)
  have hf : MeromorphicAt f p := by
    have hcomp := MeromorphicAt.comp_analyticAt
      (f := logDeriv regularizedRiemannZeta) (g := shift)
      hbase hshiftAnalytic
    simpa only [f, shift, Function.comp_apply] using hcomp
  have horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ) := by
    simpa only [f, p] using
      meromorphicOrderAt_shiftedRegularizedZeta_logDeriv_eq_neg_one q
  have htrail := hf.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [horder] at htrail
  simp only [WithTop.untop₀_coe, neg_neg, zpow_one, smul_eq_mul] at htrail
  have hres := tendsto_shiftedRegularizedZeta_logDeriv_residue q
  simpa only [f, p] using tendsto_nhds_unique htrail hres

/-- **Multiplicity formula for the dyadic source.** At a shifted right Xi zero, the source
residue is the analytic multiplicity times the explicit nonvanishing dyadic Mellin factor. -/
theorem meromorphicTrailingCoeffAt_dyadicSharpPrimeContinuedSource
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt dyadicSharpPrimeContinuedSource
        (xiRightShiftedPole q) =
      2 * sharpPrimeWindowMellin (Real.log 2) (xiRightShiftedPole q) *
        (xiRightMultiplicity q : ℂ) := by
  let p : ℂ := xiRightShiftedPole q
  let shiftedLog : ℂ → ℂ := fun z =>
    logDeriv regularizedRiemannZeta (z - 1 / 2)
  let fac : ℂ → ℂ := fun z =>
    2 * sharpPrimeWindowMellin (Real.log 2) z
  let singular : ℂ → ℂ := fun z => fac z * shiftedLog z
  let correction : ℂ → ℂ := fun z =>
    dslope dyadicSharpPrimePoleNumerator (3 / 2) z -
      2 * dyadicSharpPrimeWindowErrorSeries z
  have hpRight : 1 < p.re := by
    dsimp only [p]
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hpHalf : 1 / 2 < p.re := by linarith
  have hM : AnalyticAt ℂ (sharpPrimeWindowMellin (Real.log 2)) p :=
    (differentiable_sharpPrimeWindowMellin_logTwo.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have hfac : AnalyticAt ℂ fac p := by
    dsimp only [fac]
    exact analyticAt_const.mul hM
  have hfac0 : fac p ≠ 0 := by
    dsimp only [fac]
    exact mul_ne_zero (by norm_num)
      (sharpPrimeWindowMellin_ne_zero_of_one_lt_re
        (Real.log_pos (by norm_num)) hpRight)
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
      meromorphicOrderAt_shiftedRegularizedZeta_logDeriv_eq_neg_one q
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
  have hdiv : AnalyticAt ℂ
      (dslope dyadicSharpPrimePoleNumerator (3 / 2)) p :=
    (differentiable_dyadicSharpPrimePoleDividedDifference.differentiableOn.analyticOnNhd
      isOpen_univ) p (Set.mem_univ p)
  have herr : AnalyticAt ℂ dyadicSharpPrimeWindowErrorSeries p :=
    (differentiableOn_dyadicSharpPrimeWindowErrorSeries_rightHalf.analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)) p hpHalf
  have hcorrection : AnalyticAt ℂ correction p := by
    dsimp only [correction]
    exact hdiv.sub (analyticAt_const.mul herr)
  have hlt : meromorphicOrderAt singular p <
      meromorphicOrderAt correction p := by
    rw [hsingularOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorrection.meromorphicOrderAt_nonneg
  have hfun : dyadicSharpPrimeContinuedSource = singular + correction := by
    funext z
    simp only [dyadicSharpPrimeContinuedSource, dyadicSharpPrimePoleFilledMain,
      singular, fac, shiftedLog, correction, Pi.add_apply]
    ring
  rw [hfun]
  change meromorphicTrailingCoeffAt (fun z => singular z + correction z) p =
    fac p * (xiRightMultiplicity q : ℂ)
  rw [hcorrection.meromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt hlt]
  dsimp only [singular]
  rw [hfac.meromorphicAt.meromorphicTrailingCoeffAt_fun_mul hshiftedLog,
    hfac.meromorphicTrailingCoeffAt_of_ne_zero hfac0]
  have hlogTrail :=
    meromorphicTrailingCoeffAt_shiftedRegularizedZeta_logDeriv q
  rw [hlogTrail]

/-- Every zero of the shifted pole-filled zeta in `Re s > 1` names a multiplicity copy of the
right Xi divisor at that shifted coordinate. -/
theorem exists_xiRightZeroCopy_of_shiftedRegularizedZeta_eq_zero
    {s : ℂ} (hs : 1 < s.re)
    (hzero : regularizedRiemannZeta (s - 1 / 2) = 0) :
    ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s := by
  have ht1 : s - 1 / 2 ≠ 1 := by
    intro ht
    rw [ht, regularizedRiemannZeta_one] at hzero
    norm_num at hzero
  have hzeta : riemannZeta (s - 1 / 2) = 0 := by
    rw [regularizedRiemannZeta_of_ne_one ht1] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr ht1)
  have htpos : 0 < (s - 1 / 2).re := by
    norm_num [Complex.sub_re]
    linarith
  have hxi : xi (s - 1 / 2) = 0 :=
    (xi_eq_zero_iff htpos ht1).mpr hzeta
  let ρ : XiDivisorSupport :=
    ⟨s - 1 / 2, mem_xi_divisor_support_of_eq_zero hxi⟩
  have hm : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    have hpos := xi_divisor_pos_on_support ρ
    omega
  let q0 : XiZeroCopy := ⟨ρ, ⟨0, hm⟩⟩
  have hq0 : 0 < (I * xiSpectralPoint q0).re := by
    rw [I_mul_xiSpectralPoint]
    dsimp only [q0, ρ]
    norm_num [Complex.sub_re]
    linarith
  let q : XiRightZeroCopy := ⟨q0, hq0⟩
  refine ⟨q, ?_⟩
  rw [xiRightShiftedPole, xiRightCenteredZero, I_mul_xiSpectralPoint]
  dsimp only [q, q0, ρ]
  ring

/-- Route-local multiplicity witness for a shifted Xi zero in `Re s > 1`. -/
theorem exists_xiRightZeroCopy_of_xi_shifted_eq_zero
    {s : ℂ} (hs : 1 < s.re) (hzero : xi (s - 1 / 2) = 0) :
    ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s := by
  let ρ : XiDivisorSupport :=
    ⟨s - 1 / 2, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hm : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    have hpos := xi_divisor_pos_on_support ρ
    omega
  let q0 : XiZeroCopy := ⟨ρ, ⟨0, hm⟩⟩
  have hq0 : 0 < (I * xiSpectralPoint q0).re := by
    rw [I_mul_xiSpectralPoint]
    dsimp only [q0, ρ]
    norm_num [Complex.sub_re]
    linarith
  let q : XiRightZeroCopy := ⟨q0, hq0⟩
  refine ⟨q, ?_⟩
  rw [xiRightShiftedPole, xiRightCenteredZero, I_mul_xiSpectralPoint]
  dsimp only [q, q0, ρ]
  ring

/-- The simple-pole support of the dyadic continued source is exactly the shifted right Xi
divisor support. There are no extraneous source poles on `Re s > 1`. -/
theorem meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one_iff
    {s : ℂ} (hs : 1 < s.re) :
    meromorphicOrderAt dyadicSharpPrimeContinuedSource s =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s := by
  constructor
  · intro horder
    have hzero : regularizedRiemannZeta (s - 1 / 2) = 0 := by
      by_contra hne
      have han :=
        analyticAt_dyadicSharpPrimeContinuedSource_of_regularizedZeta_ne_zero
          (by linarith) hne
      have hnonneg : (0 : WithTop ℤ) ≤
          meromorphicOrderAt dyadicSharpPrimeContinuedSource s :=
        han.meromorphicOrderAt_nonneg
      rw [horder] at hnonneg
      have hnot : ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) := by
        exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)
      exact hnot hnonneg
    exact exists_xiRightZeroCopy_of_shiftedRegularizedZeta_eq_zero hs hzero
  · rintro ⟨q, hq⟩
    rw [← hq]
    exact meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one q

/-- Dividing the dyadic source residue by its explicit nonzero Mellin weight recovers the exact
analytic multiplicity. -/
theorem normalizedDyadicSharpPrimeSourceResidue_eq_xiRightMultiplicity
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt dyadicSharpPrimeContinuedSource
          (xiRightShiftedPole q) /
        (2 * sharpPrimeWindowMellin (Real.log 2) (xiRightShiftedPole q)) =
      (xiRightMultiplicity q : ℂ) := by
  rw [meromorphicTrailingCoeffAt_dyadicSharpPrimeContinuedSource]
  have hpRight : 1 < (xiRightShiftedPole q).re := by
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hM : sharpPrimeWindowMellin (Real.log 2)
      (xiRightShiftedPole q) ≠ 0 :=
    sharpPrimeWindowMellin_ne_zero_of_one_lt_re
      (Real.log_pos (by norm_num)) hpRight
  field_simp [hM]

/-- The complete right off-critical Xi support is the translated simple-pole support of one
source-defined dyadic continuation. -/
theorem xiRightZeroSupport_eq_image_dyadicSharpPrimeSimplePoleSupport :
    {ρ : ℂ | xi ρ = 0 ∧ 1 / 2 < ρ.re} =
      (fun s : ℂ => s - 1 / 2) ''
        {s : ℂ | 1 < s.re ∧
          meromorphicOrderAt dyadicSharpPrimeContinuedSource s =
            ((-1 : ℤ) : WithTop ℤ)} := by
  ext ρ
  constructor
  · rintro ⟨hzero, hρ⟩
    let s : ℂ := ρ + 1 / 2
    have hs : 1 < s.re := by
      dsimp only [s]
      norm_num [Complex.add_re] at hρ ⊢
      linarith
    have hshift : s - 1 / 2 = ρ := by
      dsimp only [s]
      ring
    have hzero' : xi (s - 1 / 2) = 0 := by rwa [hshift]
    obtain ⟨q, hq⟩ :=
      exists_xiRightZeroCopy_of_xi_shifted_eq_zero hs hzero'
    have horder :
        meromorphicOrderAt dyadicSharpPrimeContinuedSource s =
          ((-1 : ℤ) : WithTop ℤ) :=
      (meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one_iff
        hs).mpr ⟨q, hq⟩
    exact ⟨s, ⟨hs, horder⟩, hshift⟩
  · rintro ⟨s, ⟨hs, horder⟩, rfl⟩
    obtain ⟨q, hq⟩ :=
      (meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one_iff
        hs).mp horder
    constructor
    · rw [← hq]
      change xi (xiRightShiftedPole q - 1 / 2) = 0
      rw [xiRightShiftedPole_sub_half]
      exact xi_eq_zero_of_mem_divisor_support q.1.1
    · norm_num [Complex.sub_re] at hs ⊢
      linarith

/-- **Critical source-energy endpoint.** Absolute convergence at the single critical abscissa
`1` of the positive dyadic prime-window overshoot excludes every right Xi zero and proves RH. -/
theorem riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcess_summable_at_one
    (henergy : LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ)) 1) :
    RiemannHypothesis := by
  apply rh_iff_xi_ne_zero_right.mpr
  intro s hs hzero
  have hbound :=
    xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable
      (alpha := 0) (by norm_num) (by simpa using henergy) hzero
  rw [mem_rightHalf] at hs
  norm_num at hbound
  linarith

/-- **Dyadic prime-source divisor tomography.** One source-defined coefficient sequence has an
ordinary Dirichlet series on `Re s > 3/2`, a canonical meromorphic continuation on
`Re s > 1/2`, simple-pole support exactly equal to the shifted right Xi divisor, normalized
pole weights equal to the analytic multiplicities, and no poles on `Re s > 1` exactly under
RH. -/
theorem dyadicSharpPrimeSourceDivisorTomography_capstone :
    (∀ s : ℂ, 3 / 2 < s.re →
      LSeries
          (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s =
        dyadicSharpPrimeContinuedSource s) ∧
    MeromorphicOn dyadicSharpPrimeContinuedSource
      {s : ℂ | 1 / 2 < s.re} ∧
    (∀ s : ℂ, 1 < s.re →
      (meromorphicOrderAt dyadicSharpPrimeContinuedSource s =
          ((-1 : ℤ) : WithTop ℤ) ↔
        ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s)) ∧
    (∀ q : XiRightZeroCopy,
      meromorphicTrailingCoeffAt dyadicSharpPrimeContinuedSource
          (xiRightShiftedPole q) =
        2 * sharpPrimeWindowMellin (Real.log 2) (xiRightShiftedPole q) *
          (xiRightMultiplicity q : ℂ) ∧
      meromorphicTrailingCoeffAt dyadicSharpPrimeContinuedSource
            (xiRightShiftedPole q) /
          (2 * sharpPrimeWindowMellin (Real.log 2) (xiRightShiftedPole q)) =
        (xiRightMultiplicity q : ℂ)) ∧
    ({ρ : ℂ | xi ρ = 0 ∧ 1 / 2 < ρ.re} =
      (fun s : ℂ => s - 1 / 2) ''
        {s : ℂ | 1 < s.re ∧
          meromorphicOrderAt dyadicSharpPrimeContinuedSource s =
            ((-1 : ℤ) : WithTop ℤ)}) ∧
    (∀ alpha : ℝ, 0 ≤ alpha →
      LSeriesSummable
          (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
          (((1 + alpha : ℝ) : ℂ)) →
      ∀ rho : ℂ, xi rho = 0 → rho.re ≤ 1 / 2 + alpha) ∧
    (LSeriesSummable
        (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ)) 1 →
      RiemannHypothesis) ∧
    (RiemannHypothesis ↔
      AnalyticOnNhd ℂ dyadicSharpPrimeContinuedSource
        {s : ℂ | 1 < s.re}) := by
  refine ⟨?_, meromorphicOn_dyadicSharpPrimeContinuedSource_rightHalf,
    ?_, ?_, xiRightZeroSupport_eq_image_dyadicSharpPrimeSimplePoleSupport,
    ?_, riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcess_summable_at_one,
    riemannHypothesis_iff_dyadicSharpPrimeContinuedSource_analyticOn_rightOne⟩
  · intro s hs
    exact LSeries_dyadicSharpPrimeSourceCoefficient_eq_continuedSource hs
  · intro s hs
    exact meromorphicOrderAt_dyadicSharpPrimeContinuedSource_eq_neg_one_iff hs
  · intro q
    exact ⟨meromorphicTrailingCoeffAt_dyadicSharpPrimeContinuedSource q,
      normalizedDyadicSharpPrimeSourceResidue_eq_xiRightMultiplicity q⟩
  · intro alpha halpha henergy rho hzero
    exact xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable
      halpha henergy hzero

end

end RHTower
