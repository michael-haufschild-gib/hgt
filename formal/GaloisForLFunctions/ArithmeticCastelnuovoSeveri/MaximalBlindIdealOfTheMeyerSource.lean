import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CriticalMeyerTraceDegree
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheOrientationOfACycle

/-!
# The maximum sharp-stable positive ideal of the Meyer source

Mixed-trace boundedness along the centered scaling flow defines a pre-divisor
subspace of the genuine Meyer strong-log source algebra without mentioning Xi
zeros or Hasse multiplicities. Evaluating against reflected point sources shows
that this carrier consists precisely of sources whose Mellin transform vanishes
at every off-line Xi zero, while retaining all critical jets of every order.

Unlike the full-Hasse Hilbert–Schmidt bounded-orbit carrier, this pre-divisor
carrier is a two-sided sharp-stable convolution ideal whose restricted polar
surface satisfies the Hodge index, Riemann–Roch, Bézout, ampleness, and additive
closure unconditionally without assuming critical simplicity. Moreover, it is the
unique maximum sharp-stable convolution ideal on which the source trace is
nonnegative: single-channel additive positivity on any correspondence-stable
ideal is algebraically exhausted by off-line blindness.
-/

noncomputable section

open Complex Zeta23 RHTower ContinuousLinearMap Set
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Pre-divisor mixed-trace orbit boundedness on the genuine Meyer source space:
every mixed trace along the centered scaling orbit of `g` is uniformly bounded. -/
def MeyerTraceOrbitBounded (g : DeningerMeyerStrongLogTarget) : Prop :=
  ∀ h : DeningerMeyerStrongLogTarget, ∃ C : ℝ, ∀ c : ℝ,
    |meyerSourceTrace (deningerMeyerStrongLogCenteredFlow c g) h| ≤ C

private theorem sharp_sq (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerSourceSharp (deningerMeyerSourceSharp g) = g := by
  simp only [deningerMeyerSourceSharp, deningerMeyerStrongLogConj_J,
    deningerMeyerStrongLogConj_sq, deningerMeyerStrongLogJ_sq]

private theorem point_trace_reading (g : DeningerMeyerStrongLogTarget)
    (rho : XiDivisorSupport) (a : ℂ) :
    meyerSourceTrace g (deningerMeyerSourceSharp (a • meyerPointSource rho)) =
      (a * ((xiSupportMultiplicity rho : ℂ) * deningerMeyerStrongLogMellin g (rho : ℂ))).re := by
  rw [meyerSourceTrace, sharp_sq, meyerPointSource_product_trace]

private theorem critical_reflect_eq_self (rho : XiDivisorSupport)
    (hr : (rho : ℂ).re = 1 / 2) : meyerLineReflect rho = rho := by
  apply Subtype.ext
  apply Complex.ext
  · change 1 - (rho : ℂ).re = (rho : ℂ).re
    linarith only [hr]
  · change -(0 - (rho : ℂ).im) = (rho : ℂ).im
    ring

/-- When all off-line Mellin values of `g` vanish, every mixed trace of `g` reduces to
the absolutely convergent critical trace degree. -/
theorem meyerSourceTrace_eq_critical_of_offLine_zero {g : DeningerMeyerStrongLogTarget}
    (hg : ∀ rho : XiDivisorSupport, (rho : ℂ).re ≠ 1 / 2 →
      deningerMeyerStrongLogMellin g (rho : ℂ) = 0)
    (h : DeningerMeyerStrongLogTarget) :
    meyerSourceTrace g h =
      (meyerCriticalSourceTraceDegree
        (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h))).re := by
  rw [meyerSourceTrace_eq_degree_product, meyerCohomologyTraceDegree_mk]
  congr 1
  symm
  let p := deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h)
  change (∑' q : MeyerCriticalXiCopy, deningerMeyerStrongLogMellin p (q.1.1 : ℂ)) =
    opTrace (deningerMeyerHilbertConvolution p)
  rw [deningerMeyerHilbertConvolution_opTrace]
  calc
    _ = ∑' q : XiZeroCopy, ({q : XiZeroCopy | (q.1 : ℂ).re = 1 / 2}).indicator
        (fun q => deningerMeyerStrongLogMellin p (q.1 : ℂ)) q := tsum_subtype _ _
    _ = _ := by
      apply tsum_congr
      intro q
      by_cases hq : (q.1 : ℂ).re = 1 / 2
      · exact Set.indicator_of_mem hq _
      · rw [Set.indicator_of_notMem hq]
        symm
        change deningerMeyerStrongLogMellin
          (deningerMeyerSourceConvolution g (deningerMeyerSourceSharp h)) (q.1 : ℂ) = 0
        rw [deningerMeyerSourceConvolution_mellin, hg q.1 hq, zero_mul]

/-- Off-line Mellin vanishing bounds the entire centered-flow mixed trace orbit by the
arithmetic mean of the two critical square energies. -/
theorem meyerTraceOrbit_le_criticalSquareEnergy_of_offLine_zero {g : DeningerMeyerStrongLogTarget}
    (hg : ∀ rho : XiDivisorSupport, (rho : ℂ).re ≠ 1 / 2 →
      deningerMeyerStrongLogMellin g (rho : ℂ) = 0)
    (h : DeningerMeyerStrongLogTarget) (c : ℝ) :
    |meyerSourceTrace (deningerMeyerStrongLogCenteredFlow c g) h| ≤
      (meyerCriticalSquareEnergy g + meyerCriticalSquareEnergy h) / 2 := by
  have hg_flow : ∀ rho : XiDivisorSupport, (rho : ℂ).re ≠ 1 / 2 →
      deningerMeyerStrongLogMellin (deningerMeyerStrongLogCenteredFlow c g) (rho : ℂ) = 0 := by
    intro rho hr
    rw [meyerCenteredSourceFlow_mellin, hg rho hr, mul_zero]
  rw [meyerSourceTrace_eq_critical_of_offLine_zero hg_flow h]
  let p := deningerMeyerSourceConvolution
    (deningerMeyerStrongLogCenteredFlow c g) (deningerMeyerSourceSharp h)
  have hp_sum : Summable (fun q : MeyerCriticalXiCopy =>
      deningerMeyerStrongLogMellin p (q.1.1 : ℂ)) :=
    (deningerMeyerHilbertConvolution_summable_diagonal p).subtype _
  have hre : |(meyerCriticalSourceTraceDegree p).re| ≤
      ‖∑' q : MeyerCriticalXiCopy, deningerMeyerStrongLogMellin p (q.1.1 : ℂ)‖ :=
    Complex.abs_re_le_norm _
  have hnorm_sum : ‖∑' q : MeyerCriticalXiCopy, deningerMeyerStrongLogMellin p (q.1.1 : ℂ)‖ ≤
      ∑' q : MeyerCriticalXiCopy, ‖deningerMeyerStrongLogMellin p (q.1.1 : ℂ)‖ :=
    norm_tsum_le_tsum_norm hp_sum.norm
  have hmaj_sum : Summable (fun q : MeyerCriticalXiCopy =>
      (Complex.normSq (deningerMeyerStrongLogMellin g (q.1.1 : ℂ)) +
        Complex.normSq (deningerMeyerStrongLogMellin h (q.1.1 : ℂ))) / 2) :=
    ((meyerCriticalSquares_summable g).add (meyerCriticalSquares_summable h)).div_const 2
  have hterm (q : MeyerCriticalXiCopy) :
      ‖deningerMeyerStrongLogMellin p (q.1.1 : ℂ)‖ ≤
        (Complex.normSq (deningerMeyerStrongLogMellin g (q.1.1 : ℂ)) +
          Complex.normSq (deningerMeyerStrongLogMellin h (q.1.1 : ℂ))) / 2 := by
    let rho : XiDivisorSupport := q.1.1
    have hr : (rho : ℂ).re = 1 / 2 := q.2
    have hnorm_flow : ‖deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogCenteredFlow c g) (rho : ℂ)‖ =
        ‖deningerMeyerStrongLogMellin g (rho : ℂ)‖ := by
      rw [meyerCenteredSourceFlow_mellin, norm_mul, Complex.norm_exp]
      have hre0 : ((c : ℂ) * ((rho : ℂ) - 1 / 2)).re = 0 := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, zero_mul, sub_zero, hr, sub_self,
          mul_zero]
      rw [hre0, Real.exp_zero, one_mul]
    have hnorm_sharp : ‖deningerMeyerStrongLogMellin (deningerMeyerSourceSharp h) (rho : ℂ)‖ =
        ‖deningerMeyerStrongLogMellin h (rho : ℂ)‖ := by
      rw [deningerMeyerSourceSharp_mellin, ← meyerLineReflect_val,
        critical_reflect_eq_self rho hr, norm_star]
    change ‖deningerMeyerStrongLogMellin
      (deningerMeyerSourceConvolution (deningerMeyerStrongLogCenteredFlow c g)
        (deningerMeyerSourceSharp h)) (rho : ℂ)‖ ≤ _
    rw [deningerMeyerSourceConvolution_mellin, norm_mul, hnorm_flow, hnorm_sharp,
      ← Complex.sq_norm, ← Complex.sq_norm]
    nlinarith only [sq_nonneg (‖deningerMeyerStrongLogMellin g (rho : ℂ)‖ -
      ‖deningerMeyerStrongLogMellin h (rho : ℂ)‖)]
  have htsum_le := hp_sum.norm.tsum_le_tsum hterm hmaj_sum
  have hmaj_eq : (∑' q : MeyerCriticalXiCopy,
      (Complex.normSq (deningerMeyerStrongLogMellin g (q.1.1 : ℂ)) +
        Complex.normSq (deningerMeyerStrongLogMellin h (q.1.1 : ℂ))) / 2) =
      (meyerCriticalSquareEnergy g + meyerCriticalSquareEnergy h) / 2 := by
    rw [tsum_div_const,
      (meyerCriticalSquares_summable g).tsum_add (meyerCriticalSquares_summable h),
      ← meyerCriticalSquareEnergy_eq_tsum, ← meyerCriticalSquareEnergy_eq_tsum]
  linarith only [hre, hnorm_sum, htsum_le, hmaj_eq]

/-- Pre-divisor mixed-trace orbit boundedness holds if and only if the Mellin transform
vanishes at every off-line Xi zero, with no restriction on critical jet multiplicities. -/
theorem meyerTraceOrbitBounded_iff_offLine_values_zero (g : DeningerMeyerStrongLogTarget) :
    MeyerTraceOrbitBounded g ↔
      ∀ rho : XiDivisorSupport, (rho : ℂ).re ≠ 1 / 2 →
        deningerMeyerStrongLogMellin g (rho : ℂ) = 0 := by
  constructor
  · intro hg rho hoff
    by_contra hz
    obtain ⟨C0, hC0⟩ := hg (deningerMeyerSourceSharp ((1 : ℂ) • meyerPointSource rho))
    obtain ⟨C1, hC1⟩ := hg (deningerMeyerSourceSharp (I • meyerPointSource rho))
    let z := deningerMeyerStrongLogMellin g (rho : ℂ)
    have hz_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let δ : ℝ := (rho : ℂ).re - 1 / 2
    have hδ : δ ≠ 0 := sub_ne_zero.mpr hoff
    let B : ℝ := |C0| + |C1| + 1
    let c : ℝ := (B / ‖z‖) / δ
    let wc : ℂ := deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogCenteredFlow c g) (rho : ℂ)
    let m : ℝ := xiSupportMultiplicity rho
    have hm : 1 ≤ m := by
      dsimp only [m]
      exact_mod_cast (show 1 ≤ xiSupportMultiplicity rho from xiSupportMultiplicity_pos rho)
    have hr0 : meyerSourceTrace (deningerMeyerStrongLogCenteredFlow c g)
        (deningerMeyerSourceSharp ((1 : ℂ) • meyerPointSource rho)) = m * wc.re := by
      rw [point_trace_reading]
      simp only [one_mul, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
      rfl
    have hi1 : meyerSourceTrace (deningerMeyerStrongLogCenteredFlow c g)
        (deningerMeyerSourceSharp (I • meyerPointSource rho)) = -(m * wc.im) := by
      rw [point_trace_reading]
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.natCast_re, Complex.natCast_im, zero_mul, one_mul, add_zero, sub_zero, zero_sub]
      rfl
    have hb0 : m * |wc.re| ≤ |C0| := by
      have h0 := (hC0 c).trans (le_abs_self C0)
      rwa [hr0, abs_mul, abs_of_pos (by linarith only [hm])] at h0
    have hb1 : m * |wc.im| ≤ |C1| := by
      have h1 := (hC1 c).trans (le_abs_self C1)
      rwa [hi1, abs_neg, abs_mul, abs_of_pos (by linarith only [hm])] at h1
    have hre_le : |wc.re| ≤ |C0| := by
      nlinarith only [hm, hb0, abs_nonneg wc.re]
    have him_le : |wc.im| ≤ |C1| := by
      nlinarith only [hm, hb1, abs_nonneg wc.im]
    have hwc_upper : ‖wc‖ ≤ |C0| + |C1| :=
      (Complex.norm_le_abs_re_add_abs_im wc).trans (add_le_add hre_le him_le)
    have hwc_norm : ‖wc‖ = Real.exp (c * δ) * ‖z‖ := by
      dsimp only [wc, z, δ]
      rw [meyerCenteredSourceFlow_mellin, norm_mul, Complex.norm_exp]
      congr 2
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.div_ofNat_re, Complex.one_re, zero_mul, sub_zero]
    have hcδ : c * δ = B / ‖z‖ := div_mul_cancel₀ (B / ‖z‖) hδ
    have hexp : B / ‖z‖ + 1 ≤ Real.exp (c * δ) := by
      rw [hcδ]
      exact Real.add_one_le_exp (B / ‖z‖)
    have hwc_lower : B + ‖z‖ ≤ ‖wc‖ := by
      rw [hwc_norm]
      have hmul := mul_le_mul_of_nonneg_right hexp hz_pos.le
      rwa [add_mul, div_mul_cancel₀ B (ne_of_gt hz_pos), one_mul] at hmul
    dsimp only [B] at hwc_lower
    linarith only [hwc_upper, hwc_lower, hz_pos]
  · intro hg h
    exact ⟨(meyerCriticalSquareEnergy g + meyerCriticalSquareEnergy h) / 2,
      meyerTraceOrbit_le_criticalSquareEnergy_of_offLine_zero hg h⟩

/-- The pre-divisor trace-orbit-bounded sources form a complex linear subspace. -/
def meyerTraceBoundedIdeal : Submodule ℂ DeningerMeyerStrongLogTarget where
  carrier := {g | MeyerTraceOrbitBounded g}
  zero_mem' := by
    rw [Set.mem_setOf_eq, meyerTraceOrbitBounded_iff_offLine_values_zero]
    intro rho _
    exact map_zero (deningerMeyerStrongLogMellinLM (rho : ℂ))
  add_mem' := by
    intro g h hg hh
    rw [Set.mem_setOf_eq, meyerTraceOrbitBounded_iff_offLine_values_zero] at hg hh ⊢
    intro rho hr
    change deningerMeyerStrongLogMellinLM (rho : ℂ) (g + h) = 0
    rw [map_add]
    change deningerMeyerStrongLogMellin g (rho : ℂ) +
      deningerMeyerStrongLogMellin h (rho : ℂ) = 0
    rw [hg rho hr, hh rho hr, add_zero]
  smul_mem' := by
    intro a g hg
    rw [Set.mem_setOf_eq, meyerTraceOrbitBounded_iff_offLine_values_zero] at hg ⊢
    intro rho hr
    change deningerMeyerStrongLogMellinLM (rho : ℂ) (a • g) = 0
    rw [map_smul]
    change a * deningerMeyerStrongLogMellin g (rho : ℂ) = 0
    rw [hg rho hr, mul_zero]

/-- Arithmetic sharp preserves pre-divisor trace-orbit boundedness. -/
theorem meyerTraceOrbitBounded_sharp {g : DeningerMeyerStrongLogTarget}
    (hg : MeyerTraceOrbitBounded g) :
    MeyerTraceOrbitBounded (deningerMeyerSourceSharp g) := by
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero] at hg ⊢
  intro rho hr
  have href : (meyerLineReflect rho : ℂ).re ≠ 1 / 2 := by
    intro hre
    change 1 - (rho : ℂ).re = 1 / 2 at hre
    exact hr (by linarith only [hre])
  rw [deningerMeyerSourceSharp_mellin, ← meyerLineReflect_val, hg _ href, star_zero]

/-- Centered scaling flow preserves pre-divisor trace-orbit boundedness. -/
theorem meyerTraceOrbitBounded_centeredFlow_iff (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    MeyerTraceOrbitBounded (deningerMeyerStrongLogCenteredFlow c g) ↔
      MeyerTraceOrbitBounded g := by
  simp only [meyerTraceOrbitBounded_iff_offLine_values_zero, meyerCenteredSourceFlow_mellin,
    mul_eq_zero, Complex.exp_ne_zero, false_or]

/-- Right convolution with any source preserves `MeyerTraceOrbitBounded`: the blind carrier
is a right convolution ideal of `DeningerMeyerStrongLogTarget`. -/
theorem meyerTraceOrbitBounded_convolution_right {g : DeningerMeyerStrongLogTarget}
    (hg : MeyerTraceOrbitBounded g) (h : DeningerMeyerStrongLogTarget) :
    MeyerTraceOrbitBounded (deningerMeyerSourceConvolution g h) := by
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero] at hg ⊢
  intro rho hr
  rw [deningerMeyerSourceConvolution_mellin, hg rho hr, zero_mul]

/-- Left convolution with any source also preserves `MeyerTraceOrbitBounded`: the blind carrier
is a two-sided convolution ideal of `DeningerMeyerStrongLogTarget`. -/
theorem meyerTraceOrbitBounded_convolution_left (g : DeningerMeyerStrongLogTarget)
    {h : DeningerMeyerStrongLogTarget} (hh : MeyerTraceOrbitBounded h) :
    MeyerTraceOrbitBounded (deningerMeyerSourceConvolution g h) := by
  rw [deningerMeyerSourceConvolution_comm]
  exact meyerTraceOrbitBounded_convolution_right hh g

/-- Every genuine Poisson boundary lies in the pre-divisor blind ideal. -/
theorem meyerTraceOrbitBounded_boundary (f : DeningerMeyerCap) :
    MeyerTraceOrbitBounded (deningerMeyerStrongLogSumLM f) := by
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
  intro rho _
  exact (meyerSource_boundary_iff_jets_zero (deningerMeyerStrongLogSumLM f)).mp
    ⟨f, rfl⟩ rho ⟨0, xiSupportMultiplicity_pos rho⟩

/-- Every local jet at every critical Xi zero—including lower jets at multiple critical
zeros—lies in the pre-divisor blind ideal. -/
theorem meyerSingleJetSource_traceOrbitBounded_of_critical (rho : XiDivisorSupport)
    (hr : (rho : ℂ).re = 1 / 2) (j : DeningerArithmeticJetIndex rho) :
    MeyerTraceOrbitBounded (meyerSingleJetSource rho j) := by
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
  intro sigma hsigma
  have hne : sigma ≠ rho := fun he => hsigma (he ▸ hr)
  have hj := meyerSingleJetSource_jet rho j sigma ⟨0, xiSupportMultiplicity_pos sigma⟩
  rw [if_neg (fun h => hne h.1)] at hj
  exact hj

/-- Every critical point source lies in the blind ideal, regardless of critical multiplicity. -/
theorem meyerPointSource_traceOrbitBounded_of_critical (rho : XiDivisorSupport)
    (hr : (rho : ℂ).re = 1 / 2) :
    MeyerTraceOrbitBounded (meyerPointSource rho) :=
  meyerSingleJetSource_traceOrbitBounded_of_critical rho hr _

/-- On the pre-divisor blind ideal, the diagonal source trace equals the positive critical
square energy and is unconditionally nonnegative. -/
theorem meyerSourceTrace_self_eq_criticalSquareEnergy {g : DeningerMeyerStrongLogTarget}
    (hg : MeyerTraceOrbitBounded g) :
    meyerSourceTrace g g = meyerCriticalSquareEnergy g :=
  meyerSourceTrace_eq_critical_of_offLine_zero
    ((meyerTraceOrbitBounded_iff_offLine_values_zero g).mp hg) g

theorem meyerTraceOrbitBounded_trace_nonneg {g : DeningerMeyerStrongLogTarget}
    (hg : MeyerTraceOrbitBounded g) :
    0 ≤ meyerSourceTrace g g := by
  rw [meyerSourceTrace_self_eq_criticalSquareEnergy hg]
  exact meyerCriticalSquareEnergy_nonneg g

/-- The pre-divisor blind ideal exhausts the whole Meyer source space if and only if RH holds,
with no critical-simplicity side condition. -/
theorem meyerTraceBoundedIdeal_eq_top_iff :
    meyerTraceBoundedIdeal = ⊤ ↔ RiemannHypothesis := by
  constructor
  · intro htop
    rw [rh_iff_xi_ne_zero_right]
    intro z hz hzero
    let rho : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
    have hoff : (rho : ℂ).re ≠ 1 / 2 := ne_of_gt (mem_rightHalf.mp hz)
    have hmem : meyerPointSource rho ∈ meyerTraceBoundedIdeal := by
      rw [htop]
      exact Submodule.mem_top
    have hv := (meyerTraceOrbitBounded_iff_offLine_values_zero _).mp hmem rho hoff
    rw [meyerPointSource_values, if_pos rfl] at hv
    exact one_ne_zero hv
  · intro hRH
    apply top_unique
    intro g _
    change MeyerTraceOrbitBounded g
    rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
    intro rho hoff
    exact False.elim (hoff (xi_divisor_support_re_eq_half_of_rh hRH rho))

/-! ### Unconditional intersection geometry on the blind Meyer surface -/

/-- Scaling cycles whose source component lies in the pre-divisor blind ideal. -/
def meyerTraceBoundedCycleSubmodule : Submodule ℝ MeyerScalingCycle where
  carrier := {x | MeyerTraceOrbitBounded x.2.2}
  zero_mem' := meyerTraceBoundedIdeal.zero_mem
  add_mem' := fun _ _ hx hy => meyerTraceBoundedIdeal.add_mem hx hy
  smul_mem' a _ hx := meyerTraceBoundedIdeal.smul_mem (a : ℂ) hx

private theorem traceBounded_H : meyerScalingSurface.H ∈ meyerTraceBoundedCycleSubmodule :=
  meyerTraceBoundedIdeal.zero_mem

private theorem traceBounded_V : meyerScalingSurface.V ∈ meyerTraceBoundedCycleSubmodule :=
  meyerTraceBoundedIdeal.zero_mem

/-- Restriction of the genuine Meyer scaling surface to the pre-divisor blind ideal. -/
def meyerTraceBoundedSurface : PolarSurface meyerTraceBoundedCycleSubmodule :=
  meyerScalingSurface.restrict meyerTraceBoundedCycleSubmodule traceBounded_H traceBounded_V

theorem meyerTraceBoundedSurface_defect (x y : meyerTraceBoundedCycleSubmodule) :
    meyerTraceBoundedSurface.defect x y = meyerSourceTrace x.1.2.2 y.1.2.2 :=
  meyerScalingSurface_defect x.1 y.1

/-- The restricted blind Meyer surface satisfies the Hodge index theorem unconditionally,
without assuming simplicity of critical zeros. -/
theorem meyerTraceBoundedSurface_hodgeIndex : meyerTraceBoundedSurface.HodgeIndex := by
  apply meyerTraceBoundedSurface.hodgeIndex_iff_defect_nonneg.mpr
  intro x
  rw [meyerTraceBoundedSurface_defect]
  exact meyerTraceOrbitBounded_trace_nonneg x.2

/-- The genuine cohomological degree cone restricted to the blind Meyer surface. -/
def meyerTraceBoundedDegreeCone : Set meyerTraceBoundedCycleSubmodule :=
  {x | x.1 ∈ meyerDegreeSourceCone}

theorem meyerTraceBoundedDegreeCone_eq_positiveCone :
    meyerTraceBoundedDegreeCone = meyerTraceBoundedSurface.positiveCone := by
  unfold meyerTraceBoundedDegreeCone
  rw [meyerDegreeSourceCone_eq_positiveCone]
  rfl

/-- Riemann–Roch, Bézout, ampleness, and additive closure all hold unconditionally on the
blind Meyer surface without any critical-simplicity hypothesis. -/
theorem meyerTraceBoundedDegreeCone_riemannRoch :
    meyerTraceBoundedSurface.RiemannRochAxiom meyerTraceBoundedDegreeCone := by
  rw [meyerTraceBoundedDegreeCone_eq_positiveCone]
  exact meyerTraceBoundedSurface.positiveCone_riemannRoch

theorem meyerTraceBoundedDegreeCone_bezout :
    meyerTraceBoundedSurface.BezoutAxiom meyerTraceBoundedDegreeCone := by
  rw [meyerTraceBoundedDegreeCone_eq_positiveCone]
  exact meyerTraceBoundedSurface.positiveCone_bezout meyerTraceBoundedSurface_hodgeIndex

theorem meyerTraceBoundedDegreeCone_ample :
    meyerTraceBoundedSurface.AmpleAxiom meyerTraceBoundedDegreeCone := by
  rw [meyerTraceBoundedDegreeCone_eq_positiveCone]
  exact meyerTraceBoundedSurface.positiveCone_ample_iff_hodgeIndex.mpr
    meyerTraceBoundedSurface_hodgeIndex

theorem meyerTraceBoundedDegreeCone_add_closed :
    ∀ x ∈ meyerTraceBoundedDegreeCone, ∀ y ∈ meyerTraceBoundedDegreeCone,
      x + y ∈ meyerTraceBoundedDegreeCone := by
  rw [meyerTraceBoundedDegreeCone_eq_positiveCone]
  exact meyerTraceBoundedSurface.positiveCone_add_closed_iff_hodgeIndex.mpr
    meyerTraceBoundedSurface_hodgeIndex

theorem meyerTraceBoundedCycleSubmodule_eq_top_iff :
    meyerTraceBoundedCycleSubmodule = ⊤ ↔ RiemannHypothesis := by
  rw [← meyerTraceBoundedIdeal_eq_top_iff]
  constructor
  · intro htop
    apply top_unique
    intro g _
    have hg : (0, 0, g) ∈ meyerTraceBoundedCycleSubmodule := by
      rw [htop]
      exact Submodule.mem_top
    exact hg
  · intro htop
    apply top_unique
    intro x _
    change x.2.2 ∈ meyerTraceBoundedIdeal
    rw [htop]
    exact Submodule.mem_top

/-! ### Unique maximality among sharp-stable positive ideals -/

/-- A complex subspace of the Meyer source space is a sharp-stable positive convolution ideal
when it is closed under arithmetic sharp, closed under right source convolution, and has
nonnegative diagonal source trace on every member. -/
def MeyerSharpPositiveIdeal (I : Submodule ℂ DeningerMeyerStrongLogTarget) : Prop :=
  (∀ g ∈ I, deningerMeyerSourceSharp g ∈ I) ∧
  (∀ g ∈ I, ∀ h : DeningerMeyerStrongLogTarget, deningerMeyerSourceConvolution g h ∈ I) ∧
  (∀ g ∈ I, 0 ≤ meyerSourceTrace g g)

theorem meyerTraceBoundedIdeal_sharpPositiveIdeal :
    MeyerSharpPositiveIdeal meyerTraceBoundedIdeal :=
  ⟨fun _ hg => meyerTraceOrbitBounded_sharp hg,
   fun _ hg h => meyerTraceOrbitBounded_convolution_right hg h,
   fun _ hg => meyerTraceOrbitBounded_trace_nonneg hg⟩

private theorem meyerSourceTrace_self_eq_of_values_eq {a b : DeningerMeyerStrongLogTarget}
    (hab : ∀ sigma : XiDivisorSupport,
      deningerMeyerStrongLogMellin a (sigma : ℂ) =
        deningerMeyerStrongLogMellin b (sigma : ℂ)) :
    meyerSourceTrace a a = meyerSourceTrace b b := by
  have hdiff : ∀ k : DeningerMeyerStrongLogTarget, meyerSourceTrace (a - b) k = 0 := by
    apply (meyerSourceTrace_radical_iff_values_zero (a - b)).mpr
    intro sigma
    change deningerMeyerStrongLogMellinLM (sigma : ℂ) (a - b) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (hab sigma)
  have hsub_left (x y z : DeningerMeyerStrongLogTarget) :
      meyerSourceTrace (x - y) z = meyerSourceTrace x z - meyerSourceTrace y z := by
    have he := meyerScalingSurface.defect_sub_left (0, 0, x) (0, 0, y) (0, 0, z)
    simpa only [meyerScalingSurface_defect] using he
  have h1 : meyerSourceTrace a a = meyerSourceTrace b a :=
    sub_eq_zero.mp (by rw [← hsub_left]; exact hdiff a)
  have h2 : meyerSourceTrace a b = meyerSourceTrace b b :=
    sub_eq_zero.mp (by rw [← hsub_left]; exact hdiff b)
  rw [h1, meyerSourceTrace_comm b a, h2]

/-- Every sharp-stable convolution ideal with nonnegative diagonal source trace is contained
in `meyerTraceBoundedIdeal`. Single-channel additive positivity on an ideal cannot escape
off-line blindness. -/
theorem le_meyerTraceBoundedIdeal_of_sharpPositiveIdeal
    {I : Submodule ℂ DeningerMeyerStrongLogTarget} (hI : MeyerSharpPositiveIdeal I) :
    I ≤ meyerTraceBoundedIdeal := by
  rcases hI with ⟨hsharp, hmul, hpos⟩
  intro g hg
  change MeyerTraceOrbitBounded g
  rw [meyerTraceOrbitBounded_iff_offLine_values_zero]
  intro rho hoff
  by_contra hz
  let z : ℂ := deningerMeyerStrongLogMellin g (rho : ℂ)
  let r : ℝ := Complex.normSq z
  have hr_pos : 0 < r := Complex.normSq_pos.mpr hz
  let u : DeningerMeyerStrongLogTarget :=
    (conj z) • deningerMeyerSourceConvolution g (meyerPointSource rho)
  have hu : u ∈ I := I.smul_mem (conj z) (hmul g hg (meyerPointSource rho))
  let w : DeningerMeyerStrongLogTarget := u - deningerMeyerSourceSharp u
  have hw : w ∈ I := I.sub_mem hu (hsharp u hu)
  let p : DeningerMeyerStrongLogTarget :=
    (r : ℂ) • (meyerPointSource rho - meyerPointSource (meyerLineReflect rho))
  have hval_u (sigma : XiDivisorSupport) :
      deningerMeyerStrongLogMellin u (sigma : ℂ) =
        (r : ℂ) * deningerMeyerStrongLogMellin (meyerPointSource rho) (sigma : ℂ) := by
    change deningerMeyerStrongLogMellinLM (sigma : ℂ)
      ((conj z) • deningerMeyerSourceConvolution g (meyerPointSource rho)) = _
    rw [map_smul, smul_eq_mul]
    change conj z * deningerMeyerStrongLogMellin
      (deningerMeyerSourceConvolution g (meyerPointSource rho)) (sigma : ℂ) = _
    rw [deningerMeyerSourceConvolution_mellin, meyerPointSource_values]
    by_cases hs : sigma = rho
    · subst hs
      simp only [↓reduceIte, mul_one]
      dsimp only [r, z]
      rw [mul_comm, Complex.mul_conj]
    · simp only [hs, ↓reduceIte, mul_zero]
  have hval_w (sigma : XiDivisorSupport) :
      deningerMeyerStrongLogMellin w (sigma : ℂ) =
        deningerMeyerStrongLogMellin p (sigma : ℂ) := by
    change deningerMeyerStrongLogMellinLM (sigma : ℂ) (u - deningerMeyerSourceSharp u) =
      deningerMeyerStrongLogMellinLM (sigma : ℂ)
        ((r : ℂ) • (meyerPointSource rho - meyerPointSource (meyerLineReflect rho)))
    rw [map_sub, map_smul, map_sub, smul_eq_mul]
    change deningerMeyerStrongLogMellin u (sigma : ℂ) -
      deningerMeyerStrongLogMellin (deningerMeyerSourceSharp u) (sigma : ℂ) =
      (r : ℂ) * (deningerMeyerStrongLogMellin (meyerPointSource rho) (sigma : ℂ) -
        deningerMeyerStrongLogMellin (meyerPointSource (meyerLineReflect rho)) (sigma : ℂ))
    rw [hval_u sigma, deningerMeyerSourceSharp_mellin, ← meyerLineReflect_val,
      hval_u (meyerLineReflect sigma)]
    have href_iff : meyerLineReflect sigma = rho ↔ sigma = meyerLineReflect rho := by
      constructor
      · intro h
        rw [← h, meyerLineReflect_sq]
      · intro h
        rw [h, meyerLineReflect_sq]
    rw [meyerPointSource_values, meyerPointSource_values, meyerPointSource_values]
    simp only [href_iff]
    by_cases hs : sigma = meyerLineReflect rho
    · simp only [hs, ↓reduceIte, mul_one, star_def, Complex.conj_ofReal, mul_sub]
    · simp only [hs, ↓reduceIte, mul_zero, star_zero, mul_sub]
  have htrace_eq : meyerSourceTrace w w = meyerSourceTrace p p :=
    meyerSourceTrace_self_eq_of_values_eq hval_w
  have hp_smul : p = r • (meyerPointSource rho - meyerPointSource (meyerLineReflect rho)) := rfl
  have hp_trace : meyerSourceTrace p p =
      r ^ 2 * meyerSourceTrace
        (meyerPointSource rho - meyerPointSource (meyerLineReflect rho))
        (meyerPointSource rho - meyerPointSource (meyerLineReflect rho)) := by
    let q0 := meyerPointSource rho - meyerPointSource (meyerLineReflect rho)
    have hsmul1 := meyerScalingSurface.defect_smul_left r (0, 0, q0) (0, 0, p)
    have hsmul2 := meyerScalingSurface.defect_smul_right r (0, 0, q0) (0, 0, q0)
    simp only [meyerScalingSurface_defect] at hsmul1 hsmul2
    change meyerSourceTrace (r • q0) p = r * meyerSourceTrace q0 p at hsmul1
    change meyerSourceTrace q0 (r • q0) = r * meyerSourceTrace q0 q0 at hsmul2
    rw [hp_smul]
    change meyerSourceTrace (r • q0) (r • q0) = r ^ 2 * meyerSourceTrace q0 q0
    rw [← hp_smul, hsmul1, hp_smul, hsmul2]
    ring
  have hneg := meyerOffLinePacket_trace_neg rho hoff
  have hw_neg : meyerSourceTrace w w < 0 := by
    rw [htrace_eq, hp_trace]
    exact mul_neg_of_pos_of_neg (pow_pos hr_pos 2) hneg
  exact (not_lt_of_ge (hpos w hw)) hw_neg

/-- `meyerTraceBoundedIdeal` is the unique greatest element among all sharp-stable positive
convolution ideals of the genuine Meyer source space. -/
theorem isGreatest_meyerSharpPositiveIdeal :
    IsGreatest {I : Submodule ℂ DeningerMeyerStrongLogTarget | MeyerSharpPositiveIdeal I}
      meyerTraceBoundedIdeal :=
  ⟨meyerTraceBoundedIdeal_sharpPositiveIdeal,
   fun _ hI => le_meyerTraceBoundedIdeal_of_sharpPositiveIdeal hI⟩

/-- On any functional-equation-symmetric tempered configuration, every scale-shift-invariant
subspace of smooth compact real tests with nonnegative Weil quadratic form consists solely
of tests blind to off-line zeros. -/
theorem blindOffLine_of_scaleShift_subspace_weil_nonneg
    (Z : ZeroConfig) (hZ : SquareRootThreshold.TemperedConfig Z) (hFE : FESymmetric Z)
    (U : Submodule ℝ (ℝ → ℝ)) (hU : U ≤ realTests)
    (hshift : ∀ (t : ℝ) {f : ℝ → ℝ}, f ∈ U → scaleShift t f ∈ U)
    (hpos : ∀ f ∈ U, 0 ≤ (Z.W (cx f) (cx f)).re) :
    ∀ f ∈ U, ArithmeticOrientationGeometry.BlindOffLine Z f := by
  intro f hf
  let x : ScalingCycle := (0, 0, ⟨f, hU hf⟩)
  apply ((ArithmeticOrientationGeometry.orientation_tfae Z hZ hFE x).out 1 2).mp
  rw [ScalingDatum.orbitHodgeIndex_iff_defect_nonneg]
  intro S c
  change 0 ≤ (configSurface Z hZ).defect _ _
  rw [configSurface_defect, configWeil, ArithmeticOrientationGeometry.orbitComb_test Z hZ x S c]
  exact hpos _ (U.sum_mem fun t _ => U.smul_mem (c t) (hshift t hf))

/-- Specialization to `ζ`: every scale-shift-invariant Weil-nonnegative subspace of compact
smooth real tests is trapped inside `BlindOffLine zetaZeroConfig`. -/
theorem zeta_blindOffLine_of_scaleShift_subspace_weil_nonneg
    (U : Submodule ℝ (ℝ → ℝ)) (hU : U ≤ realTests)
    (hshift : ∀ (t : ℝ) {f : ℝ → ℝ}, f ∈ U → scaleShift t f ∈ U)
    (hpos : ∀ f ∈ U, 0 ≤ (zetaZeroConfig.W (cx f) (cx f)).re) :
    ∀ f ∈ U, ArithmeticOrientationGeometry.BlindOffLine zetaZeroConfig f :=
  blindOffLine_of_scaleShift_subspace_weil_nonneg zetaZeroConfig
    SquareRootThreshold.temperedConfig_zetaZeroConfig fesSymmetric_zetaZeroConfig U hU hshift hpos

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
