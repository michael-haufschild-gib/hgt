import GaloisForLFunctions.RHTower.CCM.CCMRectangularObservablePoleTomography
import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Multiplicity-exact divisor tomography from one observable rectangular Weil tail

The simple-pole support of the fixed-window observable tail already locates every Xi zero to the
right of the critical line.  This module computes the pole weights.  At the shifted pole of a zero
of analytic multiplicity `m`, the trailing coefficient is exactly twice `m` times the nonvanishing
rectangular window coefficient.  Hence one observable tail recovers the right Xi divisor with its
full analytic multiplicities, not merely its support.
-/

open Complex Filter Function Set
open scoped Topology

namespace RHTower

noncomputable section


/-- The shifted zeta factor has normalized residue one at its translated pole. -/
lemma tendsto_shiftedRiemannZeta_residue_one (q : XiRightZeroCopy) :
    Tendsto
      (fun s : ℂ => (s - xiRightShiftedPole q) *
        riemannZeta (s - xiRightCenteredZero q))
      (𝓝[≠] (xiRightShiftedPole q)) (𝓝 1) := by
  have hshift : Tendsto
      (fun s : ℂ => s - xiRightCenteredZero q)
      (𝓝[≠] (xiRightShiftedPole q)) (𝓝[≠] 1) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hc : ContinuousAt (fun s : ℂ => s - xiRightCenteredZero q)
          (xiRightShiftedPole q) := continuousAt_id.sub_const _
      have hle : 𝓝[≠] (xiRightShiftedPole q) ≤
          𝓝 (xiRightShiftedPole q) := inf_le_left
      simpa only [xiRightShiftedPole_sub_centeredZero] using
        hc.tendsto.mono_left hle
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s - xiRightCenteredZero q ≠ 1
      intro heq
      have hsp : s ≠ xiRightShiftedPole q := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
      exact hsp (by rw [xiRightShiftedPole]; linear_combination heq)
  have hres := riemannZeta_residue_one.comp hshift
  convert hres using 1
  funext s
  rw [Function.comp_apply, xiRightShiftedPole]
  ring

/-- One cancelled shifted-zeta quotient has unit trailing coefficient. -/
lemma meromorphicOrderAt_cancelledTerm_div_shiftedXi
    (q : XiRightZeroCopy) :
    meromorphicOrderAt
      (fun s : ℂ => xiShiftedZetaCancelledTerm q s /
        xi (s - 1 / 2))
      (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ) := by
  have hnum : AnalyticAt ℂ (xiShiftedZetaCancelledTerm q)
      (xiRightShiftedPole q) :=
    differentiable_xiShiftedZetaCancelledTerm q |>.analyticAt _
  have hden : AnalyticAt ℂ (fun s : ℂ => xi (s - 1 / 2))
      (xiRightShiftedPole q) :=
    (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_id.sub analyticAt_const)
  rw [fun_meromorphicOrderAt_div hnum.meromorphicAt hden.meromorphicAt,
    hnum.meromorphicOrderAt_eq, hden.meromorphicOrderAt_eq,
    xiShiftedZetaCancelledTerm_order, xi_shifted_half_order]
  rw [ENat.map_coe, ENat.map_coe]
  have hm := xiRightMultiplicity_pos q
  exact_mod_cast (show
    ((xiRightMultiplicity q - 1 : ℕ) : ℤ) - xiRightMultiplicity q = -1 by
      omega)

/-- One cancelled shifted-zeta quotient has unit trailing coefficient. -/
lemma meromorphicTrailingCoeffAt_cancelledTerm_div_shiftedXi
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt
      (fun s : ℂ => xiShiftedZetaCancelledTerm q s /
        xi (s - 1 / 2))
      (xiRightShiftedPole q) = 1 := by
  let p := xiRightShiftedPole q
  let f : ℂ → ℂ := fun s => xiShiftedZetaCancelledTerm q s /
    xi (s - 1 / 2)
  have hnum : AnalyticAt ℂ (xiShiftedZetaCancelledTerm q) p :=
    differentiable_xiShiftedZetaCancelledTerm q |>.analyticAt p
  have hden : AnalyticAt ℂ (fun s : ℂ => xi (s - 1 / 2)) p :=
    (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_id.sub analyticAt_const)
  have hf : MeromorphicAt f p := hnum.meromorphicAt.div hden.meromorphicAt
  have horder : meromorphicOrderAt f p = ((-1 : ℤ) : WithTop ℤ) := by
    simpa only [f, p] using
      meromorphicOrderAt_cancelledTerm_div_shiftedXi q
  have htrail := hf.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [horder] at htrail
  simp only [WithTop.untop₀_coe, neg_neg, zpow_one, smul_eq_mul] at htrail
  have hres : Tendsto (fun s : ℂ => (s - p) * f s)
      (𝓝[≠] p) (𝓝 1) := by
    obtain ⟨R, hR, h, hhan, hh0, hfact⟩ := xi_peel_ball (q.1.1 : ℂ)
    have hpball : p - 1 / 2 ∈ Metric.ball (q.1.1 : ℂ) R := by
      dsimp only [p]
      rw [xiRightShiftedPole_sub_half]
      exact Metric.mem_ball_self hR
    have hevball : ∀ᶠ s : ℂ in 𝓝[≠] p,
        s - 1 / 2 ∈ Metric.ball (q.1.1 : ℂ) R :=
      ((continuousAt_id.sub_const (1 / 2 : ℂ)).eventually
        (Metric.isOpen_ball.mem_nhds hpball)).filter_mono inf_le_left
    apply Tendsto.congr' _ (tendsto_shiftedRiemannZeta_residue_one q)
    filter_upwards [self_mem_nhdsWithin, hevball] with s hs hsball
    dsimp only [f, p]
    have hxi : xi (s - 1 / 2) ≠ 0 := by
      intro hzero
      rw [hfact (s - 1 / 2) hsball] at hzero
      have hcoord : (s - 1 / 2) - (q.1.1 : ℂ) = s - p := by
        dsimp only [p]
        rw [xiRightShiftedPole, xiRightCenteredZero_eq_support_sub_half]
        ring
      rw [hcoord] at hzero
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hs))
        (hh0 _ hsball) hzero
    rw [xiShiftedZetaCancelledTerm, Function.update_of_ne hs,
      mul_div_cancel_left₀ _ hxi]
  exact tendsto_nhds_unique htrail hres

/-- The canonical right-divisor continuation has residue equal to the zero multiplicity times the
nonvanishing rectangular window weight. -/
theorem meromorphicTrailingCoeffAt_xiRectangularRightDirichletContinuation
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt (xiRectangularRightDirichletContinuation L)
        (xiRightShiftedPole q) =
      (xiRightMultiplicity q : ℂ) * xiRectangularRightCoefficient L q := by
  let p := xiRightShiftedPole q
  let den : ℂ → ℂ := fun s => xi (s - 1 / 2)
  let single : ℂ → ℂ := fun s => xiShiftedZetaCancelledTerm q s / den s
  let main : ℂ → ℂ := fun s =>
    ((xiRightMultiplicity q : ℂ) * xiRectangularRightCoefficient L q) * single s
  let other : ℂ → ℂ := fun s => xiRectangularOtherSupportSeries L q s / den s
  have hpU : p ∈ {s : ℂ | 1 < s.re} := by
    change 1 < p.re
    dsimp only [p]
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hden : AnalyticAt ℂ den p := by
    dsimp only [den]
    exact (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_id.sub analyticAt_const)
  have hterm : AnalyticAt ℂ (xiShiftedZetaCancelledTerm q) p :=
    differentiable_xiShiftedZetaCancelledTerm q |>.analyticAt _
  have hsingle : MeromorphicAt single p := by
    dsimp only [single]
    exact hterm.meromorphicAt.div hden.meromorphicAt
  have hsingleOrder : meromorphicOrderAt single p =
      ((-1 : ℤ) : WithTop ℤ) := by
    simpa only [single, den, p] using
      meromorphicOrderAt_cancelledTerm_div_shiftedXi q
  have hsingleTrail : meromorphicTrailingCoeffAt single p = 1 := by
    simpa only [single, den, p] using
      meromorphicTrailingCoeffAt_cancelledTerm_div_shiftedXi q
  have hotherAnalytic : AnalyticAt ℂ (xiRectangularOtherSupportSeries L q) p := by
    let U : Set ℂ := {s : ℂ | 1 < s.re}
    have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hnormal : SummableLocallyUniformlyOn
        (fun r : XiRightOtherSupport q =>
          xiRectangularCancelledTerm L r.1) U :=
      SummableLocallyUniformlyOn.comp_injective_local hU
        (summableLocallyUniformlyOn_xiRectangularCancelledTerm_rightOne (L := L))
        Subtype.val_injective
    exact (hnormal.differentiableOn hU (fun r s hs =>
      (analyticAt_const.mul
        (differentiable_xiShiftedZetaCancelledTerm r.1 |>.analyticAt s)).differentiableAt)
      |>.analyticOnNhd hU) p hpU
  have hother : MeromorphicAt other p := by
    dsimp only [other]
    exact hotherAnalytic.meromorphicAt.div hden.meromorphicAt
  have hdenOrder : meromorphicOrderAt den p =
      (((xiRightMultiplicity q : ℕ) : ℤ) : WithTop ℤ) := by
    dsimp only [den, p]
    rw [hden.meromorphicOrderAt_eq, xi_shifted_half_order, ENat.map_coe]
  have hotherOrderNonneg : (0 : WithTop ℤ) ≤ meromorphicOrderAt other p := by
    rw [show meromorphicOrderAt other p =
        meromorphicOrderAt (xiRectangularOtherSupportSeries L q) p -
          meromorphicOrderAt den p by
      dsimp only [other]
      exact fun_meromorphicOrderAt_div hotherAnalytic.meromorphicAt hden.meromorphicAt]
    rw [hotherAnalytic.meromorphicOrderAt_eq, hdenOrder]
    have hge := xiRectangularOtherSupportSeries_order_ge L q
    generalize hord : analyticOrderAt (xiRectangularOtherSupportSeries L q) p = o at hge ⊢
    induction o using ENat.recTopCoe with
    | top => simp
    | coe k =>
        rw [ENat.map_coe]
        have hmk : xiRightMultiplicity q ≤ k := by
          exact_mod_cast hge
        exact_mod_cast (show (0 : ℤ) ≤ (k : ℤ) - xiRightMultiplicity q by
          omega)
  have hmain : MeromorphicAt main p := by
    dsimp only [main]
    exact analyticAt_const.meromorphicAt.mul hsingle
  have hmainOrder : meromorphicOrderAt main p =
      ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [main]
    rw [fun_meromorphicOrderAt_mul analyticAt_const.meromorphicAt hsingle,
      meromorphicOrderAt_const, hsingleOrder]
    have hconst : (xiRightMultiplicity q : ℂ) *
        xiRectangularRightCoefficient L q ≠ 0 :=
      mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt (xiRightMultiplicity_pos q)))
        (xiRectangularRightCoefficient_ne_zero hL q)
    rw [if_neg hconst]
    norm_num
  have hlt : meromorphicOrderAt main p < meromorphicOrderAt other p :=
    hmainOrder.symm ▸ (show ((-1 : ℤ) : WithTop ℤ) <
      meromorphicOrderAt other p by
        exact lt_of_lt_of_le (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
          hotherOrderNonneg)
  have heq : xiRectangularRightDirichletContinuation L =ᶠ[𝓝[≠] p]
      fun s => main s + other s := by
    have hsplit := xiRectangularCancelledSeries_eventuallyEq_same_add_other L q
    have hle : 𝓝[≠] p ≤ 𝓝 p := inf_le_left
    have hsplit' := hsplit.filter_mono hle
    filter_upwards [hsplit'] with s hs
    rw [xiRectangularRightDirichletContinuation, hs,
      xiRectangularSameSupportSeries_eq_card_mul,
      card_xiRightSupportFiber]
    dsimp only [main, single, other, den]
    simp only [Pi.add_apply, xiRectangularCancelledTerm, div_eq_mul_inv]
    ring
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE heq,
    hother.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt hlt]
  dsimp only [main]
  rw [analyticAt_const.meromorphicAt.meromorphicTrailingCoeffAt_fun_mul hsingle,
    meromorphicTrailingCoeffAt_const, hsingleTrail, mul_one]

/-- **Trailing coefficient of a polar-plus-analytic continuation.**  If a function agrees with
`2 · xiRectangularRightDirichletContinuation L + correction` and the correction is analytic at the
shifted pole of `q`, its meromorphic trailing coefficient there is
`2 · multiplicity q · xiRectangularRightCoefficient L q`.  The polar term has meromorphic order
`−1`, strictly below the nonnegative order of an analytic function, so the sum inherits the polar
trailing coefficient. -/
theorem meromorphicTrailingCoeffAt_of_rightDirichlet_add_analytic
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) {F correction : ℂ → ℂ}
    (hcorrection : AnalyticAt ℂ correction (xiRightShiftedPole q))
    (heq : F = fun s => 2 * xiRectangularRightDirichletContinuation L s + correction s) :
    meromorphicTrailingCoeffAt F (xiRightShiftedPole q) =
      2 * (xiRightMultiplicity q : ℂ) * xiRectangularRightCoefficient L q := by
  let p := xiRightShiftedPole q
  let polar : ℂ → ℂ := fun s =>
    2 * xiRectangularRightDirichletContinuation L s
  have hp : 1 < p.re := by
    dsimp only [p]
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hbase : MeromorphicAt
      (xiRectangularRightDirichletContinuation L) p :=
    meromorphicOn_xiRectangularRightDirichletContinuation_rightOne L p hp
  have hpolarOrder : meromorphicOrderAt polar p =
      ((-1 : ℤ) : WithTop ℤ) := by
    dsimp only [polar, p]
    rw [fun_meromorphicOrderAt_mul analyticAt_const.meromorphicAt hbase,
      meromorphicOrderAt_const, if_neg (by norm_num : (2 : ℂ) ≠ 0),
      meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one hL q]
    norm_num
  have hlt : meromorphicOrderAt polar p <
      meromorphicOrderAt correction p := by
    rw [hpolarOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorrection.meromorphicOrderAt_nonneg
  rw [heq,
    hcorrection.meromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt hlt]
  rw [analyticAt_const.meromorphicAt.meromorphicTrailingCoeffAt_fun_mul hbase,
    meromorphicTrailingCoeffAt_const,
    meromorphicTrailingCoeffAt_xiRectangularRightDirichletContinuation hL q]
  ring


/-- The actual observable tail continuation has the same multiplicity-exact residue, with the
factor two coming from the functional-equation fold. -/
theorem meromorphicTrailingCoeffAt_xiRectangularWeilTailContinuation
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L N)
        (xiRightShiftedPole q) =
      2 * (xiRightMultiplicity q : ℂ) * xiRectangularRightCoefficient L q := by
  refine meromorphicTrailingCoeffAt_of_rightDirichlet_add_analytic hL q
    (correction := fun s => -xiRectangularLandauPrefixSeries L 0 N s +
      LSeries (xiRectangularWeilRemainderCoefficient L N) s) ?_ ?_
  · refine analyticAt_xiRectangularWeilTailCorrection hN ?_
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  · funext s
    simp only [xiRectangularWeilTailContinuation]
    ring

/-- Normalizing the observable residue by its nonzero rectangular weight recovers the exact
analytic multiplicity of the underlying right Xi zero. -/
theorem normalizedObservableResidue_eq_xiRightMultiplicity
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L N)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L q) =
      (xiRightMultiplicity q : ℂ) := by
  rw [meromorphicTrailingCoeffAt_xiRectangularWeilTailContinuation hL hN q]
  field_simp [xiRectangularRightCoefficient_ne_zero hL q]

/-- The normalized pole weight is intrinsic to the Xi support point.  It is independent of the
positive rectangular width, the admissible finite deletion, and the multiplicity copy used to
name that support point. -/
theorem normalizedObservableResidue_intrinsic
    {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    {N₁ N₂ : ℕ}
    (hN₁ : ∀ n : ℕ, N₁ ≤ n →
      1 ≤ n ∧ L₁ ≤ Real.log n / 2)
    (hN₂ : ∀ n : ℕ, N₂ ≤ n →
      1 ≤ n ∧ L₂ ≤ Real.log n / 2)
    {q r : XiRightZeroCopy} (hqr : q.1.1 = r.1.1) :
    meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L₁ N₁)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L₁ q) =
      meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L₂ N₂)
          (xiRightShiftedPole r) /
        (2 * xiRectangularRightCoefficient L₂ r) := by
  rw [normalizedObservableResidue_eq_xiRightMultiplicity hL₁ hN₁ q,
    normalizedObservableResidue_eq_xiRightMultiplicity hL₂ hN₂ r,
    xiRightMultiplicity_eq_of_support_eq hqr]

/-- For a fixed positive window, deleting different admissible finite prefixes changes only the
holomorphic part of the observable continuation: the complete weighted pole divisor is unchanged. -/
theorem meromorphicTrailingCoeffAt_xiRectangularWeilTailContinuation_cutoff_invariant
    {L : ℝ} (hL : 0 < L) {N₁ N₂ : ℕ}
    (hN₁ : ∀ n : ℕ, N₁ ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (hN₂ : ∀ n : ℕ, N₂ ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L N₁)
        (xiRightShiftedPole q) =
      meromorphicTrailingCoeffAt (xiRectangularWeilTailContinuation L N₂)
        (xiRightShiftedPole q) := by
  rw [meromorphicTrailingCoeffAt_xiRectangularWeilTailContinuation hL hN₁ q,
    meromorphicTrailingCoeffAt_xiRectangularWeilTailContinuation hL hN₂ q]

end

end RHTower
