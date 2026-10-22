import GaloisForLFunctions.RHTower.CCM.CCMRectangularObservableDivisorTomography

/-!
# Cutoff-free divisor tomography from the full rectangular Weil sequence

The tail cutoff used to prove boundedness is auxiliary.  The complete observable coefficient
differs from the right-divisor carrier by one globally defined sequence whose L-series is analytic
in `Re s > 1`.  This produces a cutoff-free meromorphic continuation of the full observable
sequence.  Its simple poles and normalized residues recover the complete right Xi divisor with
analytic multiplicity.
-/

open Complex Filter Function Set
open scoped Topology

namespace RHTower

noncomputable section

/-- Every fixed rectangular width admits a cutoff beyond which the logarithmic aperture contains
the window.  The cutoff is used only in the proof of summability. -/
theorem exists_xiRectangularAdmissibleCutoff (L : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2 := by
  have hlog : Tendsto (fun n : ℕ => Real.log n / 2) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 2)
  have hL : ∀ᶠ n : ℕ in atTop, L ≤ Real.log n / 2 :=
    hlog.eventually_ge_atTop L
  have h1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  exact eventually_atTop.1 (h1.and hL)

/-- The cutoff-free correction between the full observable Weil coefficient and its complete
right-divisor carrier. -/
def xiRectangularWeilFullRemainderCoefficient (L : ℝ) (n : ℕ) : ℂ :=
  xiRectangularWeilLogCoefficient L n -
    xiRectangularRightDirichletComplex L n

/-- The finite prefix by which the cutoff-free remainder differs from a tail remainder. -/
def xiRectangularWeilFullRemainderPrefixCoefficient
    (L : ℝ) (N n : ℕ) : ℂ :=
  if n < N then xiRectangularWeilFullRemainderCoefficient L n else 0

/-- The global remainder is a bounded tail remainder plus a finite prefix. -/
theorem xiRectangularWeilFullRemainderCoefficient_eq_tail_add_prefix
    (L : ℝ) (N n : ℕ) :
    xiRectangularWeilFullRemainderCoefficient L n =
      xiRectangularWeilRemainderCoefficient L N n +
        xiRectangularWeilFullRemainderPrefixCoefficient L N n := by
  by_cases hn : N ≤ n
  · rw [xiRectangularWeilFullRemainderCoefficient,
      xiRectangularWeilRemainderCoefficient,
      xiRectangularWeilTailCoefficient, if_pos hn,
      xiRectangularLandauPrefixCoefficient, if_neg (not_lt.mpr hn),
      xiRectangularWeilFullRemainderPrefixCoefficient,
      if_neg (not_lt.mpr hn)]
    ring
  · have hnlt : n < N := Nat.lt_of_not_ge hn
    rw [xiRectangularWeilFullRemainderCoefficient,
      xiRectangularWeilRemainderCoefficient,
      xiRectangularWeilTailCoefficient, if_neg hn,
      xiRectangularLandauPrefixCoefficient, if_pos hnlt,
      xiRectangularWeilFullRemainderPrefixCoefficient, if_pos hnlt]
    simp [xiRectangularWeilFullRemainderCoefficient]

/-- The auxiliary finite remainder prefix is L-series summable at every point. -/
theorem xiRectangularWeilFullRemainderPrefixCoefficient_LSeriesSummable
    (L : ℝ) (N : ℕ) (s : ℂ) :
    LSeriesSummable (xiRectangularWeilFullRemainderPrefixCoefficient L N) s := by
  apply summable_of_ne_finset_zero (s := Finset.range N)
  intro n hn
  have hNn : N ≤ n := by
    simpa only [Finset.mem_range, not_lt] using hn
  rcases n.eq_zero_or_pos with rfl | hnpos
  · exact LSeries.term_zero _ _
  · rw [LSeries.term_of_ne_zero hnpos.ne',
      xiRectangularWeilFullRemainderPrefixCoefficient,
      if_neg (not_lt.mpr hNn), zero_div]

/-- The cutoff-free correction L-series converges absolutely throughout `Re s > 1`. -/
theorem xiRectangularWeilFullRemainderCoefficient_LSeriesSummable
    (L : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (xiRectangularWeilFullRemainderCoefficient L) s := by
  obtain ⟨N, hN⟩ := exists_xiRectangularAdmissibleCutoff L
  have htail := xiRectangularWeilRemainderCoefficient_LSeriesSummable hN hs
  have hprefix :=
    xiRectangularWeilFullRemainderPrefixCoefficient_LSeriesSummable L N s
  have hcoeff : xiRectangularWeilFullRemainderCoefficient L =
      xiRectangularWeilRemainderCoefficient L N +
        xiRectangularWeilFullRemainderPrefixCoefficient L N := by
    funext n
    exact xiRectangularWeilFullRemainderCoefficient_eq_tail_add_prefix L N n
  rw [hcoeff]
  exact htail.add hprefix

/-- The cutoff-free correction has absolute-convergence abscissa at most one. -/
theorem abscissaOfAbsConv_xiRectangularWeilFullRemainderCoefficient_le_one
    (L : ℝ) :
    LSeries.abscissaOfAbsConv
        (xiRectangularWeilFullRemainderCoefficient L) ≤ (1 : ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact xiRectangularWeilFullRemainderCoefficient_LSeriesSummable L
    (by simpa only [ofReal_re] using hy)

/-- The cutoff-free correction L-series is analytic throughout `Re s > 1`. -/
theorem analyticAt_LSeries_xiRectangularWeilFullRemainderCoefficient
    (L : ℝ) {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ
      (LSeries (xiRectangularWeilFullRemainderCoefficient L)) s := by
  apply LSeries_analyticOnNhd _ s
  exact
    (abscissaOfAbsConv_xiRectangularWeilFullRemainderCoefficient_le_one L).trans_lt
      (by exact_mod_cast hs)

/-- Canonical cutoff-free meromorphic continuation of the ordinary L-series of the complete
observable logarithmic Weil sequence. -/
def xiRectangularWeilFullContinuation (L : ℝ) (s : ℂ) : ℂ :=
  2 * xiRectangularRightDirichletContinuation L s +
    LSeries (xiRectangularWeilFullRemainderCoefficient L) s

/-- On every initial half-plane of absolute convergence, the full observable L-series equals its
cutoff-free continuation. -/
theorem LSeries_xiRectangularWeilLogCoefficient_eq_fullContinuation
    (L : ℝ) {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hs : 1 + delta < s.re) :
    LSeries (xiRectangularWeilLogCoefficient L) s =
      xiRectangularWeilFullContinuation L s := by
  have hs1 : 1 < s.re := by linarith
  have hcarrier := xiRectangularRightDirichletComplex_LSeriesSummable
    L hupper hs
  have hrem :=
    xiRectangularWeilFullRemainderCoefficient_LSeriesSummable L hs1
  have hcoeff : xiRectangularWeilLogCoefficient L =
      (fun n => xiRectangularRightDirichletComplex L n) +
        xiRectangularWeilFullRemainderCoefficient L := by
    funext n
    simp only [Pi.add_apply, xiRectangularWeilFullRemainderCoefficient]
    ring
  rw [hcoeff, LSeries_add hcarrier hrem,
    LSeries_xiRectangularRightDirichletComplex_eq_continuation
      L hdelta0 hupper hs]
  rfl

/-- Every right Xi divisor point is a simple pole of the cutoff-free full continuation. -/
theorem meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    meromorphicOrderAt (xiRectangularWeilFullContinuation L)
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ) := by
  let p := xiRightShiftedPole q
  have hp : 1 < p.re := by
    dsimp only [p]
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hbase : MeromorphicAt
      (xiRectangularRightDirichletContinuation L) p :=
    meromorphicOn_xiRectangularRightDirichletContinuation_rightOne L p hp
  have hmainOrder :
      meromorphicOrderAt
          (fun z => 2 * xiRectangularRightDirichletContinuation L z) p =
        ((-1 : ℤ) : WithTop ℤ) := by
    rw [fun_meromorphicOrderAt_mul analyticAt_const.meromorphicAt hbase,
      meromorphicOrderAt_const p (2 : ℂ),
      meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one
        hL q]
    norm_num
  have hcorr :=
    analyticAt_LSeries_xiRectangularWeilFullRemainderCoefficient L hp
  have hlt :
      meromorphicOrderAt
          (fun z => 2 * xiRectangularRightDirichletContinuation L z) p <
        meromorphicOrderAt
          (LSeries (xiRectangularWeilFullRemainderCoefficient L)) p := by
    rw [hmainOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorr.meromorphicOrderAt_nonneg
  have hfun : xiRectangularWeilFullContinuation L =
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) +
        LSeries (xiRectangularWeilFullRemainderCoefficient L) := by
    funext z
    simp only [xiRectangularWeilFullContinuation, Pi.add_apply]
  rw [hfun, meromorphicOrderAt_add_eq_left_of_lt hcorr.meromorphicAt hlt,
    hmainOrder]

/-- Away from the shifted right Xi divisor, the cutoff-free full continuation is analytic. -/
theorem analyticAt_xiRectangularWeilFullContinuation_of_ne_poles
    {L : ℝ} {s : ℂ} (hs : 1 < s.re)
    (hne : ∀ q : XiRightZeroCopy, xiRightShiftedPole q ≠ s) :
    AnalyticAt ℂ (xiRectangularWeilFullContinuation L) s := by
  have hmain : AnalyticAt ℂ
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) s :=
    analyticAt_const.mul
      (analyticAt_xiRectangularRightDirichletContinuation_of_ne_poles
        L hs hne)
  have hcorr :=
    analyticAt_LSeries_xiRectangularWeilFullRemainderCoefficient L hs
  have hfun : xiRectangularWeilFullContinuation L =
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) +
        LSeries (xiRectangularWeilFullRemainderCoefficient L) := by
    funext z
    simp only [xiRectangularWeilFullContinuation, Pi.add_apply]
  rw [hfun]
  exact hmain.add hcorr

/-- The simple poles of the cutoff-free full continuation are exactly the shifted right Xi zeros. -/
theorem meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one_iff
    {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 1 < s.re) :
    meromorphicOrderAt (xiRectangularWeilFullContinuation L) s =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s := by
  constructor
  · intro horder
    by_contra hnone
    push Not at hnone
    have han :=
      analyticAt_xiRectangularWeilFullContinuation_of_ne_poles
        (L := L) hs hnone
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [horder] at hnonneg
    exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg
  · rintro ⟨q, rfl⟩
    exact meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one hL q

/-- The cutoff-free full continuation is meromorphic throughout `Re s > 1`. -/
theorem meromorphicOn_xiRectangularWeilFullContinuation_rightOne (L : ℝ) :
    MeromorphicOn (xiRectangularWeilFullContinuation L)
      {s : ℂ | 1 < s.re} := by
  intro s hs
  have hbase : MeromorphicAt
      (xiRectangularRightDirichletContinuation L) s :=
    meromorphicOn_xiRectangularRightDirichletContinuation_rightOne L s hs
  have hmain : MeromorphicAt
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) s :=
    analyticAt_const.meromorphicAt.mul hbase
  have hcorr :=
    analyticAt_LSeries_xiRectangularWeilFullRemainderCoefficient L hs
  have hfun : xiRectangularWeilFullContinuation L =
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) +
        LSeries (xiRectangularWeilFullRemainderCoefficient L) := by
    funext z
    simp only [xiRectangularWeilFullContinuation, Pi.add_apply]
  rw [hfun]
  exact hmain.add hcorr.meromorphicAt

/-- The residue of the cutoff-free full continuation is the exact multiplicity-weighted window
coefficient. -/
theorem meromorphicTrailingCoeffAt_xiRectangularWeilFullContinuation
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L)
        (xiRightShiftedPole q) =
      2 * (xiRightMultiplicity q : ℂ) *
        xiRectangularRightCoefficient L q := by
  refine meromorphicTrailingCoeffAt_of_rightDirichlet_add_analytic hL q
    (correction := LSeries (xiRectangularWeilFullRemainderCoefficient L)) ?_ ?_
  · refine analyticAt_LSeries_xiRectangularWeilFullRemainderCoefficient L ?_
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  · funext s
    simp only [xiRectangularWeilFullContinuation]

/-- The cutoff-free normalized residue is exactly the analytic multiplicity. -/
theorem normalizedFullObservableResidue_eq_xiRightMultiplicity
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L q) =
      (xiRightMultiplicity q : ℂ) := by
  rw [meromorphicTrailingCoeffAt_xiRectangularWeilFullContinuation hL q]
  field_simp [xiRectangularRightCoefficient_ne_zero hL q]

/-- The normalized polar divisor of the cutoff-free continuation is independent of the positive
rectangular width and of the multiplicity copy used to name a support point. -/
theorem normalizedFullObservableResidue_intrinsic
    {L₁ L₂ : ℝ} (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    {q r : XiRightZeroCopy} (hqr : q.1.1 = r.1.1) :
    meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L₁)
          (xiRightShiftedPole q) /
        (2 * xiRectangularRightCoefficient L₁ q) =
      meromorphicTrailingCoeffAt (xiRectangularWeilFullContinuation L₂)
          (xiRightShiftedPole r) /
        (2 * xiRectangularRightCoefficient L₂ r) := by
  rw [normalizedFullObservableResidue_eq_xiRightMultiplicity hL₁ q,
    normalizedFullObservableResidue_eq_xiRightMultiplicity hL₂ r,
    xiRightMultiplicity_eq_of_support_eq hqr]

/-- RH is equivalent to holomorphy of the cutoff-free continuation of one full observable
rectangular Weil sequence. -/
theorem riemannHypothesis_iff_fullObservableContinuation_analytic_rightOne
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∀ s : ℂ, 1 < s.re →
        AnalyticAt ℂ (xiRectangularWeilFullContinuation L) s := by
  constructor
  · intro hRH s hs
    apply analyticAt_xiRectangularWeilFullContinuation_of_ne_poles hs
    intro q
    have hzero : xi (q.1.1 : ℂ) = 0 :=
      xi_eq_zero_of_mem_divisor_support q.1.1
    have hright : (q.1.1 : ℂ) ∈ rightHalf := by
      rw [mem_rightHalf]
      have hq := q.2
      rw [I_mul_xiSpectralPoint] at hq
      simp only [Complex.sub_re] at hq
      norm_num at hq ⊢
      linarith
    exact False.elim ((rh_iff_xi_ne_zero_right.mp hRH)
      (q.1.1 : ℂ) hright hzero)
  · intro han
    by_contra hnot
    obtain ⟨q⟩ := nonempty_xiRightZeroCopy_of_not_riemannHypothesis hnot
    have hp : 1 < (xiRightShiftedPole q).re := by
      rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
      linarith [xiRightCenteredZero_re_pos q]
    have hanalytic := han (xiRightShiftedPole q) hp
    have hnonneg := hanalytic.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_xiRectangularWeilFullContinuation_eq_neg_one
      hL q] at hnonneg
    exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg

end

end RHTower
