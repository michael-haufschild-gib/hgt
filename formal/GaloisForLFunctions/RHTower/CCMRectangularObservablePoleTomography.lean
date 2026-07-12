import GaloisForLFunctions.RHTower.CCMRectangularPoleTomography

/-!
# Pole tomography from the observable rectangular Weil sequence

After deleting any finite initial segment, the logarithmically sampled
rectangular Weil values differ from their right-divisor Dirichlet carrier by
a bounded sequence.  Its L-series is therefore analytic in `Re s > 1`.
Consequently the observable tail L-series has a canonical meromorphic
continuation whose simple poles recover exactly the full right Xi divisor
support, not only its maximal horizontal displacement.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- The directly observable fixed-width Weil value at logarithmic sample
`n`. -/
def xiRectangularWeilLogCoefficient (L : ℝ) (n : ℕ) : ℂ :=
  xiWeilPolarization
    (xiRectangularTwoEdgeTransform L (Real.log n / 2))
    (xiRectangularTwoEdgeTransform L (Real.log n / 2))

/-- Every diagonal Xi-Weil polarization is real, without assuming RH. -/
theorem xiWeilPolarization_diagonal_im_eq_zero (F : ℂ → ℂ) :
    (xiWeilPolarization F F).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  exact (xiWeilPolarization_conj_symm F F).symm

/-- In particular, every observable rectangular logarithmic coefficient is
real. -/
theorem xiRectangularWeilLogCoefficient_im_eq_zero (L : ℝ) (n : ℕ) :
    (xiRectangularWeilLogCoefficient L n).im = 0 := by
  exact xiWeilPolarization_diagonal_im_eq_zero _

/-- The observable sequence after deletion of its first `N` entries. -/
def xiRectangularWeilTailCoefficient (L : ℝ) (N n : ℕ) : ℂ :=
  if N ≤ n then xiRectangularWeilLogCoefficient L n else 0

/-- The bounded correction between the observable tail and the complete
right-divisor Dirichlet carrier, with the deleted carrier prefix restored. -/
def xiRectangularWeilRemainderCoefficient (L : ℝ) (N n : ℕ) : ℂ :=
  xiRectangularWeilTailCoefficient L N n -
    xiRectangularRightDirichletComplex L n +
      xiRectangularLandauPrefixCoefficient L 0 N n

/-- The observable tail splits exactly into the full right-divisor carrier,
its deleted finite prefix, and the bounded correction. -/
theorem xiRectangularWeilTailCoefficient_eq_carrier_sub_prefix_add_remainder
    (L : ℝ) (N n : ℕ) :
    xiRectangularWeilTailCoefficient L N n =
      xiRectangularRightDirichletComplex L n -
        xiRectangularLandauPrefixCoefficient L 0 N n +
          xiRectangularWeilRemainderCoefficient L N n := by
  rw [xiRectangularWeilRemainderCoefficient]
  ring

/-- Once the logarithmic aperture contains the fixed window, the correction
is bounded by the global reciprocal-square Xi mass. -/
theorem norm_xiRectangularWeilRemainderCoefficient_le
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (n : ℕ) :
    ‖xiRectangularWeilRemainderCoefficient L N n‖ ≤
      rectangularTwoEdgeRemainderBound L *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
  by_cases hn : N ≤ n
  · obtain ⟨hn1, hLa⟩ := hN n hn
    have hrem := norm_xiWeilPolarization_rectangular_sub_dominant_le hLa
    rw [tsum_xiRectangularTwoEdgeDominant_logSample_eq_rightCoefficient
      L hn1 hLa] at hrem
    simpa only [xiRectangularWeilRemainderCoefficient,
      xiRectangularWeilTailCoefficient, if_pos hn,
      xiRectangularLandauPrefixCoefficient, if_neg (not_lt.mpr hn),
      add_zero, xiRectangularWeilLogCoefficient] using hrem
  · have hnlt : n < N := Nat.lt_of_not_ge hn
    rw [xiRectangularWeilRemainderCoefficient,
      xiRectangularWeilTailCoefficient, if_neg hn,
      xiRectangularLandauPrefixCoefficient, if_pos hnlt]
    simp
    exact mul_nonneg
      (by unfold rectangularTwoEdgeRemainderBound; positivity)
      (tsum_nonneg fun q => by positivity)

/-- The bounded correction L-series converges absolutely throughout
`Re s > 1`. -/
theorem xiRectangularWeilRemainderCoefficient_LSeriesSummable
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (xiRectangularWeilRemainderCoefficient L N) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re
    (m := rectangularTwoEdgeRemainderBound L *
      ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) _ hs
  intro n hn
  exact norm_xiRectangularWeilRemainderCoefficient_le hN n

/-- The absolute-convergence abscissa of the observable correction is at
most one. -/
theorem abscissaOfAbsConv_xiRectangularWeilRemainderCoefficient_le_one
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    LSeries.abscissaOfAbsConv
        (xiRectangularWeilRemainderCoefficient L N) ≤ (1 : ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact xiRectangularWeilRemainderCoefficient_LSeriesSummable hN
    (by simpa only [ofReal_re] using hy)

/-- The bounded correction L-series is analytic at every point of
`Re s > 1`. -/
theorem analyticAt_LSeries_xiRectangularWeilRemainderCoefficient
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ
      (LSeries (xiRectangularWeilRemainderCoefficient L N)) s := by
  apply LSeries_analyticOnNhd _ s
  exact (abscissaOfAbsConv_xiRectangularWeilRemainderCoefficient_le_one hN).trans_lt
    (by exact_mod_cast hs)

/-- Canonical meromorphic continuation of the observable tail L-series. -/
def xiRectangularWeilTailContinuation (L : ℝ) (N : ℕ) (s : ℂ) : ℂ :=
  2 * xiRectangularRightDirichletContinuation L s -
    xiRectangularLandauPrefixSeries L 0 N s +
      LSeries (xiRectangularWeilRemainderCoefficient L N) s

/-- On the initial half-plane of absolute convergence, the observable tail
L-series equals its canonical continuation. -/
theorem LSeries_xiRectangularWeilTailCoefficient_eq_continuation
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {delta : ℝ} (hdelta0 : 0 ≤ delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hs : 1 + delta < s.re) :
    LSeries (xiRectangularWeilTailCoefficient L N) s =
      xiRectangularWeilTailContinuation L N s := by
  have hs1 : 1 < s.re := by linarith
  have hfull := xiRectangularRightDirichletComplex_LSeriesSummable
    L hupper hs
  have hprefix := xiRectangularLandauPrefixCoefficient_LSeriesSummable
    L 0 N s
  have hrem := xiRectangularWeilRemainderCoefficient_LSeriesSummable hN hs1
  have hcoeff : xiRectangularWeilTailCoefficient L N =
      (fun n => xiRectangularRightDirichletComplex L n -
        xiRectangularLandauPrefixCoefficient L 0 N n) +
          xiRectangularWeilRemainderCoefficient L N := by
    funext n
    exact xiRectangularWeilTailCoefficient_eq_carrier_sub_prefix_add_remainder
      L N n
  rw [hcoeff]
  change LSeries
      ((fun n => xiRectangularRightDirichletComplex L n) -
        xiRectangularLandauPrefixCoefficient L 0 N +
          xiRectangularWeilRemainderCoefficient L N) s = _
  rw [LSeries_add (hfull.sub hprefix) hrem,
    LSeries_sub hfull hprefix,
    LSeries_xiRectangularRightDirichletComplex_eq_continuation
      L hdelta0 hupper hs,
    LSeries_xiRectangularLandauPrefixCoefficient_eq]
  rfl

/-- The nonpolar correction in the observable continuation is analytic in
`Re s > 1`. -/
theorem analyticAt_xiRectangularWeilTailCorrection
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ
      (fun z => -xiRectangularLandauPrefixSeries L 0 N z +
        LSeries (xiRectangularWeilRemainderCoefficient L N) z) s := by
  have hprefix : AnalyticAt ℂ
      (xiRectangularLandauPrefixSeries L 0 N) s :=
    ((differentiable_xiRectangularLandauPrefixSeries L 0 N).differentiableOn.analyticOnNhd
      isOpen_univ) s (Set.mem_univ s)
  exact hprefix.neg.add
    (analyticAt_LSeries_xiRectangularWeilRemainderCoefficient hN hs)

/-- Every right Xi divisor point remains a simple pole of the continuation
formed from the directly observable Weil tail. -/
theorem meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    (q : XiRightZeroCopy) :
    meromorphicOrderAt (xiRectangularWeilTailContinuation L N)
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ) := by
  let p := xiRightShiftedPole q
  have hp : 1 < p.re := by
    dsimp only [p]
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
    linarith [xiRightCenteredZero_re_pos q]
  have hcontMer : MeromorphicAt
      (xiRectangularRightDirichletContinuation L) p :=
    meromorphicOn_xiRectangularRightDirichletContinuation_rightOne L
      p hp
  have hmainOrder :
      meromorphicOrderAt
          (fun z => 2 * xiRectangularRightDirichletContinuation L z) p =
        ((-1 : ℤ) : WithTop ℤ) := by
    rw [fun_meromorphicOrderAt_mul (analyticAt_const.meromorphicAt) hcontMer,
      meromorphicOrderAt_const p (2 : ℂ),
      meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one
        hL q]
    norm_num
  have hcorr := analyticAt_xiRectangularWeilTailCorrection hN hp
  have hlt :
      meromorphicOrderAt
          (fun z => 2 * xiRectangularRightDirichletContinuation L z) p <
        meromorphicOrderAt
          (fun z => -xiRectangularLandauPrefixSeries L 0 N z +
            LSeries (xiRectangularWeilRemainderCoefficient L N) z) p := by
    rw [hmainOrder]
    exact lt_of_lt_of_le
      (by exact_mod_cast (show (-1 : ℤ) < 0 by omega))
      hcorr.meromorphicOrderAt_nonneg
  have hfun : xiRectangularWeilTailContinuation L N =
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) +
        (fun z => -xiRectangularLandauPrefixSeries L 0 N z +
          LSeries (xiRectangularWeilRemainderCoefficient L N) z) := by
    funext z
    simp only [xiRectangularWeilTailContinuation, Pi.add_apply]
    ring
  rw [hfun,
    meromorphicOrderAt_add_eq_left_of_lt hcorr.meromorphicAt hlt,
    hmainOrder]

/-- Away from the shifted right Xi divisor, the observable continuation is
analytic throughout `Re s > 1`. -/
theorem analyticAt_xiRectangularWeilTailContinuation_of_ne_poles
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {s : ℂ} (hs : 1 < s.re)
    (hne : ∀ q : XiRightZeroCopy, xiRightShiftedPole q ≠ s) :
    AnalyticAt ℂ (xiRectangularWeilTailContinuation L N) s := by
  have hmain : AnalyticAt ℂ
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) s :=
    analyticAt_const.mul
      (analyticAt_xiRectangularRightDirichletContinuation_of_ne_poles
        L hs hne)
  have hcorr := analyticAt_xiRectangularWeilTailCorrection hN hs
  have hfun : xiRectangularWeilTailContinuation L N =
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) +
        (fun z => -xiRectangularLandauPrefixSeries L 0 N z +
          LSeries (xiRectangularWeilRemainderCoefficient L N) z) := by
    funext z
    simp only [xiRectangularWeilTailContinuation, Pi.add_apply]
    ring
  rw [hfun]
  exact hmain.add hcorr

/-- Exact observable pole-support tomography: in `Re s > 1`, the simple
poles of a single fixed-width Weil tail continuation are exactly the shifted
right Xi zeros. -/
theorem meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one_iff
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2)
    {s : ℂ} (hs : 1 < s.re) :
    meromorphicOrderAt (xiRectangularWeilTailContinuation L N) s =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s := by
  constructor
  · intro horder
    by_contra hnone
    push Not at hnone
    have han :=
      analyticAt_xiRectangularWeilTailContinuation_of_ne_poles hN hs hnone
    have hnonneg := han.meromorphicOrderAt_nonneg
    rw [horder] at hnonneg
    exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg
  · rintro ⟨q, rfl⟩
    exact meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one
      hL hN q

/-- The observable continuation is meromorphic on the whole half-plane
`Re s > 1`. -/
theorem meromorphicOn_xiRectangularWeilTailContinuation_rightOne
    {L : ℝ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    MeromorphicOn (xiRectangularWeilTailContinuation L N)
      {s : ℂ | 1 < s.re} := by
  intro s hs
  have hbase : MeromorphicAt
      (xiRectangularRightDirichletContinuation L) s :=
    meromorphicOn_xiRectangularRightDirichletContinuation_rightOne L s hs
  have hmain : MeromorphicAt
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) s :=
    analyticAt_const.meromorphicAt.mul hbase
  have hcorr := analyticAt_xiRectangularWeilTailCorrection hN hs
  have hfun : xiRectangularWeilTailContinuation L N =
      (fun z => 2 * xiRectangularRightDirichletContinuation L z) +
        (fun z => -xiRectangularLandauPrefixSeries L 0 N z +
          LSeries (xiRectangularWeilRemainderCoefficient L N) z) := by
    funext z
    simp only [xiRectangularWeilTailContinuation, Pi.add_apply]
    ring
  rw [hfun]
  exact hmain.add hcorr.meromorphicAt

/-- The simple-pole support of the observable continuation is exactly the
range of the shifted right Xi divisor. -/
theorem observableSimplePoleSupport_eq_range_xiRightShiftedPole
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    {s : ℂ | 1 < s.re ∧
      meromorphicOrderAt (xiRectangularWeilTailContinuation L N) s =
        ((-1 : ℤ) : WithTop ℤ)} =
      Set.range xiRightShiftedPole := by
  ext s
  constructor
  · rintro ⟨hs, horder⟩
    exact (meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one_iff
      hL hN hs).mp horder
  · rintro ⟨q, rfl⟩
    have hp : 1 < (xiRightShiftedPole q).re := by
      rw [xiRightShiftedPole, Complex.add_re, Complex.one_re]
      linarith [xiRightCenteredZero_re_pos q]
    exact ⟨hp,
      meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one
        hL hN q⟩

/-- Direct manuscript-facing holomorphy criterion: RH is equivalent to the
observable continuation being analytic at every point of `Re s > 1`. -/
theorem riemannHypothesis_iff_observableTailContinuation_analytic_rightOne
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      ∀ s : ℂ, 1 < s.re →
        AnalyticAt ℂ (xiRectangularWeilTailContinuation L N) s := by
  constructor
  · intro hRH s hs
    apply analyticAt_xiRectangularWeilTailContinuation_of_ne_poles hN hs
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
    rw [meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one
      hL hN q] at hnonneg
    exact (show ¬ ((0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) by
      exact_mod_cast (show ¬ (0 : ℤ) ≤ -1 by omega)) hnonneg

/-- Exact centered-divisor recovery from the observable simple-pole set. -/
theorem xiRightZeroSupport_eq_image_observableSimplePoleSupport
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n →
      1 ≤ n ∧ L ≤ Real.log n / 2) :
    {ρ : ℂ | xi ρ = 0 ∧ 1 / 2 < ρ.re} =
      (fun s : ℂ => s - 1 / 2) ''
        {s : ℂ | 1 < s.re ∧
          meromorphicOrderAt (xiRectangularWeilTailContinuation L N) s =
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
      exists_xiRightZeroCopy_shiftedPole_eq_of_xi_shifted_eq_zero hs hzero'
    have horder :
        meromorphicOrderAt (xiRectangularWeilTailContinuation L N) s =
          ((-1 : ℤ) : WithTop ℤ) :=
      (meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one_iff
        hL hN hs).mpr ⟨q, hq⟩
    exact ⟨s, ⟨hs, horder⟩, hshift⟩
  · rintro ⟨s, ⟨hs, horder⟩, rfl⟩
    obtain ⟨q, hq⟩ :=
      (meromorphicOrderAt_xiRectangularWeilTailContinuation_eq_neg_one_iff
        hL hN hs).mp horder
    constructor
    · rw [← hq]
      exact xi_shifted_eq_zero_at_xiRightShiftedPole q
    · norm_num [Complex.sub_re] at hs ⊢
      linarith

end

end RHTower
