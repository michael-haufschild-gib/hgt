import GaloisForLFunctions.RHTower.XiHeatCassiniLogMeshDefectPrimeGapEquivalence

/-!
# The `3/2` consecutive-prime-gap moment threshold for the Route-T mesh

The critical physical mesh energy is

`gap_N^(2 : ℕ) * exp (-(3/2) * log p_N)`.

Discrete Abel summation shows that a prefix-square moment of order `theta < 3/2` forces this
energy to be summable.  The proof keeps the exact logarithmic prime mesh: Bertrand bounds each
logarithmic cell by one, while an exponential-potential telescope absorbs the remaining cell
length.  Thus `3/2` is the precise Abel threshold, not a heuristic exponent comparison.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Square of the `N`th consecutive ordered-prime gap. -/
def xiHeatCassiniPrimeGapSquare (N : ℕ) : ℝ :=
  xiHeatCassiniOrderedPrimeGap N ^ 2

/-- Prefix second moment of consecutive ordered-prime gaps. -/
def xiHeatCassiniPrimeGapSquarePrefix (M : ℕ) : ℝ :=
  ∑ N ∈ Finset.range M, xiHeatCassiniPrimeGapSquare N

theorem xiHeatCassiniPrimeGapSquare_nonneg (N : ℕ) :
    0 ≤ xiHeatCassiniPrimeGapSquare N := by
  exact sq_nonneg _

theorem xiHeatCassiniPrimeGapSquarePrefix_nonneg (M : ℕ) :
    0 ≤ xiHeatCassiniPrimeGapSquarePrefix M := by
  exact Finset.sum_nonneg fun N _ => xiHeatCassiniPrimeGapSquare_nonneg N

/-- Critical `p^(-3/2)` Abel weight, written in prime-log coordinates. -/
def xiHeatCassiniPrimeGapCriticalAbelWeight (N : ℕ) : ℝ :=
  Real.exp (-(3 / 2 : ℝ) * xiMassNthPrimeLogHeight N)

theorem xiHeatCassiniPrimeGapCriticalAbelWeight_pos (N : ℕ) :
    0 < xiHeatCassiniPrimeGapCriticalAbelWeight N := by
  exact Real.exp_pos _

theorem xiHeatCassiniPrimeGapCriticalAbelWeight_antitone :
    Antitone xiHeatCassiniPrimeGapCriticalAbelWeight := by
  intro M N hMN
  apply Real.exp_le_exp.mpr
  have hheight := nthPrimeSubtype_log_strictMono.monotone hMN
  have hheight' : xiMassNthPrimeLogHeight M ≤ xiMassNthPrimeLogHeight N := by
    simpa [xiMassNthPrimeLogHeight] using hheight
  linarith

/-- The physical critical energy is exactly gap-square against the `p^(-3/2)` Abel weight. -/
theorem xiHeatCassiniPrimeGapCriticalEnergy_eq_square_mul_abelWeight (N : ℕ) :
    xiHeatCassiniPrimeGapCriticalEnergy N =
      xiHeatCassiniPrimeGapSquare N * xiHeatCassiniPrimeGapCriticalAbelWeight N := by
  let p : ℝ := nthPrimeSubtype N
  have hp : 0 < p := nthPrimeSubtype_pos N
  have hsqrt : Real.exp (Real.log p / 2) = Real.sqrt p := by
    rw [← Real.log_sqrt hp.le, Real.exp_log (Real.sqrt_pos.mpr hp)]
  have hp2 : Real.exp (2 * Real.log p) = p ^ 2 := by
    rw [show 2 * Real.log p = Real.log p + Real.log p by ring, Real.exp_add,
      Real.exp_log hp]
    exact (pow_two p).symm
  have hweight : Real.exp (-(3 / 2 : ℝ) * Real.log p) = Real.sqrt p / p ^ 2 := by
    rw [show -(3 / 2 : ℝ) * Real.log p = Real.log p / 2 - 2 * Real.log p by ring,
      Real.exp_sub, hsqrt, hp2]
  unfold xiHeatCassiniPrimeGapCriticalEnergy xiHeatCassiniPrimeGapSquare
    xiHeatCassiniPrimeGapCriticalAbelWeight xiMassNthPrimeLogHeight
  change (xiHeatCassiniOrderedPrimeGap N / p) ^ 2 * Real.sqrt p =
    xiHeatCassiniOrderedPrimeGap N ^ 2 * Real.exp (-(3 / 2 : ℝ) * Real.log p)
  rw [hweight]
  field_simp [hp.ne']

/-- Exact range-form Abel identity with the boundary placed one step beyond the last term. -/
theorem sum_range_mul_eq_prefix_boundary_add_sum_prefix_drop
    (d w : ℕ → ℝ) (M : ℕ) :
    ∑ N ∈ Finset.range M, d N * w N =
      (∑ N ∈ Finset.range M, d N) * w M +
        ∑ N ∈ Finset.range M,
          (∑ j ∈ Finset.range (N + 1), d j) * (w N - w (N + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [Finset.sum_range_succ]
      ring

/-- Every exponentially damped ordered-prime log-gap is summable.  This uses only monotonicity,
Bertrand's unit log-cell bound, and an exact exponential-potential telescope. -/
theorem summable_primeLogGap_mul_exp_neg_height
    {c : ℝ} (hc : 0 < c) :
    Summable (fun N : ℕ =>
      xiHeatCassiniOrderedPrimeLogGap N *
        Real.exp (-c * xiMassNthPrimeLogHeight N)) := by
  let w : ℕ → ℝ := fun N => Real.exp (-c * xiMassNthPrimeLogHeight N)
  have hdrop_nonneg (N : ℕ) : 0 ≤ w N - w (N + 1) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_exp.mpr
    have hheight := nthPrimeSubtype_log_strictMono.monotone (Nat.le_succ N)
    have hheight' : xiMassNthPrimeLogHeight N ≤ xiMassNthPrimeLogHeight (N + 1) := by
      simpa [xiMassNthPrimeLogHeight] using hheight
    nlinarith
  have hdrop_summable : Summable (fun N : ℕ => w N - w (N + 1)) := by
    apply summable_of_sum_range_le (c := w 0) hdrop_nonneg
    intro M
    rw [Finset.sum_range_sub']
    have hwM : 0 ≤ w M := (Real.exp_pos _).le
    linarith
  have hpoint (N : ℕ) :
      xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (-c * xiMassNthPrimeLogHeight N) ≤
        (Real.exp c / c) * (w N - w (N + 1)) := by
    let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
    let h : ℝ := xiMassNthPrimeLogHeight N
    have hdelta0 : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
    have hdelta1 : delta ≤ 1 := xiHeatCassiniOrderedPrimeLogGap_le_one N
    have hheight : xiMassNthPrimeLogHeight (N + 1) = h + delta := by
      simp only [h, delta, xiHeatCassiniOrderedPrimeLogGap]
      ring
    have hbase := Real.add_one_le_exp (c * delta)
    have hmul := mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg (-(c * delta)))
    have hexpcancel : Real.exp (c * delta) * Real.exp (-(c * delta)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hcore :
        c * delta * Real.exp (-(c * delta)) ≤ 1 - Real.exp (-(c * delta)) := by
      rw [hexpcancel] at hmul
      linarith
    have hexpmono : Real.exp (-c) ≤ Real.exp (-(c * delta)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hsmall :
        c * delta * Real.exp (-c) ≤ 1 - Real.exp (-(c * delta)) := by
      exact (mul_le_mul_of_nonneg_left hexpmono
        (mul_nonneg hc.le hdelta0)).trans hcore
    have hdelta :
        delta ≤ (Real.exp c / c) * (1 - Real.exp (-(c * delta))) := by
      calc
        delta = (Real.exp c / c) * (c * delta * Real.exp (-c)) := by
          field_simp [hc.ne']
          rw [show delta * Real.exp c * Real.exp (-c) =
            delta * (Real.exp c * Real.exp (-c)) by ring, ← Real.exp_add]
          simp
        _ ≤ (Real.exp c / c) * (1 - Real.exp (-(c * delta))) :=
          mul_le_mul_of_nonneg_left hsmall (by positivity)
    calc
      xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (-c * xiMassNthPrimeLogHeight N) =
          delta * Real.exp (-c * h) := rfl
      _ ≤ ((Real.exp c / c) * (1 - Real.exp (-(c * delta)))) *
          Real.exp (-c * h) :=
        mul_le_mul_of_nonneg_right hdelta (Real.exp_nonneg _)
      _ = (Real.exp c / c) * (w N - w (N + 1)) := by
        dsimp only [w]
        rw [hheight, show -c * (h + delta) = -c * h + -(c * delta) by ring,
          Real.exp_add]
        ring
  have hmajor := hdrop_summable.mul_left (Real.exp c / c)
  exact Summable.of_nonneg_of_le
    (fun N => mul_nonneg (xiHeatCassiniOrderedPrimeLogGap_nonneg N) (Real.exp_nonneg _))
    hpoint hmajor

/-- One critical Abel-weight drop costs at most one log-gap times the left-endpoint weight. -/
theorem criticalAbelWeight_sub_succ_le_logGap (N : ℕ) :
    xiHeatCassiniPrimeGapCriticalAbelWeight N -
        xiHeatCassiniPrimeGapCriticalAbelWeight (N + 1) ≤
      (3 / 2 : ℝ) * xiHeatCassiniOrderedPrimeLogGap N *
        xiHeatCassiniPrimeGapCriticalAbelWeight N := by
  let delta : ℝ := xiHeatCassiniOrderedPrimeLogGap N
  let h : ℝ := xiMassNthPrimeLogHeight N
  have hdelta0 : 0 ≤ delta := xiHeatCassiniOrderedPrimeLogGap_nonneg N
  have hheight : xiMassNthPrimeLogHeight (N + 1) = h + delta := by
    simp only [h, delta, xiHeatCassiniOrderedPrimeLogGap]
    ring
  have hbase := Real.add_one_le_exp (-((3 / 2 : ℝ) * delta))
  have hrem : 1 - Real.exp (-((3 / 2 : ℝ) * delta)) ≤ (3 / 2 : ℝ) * delta := by
    linarith
  unfold xiHeatCassiniPrimeGapCriticalAbelWeight
  change Real.exp (-(3 / 2 : ℝ) * h) -
      Real.exp (-(3 / 2 : ℝ) * xiMassNthPrimeLogHeight (N + 1)) ≤
    (3 / 2 : ℝ) * delta * Real.exp (-(3 / 2 : ℝ) * h)
  rw [hheight,
    show -(3 / 2 : ℝ) * (h + delta) =
      -(3 / 2 : ℝ) * h + -((3 / 2 : ℝ) * delta) by ring,
    Real.exp_add]
  nlinarith [Real.exp_pos (-(3 / 2 : ℝ) * h)]

/-- A prefix second moment of any order `theta < 3/2` forces critical Route-T mesh energy.
This is the exact Abel threshold theorem needed by the Maynard--Peck gap moment. -/
theorem summable_primeGapCriticalEnergy_of_prefix_moment_lt_three_halves
    {theta C : ℝ} (htheta0 : 0 ≤ theta) (htheta : theta < 3 / 2)
    (hC : 0 ≤ C)
    (hmoment : ∀ M : ℕ,
      xiHeatCassiniPrimeGapSquarePrefix M ≤
        C * Real.exp (theta * xiMassNthPrimeLogHeight M)) :
    Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  let c : ℝ := 3 / 2 - theta
  let K : ℝ := C * Real.exp theta * (3 / 2 : ℝ)
  have hc : 0 < c := by dsimp only [c]; linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hlogsum := summable_primeLogGap_mul_exp_neg_height hc
  have hmajor : Summable (fun N : ℕ =>
      K * (xiHeatCassiniOrderedPrimeLogGap N *
        Real.exp (-c * xiMassNthPrimeLogHeight N))) := hlogsum.mul_left K
  apply summable_of_sum_range_le xiHeatCassiniPrimeGapCriticalEnergy_nonneg
  intro M
  rw [show (∑ N ∈ Finset.range M, xiHeatCassiniPrimeGapCriticalEnergy N) =
      ∑ N ∈ Finset.range M,
        xiHeatCassiniPrimeGapSquare N * xiHeatCassiniPrimeGapCriticalAbelWeight N by
      apply Finset.sum_congr rfl
      intro N _
      exact xiHeatCassiniPrimeGapCriticalEnergy_eq_square_mul_abelWeight N]
  rw [sum_range_mul_eq_prefix_boundary_add_sum_prefix_drop]
  have hboundary :
      xiHeatCassiniPrimeGapSquarePrefix M *
          xiHeatCassiniPrimeGapCriticalAbelWeight M ≤ C := by
    have hmom := hmoment M
    have hweight : 0 ≤ xiHeatCassiniPrimeGapCriticalAbelWeight M :=
      (xiHeatCassiniPrimeGapCriticalAbelWeight_pos M).le
    calc
      xiHeatCassiniPrimeGapSquarePrefix M *
          xiHeatCassiniPrimeGapCriticalAbelWeight M ≤
        (C * Real.exp (theta * xiMassNthPrimeLogHeight M)) *
          xiHeatCassiniPrimeGapCriticalAbelWeight M :=
        mul_le_mul_of_nonneg_right hmom hweight
      _ = C * Real.exp (-c * xiMassNthPrimeLogHeight M) := by
        have hexpcombine :
            Real.exp (theta * xiMassNthPrimeLogHeight M) *
                Real.exp (-(3 / 2 : ℝ) * xiMassNthPrimeLogHeight M) =
              Real.exp (-c * xiMassNthPrimeLogHeight M) := by
          rw [← Real.exp_add]
          congr 1
          dsimp only [c]
          ring
        dsimp only [xiHeatCassiniPrimeGapCriticalAbelWeight]
        rw [show (C * Real.exp (theta * xiMassNthPrimeLogHeight M)) *
            Real.exp (-(3 / 2 : ℝ) * xiMassNthPrimeLogHeight M) =
          C * (Real.exp (theta * xiMassNthPrimeLogHeight M) *
            Real.exp (-(3 / 2 : ℝ) * xiMassNthPrimeLogHeight M)) by ring,
          hexpcombine]
      _ ≤ C := by
        have hheight := xiMassNthPrimeLogHeight_pos M
        have hexp : Real.exp (-c * xiMassNthPrimeLogHeight M) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by nlinarith)
        nlinarith [Real.exp_nonneg (-c * xiMassNthPrimeLogHeight M)]
  have hterms (N : ℕ) :
      xiHeatCassiniPrimeGapSquarePrefix (N + 1) *
          (xiHeatCassiniPrimeGapCriticalAbelWeight N -
            xiHeatCassiniPrimeGapCriticalAbelWeight (N + 1)) ≤
        K * (xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (-c * xiMassNthPrimeLogHeight N)) := by
    have hprefix := hmoment (N + 1)
    have hdrop0 : 0 ≤ xiHeatCassiniPrimeGapCriticalAbelWeight N -
        xiHeatCassiniPrimeGapCriticalAbelWeight (N + 1) :=
      sub_nonneg.mpr (xiHeatCassiniPrimeGapCriticalAbelWeight_antitone
        (Nat.le_succ N))
    have hdrop := criticalAbelWeight_sub_succ_le_logGap N
    have hprefix0 := xiHeatCassiniPrimeGapSquarePrefix_nonneg (N + 1)
    have hthetaShift :
        Real.exp (theta * xiMassNthPrimeLogHeight (N + 1)) ≤
          Real.exp theta * Real.exp (theta * xiMassNthPrimeLogHeight N) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hgap := xiHeatCassiniOrderedPrimeLogGap_le_one N
      have hheight : xiMassNthPrimeLogHeight (N + 1) =
          xiMassNthPrimeLogHeight N + xiHeatCassiniOrderedPrimeLogGap N := by
        unfold xiHeatCassiniOrderedPrimeLogGap
        ring
      rw [hheight]
      nlinarith
    calc
      xiHeatCassiniPrimeGapSquarePrefix (N + 1) *
          (xiHeatCassiniPrimeGapCriticalAbelWeight N -
            xiHeatCassiniPrimeGapCriticalAbelWeight (N + 1)) ≤
        (C * Real.exp (theta * xiMassNthPrimeLogHeight (N + 1))) *
          (xiHeatCassiniPrimeGapCriticalAbelWeight N -
            xiHeatCassiniPrimeGapCriticalAbelWeight (N + 1)) :=
        mul_le_mul_of_nonneg_right hprefix hdrop0
      _ ≤ (C * Real.exp (theta * xiMassNthPrimeLogHeight (N + 1))) *
          ((3 / 2 : ℝ) * xiHeatCassiniOrderedPrimeLogGap N *
            xiHeatCassiniPrimeGapCriticalAbelWeight N) :=
        mul_le_mul_of_nonneg_left hdrop
          (mul_nonneg hC (Real.exp_nonneg _))
      _ ≤ (C * (Real.exp theta * Real.exp
          (theta * xiMassNthPrimeLogHeight N))) *
          ((3 / 2 : ℝ) * xiHeatCassiniOrderedPrimeLogGap N *
            xiHeatCassiniPrimeGapCriticalAbelWeight N) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hthetaShift hC
        · exact mul_nonneg
            (mul_nonneg (by norm_num) (xiHeatCassiniOrderedPrimeLogGap_nonneg N))
            (xiHeatCassiniPrimeGapCriticalAbelWeight_pos N).le
      _ = K * (xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (-c * xiMassNthPrimeLogHeight N)) := by
        have hexpcombine :
            Real.exp (theta * xiMassNthPrimeLogHeight N) *
                Real.exp (-(3 / 2 : ℝ) * xiMassNthPrimeLogHeight N) =
              Real.exp (-c * xiMassNthPrimeLogHeight N) := by
          rw [← Real.exp_add]
          congr 1
          dsimp only [c]
          ring
        dsimp only [K, xiHeatCassiniPrimeGapCriticalAbelWeight]
        calc
          (C * (Real.exp theta * Real.exp
              (theta * xiMassNthPrimeLogHeight N))) *
              ((3 / 2 : ℝ) * xiHeatCassiniOrderedPrimeLogGap N *
                Real.exp (-(3 / 2 : ℝ) * xiMassNthPrimeLogHeight N)) =
            (C * Real.exp theta * (3 / 2 : ℝ)) *
              xiHeatCassiniOrderedPrimeLogGap N *
                (Real.exp (theta * xiMassNthPrimeLogHeight N) *
                  Real.exp (-(3 / 2 : ℝ) * xiMassNthPrimeLogHeight N)) := by ring
          _ = (C * Real.exp theta * (3 / 2 : ℝ)) *
              (xiHeatCassiniOrderedPrimeLogGap N *
                Real.exp (-c * xiMassNthPrimeLogHeight N)) := by
            rw [hexpcombine]
            ring
  calc
    xiHeatCassiniPrimeGapSquarePrefix M *
          xiHeatCassiniPrimeGapCriticalAbelWeight M +
        ∑ N ∈ Finset.range M,
          xiHeatCassiniPrimeGapSquarePrefix (N + 1) *
            (xiHeatCassiniPrimeGapCriticalAbelWeight N -
              xiHeatCassiniPrimeGapCriticalAbelWeight (N + 1)) ≤
      C + ∑ N ∈ Finset.range M,
        K * (xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (-c * xiMassNthPrimeLogHeight N)) := by
      exact add_le_add hboundary (Finset.sum_le_sum fun N _ => hterms N)
    _ ≤ C + ∑' N : ℕ,
        K * (xiHeatCassiniOrderedPrimeLogGap N *
          Real.exp (-c * xiMassNthPrimeLogHeight N)) := by
      gcongr
      exact hmajor.sum_le_tsum (Finset.range M) (fun N _ =>
        mul_nonneg hK (mul_nonneg (xiHeatCassiniOrderedPrimeLogGap_nonneg N)
          (Real.exp_nonneg _)))

/-- Concrete margin selected from the classical `5/4 + epsilon` prime-gap second moment. -/
theorem summable_primeGapCriticalEnergy_of_eleven_eighth_prefix_moment
    {C : ℝ} (hC : 0 ≤ C)
    (hmoment : ∀ M : ℕ,
      xiHeatCassiniPrimeGapSquarePrefix M ≤
        C * Real.exp ((11 / 8 : ℝ) * xiMassNthPrimeLogHeight M)) :
    Summable xiHeatCassiniPrimeGapCriticalEnergy := by
  exact summable_primeGapCriticalEnergy_of_prefix_moment_lt_three_halves
    (theta := 11 / 8) (C := C) (by norm_num) (by norm_num) hC hmoment

/-- The `11/8` prime-gap moment closes every complex physical mesh defect throughout the shifted
zeta half-strip. -/
theorem summable_logMeshDefect_of_eleven_eighth_prefix_moment
    {C : ℝ} (hC : 0 ≤ C)
    (hmoment : ∀ M : ℕ,
      xiHeatCassiniPrimeGapSquarePrefix M ≤
        C * Real.exp ((11 / 8 : ℝ) * xiMassNthPrimeLogHeight M))
    {s : ℂ} (hsleft : -(1 / 2 : ℝ) ≤ s.re) (hsright : s.re ≤ 0) :
    Summable (fun N : ℕ =>
      ‖xiHeatCassiniLogMeshLaplaceScaledDefect s N‖) := by
  exact summable_norm_xiHeatCassiniLogMeshLaplaceScaledDefect_of_criticalEnergy
    hsleft hsright
    (summable_primeGapCriticalEnergy_of_eleven_eighth_prefix_moment hC hmoment)

end

end RHTower
