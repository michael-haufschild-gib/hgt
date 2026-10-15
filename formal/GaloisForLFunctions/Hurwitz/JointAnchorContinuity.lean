import GaloisForLFunctions.Hurwitz.AnchorTransversality
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Normal convergence of the Hurwitz source near its anchor

The zero-degree Hurwitz remainder converges normally when the exponent varies
over a compact subset of `Re s > 0` and the shift varies near `1`. The bound
comes from the derivative of the binomial factor on a compact set.
-/

open Complex Filter Metric Set
open scoped Topology

namespace HurwitzZetaContinuation

private theorem one_add_mem_slitPlane_of_norm_le_half {y : ℂ}
    (hy : ‖y‖ ≤ (1 / 2 : ℝ)) : 1 + y ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hr := Complex.abs_re_le_norm y
  simp only [Complex.add_re, Complex.one_re]
  linarith [(abs_le.mp (hr.trans hy)).1]

/-- The first binomial remainder is uniformly Lipschitz on a compact exponent set. -/
theorem exists_binomial_first_bound_on_compact {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ y : ℂ, ‖y‖ ≤ (1 / 2 : ℝ) →
      ‖(1 + y) ^ (-s) - 1‖ ≤ C * ‖y‖ := by
  let D : ℂ × ℂ → ℂ := fun p => -p.1 * (1 + p.2) ^ (-p.1 - 1)
  have hD : ContinuousOn D (K ×ˢ closedBall (0 : ℂ) (1 / 2 : ℝ)) := by
    intro p hp
    have hp2 : ‖p.2‖ ≤ (1 / 2 : ℝ) := by simpa using hp.2
    exact (continuousAt_fst.neg.mul
      ((continuousAt_const.add continuousAt_snd).cpow
        (continuousAt_fst.neg.sub continuousAt_const)
        (one_add_mem_slitPlane_of_norm_le_half hp2))).continuousWithinAt
  obtain ⟨C, hC, hbound⟩ :=
    ((hK.prod (isCompact_closedBall (0 : ℂ) (1 / 2 : ℝ))).image_of_continuousOn hD).isBounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro s hs y hy
  have hder : ∀ z ∈ closedBall (0 : ℂ) (1 / 2 : ℝ),
      HasDerivWithinAt (fun z : ℂ => (1 + z) ^ (-s))
        (-s * (1 + z) ^ (-s - 1)) (closedBall (0 : ℂ) (1 / 2 : ℝ)) z := by
    intro z hz
    have hz' : ‖z‖ ≤ (1 / 2 : ℝ) := by simpa using hz
    have hd := (Complex.hasStrictDerivAt_cpow_const
      (c := -s) (one_add_mem_slitPlane_of_norm_le_half hz')).hasDerivAt.comp z
      ((hasDerivAt_const z (1 : ℂ)).add (hasDerivAt_id z))
    simpa only [Function.comp_def, zero_add, mul_one] using hd.hasDerivWithinAt
  have hb : ∀ z ∈ closedBall (0 : ℂ) (1 / 2 : ℝ),
      ‖-s * (1 + z) ^ (-s - 1)‖ ≤ C := by
    intro z hz
    exact hbound _ ⟨(s, z), ⟨hs, hz⟩, rfl⟩
  have hv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hder hb
    (convex_closedBall (0 : ℂ) (1 / 2 : ℝ))
    (mem_closedBall_self (by norm_num)) (show y ∈ closedBall (0 : ℂ) (1 / 2 : ℝ) by
      simpa using hy)
  simpa using hv

/-- A summable majorant for the actual Hurwitz remainder, uniform in both variables. -/
theorem exists_remainder_zero_bound_on_compact {K : Set ℂ} (hK : IsCompact K)
    {δ : ℝ} (hKδ : ∀ s ∈ K, δ ≤ s.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (s : ℂ), s ∈ K →
      ∀ a : ℂ, ‖a - 1‖ ≤ (1 / 2 : ℝ) →
        ‖remainder 0 s a n‖ ≤ C * ((n + 1 : ℕ) : ℝ) ^ (-(δ + 1)) := by
  obtain ⟨C, hC, hbin⟩ := exists_binomial_first_bound_on_compact hK
  refine ⟨C, hC, ?_⟩
  intro n s hs a ha
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
  have hy : ‖(a - 1) / ((n + 1 : ℕ) : ℂ)‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_div, Complex.norm_natCast]
    exact (div_le_self (norm_nonneg _) hn).trans ha
  have hfactor : remainder 0 s a n =
      ((n + 1 : ℕ) : ℂ) ^ (-s) *
        ((1 + (a - 1) / ((n + 1 : ℕ) : ℂ)) ^ (-s) - 1) := by
    rw [remainder, taylorPoly_zero,
      term_factor_of_norm_lt_one n (lt_of_le_of_lt hy (by norm_num))]
    ring
  have hmaj : ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖ *
      ‖(a - 1) / ((n + 1 : ℕ) : ℂ)‖ =
        ‖a - 1‖ * ‖((n + 1 : ℕ) : ℂ) ^ (-(s + 1))‖ := by
    simpa using majorant_eq 0 s a n
  have hpow : ‖((n + 1 : ℕ) : ℂ) ^ (-(s + 1))‖ ≤
      ((n + 1 : ℕ) : ℝ) ^ (-(δ + 1)) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re,
      Complex.add_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_exponent_le hn (by linarith [hKδ s hs])
  calc
    ‖remainder 0 s a n‖ = ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖ *
        ‖(1 + (a - 1) / ((n + 1 : ℕ) : ℂ)) ^ (-s) - 1‖ := by
      rw [hfactor, norm_mul]
    _ ≤ ‖((n + 1 : ℕ) : ℂ) ^ (-s)‖ *
        (C * ‖(a - 1) / ((n + 1 : ℕ) : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (hbin s hs _ hy) (norm_nonneg _)
    _ = C * (‖a - 1‖ * ‖((n + 1 : ℕ) : ℂ) ^ (-(s + 1))‖) := by
      rw [← hmaj]
      ring
    _ ≤ C * (1 * ((n + 1 : ℕ) : ℝ) ^ (-(δ + 1))) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact mul_le_mul (le_trans ha (by norm_num)) hpow (norm_nonneg _)
        (by norm_num)
    _ = C * ((n + 1 : ℕ) : ℝ) ^ (-(δ + 1)) := by rw [one_mul]

/-- Each remainder is jointly continuous on the closed anchor tube. -/
theorem continuousOn_remainder_zero (K : Set ℂ) (n : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => remainder 0 p.1 p.2 n)
      (K ×ˢ closedBall (1 : ℂ) (1 / 2 : ℝ)) := by
  intro p hp
  have ha : ‖p.2 - 1‖ ≤ (1 / 2 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hp.2
  have hare : 0 < p.2.re := by
    have hr := (abs_le.mp ((Complex.abs_re_le_norm (p.2 - 1)).trans ha)).1
    simp only [Complex.sub_re, Complex.one_re] at hr
    linarith
  have hna : (n : ℂ) + p.2 ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.add_re, Complex.natCast_re]
    positivity
  have hn1 : ((n + 1 : ℕ) : ℂ) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.natCast_re]
    positivity
  simpa only [remainder, taylorPoly_zero, Pi.add_apply, Pi.neg_apply] using
    (((continuousAt_const.add continuousAt_snd).cpow continuousAt_fst.neg hna).fun_sub
      (continuousAt_const.cpow continuousAt_fst.neg hn1)).continuousWithinAt

/-- The remainder sum is jointly continuous on every compact exponent tube. -/
theorem continuousOn_tsum_remainder_zero {K : Set ℂ} (hK : IsCompact K)
    {δ : ℝ} (hδ : 0 < δ) (hKδ : ∀ s ∈ K, δ ≤ s.re) :
    ContinuousOn (fun p : ℂ × ℂ => ∑' n, remainder 0 p.1 p.2 n)
      (K ×ˢ closedBall (1 : ℂ) (1 / 2 : ℝ)) := by
  obtain ⟨C, _, hC⟩ := exists_remainder_zero_bound_on_compact hK hKδ
  have hu : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(δ + 1))) := by
    apply (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(δ + 1))) 1).mpr
    simpa only [Real.rpow_neg (Nat.cast_nonneg _)] using
      (Real.summable_nat_rpow_inv.mpr (show 1 < δ + 1 by linarith))
  apply continuousOn_tsum (continuousOn_remainder_zero K) (hu.mul_left C)
  intro n p hp
  exact hC n p.1 hp.1 p.2 (by
    simpa only [mem_closedBall, dist_eq_norm] using hp.2)

/-- Local joint continuity of the normally convergent arithmetic remainder. -/
theorem continuousAt_tsum_remainder_zero {s a : ℂ} (hs : 0 < s.re)
    (ha : ‖a - 1‖ < (1 / 2 : ℝ)) :
    ContinuousAt (fun p : ℂ × ℂ => ∑' n, remainder 0 p.1 p.2 n) (s, a) := by
  have hKδ : ∀ z ∈ closedBall s (s.re / 2), s.re / 2 ≤ z.re := by
    intro z hz
    have hz' : ‖z - s‖ ≤ s.re / 2 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hr := (abs_le.mp ((Complex.abs_re_le_norm (z - s)).trans hz')).1
    simp only [Complex.sub_re] at hr
    linarith
  apply (continuousOn_tsum_remainder_zero (isCompact_closedBall s (s.re / 2))
    (half_pos hs) hKδ).continuousAt
  apply Filter.mem_of_superset
    ((isOpen_ball.prod isOpen_ball).mem_nhds
      (show (s, a) ∈ ball s (s.re / 2) ×ˢ ball (1 : ℂ) (1 / 2 : ℝ) from
        ⟨mem_ball_self (half_pos hs), by simpa only [mem_ball, dist_eq_norm] using ha⟩))
  exact fun p hp => ⟨ball_subset_closedBall hp.1, ball_subset_closedBall hp.2⟩

/-- The actual continued Hurwitz source is jointly continuous near the anchor. -/
theorem continuousAt_continuedHzeta_joint {s a : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (ha : ‖a - 1‖ < (1 / 2 : ℝ)) :
    ContinuousAt (fun p : ℂ × ℂ => continuedHzeta p.1 p.2) (s, a) := by
  have hc := (continuousAt_tsum_remainder_zero hs ha).fun_add
    ((differentiableAt_riemannZeta hs1).continuousAt.comp continuousAt_fst)
  apply hc.congr
  filter_upwards [((isOpen_lt continuous_const
    (Complex.continuous_re.comp continuous_fst)).mem_nhds hs)] with p hp
  simp only [continuedHzeta, regularizationOrder_eq_zero hp, continuedAt, restoration_zero,
    Function.comp_def]

end HurwitzZetaContinuation
