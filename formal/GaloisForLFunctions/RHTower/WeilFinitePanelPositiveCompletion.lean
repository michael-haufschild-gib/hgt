import GaloisForLFunctions.RHTower.WeilFiniteBlockExcessMass

/-!
# One-coordinate positive completion of a finite log-shift panel

The truncated autocorrelation is strictly positive exactly inside its support.
At window `k + 1`, the first integer above `exp (2 * (k + 1))` therefore gives
a strictly positive coefficient direction for every entry of the finite panel.
An arbitrary coefficient sequence can be raised above any prescribed panel
height by increasing that one coefficient. Earlier coefficients remain fixed.
-/

open Complex MeasureTheory Set Zeta23
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The smooth bulk cutoff is strictly positive exactly on its open support. -/
theorem bulkCutoff_pos_iff (L u : ℝ) : 0 < bulkCutoff L u ↔ |u| < L := by
  constructor
  · intro h
    by_contra hu
    rw [bulkCutoff_eq_zero (le_of_not_gt hu)] at h
    exact (lt_irrefl 0) h
  · intro hu
    obtain ⟨hlo, hhi⟩ := abs_lt.mp hu
    exact mul_pos (Real.smoothTransition.pos_of_pos (by linarith))
      (Real.smoothTransition.pos_of_pos (by linarith))

/-- Multiplication by the everywhere positive Riemann kernel preserves the cutoff support. -/
theorem truncatedRiemannKernelReal_pos_iff (L u : ℝ) :
    0 < truncatedRiemannKernelReal L u ↔ |u| < L := by
  constructor
  · intro h
    by_contra hu
    rw [truncatedRiemannKernelReal_eq_zero_of_le (le_of_not_gt hu)] at h
    exact (lt_irrefl 0) h
  · intro hu
    exact mul_pos (riemannKernelReal_pos u) ((bulkCutoff_pos_iff L u).mpr hu)

/-- Exact strict support of the truncated autocorrelation, including nonpositive truncations. -/
theorem truncatedRiemannAutocorr_pos_iff (L y : ℝ) :
    0 < truncatedRiemannAutocorr L y ↔ |y| < 2 * L := by
  constructor
  · intro h
    by_contra hy
    rw [truncatedRiemannAutocorr_eq_zero (le_of_not_gt hy)] at h
    exact (lt_irrefl 0) h
  · intro hy
    have hhalf : |y / 2| < L := by
      rw [abs_div]
      norm_num
      linarith only [hy]
    have hhalf' : |y / 2 - y| < L := by
      rw [show y / 2 - y = -(y / 2) by ring, abs_neg]
      exact hhalf
    have hc : Continuous fun t =>
        truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - y) :=
      (continuous_truncatedRiemannKernelReal L).mul
        ((continuous_truncatedRiemannKernelReal L).comp (continuous_id.sub continuous_const))
    have hs : HasCompactSupport fun t =>
        truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - y) :=
      (hasCompactSupport_truncatedRiemannKernelReal L).mul_right
    exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs
      (fun t => mul_nonneg (truncatedRiemannKernelReal_nonneg L t)
        (truncatedRiemannKernelReal_nonneg L (t - y)))
      (x := y / 2) (mul_pos ((truncatedRiemannKernelReal_pos_iff L _).mpr hhalf)
        ((truncatedRiemannKernelReal_pos_iff L _).mpr hhalf')).ne'

/-- The first coefficient beyond the panel's index block, at a positive integer window. -/
def weilLogShiftLiftIndex (k : ℕ) : ℕ := ⌊Real.exp (2 * ((k + 1 : ℕ) : ℝ))⌋₊ + 1

/-- The lift coordinate lies beyond all probe indices and inside the visible coefficient block. -/
theorem weilLogShiftLiftIndex_bounds (k : ℕ) :
    2 ≤ weilLogShiftLiftIndex k ∧
    Real.exp (2 * ((k + 1 : ℕ) : ℝ)) < (weilLogShiftLiftIndex k : ℝ) ∧
    (weilLogShiftLiftIndex k : ℝ) < 2 * Real.exp (2 * ((k + 1 : ℕ) : ℝ)) ∧
    (weilLogShiftLiftIndex k : ℝ) ≤ Real.exp (4 * ((k + 1 : ℕ) : ℝ)) := by
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
  have hx : 0 < 2 * ((k + 1 : ℕ) : ℝ) := by linarith only [hk]
  have hE : 2 < Real.exp (2 * ((k + 1 : ℕ) : ℝ)) := by
    have h := Real.add_one_lt_exp hx.ne'
    linarith only [hk, h]
  have hlo : Real.exp (2 * ((k + 1 : ℕ) : ℝ)) < (weilLogShiftLiftIndex k : ℝ) := by
    simpa only [weilLogShiftLiftIndex, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (Real.exp (2 * ((k + 1 : ℕ) : ℝ)))
  have hle : (weilLogShiftLiftIndex k : ℝ) ≤ Real.exp (2 * ((k + 1 : ℕ) : ℝ)) + 1 := by
    dsimp only [weilLogShiftLiftIndex]
    rw [Nat.cast_add, Nat.cast_one]
    have hfloor := Nat.floor_le (Real.exp_pos (2 * ((k + 1 : ℕ) : ℝ))).le
    linarith only [hfloor]
  have hhi : (weilLogShiftLiftIndex k : ℝ) < 2 * Real.exp (2 * ((k + 1 : ℕ) : ℝ)) := by
    linarith only [hle, hE]
  refine ⟨?_, hlo, hhi, ?_⟩
  · exact_mod_cast (show (2 : ℝ) ≤ (weilLogShiftLiftIndex k : ℝ) by linarith only [hE, hlo])
  · rw [show 4 * ((k + 1 : ℕ) : ℝ) =
        2 * ((k + 1 : ℕ) : ℝ) + 2 * ((k + 1 : ℕ) : ℝ) by ring, Real.exp_add]
    nlinarith only [hhi, hE]

/-- Every probe has a strictly negative paired kernel at the same lift coordinate. -/
theorem weilLogShiftLiftIndex_kernel (k : ℕ)
    (m : Finset.Icc 2 ⌊Real.exp (2 * ((k + 1 : ℕ) : ℝ))⌋₊) :
    0 < truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ)
      (Real.log (weilLogShiftLiftIndex k) - Real.log m.1) ∧
    EF.weilTest (logShiftRiemannDifference ((k + 1 : ℕ) : ℝ) (Real.log m.1))
        (logShiftRiemannDifference ((k + 1 : ℕ) : ℝ) (Real.log m.1)) (Real.log (weilLogShiftLiftIndex k)) +
      EF.weilTest (logShiftRiemannDifference ((k + 1 : ℕ) : ℝ) (Real.log m.1))
        (logShiftRiemannDifference ((k + 1 : ℕ) : ℝ) (Real.log m.1)) (-Real.log (weilLogShiftLiftIndex k)) =
      ((-2 * truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ)
        (Real.log (weilLogShiftLiftIndex k) - Real.log m.1) : ℝ) : ℂ) := by
  obtain ⟨hN2, hNlo, hNhi, _⟩ := weilLogShiftLiftIndex_bounds k
  have hNr : (0 : ℝ) < weilLogShiftLiftIndex k := by exact_mod_cast (show 0 < weilLogShiftLiftIndex k by omega)
  have hm2 : (2 : ℝ) ≤ m.1 := by exact_mod_cast (Finset.mem_Icc.mp m.2).1
  have hm0 : (0 : ℝ) < m.1 := by linarith only [hm2]
  have hmE : (m.1 : ℝ) ≤ Real.exp (2 * ((k + 1 : ℕ) : ℝ)) :=
    (by exact_mod_cast (Finset.mem_Icc.mp m.2).2 :
      (m.1 : ℝ) ≤ (⌊Real.exp (2 * ((k + 1 : ℕ) : ℝ))⌋₊ : ℝ)).trans
        (Nat.floor_le (Real.exp_pos _).le)
  have hc0 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hclo := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hm2
  have hchi := Real.log_le_log hm0 hmE
  rw [Real.log_exp] at hchi
  have hylo := Real.log_lt_log (Real.exp_pos _) hNlo
  rw [Real.log_exp] at hylo
  have hyhi := Real.log_lt_log hNr hNhi
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_pos _).ne', Real.log_exp] at hyhi
  have hyc : 0 < Real.log (weilLogShiftLiftIndex k) - Real.log m.1 := by
    linarith only [hylo, hchi]
  have hpos : 0 < truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ)
      (Real.log (weilLogShiftLiftIndex k) - Real.log m.1) := by
    apply (truncatedRiemannAutocorr_pos_iff _ _).mpr
    rw [abs_of_pos hyc]
    linarith only [hyhi, hclo]
  have h0 : truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ) (Real.log (weilLogShiftLiftIndex k)) = 0 := by
    apply truncatedRiemannAutocorr_eq_zero
    exact hylo.le.trans (le_abs_self _)
  have h1 : truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ)
      (Real.log (weilLogShiftLiftIndex k) + Real.log m.1) = 0 := by
    apply truncatedRiemannAutocorr_eq_zero
    have ha := le_abs_self (Real.log (weilLogShiftLiftIndex k) + Real.log m.1)
    linarith only [hylo, hclo, hc0, ha]
  refine ⟨hpos, ?_⟩
  rw [weilTest_logShiftRiemannDifference, weilTest_logShiftRiemannDifference,
    truncatedRiemannAutocorr_neg,
    show -Real.log (weilLogShiftLiftIndex k) + Real.log m.1 =
      -(Real.log (weilLogShiftLiftIndex k) - Real.log m.1) by ring,
    show -Real.log (weilLogShiftLiftIndex k) - Real.log m.1 =
      -(Real.log (weilLogShiftLiftIndex k) + Real.log m.1) by ring,
    truncatedRiemannAutocorr_neg, truncatedRiemannAutocorr_neg, h0, h1]
  push_cast
  ring

/-- Exact complex gain from increasing the single lift coefficient. -/
theorem weilLogShiftWindowPanel_singleSpike (k : ℕ) (lam : ℕ → ℝ) (a : ℝ)
    (m : Finset.Icc 2 ⌊Real.exp (2 * ((k + 1 : ℕ) : ℝ))⌋₊) :
    weilLogShiftWindowPanel (k + 1)
        (fun n => lam n + if n = weilLogShiftLiftIndex k then a else 0) m =
      weilLogShiftWindowPanel (k + 1) lam m +
        ((a * (2 * truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ)
          (Real.log (weilLogShiftLiftIndex k) - Real.log m.1) /
            Real.sqrt (weilLogShiftLiftIndex k)) : ℝ) : ℂ) := by
  let v : ℕ → ℝ := fun n => lam n + if n = weilLogShiftLiftIndex k then a else 0
  let g := EF.weilTest
    (logShiftRiemannDifference ((k + 1 : ℕ) : ℝ) (Real.log m.1))
    (logShiftRiemannDifference ((k + 1 : ℕ) : ℝ) (Real.log m.1))
  have hN := weilLogShiftLiftIndex_bounds k
  have hmem : weilLogShiftLiftIndex k ∈ Finset.Icc 2 ⌊Real.exp (4 * ((k + 1 : ℕ) : ℝ))⌋₊ :=
    Finset.mem_Icc.mpr ⟨hN.1, Nat.le_floor hN.2.2.2⟩
  have hsum : (∑ n ∈ Finset.Icc 2 ⌊Real.exp (4 * ((k + 1 : ℕ) : ℝ))⌋₊,
      (((v n - lam n) / Real.sqrt n : ℝ) : ℂ) *
        (g (Real.log n) + g (-Real.log n))) =
      ((a / Real.sqrt (weilLogShiftLiftIndex k) : ℝ) : ℂ) *
        ((-2 * truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ)
          (Real.log (weilLogShiftLiftIndex k) - Real.log m.1) : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single (weilLogShiftLiftIndex k)]
    · simp only [v, ite_true, add_sub_cancel_left]
      rw [(weilLogShiftLiftIndex_kernel k m).2]
    · intro n _ hn
      simp only [v, if_neg hn, add_zero, sub_self, zero_div, Complex.ofReal_zero, zero_mul]
    · intro hn
      exact False.elim (hn hmem)
  have hdiff := weilLogShiftWindowPanel_sub (k + 1) v lam m
  change weilLogShiftWindowPanel (k + 1) v m - weilLogShiftWindowPanel (k + 1) lam m =
    -∑ n ∈ Finset.Icc 2 ⌊Real.exp (4 * ((k + 1 : ℕ) : ℝ))⌋₊,
      (((v n - lam n) / Real.sqrt n : ℝ) : ℂ) *
        (g (Real.log n) + g (-Real.log n)) at hdiff
  rw [hsum] at hdiff
  change weilLogShiftWindowPanel (k + 1) v m = _
  calc _ = weilLogShiftWindowPanel (k + 1) lam m +
      (weilLogShiftWindowPanel (k + 1) v m - weilLogShiftWindowPanel (k + 1) lam m) := by ring
    _ = _ := by rw [hdiff]; push_cast; ring

/-- Every finite panel at a positive integer window admits a positive one-coordinate
completion above any real height, preserving all coefficients at earlier probe indices. -/
theorem exists_weilLogShiftWindowPanel_positive_completion (k : ℕ) (lam : ℕ → ℝ) (r : ℝ) :
    ∃ a : ℝ, 0 < a ∧
      (∀ n : ℕ, (n : ℝ) ≤ Real.exp (2 * ((k + 1 : ℕ) : ℝ)) →
        lam n + (if n = weilLogShiftLiftIndex k then a else 0) = lam n) ∧
      ∀ m, r < (weilLogShiftWindowPanel (k + 1)
        (fun n => lam n + if n = weilLogShiftLiftIndex k then a else 0) m).re := by
  classical
  let slope (m : Finset.Icc 2 ⌊Real.exp (2 * ((k + 1 : ℕ) : ℝ))⌋₊) : ℝ :=
    2 * truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ)
      (Real.log (weilLogShiftLiftIndex k) - Real.log m.1) / Real.sqrt (weilLogShiftLiftIndex k)
  let cost (m : Finset.Icc 2 ⌊Real.exp (2 * ((k + 1 : ℕ) : ℝ))⌋₊) : ℝ :=
    max ((r - (weilLogShiftWindowPanel (k + 1) lam m).re) / slope m) 0
  let a : ℝ := 1 + ∑ m, cost m
  have hcost (m) : 0 ≤ cost m := le_max_right _ _
  have ha : 0 < a := by
    have hsum : 0 ≤ ∑ m, cost m := Finset.sum_nonneg fun m _ => hcost m
    dsimp only [a]
    linarith only [hsum]
  have hN := weilLogShiftLiftIndex_bounds k
  have hNr : (0 : ℝ) < weilLogShiftLiftIndex k := by
    exact_mod_cast (show 0 < weilLogShiftLiftIndex k by omega)
  have hslope (m) : 0 < slope m :=
    div_pos (mul_pos (by norm_num) (weilLogShiftLiftIndex_kernel k m).1)
      (Real.sqrt_pos.mpr hNr)
  refine ⟨a, ha, ?_, ?_⟩
  · intro n hn
    have hne : n ≠ weilLogShiftLiftIndex k := by
      intro heq
      rw [heq] at hn
      exact (not_le_of_gt hN.2.1) hn
    simp only [if_neg hne, add_zero]
  · intro m
    have hsingle : cost m ≤ ∑ j, cost j :=
      Finset.single_le_sum (fun j _ => hcost j) (Finset.mem_univ m)
    have hratio : (r - (weilLogShiftWindowPanel (k + 1) lam m).re) / slope m < a := by
      have hmax : (r - (weilLogShiftWindowPanel (k + 1) lam m).re) / slope m ≤ cost m :=
        le_max_left _ _
      dsimp only [a]
      linarith only [hsingle, hmax]
    have hgain := congrArg Complex.re (weilLogShiftWindowPanel_singleSpike k lam a m)
    simp only [Complex.add_re, Complex.ofReal_re] at hgain
    have hraise := (div_lt_iff₀ (hslope m)).mp hratio
    change r < (weilLogShiftWindowPanel (k + 1)
      (fun n => lam n + if n = weilLogShiftLiftIndex k then a else 0) m).re
    change r - (weilLogShiftWindowPanel (k + 1) lam m).re <
      a * (2 * truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ)
        (Real.log (weilLogShiftLiftIndex k) - Real.log m.1) /
          Real.sqrt (weilLogShiftLiftIndex k)) at hraise
    linarith only [hgain, hraise]

end RHTower

end
