import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity

/-!
# Finite coefficient blocks detect log-shift deficits

The log-shift probes in integer window `k` depend only on coefficients through `exp (4k)`.
Replacing the remaining coefficients by von Mangoldt preserves the entire finite complex
probe panel. The uniform minorant separator therefore needs a minorant bound only on that
finite block; the tail can be arbitrary.

Conversely, a nonnegative finite panel with a prescribed coefficient deficit must contain
a compensating coefficient excess within the same finite block. No full Weil positivity,
tail growth condition or RH premise enters these statements.
-/

open Set Zeta23

noncomputable section

namespace RHTower

/-- Retain the visible coefficient block and complete its tail by von Mangoldt. -/
def weilLogShiftWindowCompletion (windowIndex : ℕ) (lam : ℕ → ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ)) then lam n
  else (ArithmeticFunction.vonMangoldt n : ℝ)

/-- The finite complex probe panel at one integer window. -/
def weilLogShiftWindowPanel (windowIndex : ℕ) (lam : ℕ → ℝ) :
    (Finset.Icc 2 ⌊Real.exp (2 * (windowIndex : ℝ))⌋₊) → ℂ :=
  fun m => weilFullFunctional lam (EF.weilTest
    (logShiftRiemannDifference windowIndex (Real.log m.1))
    (logShiftRiemannDifference windowIndex (Real.log m.1)))

/-- The full finite panel is unchanged by replacing its invisible coefficient tail. -/
theorem weilLogShiftWindowPanel_completion (windowIndex : ℕ) (lam : ℕ → ℝ) :
    weilLogShiftWindowPanel windowIndex (weilLogShiftWindowCompletion windowIndex lam) =
      weilLogShiftWindowPanel windowIndex lam := by
  funext m
  let c := Real.log (m.1 : ℝ)
  let f := logShiftRiemannDifference windowIndex c
  have hm2 : 2 ≤ m.1 := (Finset.mem_Icc.mp m.2).1
  have hmN : m.1 ≤ ⌊Real.exp (2 * (windowIndex : ℝ))⌋₊ :=
    (Finset.mem_Icc.mp m.2).2
  have hmR : (1 : ℝ) < m.1 := by exact_mod_cast (show 1 < m.1 by omega)
  have hc0 : 0 ≤ c := (Real.log_pos hmR).le
  have hcL : c ≤ 2 * (windowIndex : ℝ) := by
    change Real.log (m.1 : ℝ) ≤ 2 * (windowIndex : ℝ)
    rw [Real.log_le_iff_le_exp (by linarith)]
    calc (m.1 : ℝ) ≤ (⌊Real.exp (2 * (windowIndex : ℝ))⌋₊ : ℝ) := by
          exact_mod_cast hmN
      _ ≤ Real.exp (2 * (windowIndex : ℝ)) := Nat.floor_le (Real.exp_pos _).le
  have hL0 : 0 ≤ (windowIndex : ℝ) := by positivity
  have hzero : ∀ y : ℝ, 4 * (windowIndex : ℝ) ≤ |y| → EF.weilTest f f y = 0 := by
    intro y hy
    have ha : |y| ≤ |y + c| + c := by
      calc |y| = |(y + c) - c| := by congr 1; ring
        _ ≤ |y + c| + |c| := abs_sub _ _
        _ = |y + c| + c := by rw [abs_of_nonneg hc0]
    have hb : |y| ≤ |y - c| + c := by
      calc |y| = |(y - c) - (-c)| := by congr 1; ring
        _ ≤ |y - c| + |-c| := abs_sub _ _
        _ = |y - c| + c := by rw [abs_neg, abs_of_nonneg hc0]
    have h0 : 2 * (windowIndex : ℝ) ≤ |y| := by linarith only [hy, hL0]
    have h1 : 2 * (windowIndex : ℝ) ≤ |y + c| := by linarith only [hy, ha, hcL]
    have h2 : 2 * (windowIndex : ℝ) ≤ |y - c| := by linarith only [hy, hb, hcL]
    simp [f, weilTest_logShiftRiemannDifference,
      truncatedRiemannAutocorr_eq_zero h0, truncatedRiemannAutocorr_eq_zero h1,
      truncatedRiemannAutocorr_eq_zero h2]
  change weilFullFunctional (weilLogShiftWindowCompletion windowIndex lam) (EF.weilTest f f) =
    weilFullFunctional lam (EF.weilTest f f)
  unfold weilFullFunctional
  congr 3
  funext n
  by_cases hn : 2 ≤ n
  · rw [if_pos hn, if_pos hn]
    by_cases hb : (n : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ))
    · simp only [weilLogShiftWindowCompletion, if_pos hb]
    · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hlog : 4 * (windowIndex : ℝ) < Real.log n := by
        apply Real.exp_lt_exp.mp
        rw [Real.exp_log hnR]
        exact lt_of_not_ge hb
      have habs : 4 * (windowIndex : ℝ) ≤ |Real.log n| :=
        hlog.le.trans (le_abs_self _)
      have hz := hzero (Real.log n) habs
      have hzn := hzero (-Real.log n) (by simpa only [abs_neg] using habs)
      simp only [hz, hzn, add_zero, mul_zero]
  · rw [if_neg hn, if_neg hn]

/-- A finite coefficient minorant block suffices for uniform negative-margin separation;
all coefficients outside the block are unrestricted. -/
theorem exists_uniform_finiteBlock_logShift_separation (q : ℕ) (t : ℝ) :
    ∃ cutoff : ℕ, ∀ windowIndex : ℕ, cutoff ≤ windowIndex →
      {lam : ℕ → ℝ |
        (∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ)) →
          lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
        Real.exp t ≤ ((ArithmeticFunction.vonMangoldt (q + 2) : ℝ) - lam (q + 2)) /
          Real.sqrt ((q + 2 : ℕ) : ℝ)} ⊆
      {lam | ∃ m : ℕ, 2 ≤ m ∧ (m : ℝ) ≤ Real.exp (2 * (windowIndex : ℝ)) ∧
        (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference windowIndex (Real.log m))
          (logShiftRiemannDifference windowIndex (Real.log m)))).re ≤
            -(Real.exp t * riemannAutocorr 0) / 25} := by
  obtain ⟨K, hK⟩ := exists_uniform_logShift_minorant_separation q t
  refine ⟨max K ⌈Real.log ((q + 2 : ℕ) : ℝ) / 4⌉₊, ?_⟩
  rintro windowIndex hk lam ⟨hblock, hgap⟩
  have hkGlobal : K ≤ windowIndex := le_trans (le_max_left _ _) hk
  have hkLocal : ⌈Real.log ((q + 2 : ℕ) : ℝ) / 4⌉₊ ≤ windowIndex :=
    le_trans (le_max_right _ _) hk
  have hkLocalR : (⌈Real.log ((q + 2 : ℕ) : ℝ) / 4⌉₊ : ℝ) ≤
      (windowIndex : ℝ) := by exact_mod_cast hkLocal
  have hlog : Real.log ((q + 2 : ℕ) : ℝ) / 4 ≤ (windowIndex : ℝ) :=
    le_trans (Nat.le_ceil _) hkLocalR
  have hn0 : (0 : ℝ) < ((q + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < q + 2 by omega)
  have hb0 : ((q + 2 : ℕ) : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ)) := by
    calc ((q + 2 : ℕ) : ℝ) = Real.exp (Real.log ((q + 2 : ℕ) : ℝ)) :=
          (Real.exp_log hn0).symm
      _ ≤ Real.exp (4 * (windowIndex : ℝ)) := Real.exp_le_exp.mpr (by linarith)
  let completed := weilLogShiftWindowCompletion windowIndex lam
  have hglobal : ∀ n : ℕ, 2 ≤ n → completed n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
    intro n hn
    dsimp only [completed, weilLogShiftWindowCompletion]
    split_ifs with hb
    · exact hblock n hn hb
    · exact le_rfl
  have hgap' : Real.exp t ≤
      ((ArithmeticFunction.vonMangoldt (q + 2) : ℝ) - completed (q + 2)) /
        Real.sqrt ((q + 2 : ℕ) : ℝ) := by
    simpa only [completed, weilLogShiftWindowCompletion, if_pos hb0] using hgap
  obtain ⟨m, hm2, hmBound, htest⟩ := hK windowIndex hkGlobal ⟨hglobal, hgap'⟩
  have hm : m ∈ Finset.Icc 2 ⌊Real.exp (2 * (windowIndex : ℝ))⌋₊ :=
    Finset.mem_Icc.mpr ⟨hm2, Nat.le_floor hmBound⟩
  have heq : weilFullFunctional completed (EF.weilTest
      (logShiftRiemannDifference windowIndex (Real.log m))
      (logShiftRiemannDifference windowIndex (Real.log m))) =
      weilFullFunctional lam (EF.weilTest
        (logShiftRiemannDifference windowIndex (Real.log m))
        (logShiftRiemannDifference windowIndex (Real.log m))) :=
    congrFun (weilLogShiftWindowPanel_completion windowIndex lam) ⟨m, hm⟩
  refine ⟨m, hm2, hmBound, ?_⟩
  rwa [heq] at htest

/-- A prescribed deficit in a nonnegative finite probe panel forces a coefficient excess
inside the same visible block, uniformly beyond one cutoff. -/
theorem exists_uniform_finiteBlock_excess_of_deficit (q : ℕ) (t : ℝ) :
    ∃ cutoff : ℕ, ∀ windowIndex : ℕ, cutoff ≤ windowIndex →
      {lam : ℕ → ℝ |
        (∀ m, 0 ≤ (weilLogShiftWindowPanel windowIndex lam m).re) ∧
        Real.exp t ≤ ((ArithmeticFunction.vonMangoldt (q + 2) : ℝ) - lam (q + 2)) /
          Real.sqrt ((q + 2 : ℕ) : ℝ)} ⊆
      {lam | ∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ)) ∧
        (ArithmeticFunction.vonMangoldt n : ℝ) < lam n} := by
  obtain ⟨cutoff, hcutoff⟩ := exists_uniform_finiteBlock_logShift_separation q t
  refine ⟨cutoff, ?_⟩
  rintro windowIndex hk lam ⟨hpos, hgap⟩
  change ∃ n : ℕ, 2 ≤ n ∧ (n : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ)) ∧
    (ArithmeticFunction.vonMangoldt n : ℝ) < lam n
  by_contra hnone
  have hblock : ∀ n : ℕ, 2 ≤ n → (n : ℝ) ≤ Real.exp (4 * (windowIndex : ℝ)) →
      lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
    intro n hn hb
    by_contra h
    exact hnone ⟨n, hn, hb, lt_of_not_ge h⟩
  obtain ⟨m, hm2, hmBound, htest⟩ := hcutoff windowIndex hk ⟨hblock, hgap⟩
  have hm : m ∈ Finset.Icc 2 ⌊Real.exp (2 * (windowIndex : ℝ))⌋₊ :=
    Finset.mem_Icc.mpr ⟨hm2, Nat.le_floor hmBound⟩
  have hnonneg := hpos ⟨m, hm⟩
  change 0 ≤ (weilFullFunctional lam (EF.weilTest
    (logShiftRiemannDifference windowIndex (Real.log m))
    (logShiftRiemannDifference windowIndex (Real.log m)))).re at hnonneg
  have hC := riemannAutocorr_zero_pos
  have hmargin : 0 < Real.exp t * riemannAutocorr 0 := by positivity
  linarith only [hnonneg, htest, hmargin]

end RHTower

end
