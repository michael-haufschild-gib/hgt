import GaloisForLFunctions.RHTower.Sieve.LinearWindowMeasurable
import GaloisForLFunctions.RHTower.Sieve.GallagherRange

/-!
# The block estimate for linear windows

On a block `Y < x ≤ Y(1+ε)` the multiplicative window of ratio `1 + L/Y` has length
`xL/Y ∈ [L, (1+ε)L]`, so it contains the linear window `(x, x+L]` and exceeds it by at most `εL`
integers.  Integrating the pointwise transfer over the block and bounding the multiplicative mean
square by Gallagher's split bound gives

    ∫ |∑_{e^u < n ≤ e^u + L} a_n|² du ≤ 2(M₁δ + M₂·2/(π²W)) + 2(εL+1)²·|block| ,

with `δ = log(1 + L/Y)`.  Every ingredient is a proved unconditional theorem; nothing analytic is
added here.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- The pointwise transfer on a block, in window-sum form. -/
theorem normSq_linWindowSum_le_logWindowSum (a : ℕ → ℂ) (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ 1) {L Y ε u : ℝ} (hL : 0 ≤ L) (hY : 0 < Y) (hε : 0 ≤ ε)
    (hu₁ : Real.log Y < u) (hu₂ : u ≤ Real.log (Y * (1 + ε))) :
    ‖linWindowSum a s L u‖ ^ 2
      ≤ 2 * ‖logWindowSum a s (Real.log (1 + L / Y)) u‖ ^ 2 + 2 * (ε * L + 1) ^ 2 := by
  classical
  set δ : ℝ := Real.log (1 + L / Y) with hδdef
  have hratio : (0 : ℝ) < 1 + L / Y := by positivity
  have hexpδ : Real.exp δ = 1 + L / Y := Real.exp_log hratio
  set x : ℝ := Real.exp u with hxdef
  have hx0 : (0 : ℝ) < x := Real.exp_pos u
  have hxY : Y < x := by
    rw [hxdef, ← Real.exp_log hY]
    exact Real.exp_lt_exp.2 hu₁
  have hxup : x ≤ Y * (1 + ε) := by
    have hpos : (0 : ℝ) < Y * (1 + ε) := by positivity
    rw [hxdef, ← Real.exp_log hpos]
    exact Real.exp_le_exp.2 hu₂
  -- the multiplicative window contains the linear one
  have hy : x * Real.exp δ = x + x * L / Y := by
    rw [hexpδ]
    field_simp
  have hle : x + L ≤ x * Real.exp δ := by
    rw [hy]
    have : L ≤ x * L / Y := by
      rw [le_div_iff₀ hY]
      nlinarith [hxY.le, hL]
    linarith
  have hexcess : x * Real.exp δ - (x + L) ≤ ε * L := by
    rw [hy]
    have : x * L / Y ≤ (1 + ε) * L := by
      rw [div_le_iff₀ hY]
      nlinarith [hxup, hL]
    linarith
  -- rewrite both sides as window sums
  have hlin := linWindowSum_eq a s L u
  have hlog : logWindowSum a s δ u
      = ∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x * Real.exp δ), a n := by
    have h := logWindowSum_log a s hs δ hx0
    rwa [hxdef, Real.log_exp] at h
  rw [hlin, hlog]
  refine le_trans (normSq_linear_le_multiplicative_length a s ha hx0.le hL hle) ?_
  have hsq : (x * Real.exp δ - (x + L) + 1) ^ 2 ≤ (ε * L + 1) ^ 2 := by
    have h0 : (0 : ℝ) ≤ x * Real.exp δ - (x + L) + 1 := by linarith
    nlinarith [hexcess, h0]
  linarith

/-- **The block estimate.**  On a block of ratio `1+ε` the linear-window mean square is controlled by
Gallagher's split bound plus the trivial cost of the excess. -/
theorem setIntegral_normSq_linWindowSum_block_le (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n) (ha : ∀ n : ℕ, ‖a n‖ ≤ 1)
    {L Y ε M₁ M₂ W : ℝ} (hL : 0 < L) (hY : 0 < Y) (hε : 0 ≤ ε) (hW : 0 < W)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (h₁ : ∀ w ∈ Set.Icc (-W) W, ‖logPoly a s w‖ ^ 2 ≤ M₁)
    (h₂ : ∀ w : ℝ, ‖logPoly a s w‖ ^ 2 ≤ M₂) :
    (∫ u in Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε))), ‖linWindowSum a s L u‖ ^ 2)
      ≤ 2 * (M₁ * Real.log (1 + L / Y) + M₂ * (2 / (Real.pi ^ 2 * W)))
        + 2 * (ε * L + 1) ^ 2
            * volume.real (Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε)))) := by
  classical
  set δ : ℝ := Real.log (1 + L / Y) with hδdef
  set E : Set ℝ := Set.Ioc (Real.log Y) (Real.log (Y * (1 + ε))) with hEdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    refine Real.log_pos ?_
    have : 0 < L / Y := by positivity
    linarith
  have hEfin : volume E ≠ ⊤ := by
    rw [hEdef]
    simp
  have hLHS : IntegrableOn (fun u : ℝ => ‖linWindowSum a s L u‖ ^ 2) E :=
    integrableOn_normSq_linWindowSum a s L hEfin
  have hRHS : IntegrableOn
      (fun u : ℝ => 2 * ‖logWindowSum a s δ u‖ ^ 2 + 2 * (ε * L + 1) ^ 2) E := by
    refine Integrable.add ?_ (integrableOn_const hEfin (by finiteness))
    exact ((integrable_normSq_logWindowSum a s δ).const_mul 2).integrableOn
  have hstep : (∫ u in E, ‖linWindowSum a s L u‖ ^ 2)
      ≤ ∫ u in E, (2 * ‖logWindowSum a s δ u‖ ^ 2 + 2 * (ε * L + 1) ^ 2) := by
    refine setIntegral_mono_on hLHS hRHS measurableSet_Ioc fun u hu => ?_
    rw [hEdef, Set.mem_Ioc] at hu
    exact normSq_linWindowSum_le_logWindowSum a s hs ha hL.le hY hε hu.1 hu.2
  refine le_trans hstep ?_
  rw [MeasureTheory.integral_add
    (((integrable_normSq_logWindowSum a s δ).const_mul 2).integrableOn)
    (integrableOn_const hEfin (by finiteness)), integral_const_mul, setIntegral_const, smul_eq_mul]
  have hmass : (∫ u in E, ‖logWindowSum a s δ u‖ ^ 2)
      ≤ M₁ * δ + M₂ * (2 / (Real.pi ^ 2 * W)) :=
    setIntegral_normSq_logWindowSum_le a s hδ0 hW hM₁ hM₂ h₁ h₂ E
  have hvol : (0 : ℝ) ≤ volume.real E := measureReal_nonneg
  nlinarith [hmass, hvol, sq_nonneg (ε * L + 1)]

end RHTower.Sieve
