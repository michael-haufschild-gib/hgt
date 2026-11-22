import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeClassWindow
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.Density.PrimeGallagher

/-! The log-free hybrid mean square for prime-supported Dirichlet polynomials. -/

open Complex MeasureTheory Finset RHTower.Sieve

namespace QH.PrimeProgressions

private theorem mem_logWindow_iff {n : ℕ} (hn : 0 < n) (δ u : ℝ) :
    u ∈ logWindow δ n ↔ Real.exp u < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp u * Real.exp δ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [logWindow, Set.mem_Ico, ← Real.exp_add, Real.lt_log_iff_exp_lt hn',
    ← Real.log_le_iff_le_exp hn', sub_le_iff_le_add, and_comm]

private theorem integral_weighted_logWindow {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) (w : ℝ) :
    (∫ u : ℝ, w * (logWindow δ n).indicator (fun _ => (1 : ℝ)) u) = w * δ := by
  have hvol := volume_real_logWindow_inter δ n n
  rw [Set.inter_self, sub_self, abs_zero, sub_zero, max_eq_left hδ] at hvol
  rw [integral_const_mul, show (fun u : ℝ => (logWindow δ n).indicator (fun _ => (1 : ℝ)) u) =
    (logWindow δ n).indicator 1 from rfl, integral_indicator_one (measurableSet_logWindow δ n), hvol]

/-- Averaging over characters and heights costs only `p/log p` per squared
coefficient once the prime support lies beyond the square of modulus times height. -/
theorem prime_mean_value :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T N y : ℝ) (a : ℕ → ℂ), 1 ≤ T →
      (2 * q * T) ^ 2 ≤ N →
      ∑ χ : DirichletCharacter ℂ q, (∫ t in (-T)..T,
        ‖∑ p ∈ primesIoc N y, a p * χ (p : ZMod q) * (p : ℂ) ^ (-(t * I))‖ ^ 2) ≤
        C * ∑ p ∈ primesIoc N y, (p : ℝ) * ‖a p‖ ^ 2 / Real.log p := by
  obtain ⟨B, hB, hBT⟩ := brun_titchmarsh_const
  refine ⟨16 * Real.pi * B, by positivity, ?_⟩
  intro q _ T N y a hT hN
  have hT₀ : 0 < T := zero_lt_one.trans_le hT
  let δ : ℝ := 1 / T
  have hδ : 0 ≤ δ := (one_div_pos.mpr hT₀).le
  let P := primesIoc N y
  have hN₀ : 0 ≤ N := (sq_nonneg _).trans hN
  have hmem (p : ℕ) (hp : p ∈ P) : N < p ∧ (p : ℝ) ≤ y ∧ p.Prime :=
    (mem_primesIoc hN₀).mp hp
  have hpos (p : ℕ) (hp : p ∈ P) : 0 < p := (hmem p hp).2.2.pos
  let aχ (χ : DirichletCharacter ℂ q) (p : ℕ) := a p * χ (p : ZMod q)
  let F (χ : DirichletCharacter ℂ q) (u : ℝ) := ‖logWindowSum (aχ χ) P δ u‖ ^ 2
  let w (p : ℕ) : ℝ := 4 * B * p / (T * Real.log p) * ‖a p‖ ^ 2
  let H (u : ℝ) := ∑ p ∈ P, w p * (logWindow δ p).indicator (fun _ => (1 : ℝ)) u
  have hF (χ : DirichletCharacter ℂ q) : Integrable (F χ) :=
    integrable_normSq_logWindowSum (aχ χ) P δ
  have hterm (p : ℕ) : Integrable (fun u : ℝ =>
      w p * (logWindow δ p).indicator (fun _ => (1 : ℝ)) u) := by
    simpa only [Set.inter_self] using integrable_indicator_logWindow_inter δ p p (w p)
  have hpoint (u : ℝ) : ∑ χ : DirichletCharacter ℂ q, F χ u ≤ H u := by
    classical
    let x := Real.exp u
    have hx : 0 < x := Real.exp_pos u
    let S := P.filter (fun p : ℕ => x < (p : ℝ) ∧ (p : ℝ) ≤ x * Real.exp δ)
    have hS (p : ℕ) (hp : p ∈ S) :
        p.Prime ∧ N < p ∧ x < p ∧ (p : ℝ) ≤ x * Real.exp (1 / T) := by
      obtain ⟨hpP, hpx, hpy⟩ := mem_filter.mp hp
      obtain ⟨hpN, _, hprime⟩ := hmem p hpP
      exact ⟨hprime, hpN, hpx, hpy⟩
    have heq (χ : DirichletCharacter ℂ q) : F χ u = ‖∑ p ∈ S, aχ χ p‖ ^ 2 := by
      dsimp only [F, S]
      rw [← logWindowSum_log (aχ χ) P hpos δ hx, Real.log_exp]
    simp_rw [heq]
    refine (prime_class_window B hB hBT q T N x a S hT hN hx hS).trans_eq ?_
    change ∑ p ∈ S, w p = _
    dsimp only [S, H]
    rw [sum_filter]
    refine sum_congr rfl fun p hp => ?_
    have he : u ∈ logWindow δ p ↔ x < (p : ℝ) ∧ (p : ℝ) ≤ x * Real.exp δ :=
      mem_logWindow_iff (hpos p hp) δ u
    rw [Set.indicator_apply]
    simp only [he, mul_ite, mul_one, mul_zero]
  have hbound : ∑ χ : DirichletCharacter ℂ q, ∫ u : ℝ, F χ u ≤ δ * ∑ p ∈ P, w p := by
    rw [← integral_finsetSum _ (fun χ _ => hF χ)]
    refine (integral_mono (integrable_finsetSum _ (fun χ _ => hF χ))
      (integrable_finsetSum P (fun p _ => hterm p)) hpoint).trans_eq ?_
    rw [integral_finsetSum P (fun p _ => hterm p), mul_sum]
    exact sum_congr rfl fun p _ => (integral_weighted_logWindow hδ p (w p)).trans (mul_comm _ _)
  have hspec (χ : DirichletCharacter ℂ q) :=
    prime_gallagher_mean (aχ χ) P hpos hT₀
  refine (sum_le_sum (fun χ _ => hspec χ)).trans ?_
  rw [← mul_sum]
  refine (mul_le_mul_of_nonneg_left hbound (show 0 ≤ 4 * Real.pi * T ^ 2 by positivity)).trans_eq ?_
  rw [← mul_assoc (4 * Real.pi * T ^ 2) δ, mul_sum, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  have hlog := Real.log_pos (show (1 : ℝ) < p by exact_mod_cast (hmem p hp).2.2.one_lt)
  dsimp only [w, δ]
  field_simp [hT₀.ne', hlog.ne']
  <;> ring

end QH.PrimeProgressions
