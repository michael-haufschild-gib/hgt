import GaloisForLFunctions.RHTower.PrimeBlindCarlsonThreshold

/-!
# Uniqueness from the prime logarithms

A holomorphic function on the right half-plane, bounded on each smaller
right half-plane, is determined by its values at the logarithms of the
actual primes. Composing with `log (z + 2)` reduces this to the divergent
prime reciprocal zero criterion; analytic continuation removes the shift.
-/

noncomputable section
open Set Complex

namespace RHTower.PrimeBlindCarlson

private theorem shiftedPrimes_not_summable :
    ¬ Summable ({n : ℕ | 2 ≤ n ∧ (n + 2).Prime}.indicator
      fun n : ℕ => (1 : ℝ) / n) := by
  classical
  intro hs
  apply not_summable_one_div_on_primes
  rw [← summable_nat_add_iff 2]
  have hfin : Summable fun n : ℕ => if n < 2 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := Finset.range 2) fun n hn => by
      rw [Finset.mem_range] at hn
      simp [hn]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hs.add hfin)
  · by_cases hn : (n + 2).Prime
    · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hn]; positivity
    · simp [hn]
  · by_cases h2 : n < 2
    · have h1 : {p : ℕ | p.Prime}.indicator (fun n : ℕ => (1 : ℝ) / n) (n + 2) ≤ 1 := by
        by_cases hn : (n + 2).Prime
        · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hn]
          rw [div_le_one (by positivity)]; push_cast; linarith
        · simp [hn]
      have h0 : 0 ≤ {n : ℕ | 2 ≤ n ∧ (n + 2).Prime}.indicator
          (fun n : ℕ => (1 : ℝ) / n) n := by
        by_cases hn : 2 ≤ n ∧ (n + 2).Prime
        · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hn]; positivity
        · simp [hn]
      simp only [h2, if_true]
      linarith
    · have hn2 : 2 ≤ n := by omega
      by_cases hn : (n + 2).Prime
      · simp only [Set.indicator, Set.mem_setOf_eq, if_pos hn, if_pos (show 2 ≤ n ∧ (n + 2).Prime from ⟨hn2, hn⟩)]
        simp only [h2, if_false, add_zero]
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn2
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        push_cast
        linarith
      · simp [hn, h2]

/-- Prime logarithms determine a holomorphic function bounded on each smaller
right half-plane. -/
theorem eqOn_zero_of_primeLog_zeros {H : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H rightHalf)
    (hb : ∀ δ : ℝ, 0 < δ → ∃ M : ℝ, ∀ z : ℂ, δ ≤ z.re → ‖H z‖ ≤ M)
    (hz : ∀ p : ℕ, p.Prime → H (Real.log p) = 0) : EqOn H 0 rightHalf := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hre : ∀ ξ ∈ rightHalf, Real.log 2 ≤ (Complex.log (ξ + 2)).re := by
    intro ξ hξ
    rw [Complex.log_re]
    apply Real.log_le_log (by norm_num)
    calc (2 : ℝ) ≤ (ξ + 2).re := by
          have : 0 < ξ.re := hξ
          change (2 : ℝ) ≤ ξ.re + 2
          linarith
      _ ≤ ‖ξ + 2‖ := Complex.re_le_norm _
  have hmap : ∀ ξ ∈ rightHalf, Complex.log (ξ + 2) ∈ rightHalf :=
    fun ξ hξ => hlog2.trans_le (hre ξ hξ)
  let G : ℂ → ℂ := fun ξ => H (Complex.log (ξ + 2))
  have hG : AnalyticOnNhd ℂ G rightHalf := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_rightHalf
    intro ξ hξ
    have hslit : ξ + 2 ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      have : 0 < ξ.re := hξ
      change (0 : ℝ) < ξ.re + 2
      linarith
    exact ((hH _ (hmap ξ hξ)).differentiableAt.comp ξ
      ((differentiableAt_id.add_const (2 : ℂ)).clog hslit)).differentiableWithinAt
  obtain ⟨M, hM⟩ := hb (Real.log 2) hlog2
  have hGb : ∀ ξ ∈ rightHalf, ‖G ξ‖ ≤ M := fun ξ hξ => hM _ (hre ξ hξ)
  have hGz : ∀ n ∈ {n : ℕ | 2 ≤ n ∧ (n + 2).Prime}, G n = 0 := by
    intro n hn
    change H (Complex.log ((n : ℂ) + 2)) = 0
    have hcast : (n : ℂ) + 2 = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_log (by positivity)]
    exact hz (n + 2) hn.2
  have hG0 := eqOn_zero_of_halfPlane_zeros hG hGb
    (fun n hn => hn.1) shiftedPrimes_not_summable hGz
  have hray : ∀ x : ℝ, Real.log 2 < x → H (x : ℂ) = 0 := by
    intro x hx
    have hex : 2 < Real.exp x := by
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_lt_exp.mpr hx
    have hξ : ((Real.exp x - 2 : ℝ) : ℂ) ∈ rightHalf := by
      change 0 < Real.exp x - 2
      linarith
    have hzero := hG0 hξ
    change H (Complex.log (((Real.exp x - 2 : ℝ) : ℂ) + 2)) = 0 at hzero
    have hcast : (((Real.exp x - 2 : ℝ) : ℂ) + 2) = (Real.exp x : ℝ) := by push_cast; ring
    rw [hcast, ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp] at hzero
    exact hzero
  apply hH.eqOn_zero_of_preconnected_of_mem_closure isPreconnected_rightHalf
    (z₀ := ((Real.log 2 + 1 : ℝ) : ℂ)) (by change 0 < Real.log 2 + 1; linarith)
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((Real.log 2 + 1 + ε / 2 : ℝ) : ℂ), ⟨hray _ (by linarith), ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff, Complex.ofReal_inj]
    linarith
  · rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hval : Real.log 2 + 1 - (Real.log 2 + 1 + ε / 2) = -(ε / 2) := by ring
    rw [hval, abs_neg, abs_of_pos (by positivity)]
    linarith

end RHTower.PrimeBlindCarlson
