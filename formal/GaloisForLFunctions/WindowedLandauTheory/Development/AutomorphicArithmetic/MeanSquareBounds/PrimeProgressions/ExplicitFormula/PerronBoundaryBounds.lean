import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.WideZeroLocations

/-! The local zero sum bounds the logarithmic derivative on zero-free contour segments. -/

open Complex DirichletCharacter Finset Metric

open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

theorem mem_entireCharacterL_eval_disc {s : ℂ} (h₀ : -(1 / 2 : ℝ) ≤ s.re) (h₁ : s.re ≤ 3) :
    s ∈ closedBall (2 + s.im * I) (51 / 20) := by
  have e : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [mem_closedBall, Complex.dist_eq, e, norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith only [h₀], by linarith only [h₁]⟩

theorem norm_sum_order_div_sub_le {f : ℂ → ℂ} {Z : Finset ℂ} {s : ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤
      (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) / δ := by
  refine (norm_sum_le _ _).trans ?_
  rw [sum_div]
  exact sum_le_sum fun ρ hρ => by
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hδ (hd ρ hρ)

theorem norm_logDeriv_le_of_local_zero_separation {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {s : ℂ} {C δ : ℝ}
    (hδ : 0 < δ) (hs : s ∈ closedBall (2 + s.im * I) (51 / 20))
    {Z : Finset ℂ}
    (hZ : (Z : Set ℂ) = {ρ ∈ closedBall (2 + s.im * I) (341 / 125) | entireCharacterL χ ρ = 0})
    (hm : (∑ ρ ∈ Z, (analyticOrderNatAt (entireCharacterL χ) ρ : ℝ)) ≤ C)
    (hpf : entireCharacterL χ s ≠ 0 →
      ‖logDeriv (entireCharacterL χ) s -
        ∑ ρ ∈ Z, (analyticOrderNatAt (entireCharacterL χ) ρ : ℂ) / (s - ρ)‖ ≤ C)
    (hsep : ∀ ρ ∈ Z, δ ≤ ‖s - ρ‖) :
    entireCharacterL χ s ≠ 0 ∧ ‖logDeriv (entireCharacterL χ) s‖ ≤ C + C / δ := by
  have hne : entireCharacterL χ s ≠ 0 := by
    intro hz
    have hmem : s ∈ (Z : Set ℂ) := by
      rw [hZ]
      exact ⟨closedBall_subset_closedBall (by norm_num) hs, hz⟩
    have h := hsep s hmem
    rw [sub_self, norm_zero] at h
    exact hδ.not_ge h
  refine ⟨hne, ?_⟩
  let W := ∑ ρ ∈ Z, (analyticOrderNatAt (entireCharacterL χ) ρ : ℂ) / (s - ρ)
  calc
    ‖logDeriv (entireCharacterL χ) s‖ ≤ ‖logDeriv (entireCharacterL χ) s - W‖ + ‖W‖ := by
      simpa only [sub_add_cancel] using norm_add_le (logDeriv (entireCharacterL χ) s - W) W
    _ ≤ _ := add_le_add (hpf hne)
      ((norm_sum_order_div_sub_le hδ hsep).trans (div_le_div_of_nonneg_right hm hδ.le))

/-- The left edge stays separated by one half from all zeros in the local expansion. -/
theorem primitive_logDeriv_left_edge :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, s.re = -(1 / 2 : ℝ) →
      χ.LFunction s ≠ 0 ∧ ‖logDeriv χ.LFunction s‖ ≤ C * Real.log ((N : ℝ) * (|s.im| + 2)) := by
  obtain ⟨C, hC, H⟩ := entireCharacterL_partial_fraction
  refine ⟨3 * C + 2, by positivity, ?_⟩
  intro N _ χ hχ s hr
  let L := Real.log ((N : ℝ) * (|s.im| + 2))
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hL : (1 / 2 : ℝ) ≤ L :=
    (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) ((by linarith only [abs_nonneg s.im] : (2 : ℝ) ≤ |s.im| + 2).trans
        (le_mul_of_one_le_left (by positivity) hN)))
  have hs := mem_entireCharacterL_eval_disc hr.ge (hr.le.trans (by norm_num))
  obtain ⟨Z, hZ, hmass, hpf⟩ := H N χ s.im
  have hsep : ∀ ρ ∈ Z, (1 / 2 : ℝ) ≤ ‖s - ρ‖ := by
    intro ρ hρ
    change ρ ∈ (Z : Set ℂ) at hρ
    rw [hZ] at hρ
    have hreal : 0 ≤ ρ.re := by
      rcases entireCharacterL_zero_mem_strip_or_zero hχ hρ.1 hρ.2 with h | rfl
      · exact h.1.le
      · simp
    refine le_trans ?_ ((neg_le_abs _).trans (abs_re_le_norm (s - ρ)))
    rw [sub_re, hr]
    linarith only [hreal]
  obtain ⟨hf, hd⟩ := norm_logDeriv_le_of_local_zero_separation (by norm_num) hs hZ hmass (hpf s hs) hsep
  have hs₁ : s ≠ 1 := by
    intro e
    norm_num [e] at hr
  have hzero : χ.LFunction s ≠ 0 := fun h => hf ((entireCharacterL_eq_zero_iff hs₁).mpr h)
  refine ⟨hzero, ?_⟩
  have hd' : ‖logDeriv (entireCharacterL χ) s‖ ≤ 3 * (C * L) := hd.trans_eq (by ring)
  have hp : ‖if χ = 1 then 1 / (s - 1) else (0 : ℂ)‖ ≤ 1 := by
    split_ifs
    · have h := (neg_le_abs (s - 1).re).trans (abs_re_le_norm (s - 1))
      rw [sub_re, hr, one_re] at h
      have h₁ : 1 ≤ ‖s - 1‖ := by linarith only [h]
      rw [norm_div, norm_one, div_le_one (zero_lt_one.trans_le h₁)]
      exact h₁
    · simp
  calc
    ‖logDeriv χ.LFunction s‖ =
        ‖logDeriv (entireCharacterL χ) s - if χ = 1 then 1 / (s - 1) else 0‖ := by
      rw [logDeriv_entireCharacterL hs₁ hzero, add_sub_cancel_right]
    _ ≤ 3 * (C * L) + 1 := (norm_sub_le _ _).trans (add_le_add hd' hp)
    _ ≤ (3 * C + 2) * L := by linarith only [hL]

end QH.PrimeProgressions
