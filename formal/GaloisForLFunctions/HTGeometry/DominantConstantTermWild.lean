import GaloisForLFunctions.HTGeometry.AutonomousExponentDichotomy

/-!
# A dominant constant term forces the wild branch everywhere

If the coefficient of `W^(0 : ℕ)` carries strictly more total degree than every other coefficient,

```text
deg C_k + k < deg C_0    for every  1 ≤ k ≤ m,
```

then the tame alternative `‖W‖ ≤ K‖Y‖` is impossible once `‖Y‖` is large: it would bound
`‖C_0(Y)‖ ≍ ‖Y‖^{deg C_0}` by a constant multiple of `‖Y‖^{deg C_0 - 1}`.  Combined with the exponent
dichotomy, the wild bound `c‖Y‖^{m+1} ≤ ‖W‖^m` then holds at *every* point where `‖Y‖` is large,
which is what the proximity argument consumes.

This is the Newton-polygon case the formalized Gol'dberg theorem does not cover, since its top symbol
is required to carry a positive power of the derivative.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 1000000 in
/-- **A dominant constant term excludes the tame alternative.** -/
theorem exists_not_tame_of_dominant_constant_term {m : ℕ} (hm : 1 ≤ m) {C : ℕ → Polynomial ℂ}
    (hC0 : C 0 ≠ 0)
    (hdom : ∀ k, 1 ≤ k → k ≤ m → (C k).natDegree + k + 1 ≤ (C 0).natDegree)
    {Y W : ℂ → ℂ}
    (hrel : ∀ z : ℂ, ∑ k ∈ Finset.range (m + 1), (C k).eval (Y z) * (W z) ^ k = 0)
    {K : ℝ} (hK : 0 < K) :
    ∃ R₂ : ℝ, 1 ≤ R₂ ∧ ∀ z : ℂ, R₂ ≤ ‖Y z‖ → ¬ (‖W z‖ ≤ K * ‖Y z‖) := by
  classical
  obtain ⟨R', hR'1, hlow⟩ := exists_le_norm_eval (C 0) hC0
  set d₀ : ℕ := (C 0).natDegree with hd₀
  set L : ℝ := ‖(C 0).leadingCoeff‖ / 2 with hL
  have hL0 : 0 < L := by
    rw [hL]
    have : 0 < ‖(C 0).leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hC0)
    linarith
  set Bsum : ℝ := ∑ i ∈ Finset.range m,
    (∑ j ∈ Finset.range ((C (i + 1)).natDegree + 1), ‖(C (i + 1)).coeff j‖) * (max 1 K) ^ m
    with hBsum
  have hBsum0 : 0 ≤ Bsum := by
    rw [hBsum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h1 : (0 : ℝ) ≤ ∑ j ∈ Finset.range ((C (i + 1)).natDegree + 1), ‖(C (i + 1)).coeff j‖ :=
      Finset.sum_nonneg fun j _ => norm_nonneg _
    have h2 : (0 : ℝ) ≤ (max 1 K) ^ m := by positivity
    exact mul_nonneg h1 h2
  have hd₀1 : 1 ≤ d₀ := by
    have := hdom 1 le_rfl hm
    omega
  refine ⟨max R' (Bsum / L + 1), le_trans hR'1 (le_max_left _ _), ?_⟩
  intro z hz htame
  have hzR' : R' ≤ ‖Y z‖ := le_trans (le_max_left _ _) hz
  have hzB : Bsum / L + 1 ≤ ‖Y z‖ := le_trans (le_max_right _ _) hz
  have hY1 : (1 : ℝ) ≤ ‖Y z‖ := le_trans hR'1 hzR'
  have hY0 : (0 : ℝ) < ‖Y z‖ := by linarith
  -- split off the constant term
  have hsplit : (C 0).eval (Y z)
      = -∑ i ∈ Finset.range m, (C (i + 1)).eval (Y z) * (W z) ^ (i + 1) := by
    have h := hrel z
    rw [Finset.sum_range_succ'] at h
    simp only [pow_zero, mul_one] at h
    linear_combination h
  have hupper : ‖(C 0).eval (Y z)‖ ≤ Bsum * ‖Y z‖ ^ (d₀ - 1) := by
    rw [hsplit, norm_neg]
    refine le_trans (norm_sum_le _ _) ?_
    rw [hBsum, Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    have him : i < m := Finset.mem_range.mp hi
    have hdeg := hdom (i + 1) (by omega) (by omega)
    have hcoef : ‖(C (i + 1)).eval (Y z)‖
        ≤ (∑ j ∈ Finset.range ((C (i + 1)).natDegree + 1), ‖(C (i + 1)).coeff j‖)
          * ‖Y z‖ ^ (C (i + 1)).natDegree := norm_eval_le_mul_pow (C (i + 1)) hY1
    have hW : ‖W z‖ ^ (i + 1) ≤ (max 1 K) ^ m * ‖Y z‖ ^ (i + 1) := by
      have h1 : ‖W z‖ ^ (i + 1) ≤ (K * ‖Y z‖) ^ (i + 1) :=
        pow_le_pow_left₀ (norm_nonneg _) htame _
      have h2 : (K * ‖Y z‖) ^ (i + 1) = K ^ (i + 1) * ‖Y z‖ ^ (i + 1) := by rw [mul_pow]
      have h3 : K ^ (i + 1) ≤ (max 1 K) ^ m := by
        refine le_trans (pow_le_pow_left₀ hK.le (le_max_right 1 K) _) ?_
        exact pow_le_pow_right₀ (le_max_left 1 K) (by omega)
      have h4 : (0 : ℝ) ≤ ‖Y z‖ ^ (i + 1) := by positivity
      calc ‖W z‖ ^ (i + 1) ≤ K ^ (i + 1) * ‖Y z‖ ^ (i + 1) := by rw [← h2]; exact h1
        _ ≤ (max 1 K) ^ m * ‖Y z‖ ^ (i + 1) := mul_le_mul_of_nonneg_right h3 h4
    have hprodpow : ‖Y z‖ ^ (C (i + 1)).natDegree * ‖Y z‖ ^ (i + 1) ≤ ‖Y z‖ ^ (d₀ - 1) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hY1 (by omega)
    have hA0 : (0 : ℝ) ≤ ∑ j ∈ Finset.range ((C (i + 1)).natDegree + 1), ‖(C (i + 1)).coeff j‖ :=
      Finset.sum_nonneg fun j _ => norm_nonneg _
    have hmax0 : (0 : ℝ) ≤ (max 1 K) ^ m := by positivity
    rw [norm_mul, norm_pow]
    calc ‖(C (i + 1)).eval (Y z)‖ * ‖W z‖ ^ (i + 1)
        ≤ ((∑ j ∈ Finset.range ((C (i + 1)).natDegree + 1), ‖(C (i + 1)).coeff j‖)
            * ‖Y z‖ ^ (C (i + 1)).natDegree) * ((max 1 K) ^ m * ‖Y z‖ ^ (i + 1)) := by
          refine mul_le_mul hcoef hW (by positivity) (by positivity)
      _ = ((∑ j ∈ Finset.range ((C (i + 1)).natDegree + 1), ‖(C (i + 1)).coeff j‖)
            * (max 1 K) ^ m) * (‖Y z‖ ^ (C (i + 1)).natDegree * ‖Y z‖ ^ (i + 1)) := by ring
      _ ≤ ((∑ j ∈ Finset.range ((C (i + 1)).natDegree + 1), ‖(C (i + 1)).coeff j‖)
            * (max 1 K) ^ m) * ‖Y z‖ ^ (d₀ - 1) := by
          refine mul_le_mul_of_nonneg_left hprodpow (by positivity)
  have hlower : L * ‖Y z‖ ^ d₀ ≤ ‖(C 0).eval (Y z)‖ := hlow (Y z) hzR'
  have hpowsplit : ‖Y z‖ ^ d₀ = ‖Y z‖ * ‖Y z‖ ^ (d₀ - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hpos : (0 : ℝ) < ‖Y z‖ ^ (d₀ - 1) := by positivity
  rw [hpowsplit] at hlower
  have hfinal : L * ‖Y z‖ ≤ Bsum := by
    by_contra hcon
    push Not at hcon
    nlinarith [hlower, hupper, hpos, hcon]
  have hdiv : Bsum / L + 1 ≤ Bsum / L := by
    calc Bsum / L + 1 ≤ ‖Y z‖ := hzB
      _ ≤ Bsum / L := by
        rw [le_div_iff₀ hL0]
        linarith [hfinal]
  linarith [hdiv]

end GaloisForLFunctions.HTGeometry
