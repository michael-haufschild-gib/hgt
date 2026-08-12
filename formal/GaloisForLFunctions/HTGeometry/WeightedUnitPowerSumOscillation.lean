import GaloisForLFunctions.HTGeometry.UnitPowerSumOscillation

/-!
# Weighted unit power sums oscillate below every decaying floor

The oscillation theorem for unit power sums extends to complex weights, provided the weight
function is constant on value classes and conjugation-symmetric: for a finite family of
unit-modulus points, none equal to `1`, with weights `W` satisfying `v i = v j → W i = W j` and
`v j = conj (v i) → W j = conj (W i)`, and some weight nonzero, the real parts of
`A n = sum_i W i * v i ^ (n+1)` cannot stay above `-(C k^n)` with `0 ≤ k < 1`.

The two symmetry hypotheses are exactly what makes the second-moment expansion sign-definite at
the resonant pairs: `v i * conj (v j) = 1` forces `v j = v i`, hence coefficient
`W i * conj (W j) = ‖W i‖^2`, and `v i * v j = 1` forces `v j = conj (v i)`, hence coefficient
`W i * W j = ‖W i‖^2`.  Both hold automatically for weight systems inherited from
conjugation-stable divisors.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Weighted unit power sums oscillate.** -/
theorem weightedUnitPowerSum_no_decaying_lower_bound {ι : Type*} {s : Finset ι}
    {v W : ι → ℂ} (hnorm : ∀ i ∈ s, ‖v i‖ = 1) (hne : ∀ i ∈ s, v i ≠ 1)
    (hclass : ∀ i ∈ s, ∀ j ∈ s, v i = v j → W i = W j)
    (hconj : ∀ i ∈ s, ∀ j ∈ s, v j = (starRingEnd ℂ) (v i) → W j = (starRingEnd ℂ) (W i))
    {i₀ : ι} (hi₀ : i₀ ∈ s) (hW₀ : W i₀ ≠ 0)
    {C κ : ℝ} (hC : 0 ≤ C) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1)
    (hlow : ∀ n : ℕ, -(C * κ ^ n) ≤ (∑ i ∈ s, W i * v i ^ (n + 1)).re) : False := by
  classical
  set K₁ : ℝ := ∑ i ∈ s, ‖W i‖ with hK₁
  have hK₁nn : 0 ≤ K₁ := Finset.sum_nonneg fun i _ => norm_nonneg _
  set A : ℕ → ℂ := fun n => ∑ i ∈ s, W i * v i ^ (n + 1) with hA
  have hAbound : ∀ n, ‖A n‖ ≤ K₁ := by
    intro n
    calc ‖A n‖ ≤ ∑ i ∈ s, ‖W i * v i ^ (n + 1)‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖W i‖ := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [norm_mul, norm_pow, hnorm i hi, one_pow, mul_one]
      _ = K₁ := hK₁.symm
  set C₁ : ℝ := ∑ i ∈ s, ‖W i‖ * (2 / ‖v i - 1‖) with hC₁
  set B : ι → ι → ℝ := fun i j =>
    if v i * (starRingEnd ℂ) (v j) = 1 then 0
    else ‖W i‖ * ‖W j‖ * (2 / ‖v i * (starRingEnd ℂ) (v j) - 1‖) with hB
  set B' : ι → ι → ℝ := fun i j =>
    if v i * v j = 1 then 0 else ‖W i‖ * ‖W j‖ * (2 / ‖v i * v j - 1‖) with hB'
  have hBnn : ∀ i j, 0 ≤ B i j := by
    intro i j
    simp only [hB]
    split <;> positivity
  have hB'nn : ∀ i j, 0 ≤ B' i j := by
    intro i j
    simp only [hB']
    split <;> positivity
  set C₄ : ℝ := ∑ i ∈ s, ∑ j ∈ s, B i j with hC₄
  set C₅ : ℝ := ∑ i ∈ s, ∑ j ∈ s, B' i j with hC₅
  -- resonance forces value equality
  have hres : ∀ i ∈ s, ∀ j ∈ s, v i * (starRingEnd ℂ) (v j) = 1 → v j = v i := by
    intro i hi j hj h1
    have hjinv : (v j)⁻¹ = (starRingEnd ℂ) (v j) := Complex.inv_eq_conj (hnorm j hj)
    rw [← hjinv] at h1
    have hjne : v j ≠ 0 := by
      intro h0
      have h2 := hnorm j hj
      rw [h0] at h2
      simp at h2
    field_simp at h1
    exact h1.symm
  have hres' : ∀ i ∈ s, ∀ j ∈ s, v i * v j = 1 → v j = (starRingEnd ℂ) (v i) := by
    intro i hi j hj h1
    have hiinv : (v i)⁻¹ = (starRingEnd ℂ) (v i) := Complex.inv_eq_conj (hnorm i hi)
    rw [← hiinv]
    have hine : v i ≠ 0 := by
      intro h0
      have := hnorm i hi
      rw [h0] at this
      simp at this
    field_simp
    linear_combination h1
  -- (1) bounded partial sums
  have hsum1 : ∀ N, ‖∑ n ∈ Finset.range N, A n‖ ≤ C₁ := by
    intro N
    have hswap : ∑ n ∈ Finset.range N, A n =
        ∑ i ∈ s, W i * ∑ n ∈ Finset.range N, v i ^ (n + 1) := by
      rw [hA]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    rw [hswap]
    calc ‖∑ i ∈ s, W i * ∑ n ∈ Finset.range N, v i ^ (n + 1)‖
        ≤ ∑ i ∈ s, ‖W i * ∑ n ∈ Finset.range N, v i ^ (n + 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, ‖W i‖ * (2 / ‖v i - 1‖) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (norm_sum_pow_succ_le (le_of_eq (hnorm i hi)) (hne i hi) N) (norm_nonneg _)
      _ = C₁ := hC₁.symm
  -- (2) linear growth of the norm-square sums
  have hsum2 : ∀ N : ℕ, ‖W i₀‖ ^ 2 * N - C₄ ≤ ∑ n ∈ Finset.range N, ‖A n‖ ^ 2 := by
    intro N
    have hAsq : ∀ n, (‖A n‖ : ℝ) ^ 2 = (A n * (starRingEnd ℂ) (A n)).re := by
      intro n
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]
    have hexp : ∑ n ∈ Finset.range N, A n * (starRingEnd ℂ) (A n) =
        ∑ i ∈ s, ∑ j ∈ s, (W i * (starRingEnd ℂ) (W j)) *
          ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) := by
      have h1 : ∀ n, A n * (starRingEnd ℂ) (A n) =
          ∑ i ∈ s, ∑ j ∈ s, (W i * (starRingEnd ℂ) (W j)) *
            (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) := by
        intro n
        rw [hA]
        simp only [map_sum]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_pow, mul_pow]
        ring
      calc ∑ n ∈ Finset.range N, A n * (starRingEnd ℂ) (A n)
          = ∑ n ∈ Finset.range N, ∑ i ∈ s, ∑ j ∈ s,
              (W i * (starRingEnd ℂ) (W j)) * (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) :=
            Finset.sum_congr rfl fun n _ => h1 n
        _ = ∑ i ∈ s, ∑ n ∈ Finset.range N, ∑ j ∈ s,
              (W i * (starRingEnd ℂ) (W j)) * (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) :=
            Finset.sum_comm
        _ = ∑ i ∈ s, ∑ j ∈ s, ∑ n ∈ Finset.range N,
              (W i * (starRingEnd ℂ) (W j)) * (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i ∈ s, ∑ j ∈ s, (W i * (starRingEnd ℂ) (W j)) *
              ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              (Finset.mul_sum _ _ _).symm
    have hre : ∑ n ∈ Finset.range N, ‖A n‖ ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, ((W i * (starRingEnd ℂ) (W j)) *
          ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
      calc ∑ n ∈ Finset.range N, ‖A n‖ ^ 2
          = ∑ n ∈ Finset.range N, (A n * (starRingEnd ℂ) (A n)).re :=
            Finset.sum_congr rfl fun n _ => hAsq n
        _ = (∑ n ∈ Finset.range N, A n * (starRingEnd ℂ) (A n)).re :=
            (Complex.re_sum _ _).symm
        _ = ∑ i ∈ s, ∑ j ∈ s, ((W i * (starRingEnd ℂ) (W j)) *
              ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
            rw [hexp, Complex.re_sum]
            exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
    rw [hre]
    have hterm : ∀ i ∈ s, ∀ j ∈ s, (if v i * (starRingEnd ℂ) (v j) = 1
        then (if i = i₀ ∧ j = i₀ then ‖W i₀‖ ^ 2 * N else 0) else -(B i j)) ≤
        ((W i * (starRingEnd ℂ) (W j)) *
          ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re := by
      intro i hi j hj
      by_cases hcase : v i * (starRingEnd ℂ) (v j) = 1
      · rw [if_pos hcase, hcase]
        have hvij : v j = v i := hres i hi j hj hcase
        have hWij : W j = W i := hclass j hj i hi hvij
        have hval : ((W i * (starRingEnd ℂ) (W j)) *
            ∑ n ∈ Finset.range N, (1 : ℂ) ^ (n + 1)).re = ‖W i‖ ^ 2 * N := by
          rw [hWij, Complex.mul_conj]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re,
            ← Complex.sq_norm]
        rw [hval]
        by_cases hij : i = i₀ ∧ j = i₀
        · rw [if_pos hij, hij.1]
        · rw [if_neg hij]
          positivity
      · rw [if_neg hcase]
        have hznorm : ‖v i * (starRingEnd ℂ) (v j)‖ = 1 := by
          rw [norm_mul, hnorm i hi, RCLike.norm_conj, hnorm j hj, one_mul]
        have hb := norm_sum_pow_succ_le (le_of_eq hznorm) hcase N
        have h2 := Complex.abs_re_le_norm ((W i * (starRingEnd ℂ) (W j)) *
          ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1))
        have h3 := neg_abs_le ((W i * (starRingEnd ℂ) (W j)) *
          ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re
        have h4 : ‖(W i * (starRingEnd ℂ) (W j)) *
            ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)‖ ≤ B i j := by
          simp only [hB, if_neg hcase]
          rw [norm_mul, norm_mul, RCLike.norm_conj]
          exact mul_le_mul_of_nonneg_left hb (by positivity)
        linarith
    have hlower : ∑ i ∈ s, ∑ j ∈ s, (if v i * (starRingEnd ℂ) (v j) = 1
        then (if i = i₀ ∧ j = i₀ then ‖W i₀‖ ^ 2 * (N : ℝ) else 0) else -(B i j)) ≥
        ‖W i₀‖ ^ 2 * N - C₄ := by
      have hdiag : v i₀ * (starRingEnd ℂ) (v i₀) = 1 := by
        rw [Complex.mul_conj, ← Complex.sq_norm, hnorm i₀ hi₀]
        norm_num
      have hone : ∀ i ∈ s, ∀ j ∈ s, (if v i * (starRingEnd ℂ) (v j) = 1
          then (if i = i₀ ∧ j = i₀ then ‖W i₀‖ ^ 2 * (N : ℝ) else 0) else -(B i j)) ≥
          (if i = i₀ ∧ j = i₀ then ‖W i₀‖ ^ 2 * (N : ℝ) else 0) - B i j := by
        intro i hi j hj
        by_cases hcase : v i * (starRingEnd ℂ) (v j) = 1
        · rw [if_pos hcase]
          have := hBnn i j
          linarith
        · rw [if_neg hcase]
          have hne2 : ¬(i = i₀ ∧ j = i₀) := by
            rintro ⟨rfl, rfl⟩
            exact hcase hdiag
          rw [if_neg hne2]
          linarith
      calc ∑ i ∈ s, ∑ j ∈ s, (if v i * (starRingEnd ℂ) (v j) = 1
          then (if i = i₀ ∧ j = i₀ then ‖W i₀‖ ^ 2 * (N : ℝ) else 0) else -(B i j))
          ≥ ∑ i ∈ s, ∑ j ∈ s,
              ((if i = i₀ ∧ j = i₀ then ‖W i₀‖ ^ 2 * (N : ℝ) else 0) - B i j) :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hone i hi j hj
        _ = (∑ i ∈ s, ∑ j ∈ s,
              (if i = i₀ ∧ j = i₀ then ‖W i₀‖ ^ 2 * (N : ℝ) else 0)) - C₄ := by
            rw [hC₄, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_sub_distrib]
        _ = ‖W i₀‖ ^ 2 * N - C₄ := by
            congr 1
            rw [Finset.sum_eq_single i₀]
            · rw [Finset.sum_eq_single i₀]
              · simp
              · intro j _ hj
                rw [if_neg (by tauto)]
              · intro h
                exact absurd hi₀ h
            · intro i _ hi
              rw [Finset.sum_eq_zero fun j _ => by rw [if_neg (by tauto)]]
            · intro h
              exact absurd hi₀ h
    calc ‖W i₀‖ ^ 2 * N - C₄
        ≤ ∑ i ∈ s, ∑ j ∈ s, (if v i * (starRingEnd ℂ) (v j) = 1
            then (if i = i₀ ∧ j = i₀ then ‖W i₀‖ ^ 2 * (N : ℝ) else 0) else -(B i j)) :=
          hlower
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ((W i * (starRingEnd ℂ) (W j)) *
            ∑ n ∈ Finset.range N, (v i * (starRingEnd ℂ) (v j)) ^ (n + 1)).re :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
  -- (3) bounded square sums
  have hsum3 : ∀ N : ℕ, -C₅ ≤ ∑ n ∈ Finset.range N, ((A n) ^ 2).re := by
    intro N
    have hexp : ∑ n ∈ Finset.range N, (A n) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, (W i * W j) *
          ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1) := by
      have h1 : ∀ n, (A n) ^ 2 = ∑ i ∈ s, ∑ j ∈ s,
          (W i * W j) * (v i * v j) ^ (n + 1) := by
        intro n
        rw [hA, pow_two, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_pow]
        ring
      calc ∑ n ∈ Finset.range N, (A n) ^ 2
          = ∑ n ∈ Finset.range N, ∑ i ∈ s, ∑ j ∈ s,
              (W i * W j) * (v i * v j) ^ (n + 1) :=
            Finset.sum_congr rfl fun n _ => h1 n
        _ = ∑ i ∈ s, ∑ n ∈ Finset.range N, ∑ j ∈ s,
              (W i * W j) * (v i * v j) ^ (n + 1) := Finset.sum_comm
        _ = ∑ i ∈ s, ∑ j ∈ s, ∑ n ∈ Finset.range N,
              (W i * W j) * (v i * v j) ^ (n + 1) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i ∈ s, ∑ j ∈ s, (W i * W j) *
              ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
              (Finset.mul_sum _ _ _).symm
    have hre : ∑ n ∈ Finset.range N, ((A n) ^ 2).re =
        ∑ i ∈ s, ∑ j ∈ s, ((W i * W j) *
          ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re := by
      calc ∑ n ∈ Finset.range N, ((A n) ^ 2).re
          = (∑ n ∈ Finset.range N, (A n) ^ 2).re := (Complex.re_sum _ _).symm
        _ = ∑ i ∈ s, ∑ j ∈ s, ((W i * W j) *
              ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re := by
            rw [hexp, Complex.re_sum]
            exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
    rw [hre]
    have hterm : ∀ i ∈ s, ∀ j ∈ s, -(B' i j) ≤
        ((W i * W j) * ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re := by
      intro i hi j hj
      by_cases hcase : v i * v j = 1
      · have hvij : v j = (starRingEnd ℂ) (v i) := hres' i hi j hj hcase
        have hWij : W j = (starRingEnd ℂ) (W i) := hconj i hi j hj hvij
        have hval : ((W i * W j) * ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re =
            ‖W i‖ ^ 2 * N := by
          rw [hWij, Complex.mul_conj, hcase]
          simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re,
            ← Complex.sq_norm]
        rw [hval]
        have h1 := hB'nn i j
        have h2 : (0 : ℝ) ≤ ‖W i‖ ^ 2 * N := by positivity
        linarith
      · have hznorm : ‖v i * v j‖ = 1 := by
          rw [norm_mul, hnorm i hi, hnorm j hj, one_mul]
        have hb := norm_sum_pow_succ_le (le_of_eq hznorm) hcase N
        have h2 := Complex.abs_re_le_norm ((W i * W j) *
          ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1))
        have h3 := neg_abs_le ((W i * W j) *
          ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re
        have h4 : ‖(W i * W j) * ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)‖ ≤ B' i j := by
          simp only [hB', if_neg hcase]
          rw [norm_mul, norm_mul]
          exact mul_le_mul_of_nonneg_left hb (by positivity)
        linarith
    calc -C₅ = ∑ i ∈ s, ∑ j ∈ s, -(B' i j) := by
          rw [hC₅]
          simp [Finset.sum_neg_distrib]
      _ ≤ ∑ i ∈ s, ∑ j ∈ s, ((W i * W j) *
            ∑ n ∈ Finset.range N, (v i * v j) ^ (n + 1)).re :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
  -- (4) pointwise identity
  have hid : ∀ n, ((A n).re) ^ 2 = (‖A n‖ ^ 2 + ((A n) ^ 2).re) / 2 := by
    intro n
    rw [Complex.sq_norm, Complex.normSq_apply, pow_two (A n), Complex.mul_re]
    ring
  -- (5) upper bound
  have h1κ : (0 : ℝ) < 1 - κ := by linarith
  have hup : ∀ N : ℕ, ∑ n ∈ Finset.range N, ((A n).re) ^ 2 ≤
      K₁ * (C₁ + 2 * C / (1 - κ)) := by
    intro N
    have habs : ∀ n, |(A n).re| ≤ (A n).re + 2 * C * κ ^ n := by
      intro n
      rcases abs_cases (A n).re with ⟨h, _⟩ | ⟨h, _⟩
      · rw [h]
        nlinarith [mul_nonneg hC (pow_nonneg hκ0 n)]
      · rw [h]
        have := hlow n
        nlinarith
    have hgeo : ∑ n ∈ Finset.range N, κ ^ n ≤ 1 / (1 - κ) := by
      rw [geom_sum_eq (ne_of_lt hκ1)]
      rw [show κ ^ N - 1 = -(1 - κ ^ N) by ring, show κ - 1 = -(1 - κ) by ring,
        neg_div_neg_eq]
      rw [div_le_div_iff₀ h1κ h1κ]
      nlinarith [pow_nonneg hκ0 N]
    calc ∑ n ∈ Finset.range N, ((A n).re) ^ 2
        ≤ ∑ n ∈ Finset.range N, K₁ * |(A n).re| := by
          refine Finset.sum_le_sum fun n _ => ?_
          have h1 : |(A n).re| ≤ K₁ := le_trans (Complex.abs_re_le_norm _) (hAbound n)
          nlinarith [abs_nonneg ((A n).re), sq_abs ((A n).re)]
      _ = K₁ * ∑ n ∈ Finset.range N, |(A n).re| := (Finset.mul_sum _ _ _).symm
      _ ≤ K₁ * (C₁ + 2 * C / (1 - κ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK₁nn
          calc ∑ n ∈ Finset.range N, |(A n).re|
              ≤ ∑ n ∈ Finset.range N, ((A n).re + 2 * C * κ ^ n) :=
                Finset.sum_le_sum fun n _ => habs n
            _ = (∑ n ∈ Finset.range N, A n).re +
                  2 * C * ∑ n ∈ Finset.range N, κ ^ n := by
                rw [Finset.sum_add_distrib, Complex.re_sum, ← Finset.mul_sum]
            _ ≤ C₁ + 2 * C / (1 - κ) := by
                have h1 : (∑ n ∈ Finset.range N, A n).re ≤ C₁ :=
                  le_trans (Complex.re_le_norm _) (hsum1 N)
                have h2 : 2 * C * ∑ n ∈ Finset.range N, κ ^ n ≤ 2 * C * (1 / (1 - κ)) :=
                  mul_le_mul_of_nonneg_left hgeo (by linarith)
                have h3 : 2 * C * (1 / (1 - κ)) = 2 * C / (1 - κ) := by ring
                linarith
  -- (6) contradiction
  have hlowN : ∀ N : ℕ, (‖W i₀‖ ^ 2 * N - (C₄ + C₅)) / 2 ≤
      ∑ n ∈ Finset.range N, ((A n).re) ^ 2 := by
    intro N
    have h2 := hsum2 N
    have h3 := hsum3 N
    have hEq : (2 : ℝ) * ∑ n ∈ Finset.range N, ((A n).re) ^ 2 =
        (∑ n ∈ Finset.range N, ‖A n‖ ^ 2) +
          ∑ n ∈ Finset.range N, ((A n) ^ 2).re := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hid n]
      ring
    linarith
  have hW₀pos : (0 : ℝ) < ‖W i₀‖ ^ 2 := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((K₁ * (C₁ + 2 * C / (1 - κ)) * 2 + (C₄ + C₅)) / (‖W i₀‖ ^ 2))
  rw [div_lt_iff₀ hW₀pos] at hN
  have hfin1 := hlowN N
  have hfin2 := hup N
  nlinarith

end GaloisForLFunctions.HTGeometry

end
