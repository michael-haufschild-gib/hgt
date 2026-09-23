import GaloisForLFunctions.HTGeometry.RankEnergyPowerSum

/-!
# Guth–Maynard, Lemma 4.2: the largest eigenvalue from the cubic trace defect

For nonnegative reals `y₁, …, y_k` (the eigenvalues of `M M*`), Guth–Maynard (arXiv 2405.20552,
Lemma 4.2, inequality (4.3) in the variables `y = x²`) bound the largest one by

```
  y_max³ ≤ max ( 4 (Σ y_i³ − (Σ y_i)³ / k²),  8 (Σ y_i)³ / k³ ).
```

The point is the *defect* `Σ y³ − (Σ y)³/k²`: when all eigenvalues are equal the defect vanishes and
the second term is sharp, so the trace of the cube controls the top eigenvalue as if the spectrum
were flat.  The proof is Hölder on the remaining `k − 1` eigenvalues and one case split.  We record
the eigenvalue version for Hermitian matrices through the corpus's trace-power identity, so that the
statement reads off the traces `tr (H³)` and `tr H`.
-/

open Finset

namespace RHTower.GuthMaynard

/-- Power-mean inequality: `(Σ_s z)³ ≤ |s|² Σ_s z³` for nonnegative `z`. -/
theorem cube_sum_le_card_sq_mul_sum_cube {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∑ i ∈ s, z i) ^ (3 : ℕ) ≤ (s.card : ℝ) ^ (2 : ℕ) * ∑ i ∈ s, z i ^ (3 : ℕ) := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp [hs]
  have hcard : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hw : ∀ i ∈ s, (0 : ℝ) ≤ 1 / s.card := fun _ _ => by positivity
  have hw' : ∑ i ∈ s, (1 / (s.card : ℝ)) = 1 := by
    rw [sum_const, nsmul_eq_mul]
    try field_simp
  have h := Real.pow_arith_mean_le_arith_mean_pow s (fun _ => 1 / (s.card : ℝ)) z hw hw' hz 3
  rw [← mul_sum, ← mul_sum] at h
  have hc3 : (1 / (s.card : ℝ)) ^ (3 : ℕ) * (∑ i ∈ s, z i) ^ (3 : ℕ) ≤ 1 / (s.card : ℝ) * ∑ i ∈ s, z i ^ (3 : ℕ) := by
    rw [← mul_pow]
    exact h
  have hpos : (0 : ℝ) < (s.card : ℝ) ^ (3 : ℕ) := by positivity
  rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_iff₀ hpos] at hc3
  calc (∑ i ∈ s, z i) ^ (3 : ℕ) ≤ 1 / (s.card : ℝ) * (∑ i ∈ s, z i ^ (3 : ℕ)) * (s.card : ℝ) ^ (3 : ℕ) := hc3
    _ = (s.card : ℝ) ^ (2 : ℕ) * ∑ i ∈ s, z i ^ (3 : ℕ) := by
        field_simp
        try ring

/-- **Guth–Maynard (4.3).**  For nonnegative `y` on a finite type of cardinality `k` and any index
`i₀`, `y_{i₀}³ ≤ max (4 (Σ y³ − (Σ y)³ / k²)) (8 (Σ y)³ / k³)`. -/
theorem cube_le_max_trace_defect {ι : Type*} [Fintype ι] (y : ι → ℝ) (hy : ∀ i, 0 ≤ y i)
    (i₀ : ι) :
    y i₀ ^ (3 : ℕ) ≤ max (4 * (∑ i, y i ^ (3 : ℕ) - (∑ i, y i) ^ (3 : ℕ) / (Fintype.card ι : ℝ) ^ (2 : ℕ)))
      (8 * (∑ i, y i) ^ (3 : ℕ) / (Fintype.card ι : ℝ) ^ (3 : ℕ)) := by
  classical
  set k : ℝ := (Fintype.card ι : ℝ) with hk
  have hkpos : (0 : ℝ) < k := by
    rw [hk]; exact_mod_cast Fintype.card_pos_iff.2 ⟨i₀⟩
  set s : Finset ι := Finset.univ.erase i₀ with hs
  set T : ℝ := ∑ i ∈ s, y i with hT
  set Q : ℝ := ∑ i ∈ s, y i ^ (3 : ℕ) with hQ
  set P : ℝ := ∑ i, y i with hP
  set C : ℝ := ∑ i, y i ^ (3 : ℕ) with hC
  have hsplitP : P = y i₀ + T := by
    rw [hP, hT, ← Finset.add_sum_erase Finset.univ y (Finset.mem_univ i₀)]
  have hsplitC : C = y i₀ ^ (3 : ℕ) + Q := by
    rw [hC, hQ, ← Finset.add_sum_erase Finset.univ (fun i => y i ^ (3 : ℕ)) (Finset.mem_univ i₀)]
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => hy i)
  have hy0 : 0 ≤ y i₀ := hy i₀
  -- Hölder on the remaining eigenvalues: T³ ≤ (k-1)² Q ≤ k² Q
  have hcard : (s.card : ℝ) ≤ k := by
    rw [hk, hs, Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
    have : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.2 ⟨i₀⟩
    push_cast [Nat.cast_sub this]
    linarith
  have hholder : T ^ (3 : ℕ) ≤ k ^ (2 : ℕ) * Q := by
    have h1 := cube_sum_le_card_sq_mul_sum_cube s y (fun i _ => hy i)
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => pow_nonneg (hy i) 3)
    have h2 : (s.card : ℝ) ^ (2 : ℕ) * Q ≤ k ^ (2 : ℕ) * Q := by
      gcongr
    linarith
  -- y³ ≤ (C − P³/k²) + 3 y P²/k²
  have hcube : (y i₀ + T) ^ (3 : ℕ) - T ^ (3 : ℕ) ≤ 3 * y i₀ * (y i₀ + T) ^ (2 : ℕ) := by
    nlinarith [mul_nonneg hy0 (mul_nonneg hy0 hy0), mul_nonneg (mul_nonneg hy0 hy0) hT0]
  have hmain : y i₀ ^ (3 : ℕ) ≤ (C - P ^ (3 : ℕ) / k ^ (2 : ℕ)) + 3 * y i₀ * P ^ (2 : ℕ) / k ^ (2 : ℕ) := by
    have hk2 : 0 < k ^ (2 : ℕ) := by positivity
    have h1 : y i₀ ^ (3 : ℕ) ≤ C - T ^ (3 : ℕ) / k ^ (2 : ℕ) := by
      rw [hsplitC]
      have : T ^ (3 : ℕ) / k ^ (2 : ℕ) ≤ Q := by rw [div_le_iff₀ hk2]; linarith
      linarith
    have h2 : (P ^ (3 : ℕ) - T ^ (3 : ℕ)) / k ^ (2 : ℕ) ≤ 3 * y i₀ * P ^ (2 : ℕ) / k ^ (2 : ℕ) := by
      rw [hsplitP]; exact div_le_div_of_nonneg_right hcube hk2.le
    have h3 : C - T ^ (3 : ℕ) / k ^ (2 : ℕ) = (C - P ^ (3 : ℕ) / k ^ (2 : ℕ)) + (P ^ (3 : ℕ) - T ^ (3 : ℕ)) / k ^ (2 : ℕ) := by ring
    linarith
  -- case split: a + 3b ≤ max (4a) (4b)
  set a : ℝ := C - P ^ (3 : ℕ) / k ^ (2 : ℕ) with ha
  set b : ℝ := y i₀ * P ^ (2 : ℕ) / k ^ (2 : ℕ) with hb
  have hab : y i₀ ^ (3 : ℕ) ≤ a + 3 * b := by
    have : 3 * y i₀ * P ^ (2 : ℕ) / k ^ (2 : ℕ) = 3 * b := by rw [hb]; ring
    linarith
  rcases le_or_gt b a with hle | hlt
  · exact le_max_of_le_left (by linarith)
  · -- y³ ≤ 4b = 4 y P²/k²  ⇒  y² ≤ 2P/k  ⇒  y³ ≤ 8P³/k³
    have h4 : y i₀ ^ (3 : ℕ) ≤ 4 * (y i₀ * P ^ (2 : ℕ) / k ^ (2 : ℕ)) := by rw [← hb]; linarith
    refine le_max_of_le_right ?_
    have hP0 : 0 ≤ P := by rw [hsplitP]; linarith
    rcases eq_or_lt_of_le hy0 with h0 | hpos
    · rw [← h0]
      have : (0 : ℝ) ^ (3 : ℕ) = 0 := by norm_num
      rw [this]
      exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg hP0 3)) (pow_nonneg hkpos.le 3)
    · have hy2 : y i₀ ^ (2 : ℕ) ≤ 4 * P ^ (2 : ℕ) / k ^ (2 : ℕ) := by
        have : y i₀ ^ (3 : ℕ) = y i₀ * y i₀ ^ (2 : ℕ) := by ring
        rw [this] at h4
        have h5 : y i₀ * y i₀ ^ (2 : ℕ) ≤ y i₀ * (4 * P ^ (2 : ℕ) / k ^ (2 : ℕ)) := by
          have : 4 * (y i₀ * P ^ (2 : ℕ) / k ^ (2 : ℕ)) = y i₀ * (4 * P ^ (2 : ℕ) / k ^ (2 : ℕ)) := by ring
          linarith
        exact le_of_mul_le_mul_left h5 hpos
      have hy1 : y i₀ ≤ 2 * P / k := by
        have h6 : (2 * P / k) ^ (2 : ℕ) = 4 * P ^ (2 : ℕ) / k ^ (2 : ℕ) := by ring
        rw [← h6] at hy2
        exact (pow_le_pow_iff_left₀ hy0 (by positivity) (by norm_num)).1 hy2
      calc y i₀ ^ (3 : ℕ) ≤ (2 * P / k) ^ (3 : ℕ) := pow_le_pow_left₀ hy0 hy1 3
        _ = 8 * P ^ (3 : ℕ) / k ^ (3 : ℕ) := by ring

/-- The eigenvalue form for a Hermitian matrix with nonnegative eigenvalues (e.g. `M M*`): every
eigenvalue `λ` satisfies `λ³ ≤ max (4 (Re tr H³ − (Re tr H)³/m²)) (8 (Re tr H)³/m³)`. -/
theorem eigenvalue_cube_le_max_trace_defect {d : Type*} [Fintype d] [DecidableEq d]
    {H : Matrix d d ℂ} (hH : H.IsHermitian) (hnn : ∀ i, 0 ≤ hH.eigenvalues i) (i₀ : d) :
    hH.eigenvalues i₀ ^ (3 : ℕ) ≤
      max (4 * ((H ^ (3 : ℕ)).trace.re - H.trace.re ^ (3 : ℕ) / (Fintype.card d : ℝ) ^ (2 : ℕ)))
        (8 * H.trace.re ^ (3 : ℕ) / (Fintype.card d : ℝ) ^ (3 : ℕ)) := by
  have h3 := GaloisForLFunctions.HTGeometry.trace_pow_eq_sum_eigenvalues_pow hH 3
  have h1 := GaloisForLFunctions.HTGeometry.trace_pow_eq_sum_eigenvalues_pow hH 1
  have h3' : (H ^ (3 : ℕ)).trace.re = ∑ i, hH.eigenvalues i ^ (3 : ℕ) := by
    rw [h3, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have h1' : H.trace.re = ∑ i, hH.eigenvalues i := by
    rw [pow_one] at h1
    rw [h1, Complex.re_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [pow_one, Complex.ofReal_re]
  rw [h3', h1']
  exact cube_le_max_trace_defect hH.eigenvalues hnn i₀

end RHTower.GuthMaynard
