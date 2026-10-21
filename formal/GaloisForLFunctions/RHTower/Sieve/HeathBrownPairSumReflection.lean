import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumShells
import GaloisForLFunctions.RHTower.Sieve.ImprovedMeanValue
import GaloisForLFunctions.HTGeometry.BorelGrowthLemma
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma35LargeA

/-!
# Heath-Brown's pair sums: the reflection inequality for one block

Let `W` be `1`-separated with all differences at most `2^J` (`J ≥ 1`) and let `2^J < N²`.
Every difference `t₁ − t₂ ≠ 0` lies in a dyadic shell `2^j/2 ≤ |t₁ − t₂| ≤ 2^j`, `1 ≤ j ≤ J`
(corpus `exists_dyadic_band`), so the pair sum of the unit block `U_N` is at most the diagonal
`|W|` plus the shell sums of `HeathBrownPairSumShells` (corpus `sum_biUnion_le_of_nonneg'`).
In each shell the error terms cost `O(|W|(1+J)²)` because `2^j < N²`, and when
`Y_j = 2^j/(2πN) ≥ 11` the Perron part is a combination of dual pair sums: with
`B ≥ M_j ≥ Y_j/9`, `𝒜₁((B,2B]) ≤ 𝒜_{1/2}((B,2B])/B` and `log(1 + 2^j/4) ≤ J`,

`3174 (Y_j²/2^j) · 2(4 log(1 + 2^j/4))² 𝒜₁((B,2B]) ≤ 150000 J²/N · 𝒜_{1/2}((B,2B])`.

Multiplying by `2N` (`𝒜_{1/2} ≤ 2N 𝒜₁` on `(N,2N]`) gives the **reflection inequality**

`𝒜_{1/2}((N,2N]) ≤ 2N|W|(1 + 12C²J((1+J)² + 1)) + 300000 J² Σ_{j≤J} Σ_{i<3} q_{j,i}`,

`q_{j,i} = [Y_j ≥ 11] 𝒜_{1/2}((2^i M_j, 2^{i+1} M_j])` (`hbDualTerm`), `C = hbReflConst`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset Complex

noncomputable section

/-- The dual pair sum of the shell `|t| ≍ 2^j` for the block `(N, 2N]`: the weighted pair sum
on `(2^i M_j, 2^{i+1} M_j]`, `M_j = ⌊2^j/(4π(2N + 1/4))⌋`, when `2^j/(2πN) ≥ 11`, else `0`. -/
def hbDualTerm (W : Finset ℝ) (N j i : ℕ) : ℝ :=
  if 11 ≤ (2 : ℝ) ^ j / (2 * Real.pi * N) then
    hbAmp W (1 / 2) (Finset.Ioc (2 ^ i * ubDualBase (2 * N) ((2 : ℝ) ^ j))
      (2 * (2 ^ i * ubDualBase (2 * N) ((2 : ℝ) ^ j))))
  else 0

theorem hbDualTerm_nonneg (W : Finset ℝ) (N j i : ℕ) : 0 ≤ hbDualTerm W N j i := by
  unfold hbDualTerm
  split_ifs
  · exact hbAmp_nonneg W _ _
  · exact le_refl 0

/-- **Every nonzero difference lies in a dyadic shell.** -/
theorem erase_subset_biUnion_shells {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W) {J : ℕ}
    (hJ : 1 ≤ J) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ (2 : ℝ) ^ J) {t₁ : ℝ} (ht₁ : t₁ ∈ W) :
    W.erase t₁ ⊆ (Finset.Icc 1 J).biUnion fun j =>
      W.filter fun t₂ => (2 : ℝ) ^ j / 2 ≤ |t₁ - t₂| ∧ |t₁ - t₂| ≤ (2 : ℝ) ^ j := by
  intro t₂ ht₂
  obtain ⟨hne, ht₂W⟩ := Finset.mem_erase.mp ht₂
  have hx1 : 1 ≤ |t₁ - t₂| := hW t₁ ht₁ t₂ ht₂W (Ne.symm hne)
  have hxJ := hdiam t₁ ht₁ t₂ ht₂W
  obtain ⟨k, hk1, hk2⟩ := GaloisForLFunctions.Nevanlinna.exists_dyadic_band hx1
  rw [Finset.mem_biUnion]
  by_cases hkJ : k + 1 ≤ J
  · refine ⟨k + 1, Finset.mem_Icc.mpr ⟨by omega, hkJ⟩, Finset.mem_filter.mpr ⟨ht₂W, ?_, hk2.le⟩⟩
    rw [pow_succ]
    linarith
  · refine ⟨J, Finset.mem_Icc.mpr ⟨hJ, le_rfl⟩, Finset.mem_filter.mpr ⟨ht₂W, ?_, hxJ⟩⟩
    have : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have h0 : (0 : ℝ) < 2 ^ J := by positivity
    linarith

/-- The error part of one shell: `(2T + 1) E² ≤ 6(1+J)² + 6` for `T = 2^j`, `1 ≤ j ≤ J`,
`2^J < N²`, `E = (1 + log T)/N + T^{−1/2}`. -/
private theorem shell_error_le {N J j : ℕ} (hN : 1 ≤ N) (hj : j ≤ J)
    (hJN : (2 : ℝ) ^ J < (N : ℝ) ^ 2) :
    (2 * (2 : ℝ) ^ j + 1) * ((1 + Real.log ((2 : ℝ) ^ j)) / N + 1 / Real.sqrt ((2 : ℝ) ^ j)) ^ 2
      ≤ 6 * (1 + J) ^ 2 + 6 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hT0 : (0 : ℝ) < 2 ^ j := by positivity
  have hTN : (2 : ℝ) ^ j ≤ (N : ℝ) ^ 2 :=
    (pow_le_pow_right₀ (by norm_num) hj).trans hJN.le
  have hlog : Real.log ((2 : ℝ) ^ j) ≤ J := by
    rw [Real.log_pow]
    have := Real.log_two_lt_d9
    have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  have hlog0 : 0 ≤ Real.log ((2 : ℝ) ^ j) := Real.log_nonneg hT1
  obtain ⟨a, ha⟩ : ∃ a, a = (1 + Real.log ((2 : ℝ) ^ j)) / N := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = 1 / Real.sqrt ((2 : ℝ) ^ j) := ⟨_, rfl⟩
  have hb2 : b ^ 2 = 1 / 2 ^ j := by rw [hb, div_pow, one_pow, Real.sq_sqrt hT0.le]
  have ha2 : (2 : ℝ) ^ j * a ^ 2 ≤ (1 + J) ^ 2 := by
    rw [ha, div_pow, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 + Real.log ((2 : ℝ) ^ j)) ^ 2 ≤ (1 + J) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith [mul_le_mul h1 hTN (by positivity) (by positivity)]
  have hsq : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  rw [← ha, ← hb]
  calc (2 * (2 : ℝ) ^ j + 1) * (a + b) ^ 2 ≤ 3 * 2 ^ j * (2 * a ^ 2 + 2 * b ^ 2) :=
        mul_le_mul (by linarith) hsq (sq_nonneg _) (by positivity)
    _ = 6 * (2 ^ j * a ^ 2) + 6 * (2 ^ j * b ^ 2) := by ring
    _ ≤ 6 * (1 + J) ^ 2 + 6 := by
        rw [hb2, mul_one_div_cancel hT0.ne']
        linarith

/-- The Perron part of one shell is a multiple of the dual terms:
`[Y ≥ 11] 3174 (Y²/T) Σ_i 2(4 log(1+T/4))² 𝒜₁((B_i,2B_i]) ≤ (150000 J²/N) Σ_i q_{j,i}`. -/
private theorem shell_perron_le (W : Finset ℝ) {N J j : ℕ} (hN : 1 ≤ N) (hj1 : 1 ≤ j)
    (hj : j ≤ J) :
    (if 11 ≤ (2 : ℝ) ^ j / (2 * Real.pi * N) then
        3174 * (((2 : ℝ) ^ j / (2 * Real.pi * N)) ^ 2 / (2 : ℝ) ^ j) * ∑ i ∈ Finset.range 3,
          2 * (4 * Real.log (1 + (2 : ℝ) ^ j / 4)) ^ 2 *
            hbAmp W 1 (Finset.Ioc (2 ^ i * ubDualBase (2 * N) ((2 : ℝ) ^ j))
              (2 * (2 ^ i * ubDualBase (2 * N) ((2 : ℝ) ^ j))))
      else 0) ≤ 150000 * (J : ℝ) ^ 2 / N * ∑ i ∈ Finset.range 3, hbDualTerm W N j i := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi := Real.pi_gt_d2
  split_ifs with hY
  · obtain ⟨Y, hYdef⟩ : ∃ Y, Y = (2 : ℝ) ^ j / (2 * Real.pi * N) := ⟨_, rfl⟩
    have hT0 : (0 : ℝ) < 2 ^ j := by positivity
    have hMlo := ub_dualBase_ge hN (by omega : N < 2 * N) le_rfl hT0 (by linarith)
    rw [← hYdef] at hY hMlo ⊢
    have hT2 : (2 : ℝ) ≤ 2 ^ j := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj1
    have hlog : Real.log (1 + (2 : ℝ) ^ j / 4) ≤ J := by
      have h1 : Real.log (1 + (2 : ℝ) ^ j / 4) ≤ Real.log ((2 : ℝ) ^ j) :=
        Real.log_le_log (by positivity) (by linarith)
      rw [Real.log_pow] at h1
      have := Real.log_two_lt_d9
      have hjJ : (j : ℝ) ≤ J := by exact_mod_cast hj
      nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
    have hlog0 : 0 ≤ Real.log (1 + (2 : ℝ) ^ j / 4) := Real.log_nonneg (by linarith)
    have hL2 : (4 * Real.log (1 + (2 : ℝ) ^ j / 4)) ^ 2 ≤ 16 * (J : ℝ) ^ 2 := by
      nlinarith
    have hY0 : 0 < Y := by linarith
    have hYT : Y / 2 ^ j = 1 / (2 * Real.pi * N) := by
      rw [hYdef]; field_simp
    simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hbDualTerm, if_pos (hYdef ▸ hY)]
    obtain ⟨M, hM⟩ : ∃ M, M = ubDualBase (2 * N) ((2 : ℝ) ^ j) := ⟨_, rfl⟩
    rw [← hM] at hMlo ⊢
    have hMpos : (0 : ℝ) < M := by linarith
    have hB : (M : ℝ) ≤ ((2 ^ i * M : ℕ) : ℝ) := by
      push_cast
      exact le_mul_of_one_le_left (Nat.cast_nonneg _) (one_le_pow₀ (by norm_num))
    have hBpos : 0 < 2 ^ i * M := by
      have : 0 < M := by exact_mod_cast hMpos
      positivity
    have h1 := hbAmp_one_le_hbAmp_half_div W hBpos
    have hA := hbAmp_nonneg W (1 / 2) (Finset.Ioc (2 ^ i * M) (2 * (2 ^ i * M)))
    have hdiv : hbAmp W (1 / 2) (Finset.Ioc (2 ^ i * M) (2 * (2 ^ i * M))) /
        ((2 ^ i * M : ℕ) : ℝ) ≤ 9 / Y * hbAmp W (1 / 2) (Finset.Ioc (2 ^ i * M) (2 * (2 ^ i * M))) := by
      rw [div_le_iff₀ (by linarith), mul_comm (9 / Y), mul_assoc]
      refine le_mul_of_one_le_right hA ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hY0]
      linarith
    obtain ⟨A, hAdef⟩ : ∃ A, A = hbAmp W (1 / 2) (Finset.Ioc (2 ^ i * M) (2 * (2 ^ i * M))) :=
      ⟨_, rfl⟩
    rw [← hAdef] at hA hdiv h1 ⊢
    calc 3174 * (Y ^ 2 / 2 ^ j) * (2 * (4 * Real.log (1 + 2 ^ j / 4)) ^ 2 *
          hbAmp W 1 (Finset.Ioc (2 ^ i * M) (2 * (2 ^ i * M))))
        ≤ 3174 * (Y ^ 2 / 2 ^ j) * (2 * (16 * (J : ℝ) ^ 2) * (9 / Y * A)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul (by linarith) (h1.trans hdiv)
            (hbAmp_nonneg W 1 _) (by positivity)) (by positivity)
      _ = 914112 * (J : ℝ) ^ 2 * (Y / 2 ^ j) * A := by
          field_simp
          ring
      _ = 914112 * (J : ℝ) ^ 2 / (2 * Real.pi * N) * A := by rw [hYT]; ring
      _ ≤ 150000 * (J : ℝ) ^ 2 / N * A := by
          refine mul_le_mul_of_nonneg_right ?_ hA
          rw [div_le_div_iff₀ (by positivity) hN0]
          have hJN0 : 0 ≤ (J : ℝ) ^ 2 * N := by positivity
          have hc : (914112 : ℝ) ≤ 300000 * Real.pi := by linarith
          nlinarith [mul_le_mul_of_nonneg_right hc hJN0]
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => hbDualTerm_nonneg W N j i)

/-- **The reflection inequality for one block.**  For `W` `1`-separated with all differences at
most `2^J`, `1 ≤ J`, `1 ≤ N` and `2^J < N²`:
`𝒜_{1/2}((N,2N]) ≤ 2N|W|(1 + 12C²J((1+J)²+1)) + 300000 J² Σ_{1≤j≤J} Σ_{i<3} q_{j,i}`. -/
theorem hbAmp_half_le_reflection {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W) {J N : ℕ}
    (hJ : 1 ≤ J) (hN : 1 ≤ N) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ (2 : ℝ) ^ J)
    (hJN : (2 : ℝ) ^ J < (N : ℝ) ^ 2) :
    hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) ≤
      2 * N * W.card * (1 + 12 * hbReflConst ^ 2 * J * ((1 + J) ^ 2 + 1)) +
        300000 * (J : ℝ) ^ 2 *
          ∑ j ∈ Finset.Icc 1 J, ∑ i ∈ Finset.range 3, hbDualTerm W N j i := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ → ℝ, f = fun t₁ t₂ => ‖mtWattUnitBlock N (2 * N) (t₁ - t₂)‖ ^ 2 :=
    ⟨_, rfl⟩
  have hf0 : ∀ t₁ t₂, 0 ≤ f t₁ t₂ := fun _ _ => by rw [hf]; positivity
  obtain ⟨sh, hsh⟩ : ∃ sh : ℝ → ℕ → Finset ℝ, sh = fun t₁ j =>
      W.filter fun t₂ => (2 : ℝ) ^ j / 2 ≤ |t₁ - t₂| ∧ |t₁ - t₂| ≤ (2 : ℝ) ^ j := ⟨_, rfl⟩
  -- the row of `t₁`: the diagonal and the shells
  have hrow : ∀ t₁ ∈ W, ∑ t₂ ∈ W, f t₁ t₂ ≤ 1 + ∑ j ∈ Finset.Icc 1 J, ∑ t₂ ∈ sh t₁ j, f t₁ t₂ := by
    intro t₁ ht₁
    rw [← Finset.add_sum_erase _ _ ht₁]
    refine add_le_add ?_ ?_
    · simp only [hf, sub_self]
      exact pow_le_one₀ (norm_nonneg _) (norm_mtWattUnitBlock_le_one hN le_rfl 0)
    · have hsub : W.erase t₁ ⊆ (Finset.Icc 1 J).biUnion (sh t₁) := by
        rw [hsh]; exact erase_subset_biUnion_shells hW hJ hdiam ht₁
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hf0 _ _).trans ?_
      exact sum_biUnion_le_of_nonneg' _ _ _ fun t₂ => hf0 t₁ t₂
  -- the shells
  have hshell : ∀ j ∈ Finset.Icc 1 J, ∑ t₁ ∈ W, ∑ t₂ ∈ sh t₁ j, f t₁ t₂ ≤
      W.card * (2 * hbReflConst ^ 2 * (6 * (1 + J) ^ 2 + 6)) +
        150000 * (J : ℝ) ^ 2 / N * ∑ i ∈ Finset.range 3, hbDualTerm W N j i := by
    intro j hj
    obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.mp hj
    have hT2 : (2 : ℝ) ≤ 2 ^ j := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj1
    have hTN : (2 : ℝ) ^ j < (N : ℝ) ^ 2 :=
      lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) hjJ) hJN
    have h := sum_shell_sq_norm_mtWattUnitBlock_le W hW hN hT2 hTN
    have herr := shell_error_le hN hjJ hJN
    have hper := shell_perron_le W hN hj1 hjJ
    rw [hf, hsh]
    refine h.trans (add_le_add ?_ hper)
    calc (W.card : ℝ) * (2 * 2 ^ j + 1) * (2 * hbReflConst ^ 2 *
          ((1 + Real.log (2 ^ j)) / N + 1 / Real.sqrt (2 ^ j)) ^ 2)
        = W.card * (2 * hbReflConst ^ 2 * ((2 * 2 ^ j + 1) *
            ((1 + Real.log (2 ^ j)) / N + 1 / Real.sqrt (2 ^ j)) ^ 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left herr (by positivity))
          (Nat.cast_nonneg _)
  -- assemble the weight-one pair sum
  have hone : hbAmp W 1 (Finset.Ioc N (2 * N)) ≤
      W.card * (1 + 12 * hbReflConst ^ 2 * J * ((1 + J) ^ 2 + 1)) +
        150000 * (J : ℝ) ^ 2 / N *
          ∑ j ∈ Finset.Icc 1 J, ∑ i ∈ Finset.range 3, hbDualTerm W N j i := by
    rw [← sum_normSq_mtWattUnitBlock_eq_hbAmp]
    have hcardJ : ((Finset.Icc 1 J).card : ℝ) = J := by
      rw [Nat.card_Icc]; push_cast; ring
    calc ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖mtWattUnitBlock N (2 * N) (t₁ - t₂)‖ ^ 2
        = ∑ t₁ ∈ W, ∑ t₂ ∈ W, f t₁ t₂ := by rw [hf]
      _ ≤ ∑ t₁ ∈ W, (1 + ∑ j ∈ Finset.Icc 1 J, ∑ t₂ ∈ sh t₁ j, f t₁ t₂) :=
          Finset.sum_le_sum hrow
      _ = W.card + ∑ j ∈ Finset.Icc 1 J, ∑ t₁ ∈ W, ∑ t₂ ∈ sh t₁ j, f t₁ t₂ := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          simp
      _ ≤ W.card + ∑ j ∈ Finset.Icc 1 J, (W.card * (2 * hbReflConst ^ 2 * (6 * (1 + J) ^ 2 + 6)) +
            150000 * (J : ℝ) ^ 2 / N * ∑ i ∈ Finset.range 3, hbDualTerm W N j i) :=
          add_le_add le_rfl (Finset.sum_le_sum hshell)
      _ = W.card * (1 + 12 * hbReflConst ^ 2 * J * ((1 + J) ^ 2 + 1)) +
            150000 * (J : ℝ) ^ 2 / N *
              ∑ j ∈ Finset.Icc 1 J, ∑ i ∈ Finset.range 3, hbDualTerm W N j i := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcardJ, ← Finset.mul_sum]
          ring
  calc hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) ≤ 2 * N * hbAmp W 1 (Finset.Ioc N (2 * N)) :=
        hbAmp_half_le_two_mul_hbAmp_one W N
    _ ≤ 2 * N * (W.card * (1 + 12 * hbReflConst ^ 2 * J * ((1 + J) ^ 2 + 1)) +
          150000 * (J : ℝ) ^ 2 / N *
            ∑ j ∈ Finset.Icc 1 J, ∑ i ∈ Finset.range 3, hbDualTerm W N j i) :=
        mul_le_mul_of_nonneg_left hone (by positivity)
    _ = _ := by
        field_simp
        ring

end

end RHTower.Sieve
