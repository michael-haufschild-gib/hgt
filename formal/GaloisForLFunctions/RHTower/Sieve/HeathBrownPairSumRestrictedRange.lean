import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumReflection
import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumCorollary
import GaloisForLFunctions.HTGeometry.BorelGrowthLemma

/-!
# Heath-Brown's large values theorem in the range `N ≳ T^{2/3}`

Guth–Maynard, Theorem 1.6 (Heath-Brown, J. London Math. Soc. (2) 20 (1979), Theorem 1): for a
`1`-separated set `W` in an interval of length `T` and `|a_n| ≤ 1`,

`Σ_{t₁,t₂∈W} |Σ_{N<n≤2N} a_n n^{i(t₁−t₂)}|² ≤ T^{o(1)} (|W|²N + |W|N² + |W|^{5/4}T^{1/2}N)`,

and "in the range `N ∈ [T^{2/3}, T]` the last term can be ignored".  This file proves that
statement unconditionally, with explicit constants and with the range condition in the form
`T ≤ 2^J`, `2^J < N²`, `4^J ≤ 9N³` (`J ≈ log₂ T`, i.e. `N ≳ T^{2/3}`).

**Proof.**  Let `Q = 𝒜_{1/2}((N, 8N])`.  The three dyadic blocks of `(N, 8N]` satisfy the
reflection inequality (`hbAmp_half_le_reflection`), whose dual pair sums live on blocks
`(B, 2B]` with `B ≤ 2^J/(πN)`, hence `B² ≤ 4^J/(π²N²) ≤ N`.  Corollary 2.1
(`hbAmp_sq_le_rpow`) bounds each of them by `(2(C_δ(8N)^δ)⁵|W|² Q)^{1/2}`, and the closing
inequality `le_two_mul_add_of_le_add_mul_sum` solves for `Q`:

`Q ≤ 112 N|W| c(J) + (1200000 J²)² (9J)² · 2(C_δ(8N)^δ)⁵ |W|²`,  `c(J) = 1 + 12C²J((1+J)²+1)`.

The majorant principle then gives the theorem for coefficients `|a_n| ≤ 1`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A pair sum over a disjoint union is at most twice the sum of the two pair sums. -/
theorem hbPairSum_union_le (W : Finset ℝ) {S₁ S₂ : Finset ℕ} (h : Disjoint S₁ S₂)
    (a : ℕ → ℂ) :
    hbPairSum W (S₁ ∪ S₂) a ≤ 2 * hbPairSum W S₁ a + 2 * hbPairSum W S₂ a := by
  rw [hbPairSum, hbPairSum, hbPairSum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t₁ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun t₂ _ => ?_
  rw [hbPoly, Finset.sum_union h]
  have hn := norm_add_le (hbPoly S₁ a (t₁ - t₂)) (hbPoly S₂ a (t₁ - t₂))
  have h1 := norm_nonneg (hbPoly S₁ a (t₁ - t₂))
  have h2 := norm_nonneg (hbPoly S₂ a (t₁ - t₂))
  have h3 := norm_nonneg (hbPoly S₁ a (t₁ - t₂) + hbPoly S₂ a (t₁ - t₂))
  simp only [hbPoly] at hn h1 h2 h3 ⊢
  nlinarith [sq_nonneg (‖∑ n ∈ S₁, a n * hbPhase n (t₁ - t₂)‖ -
    ‖∑ n ∈ S₂, a n * hbPhase n (t₁ - t₂)‖)]

/-- `(N, 8N]` splits into the blocks `(2^b N, 2^{b+1} N]`, `b < 3`:
`𝒜_{1/2}((N, 8N]) ≤ 4 Σ_{b<3} 𝒜_{1/2}((2^b N, 2·2^b N])`. -/
theorem hbAmp_half_Ioc_eight_le (W : Finset ℝ) (N : ℕ) :
    hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) ≤
      4 * ∑ b ∈ Finset.range 3, hbAmp W (1 / 2) (Finset.Ioc (2 ^ b * N) (2 * (2 ^ b * N))) := by
  have hsplit : Finset.Ioc N (8 * N) =
      Finset.Ioc N (2 * N) ∪ (Finset.Ioc (2 * N) (4 * N) ∪ Finset.Ioc (4 * N) (8 * N)) := by
    rw [Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega),
      Finset.Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
  have h1 := hbPairSum_union_le W (S₁ := Finset.Ioc N (2 * N))
    (S₂ := Finset.Ioc (2 * N) (4 * N) ∪ Finset.Ioc (4 * N) (8 * N))
    (by rw [Finset.disjoint_union_right]
        exact ⟨Finset.Ioc_disjoint_Ioc_of_le le_rfl, Finset.Ioc_disjoint_Ioc_of_le (by omega)⟩)
    (fun n => (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
  have h2 := hbPairSum_union_le W (S₁ := Finset.Ioc (2 * N) (4 * N))
    (S₂ := Finset.Ioc (4 * N) (8 * N)) (Finset.Ioc_disjoint_Ioc_of_le le_rfl)
    (fun n => (((n : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul, pow_one]
  rw [show 2 * (2 * N) = 4 * N by ring, show (2 : ℕ) ^ 2 * N = 4 * N by ring,
    show 2 * (4 * N) = 8 * N by ring]
  have h0a := hbAmp_nonneg W (1 / 2) (Finset.Ioc N (2 * N))
  have h0b := hbAmp_nonneg W (1 / 2) (Finset.Ioc (2 * N) (4 * N))
  have h0c := hbAmp_nonneg W (1 / 2) (Finset.Ioc (4 * N) (8 * N))
  rw [hbAmp, hsplit]
  rw [hbAmp] at h0a h0b h0c ⊢
  rw [hbAmp, hbAmp]
  linarith

/-- A nonzero dual term of a block `(N_b, 2N_b]` with `N ≤ N_b` is a pair sum on `(B, 2B]` with
`1 ≤ B` and `B² ≤ N` once `4^J ≤ 9N³`; so Corollary 2.1 bounds its square by
`2(C_δ(8N)^δ)⁵|W|² 𝒜_{1/2}((N, 8N])`. -/
theorem sq_hbDualTerm_le (W : Finset ℝ) {δ : ℝ} (hδ : 0 < δ) {J N Nb j i : ℕ} (hN : 1 ≤ N)
    (hNb : N ≤ Nb) (hj : j ≤ J) (hJN3 : (4 : ℝ) ^ J ≤ 9 * (N : ℝ) ^ 3) (hi : i < 3) :
    hbDualTerm W Nb j i ^ 2 ≤ 2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 *
      (W.card : ℝ) ^ 2 * hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) := by
  have hZ : 0 ≤ 2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (W.card : ℝ) ^ 2 *
      hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) := by
    have := (divisorBoundConst_pos hδ).le
    have := hbAmp_nonneg W (1 / 2) (Finset.Ioc N (8 * N))
    positivity
  unfold hbDualTerm
  split_ifs with hY
  · have hNb1 : 1 ≤ Nb := le_trans hN hNb
    have hT0 : (0 : ℝ) < 2 ^ j := by positivity
    have hNT : (Nb : ℝ) < 2 ^ j := by
      have hNb0 : (1 : ℝ) ≤ Nb := by exact_mod_cast hNb1
      have e : (2 : ℝ) ^ j = 2 * Real.pi * Nb * ((2 : ℝ) ^ j / (2 * Real.pi * Nb)) := by
        field_simp
      have h6 : 6 * (Nb : ℝ) ≤ 2 * Real.pi * Nb := by nlinarith [Real.pi_gt_three]
      rw [e]
      nlinarith
    have hMlo := ub_dualBase_ge hNb1 (by omega : Nb < 2 * Nb) le_rfl hT0 (by linarith)
    have hMhi := (ub_dual_edges hNb1 (by omega : Nb < 2 * Nb) le_rfl hNT hY (t := (2 : ℝ) ^ j)
      (by linarith) le_rfl).2.1
    obtain ⟨M, hM⟩ : ∃ M, M = ubDualBase (2 * Nb) ((2 : ℝ) ^ j) := ⟨_, rfl⟩
    rw [← hM] at hMlo hMhi ⊢
    have hpi := Real.pi_gt_three
    have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hNbN : (N : ℝ) ≤ Nb := by exact_mod_cast hNb
    have hMpos : 0 < M := by
      have : (0 : ℝ) < M := by linarith
      exact_mod_cast this
    have hBpos : 0 < 2 ^ i * M := by positivity
    -- `B = 2^i M ≤ 4M ≤ 2Y ≤ 2^J/(πN)`, so `B² ≤ 4^J/(π²N²) ≤ N`
    have hB : ((2 ^ i * M : ℕ) : ℝ) ≤ (2 : ℝ) ^ J / (Real.pi * N) := by
      have h4 : ((2 ^ i * M : ℕ) : ℝ) ≤ 4 * M := by
        push_cast
        have : (2 : ℝ) ^ i ≤ 4 := by
          calc (2 : ℝ) ^ i ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
            _ = 4 := by norm_num
        exact mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
      have hY2 : 4 * (M : ℝ) ≤ (2 : ℝ) ^ j / (Real.pi * Nb) := by
        have e : (2 : ℝ) ^ j / (2 * Real.pi * Nb) / 2 * 4 = (2 : ℝ) ^ j / (Real.pi * Nb) := by
          field_simp; ring
        linarith
      have hjJ : (2 : ℝ) ^ j / (Real.pi * Nb) ≤ (2 : ℝ) ^ J / (Real.pi * N) := by
        apply div_le_div₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hj) (by positivity)
        exact mul_le_mul_of_nonneg_left hNbN Real.pi_pos.le
      linarith
    have hB2 : (2 ^ i * M) ^ 2 ≤ N := by
      have hBnn : (0 : ℝ) ≤ ((2 ^ i * M : ℕ) : ℝ) := Nat.cast_nonneg _
      have hsq : (((2 ^ i * M : ℕ) : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ J / (Real.pi * N)) ^ 2 :=
        pow_le_pow_left₀ hBnn hB 2
      have hR : ((2 : ℝ) ^ J / (Real.pi * N)) ^ 2 ≤ N := by
        rw [div_pow, div_le_iff₀ (by positivity), ← pow_mul, mul_comm J 2, pow_mul]
        have h4 : ((2 : ℝ) ^ 2) ^ J = 4 ^ J := by norm_num
        rw [h4]
        have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
        have hN3 : (0 : ℝ) ≤ (N : ℝ) ^ 3 := by positivity
        calc (4 : ℝ) ^ J ≤ 9 * (N : ℝ) ^ 3 := hJN3
          _ ≤ Real.pi ^ 2 * (N : ℝ) ^ 3 := mul_le_mul_of_nonneg_right hpi2 hN3
          _ = N * (Real.pi * N) ^ 2 := by ring
      have : (((2 ^ i * M) ^ 2 : ℕ) : ℝ) ≤ N := by push_cast at hsq ⊢; linarith
      exact_mod_cast this
    exact hbAmp_sq_le_rpow W hδ hBpos hB2 subset_rfl
  · rw [sq, zero_mul]
    exact hZ

/-- **Heath-Brown's theorem in the range `N ≳ T^{2/3}`, weighted form.**  For `W` `1`-separated
with all differences at most `2^J`, `1 ≤ J`, `1 ≤ N`, `2^J < N²`, `4^J ≤ 9N³` and every `δ > 0`:
`𝒜_{1/2}((N, 8N]) ≤ 112 N|W| c(J) + (1200000 J²)² (9J)² · 2 (C_δ(8N)^δ)⁵ |W|²`,
`c(J) = 1 + 12 C² J((1+J)² + 1)`, `C = hbReflConst`, `C_δ = divisorBoundConst δ`. -/
theorem hbAmp_half_Ioc_eight_le_restricted {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {J N : ℕ} (hJ : 1 ≤ J) (hN : 1 ≤ N) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ (2 : ℝ) ^ J)
    (hJN : (2 : ℝ) ^ J < (N : ℝ) ^ 2) (hJN3 : (4 : ℝ) ^ J ≤ 9 * (N : ℝ) ^ 3) {δ : ℝ}
    (hδ : 0 < δ) :
    hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) ≤
      112 * N * W.card * (1 + 12 * hbReflConst ^ 2 * J * ((1 + J) ^ 2 + 1)) +
        (1200000 * (J : ℝ) ^ 2) ^ 2 * (9 * (J : ℝ)) ^ 2 *
          (2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (W.card : ℝ) ^ 2) := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 + 12 * hbReflConst ^ 2 * J * ((1 + J) ^ 2 + 1) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  -- the index set of the dual terms of the three blocks
  obtain ⟨I, hI⟩ : ∃ I : Finset (ℕ × ℕ × ℕ),
      I = Finset.range 3 ×ˢ (Finset.Icc 1 J ×ˢ Finset.range 3) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ × ℕ × ℕ → ℝ,
      q = fun x => hbDualTerm W (2 ^ x.1 * N) x.2.1 x.2.2 := ⟨_, rfl⟩
  have hIcard : (I.card : ℝ) = 9 * J := by
    rw [hI, Finset.card_product, Finset.card_product, Nat.card_Icc, Finset.card_range]
    push_cast
    ring
  -- each block satisfies the reflection inequality
  have hblock : ∀ b ∈ Finset.range 3,
      hbAmp W (1 / 2) (Finset.Ioc (2 ^ b * N) (2 * (2 ^ b * N))) ≤
        2 * (2 ^ b * N : ℕ) * W.card * c + 300000 * (J : ℝ) ^ 2 *
          ∑ j ∈ Finset.Icc 1 J, ∑ i ∈ Finset.range 3, hbDualTerm W (2 ^ b * N) j i := by
    intro b _
    have hNb : N ≤ 2 ^ b * N := Nat.le_mul_of_pos_left N (by positivity)
    have hNb1 : 1 ≤ 2 ^ b * N := le_trans hN hNb
    have hJNb : (2 : ℝ) ^ J < ((2 ^ b * N : ℕ) : ℝ) ^ 2 := by
      have : (N : ℝ) ≤ ((2 ^ b * N : ℕ) : ℝ) := by exact_mod_cast hNb
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    rw [hc]
    exact hbAmp_half_le_reflection hW hJ hNb1 hdiam hJNb
  have hsumX : ∑ b ∈ Finset.range 3, 2 * ((2 ^ b * N : ℕ) : ℝ) * W.card * c =
      14 * N * W.card * c := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  have hmain : hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) ≤
      56 * N * W.card * c + 4 * (300000 * (J : ℝ) ^ 2) * ∑ x ∈ I, q x := by
    have hsplit := hbAmp_half_Ioc_eight_le W N
    have hsum : ∑ b ∈ Finset.range 3, hbAmp W (1 / 2) (Finset.Ioc (2 ^ b * N) (2 * (2 ^ b * N)))
        ≤ 14 * N * W.card * c + 300000 * (J : ℝ) ^ 2 * ∑ x ∈ I, q x := by
      refine (Finset.sum_le_sum hblock).trans (le_of_eq ?_)
      rw [Finset.sum_add_distrib, hsumX, ← Finset.mul_sum, hI, hq, Finset.sum_product]
      congr 2
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_product]
    linarith
  have hZ0 : 0 ≤ 2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (W.card : ℝ) ^ 2 := by
    have := (divisorBoundConst_pos hδ).le
    positivity
  have hclose := le_two_mul_add_of_le_add_mul_sum I (Q := hbAmp W (1 / 2) (Finset.Ioc N (8 * N)))
    (X := 56 * N * W.card * c) (Y := 4 * (300000 * (J : ℝ) ^ 2))
    (Z := 2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (W.card : ℝ) ^ 2) (q := q)
    (hbAmp_nonneg W (1 / 2) _) (fun x _ => by rw [hq]; exact hbDualTerm_nonneg W _ _ _)
    (by positivity) hZ0 hmain fun x hx => by
      rw [hI] at hx
      obtain ⟨-, hj, hi⟩ : x.1 ∈ Finset.range 3 ∧ x.2.1 ∈ Finset.Icc 1 J ∧
          x.2.2 ∈ Finset.range 3 := by simpa only [Finset.mem_product] using hx
      simp only [hq]
      exact sq_hbDualTerm_le W hδ (Nb := 2 ^ x.1 * N) hN
        (Nat.le_mul_of_pos_left N (pow_pos two_pos _))
        (Finset.mem_Icc.mp hj).2 hJN3 (Finset.mem_range.mp hi)
  rw [hIcard] at hclose
  calc hbAmp W (1 / 2) (Finset.Ioc N (8 * N))
      ≤ 2 * (56 * N * W.card * c) + (4 * (300000 * (J : ℝ) ^ 2)) ^ 2 * ((9 * (J : ℝ)) ^ 2 *
          (2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (W.card : ℝ) ^ 2)) := hclose
    _ = _ := by rw [hc]; ring

/-- **Heath-Brown's theorem in the range `N ≳ T^{2/3}`** (Guth–Maynard, Theorem 1.6, without the
third term).  For `W` `1`-separated with all differences at most `2^J`, `1 ≤ J`, `1 ≤ N`,
`2^J < N²`, `4^J ≤ 9N³`, every `δ > 0` and `|a_n| ≤ 1` on `(N, 2N]`:
`Σ_{t₁,t₂∈W} |Σ_{N<n≤2N} a_n n^{i(t₁−t₂)}|² ≤ 224 c(J) |W| N² + 4 (1200000J²)²(9J)² (C_δ(8N)^δ)⁵ |W|² N`.
With `J = ⌈log₂ T⌉` this is `≪_δ T^{δ}(|W| N² + |W|² N)` for `N ≥ (2T)^{2/3}`. -/
theorem hbPairSum_Ioc_le_restrictedRange {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {J N : ℕ} (hJ : 1 ≤ J) (hN : 1 ≤ N) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ (2 : ℝ) ^ J)
    (hJN : (2 : ℝ) ^ J < (N : ℝ) ^ 2) (hJN3 : (4 : ℝ) ^ J ≤ 9 * (N : ℝ) ^ 3) {δ : ℝ}
    (hδ : 0 < δ) {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc N (2 * N)) a ≤
      224 * (1 + 12 * hbReflConst ^ 2 * J * ((1 + J) ^ 2 + 1)) * W.card * (N : ℝ) ^ 2 +
        4 * (1200000 * (J : ℝ) ^ 2) ^ 2 * (9 * (J : ℝ)) ^ 2 *
          (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (W.card : ℝ) ^ 2 * N := by
  have h1 := hbPairSum_le_two_mul_hbAmp_half W ha
  have hmono : hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) ≤ hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) :=
    hbPairSum_ofReal_mono_support W (Finset.Ioc_subset_Ioc_right (by omega))
      fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h2 := hbAmp_half_Ioc_eight_le_restricted hW hJ hN hdiam hJN hJN3 hδ
  have hN0 : (0 : ℝ) ≤ 2 * N := by positivity
  calc hbPairSum W (Finset.Ioc N (2 * N)) a ≤ 2 * N * hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) := h1
    _ ≤ 2 * N * hbAmp W (1 / 2) (Finset.Ioc N (8 * N)) := mul_le_mul_of_nonneg_left hmono hN0
    _ ≤ 2 * N * (112 * N * W.card * (1 + 12 * hbReflConst ^ 2 * J * ((1 + J) ^ 2 + 1)) +
          (1200000 * (J : ℝ) ^ 2) ^ 2 * (9 * (J : ℝ)) ^ 2 *
            (2 * (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (W.card : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h2 hN0
    _ = _ := by ring

/-- **Heath-Brown's theorem for `N ≥ (2T)^{2/3}`, in terms of `T`.**  For `W` `1`-separated in an
interval of length `T ≥ 1`, `1 ≤ N` with `2T < N²` and `4T² ≤ 9N³`, every `δ > 0` and `|a_n| ≤ 1`
on `(N, 2N]`, with `L = 1 + log₂ T`:
`Σ_{t₁,t₂∈W} |Σ_{N<n≤2N} a_n n^{i(t₁−t₂)}|² ≤ 224 c(L) |W| N² + 4 (1200000L²)²(9L)² (C_δ(8N)^δ)⁵ |W|² N`,
`c(L) = 1 + 12 C² L((1+L)² + 1)`: the bound `T^{o(1)}(|W|N² + |W|²N)`. -/
theorem hbPairSum_Ioc_le_of_twoThirds {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {N : ℕ} (hN : 1 ≤ N)
    (hN2 : 2 * T < (N : ℝ) ^ 2) (hN3 : 4 * T ^ 2 ≤ 9 * (N : ℝ) ^ 3) {δ : ℝ} (hδ : 0 < δ)
    {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc N (2 * N)) a ≤
      224 * (1 + 12 * hbReflConst ^ 2 * (1 + Real.logb 2 T) * ((1 + (1 + Real.logb 2 T)) ^ 2 + 1)) *
          W.card * (N : ℝ) ^ 2 +
        4 * (1200000 * (1 + Real.logb 2 T) ^ 2) ^ 2 * (9 * (1 + Real.logb 2 T)) ^ 2 *
          (divisorBoundConst δ * ((8 * N : ℕ) : ℝ) ^ δ) ^ 5 * (W.card : ℝ) ^ 2 * N := by
  obtain ⟨k, hk1, hk2⟩ := GaloisForLFunctions.Nevanlinna.exists_dyadic_band hT
  have hpow : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hJN : (2 : ℝ) ^ (k + 1) < (N : ℝ) ^ 2 := by rw [hpow]; linarith
  have hJN3 : (4 : ℝ) ^ (k + 1) ≤ 9 * (N : ℝ) ^ 3 := by
    have h4 : (4 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1)) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have hk0 : (0 : ℝ) ≤ 2 ^ k := by positivity
    rw [h4, hpow]
    nlinarith
  have hdiam' : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ (2 : ℝ) ^ (k + 1) := fun t ht t' ht' =>
    (hdiam t ht t' ht').trans hk2.le
  have hmain := hbPairSum_Ioc_le_restrictedRange hW (J := k + 1) (by omega) hN hdiam' hJN hJN3
    hδ ha
  have hkL : ((k + 1 : ℕ) : ℝ) ≤ 1 + Real.logb 2 T := by
    have hlog : (k : ℝ) ≤ Real.logb 2 T := by
      have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hk1
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
    push_cast
    linarith
  have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  refine hmain.trans ?_
  have hC0 := (divisorBoundConst_pos hδ).le
  have hL0 : 0 ≤ 1 + Real.logb 2 T := hk0.trans hkL
  gcongr

end

end RHTower.Sieve
