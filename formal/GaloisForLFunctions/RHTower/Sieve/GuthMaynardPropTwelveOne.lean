import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropTwelveOneAlgebra
import GaloisForLFunctions.RHTower.Sieve.GuthMaynardKeyPropAssembly

/-!
# Guth–Maynard Proposition 12.1: large values for `T^{5/6} ≤ N ≤ T`

`propTwelveOne_of_fullBound`: given (12.1) for the paper's exponents `j = k`
(`FullBoundStatement w k k`), for every `ε > 0` there is `C` such that, for `T ≥ 2`,
`T^{5/6} ≤ N ≤ T`, `σ ≥ 7/10`, `|b_n| ≤ 1` and a `1`-separated `W ⊂ [T₀, T₀ + T]` with
`|Σ_{N<n≤2N} b_n n^{it}| ≥ N^σ` on `W`,

`|W| ≤ C T^ε (N^{2−2σ} + T^{1/2}N^{3−4σ} + T^{k/(k+1)}N^{(4−6σ)k/(k+1)} + N^{(5−6σ)4k/(4k+3)}T^{2/(4k+3)})`.

This is the first statement of Proposition 12.1 (`prpstn:BigN`), for each fixed `k`, and it needs
no upper bound on `σ`.  Mechanism (the proof of Proposition 12.1): split `(N, 2N]` into two plateau pieces;
on a piece of length `N_i ∈ [5N/6, 2N]` with level `V/2` a maximal `T^ε`-separated subset is bounded
by (12.1) on an interval of length `2T` (`card_le_of_fullBoundStatement`), and the rescaling
`fullBound_le_of_rescale` returns to `(N, T, σ)`; the 5th, 7th and 8th terms of (12.1) are at most
`T^{1/2}N^{3−4σ}`; and of the 2nd term `N^{5−6σ}` and the mean value term `TN^{1−2σ}` of (1.2)
the smaller is at most `T^{1/2}N^{3−4σ}` (`min_le_bigN_term_six`), so the better of the two bounds
gives the claim.  `propTwelveOne_of_S_bounds` is the same from Propositions 6.1 and 11.2.
-/

set_option autoImplicit false

open Finset Complex

namespace RHTower.GuthMaynard

open RHTower.Sieve

noncomputable section

/-! ### One plateau piece -/

/-- **(12.1) for a `1`-separated set.**  Thinning to a `(2T)^{ε/2}`-separated subset and applying
(12.1) on `[T₀, T₀ + 2T]`: `|W| ≤ C T^ε fullBound M (2T) (log_M V)` for a smoothed polynomial of
length `M ∈ [(2T)^{3/4}, 2T]` exceeding `V` on `W`. -/
theorem card_le_of_fullBoundStatement {w : CGLSmoothBump} {j k : ℕ}
    (hFB : FullBoundStatement w j k) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : ℕ) (T T₀ V : ℝ) (c : ℕ → ℂ) (W : Finset ℝ),
      1 ≤ T → (2 * T) ^ (3 / 4 : ℝ) ≤ M → (M : ℝ) ≤ 2 * T → 1 < (M : ℝ) →
      (∀ n, ‖c n‖ ≤ 1) → (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → IsSeparated 1 W → 0 < V →
      (∀ t ∈ W, V ≤ ‖smoothedDyadicPoly w M c t‖) →
      (W.card : ℝ) ≤ C * T ^ ε * fullBound M (2 * T) (Real.logb M V) j k := by
  obtain ⟨K, hK0, hK⟩ := hFB (ε / 2) (half_pos hε)
  refine ⟨3 * K * 2 ^ ε, by positivity, ?_⟩
  intro M T T₀ V c W hT hM34 hM2T hM1 hc hW hsep hV hbig
  have hT2 : 1 ≤ 2 * T := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (2 * T) ^ (ε / 2) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := hs ▸ Real.one_le_rpow hT2 (by positivity)
  obtain ⟨S, hSW, hSsep, hWS⟩ := exists_separated_subset_of_isSeparated hsep (by linarith : 0 < s)
  have hσ : (M : ℝ) ^ Real.logb M V = V := Real.rpow_logb (by linarith) hM1.ne' hV
  have hS := hK M (Real.logb M V) (2 * T) T₀ c S (by linarith) hM34 hM2T hc
    (fun t ht => ⟨(hW t (hSW ht)).1, by linarith [(hW t (hSW ht)).2]⟩) (hs ▸ hSsep)
    (fun t ht => by rw [hσ]; exact hbig t (hSW ht))
  have hF0 : 0 ≤ fullBound M (2 * T) (Real.logb M V) j k := by unfold fullBound; positivity
  have hss : s * (2 * T) ^ (ε / 2) = 2 ^ ε * T ^ ε := by
    rw [hs, ← Real.rpow_add (by linarith), add_halves, Real.mul_rpow (by norm_num) (by linarith)]
  calc (W.card : ℝ) ≤ (2 * s + 1) * S.card := hWS
    _ ≤ 3 * s * S.card := mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    _ ≤ 3 * s * (K * (2 * T) ^ (ε / 2) * fullBound M (2 * T) (Real.logb M V) j k) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = 3 * K * (s * (2 * T) ^ (ε / 2)) * fullBound M (2 * T) (Real.logb M V) j k := by ring
    _ = 3 * K * 2 ^ ε * T ^ ε * fullBound M (2 * T) (Real.logb M V) j k := by rw [hss]; ring

/-! ### Proposition 12.1 -/

/-- `(2T)^{3/4} ≤ (5/6) T^{5/6}` for `T ≥ 2^{20}`. -/
theorem two_mul_rpow_three_fourths_le {T : ℝ} (hT : 2 ^ (20 : ℝ) ≤ T) :
    (2 * T) ^ (3 / 4 : ℝ) ≤ 5 / 6 * T ^ (5 / 6 : ℝ) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have hroot : (2 : ℝ) ^ (5 / 3 : ℝ) ≤ T ^ (1 / 12 : ℝ) := by
    calc (2 : ℝ) ^ (5 / 3 : ℝ) = ((2 : ℝ) ^ (20 : ℝ)) ^ (1 / 12 : ℝ) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ T ^ (1 / 12 : ℝ) := Real.rpow_le_rpow (by positivity) hT (by norm_num)
  -- `2^{3/4} · 6/5 ≤ 2^{5/4} ≤ 2^{5/3}`
  have h65 : (6 / 5 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hc : (2 : ℝ) ^ (3 / 4 : ℝ) * (6 / 5) ≤ T ^ (1 / 12 : ℝ) := by
    calc (2 : ℝ) ^ (3 / 4 : ℝ) * (6 / 5) ≤ 2 ^ (3 / 4 : ℝ) * 2 ^ (1 / 2 : ℝ) := by gcongr
      _ = 2 ^ (5 / 4 : ℝ) := by rw [← Real.rpow_add (by norm_num)]; norm_num
      _ ≤ 2 ^ (5 / 3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ ≤ T ^ (1 / 12 : ℝ) := hroot
  have e : T ^ (5 / 6 : ℝ) = T ^ (1 / 12 : ℝ) * T ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  rw [Real.mul_rpow (by norm_num) hT0.le, e]
  have h34 : 0 ≤ T ^ (3 / 4 : ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hc h34]

/-- **Guth–Maynard, Proposition 12.1** (first statement, fixed `k ≥ 1`, every `σ ≥ 7/10`), from
(12.1) with `j = k`. -/
theorem propTwelveOne_of_fullBound {w : CGLSmoothBump} {k : ℕ} (hFB : FullBoundStatement w k k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ σ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → T ^ (5 / 6 : ℝ) ≤ N → (N : ℝ) ≤ T → 7 / 10 ≤ σ → (∀ n, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
        (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3))) := by
  classical
  obtain ⟨C₁, hC₁, hpiece⟩ := card_le_of_fullBoundStatement hFB hε
  refine ⟨2 ^ (20 : ℝ) + 1 + 627 + 5 * (2 * C₁ * 2 ^ (13 : ℝ)), by positivity, ?_⟩
  intro N T T₀ σ b W hT hTN hNT hσ hb hW hsep hbig
  have hbig' : ∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖dyadicPoly N b t‖ := hbig
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hTε : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  have hN1 : (1 : ℝ) ≤ N := (Real.one_le_rpow hT1 (by norm_num)).trans hTN
  have hN0 : (0 : ℝ) < N := by linarith
  -- the four target terms and the remaining terms of (12.1)
  obtain ⟨t1, ht1⟩ : ∃ x, x = (N : ℝ) ^ (2 - 2 * σ) := ⟨_, rfl⟩
  obtain ⟨t6, ht6⟩ : ∃ x, x = T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) := ⟨_, rfl⟩
  obtain ⟨t3, ht3⟩ : ∃ x, x = T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) :=
    ⟨_, rfl⟩
  obtain ⟨t4, ht4⟩ : ∃ x, x = (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) *
      T ^ (2 / (4 * (k : ℝ) + 3)) := ⟨_, rfl⟩
  rw [← ht1, ← ht6, ← ht3, ← ht4]
  have h1 : 0 ≤ t1 := by rw [ht1]; positivity
  have h3 : 0 ≤ t3 := by rw [ht3]; positivity
  have h4 : 0 ≤ t4 := by rw [ht4]; positivity
  have h6 : 0 ≤ t6 := by rw [ht6]; positivity
  have hP0 : 0 ≤ t1 + t6 + t3 + t4 := by positivity
  rcases W.eq_empty_or_nonempty with he | ⟨t₀, ht₀⟩
  · rw [he, card_empty, Nat.cast_zero]; positivity
  -- `σ ≤ 1`, hence `t1 ≥ 1`
  have hN2 : (1 : ℝ) < N := lt_of_lt_of_le (Real.one_lt_rpow (by linarith) (by norm_num)) hTN
  have hσ1 : σ ≤ 1 := by
    have h := (hbig' t₀ ht₀).trans (norm_dyadicPoly_le hb t₀)
    rw [← Real.rpow_le_rpow_left_iff hN2, Real.rpow_one]; exact h
  have ht1' : 1 ≤ t1 := ht1 ▸ Real.one_le_rpow hN1 (by linarith)
  have hcardT : (W.card : ℝ) ≤ T + 1 := by
    have h := card_le_of_separated (u := id) one_pos (by linarith) hsep hW
    simpa only [div_one] using h
  have hfinal : ∀ c : ℝ, 0 ≤ c → c ≤ 2 ^ (20 : ℝ) + 1 + 627 + 5 * (2 * C₁ * 2 ^ (13 : ℝ)) →
      (W.card : ℝ) ≤ c * T ^ ε * (t1 + t6 + t3 + t4) →
      (W.card : ℝ) ≤ (2 ^ (20 : ℝ) + 1 + 627 + 5 * (2 * C₁ * 2 ^ (13 : ℝ))) * T ^ ε *
        (t1 + t6 + t3 + t4) := fun c _ hc h =>
    h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hP0)
  have hc1 : (0 : ℝ) ≤ 5 * (2 * C₁ * 2 ^ (13 : ℝ)) := by positivity
  have hc2 : (0 : ℝ) ≤ 2 ^ (20 : ℝ) + 1 := by positivity
  -- small `T`: `|W| ≤ T + 1`
  rcases lt_or_ge T (2 ^ (20 : ℝ)) with hTs | hTl
  · refine hfinal (2 ^ (20 : ℝ) + 1) hc2 (by linarith) ?_
    have : 1 ≤ T ^ ε * (t1 + t6 + t3 + t4) := one_le_mul_of_one_le_of_one_le hTε (by linarith)
    nlinarith
  -- the mean value bound `|W| ≤ 627 (T N^{1−2σ} + t1)`
  have hV : (0 : ℝ) < (N : ℝ) ^ σ := Real.rpow_pos_of_pos hN0 _
  have hmv := card_mul_sq_le_meanValue (by exact_mod_cast hN1) hT0.le hV.le hb hW hsep hbig'
  obtain ⟨u, hu⟩ : ∃ u, u = T * (N : ℝ) ^ (1 - 2 * σ) := ⟨_, rfl⟩
  have hmvW : (W.card : ℝ) ≤ 627 * (u + t1) := by
    have eu : (N : ℝ) ^ (1 - 2 * σ) = N / ((N : ℝ) ^ σ) ^ 2 := by
      rw [show 1 - 2 * σ = 1 - σ * 2 by ring, Real.rpow_sub hN0, Real.rpow_one,
        Real.rpow_mul hN0.le, Real.rpow_two]
    have et : (N : ℝ) ^ (2 - 2 * σ) = N ^ 2 / ((N : ℝ) ^ σ) ^ 2 := by
      rw [show 2 - 2 * σ = 2 - σ * 2 by ring, Real.rpow_sub hN0, Real.rpow_mul hN0.le,
        Real.rpow_two, Real.rpow_two]
    have e : u + t1 = (T + N) * N / ((N : ℝ) ^ σ) ^ 2 := by
      rw [hu, ht1, eu, et]; field_simp
    rw [e, mul_div_assoc', le_div_iff₀ (by positivity)]
    linarith [hmv]
  -- the plateau pieces
  have hN6 : 6 ≤ N := by
    have h20 : (6 : ℝ) ≤ T ^ (5 / 6 : ℝ) := by
      calc (6 : ℝ) ≤ (2 ^ (20 : ℝ)) ^ (5 / 6 : ℝ) := by
            rw [← Real.rpow_mul (by norm_num)]
            calc (6 : ℝ) ≤ 2 ^ (3 : ℝ) := by norm_num
              _ ≤ 2 ^ ((20 : ℝ) * (5 / 6)) := Real.rpow_le_rpow_of_exponent_le (by norm_num)
                  (by norm_num)
        _ ≤ T ^ (5 / 6 : ℝ) := Real.rpow_le_rpow (by positivity) hTl (by norm_num)
    exact_mod_cast h20.trans hTN
  obtain ⟨N₁, N₂, P₁, P₂, hU, hD, hP₁, hP₂, h₁, h₂, h₃, h₄, h₅, h₆⟩ := exists_two_plateau_pieces hN6
  have hpieceT := two_mul_rpow_three_fourths_le hTl
  have piece : ∀ (M : ℕ) (P : Finset ℕ),
      (∀ n ∈ P, M < n ∧ n ≤ 2 * M ∧ 6 * M ≤ 5 * n ∧ 5 * n ≤ 9 * M) → 5 * N ≤ 6 * M → M ≤ 2 * N →
      2 ≤ M →
      (((W.filter fun t : ℝ => (N : ℝ) ^ σ / 2 ≤
          ‖∑ n ∈ P, b n * Complex.exp (Complex.I * t * Real.log n)‖).card : ℕ) : ℝ) ≤
        C₁ * 2 ^ (13 : ℝ) * T ^ ε * fullBound N T σ k k := by
    intro M P hP hM1 hM2 hM3
    have hM1' : (5 : ℝ) * N ≤ 6 * M := by exact_mod_cast hM1
    have hM2' : (M : ℝ) ≤ 2 * N := by exact_mod_cast hM2
    have hMg : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
    have hM0 : (0 : ℝ) < M := by linarith
    have hb' : ∀ n, ‖(fun n => if n ∈ P then b n else 0) n‖ ≤ 1 := fun n => by
      dsimp only; split_ifs
      · exact hb n
      · simp
    have hbound := hpiece M T T₀ ((N : ℝ) ^ σ / 2) (fun n => if n ∈ P then b n else 0)
      (W.filter fun t : ℝ => (N : ℝ) ^ σ / 2 ≤
        ‖∑ n ∈ P, b n * Complex.exp (Complex.I * t * Real.log n)‖) hT1
      (hpieceT.trans (by linarith [mul_le_mul_of_nonneg_left hTN (by norm_num : (0 : ℝ) ≤ 5 / 6)]))
      (by linarith) hMg hb' (fun t ht => hW t (Finset.mem_filter.mp ht).1)
      (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
      (by positivity) (fun t ht => by
        rw [smoothedDyadicPoly_indicator w hP]; exact (Finset.mem_filter.mp ht).2)
    refine hbound.trans ?_
    -- rescale `(M, 2T, log_M(V/2))` to `(N, T, σ)`
    have hσM : (M : ℝ) ^ (-Real.logb M ((N : ℝ) ^ σ / 2)) = 2 * (N : ℝ) ^ (-σ) := by
      rw [Real.rpow_neg hM0.le, Real.rpow_logb hM0 hMg.ne' (by positivity), Real.rpow_neg hN0.le]
      field_simp
    have hres := fullBound_le_of_rescale (j := k) (k := k) (T := T) (T' := 2 * T) hM0 hN0
      (by linarith) hM2' le_rfl hσM.le
    calc C₁ * T ^ ε * fullBound M (2 * T) (Real.logb M ((N : ℝ) ^ σ / 2)) k k
        ≤ C₁ * T ^ ε * (2 ^ (13 : ℝ) * fullBound N T σ k k) :=
          mul_le_mul_of_nonneg_left hres (by positivity)
      _ = C₁ * 2 ^ (13 : ℝ) * T ^ ε * fullBound N T σ k k := by ring
  have hcover : W ⊆
      (W.filter fun t : ℝ => (N : ℝ) ^ σ / 2 ≤
        ‖∑ n ∈ P₁, b n * Complex.exp (Complex.I * t * Real.log n)‖) ∪
      (W.filter fun t : ℝ => (N : ℝ) ^ σ / 2 ≤
        ‖∑ n ∈ P₂, b n * Complex.exp (Complex.I * t * Real.log n)‖) := by
    intro t ht
    have hsplit : dyadicPoly N b t = ∑ n ∈ P₁, b n * Complex.exp (Complex.I * t * Real.log n) +
        ∑ n ∈ P₂, b n * Complex.exp (Complex.I * t * Real.log n) := by
      unfold dyadicPoly; rw [hU, sum_union hD]
    have h : (N : ℝ) ^ σ ≤ ‖∑ n ∈ P₁, b n * Complex.exp (Complex.I * t * Real.log n)‖ +
        ‖∑ n ∈ P₂, b n * Complex.exp (Complex.I * t * Real.log n)‖ :=
      (hbig' t ht).trans (hsplit ▸ norm_add_le _ _)
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases le_or_gt ((N : ℝ) ^ σ / 2)
        ‖∑ n ∈ P₁, b n * Complex.exp (Complex.I * t * Real.log n)‖ with hh | hh
    · exact Or.inl ⟨ht, hh⟩
    · exact Or.inr ⟨ht, by linarith⟩
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hc' := (Nat.cast_le (α := ℝ)).mpr hc
  rw [Nat.cast_add] at hc'
  have hFBW : (W.card : ℝ) ≤ 2 * C₁ * 2 ^ (13 : ℝ) * T ^ ε * fullBound N T σ k k := by
    have e1 := piece N₁ P₁ hP₁ h₁ h₂ h₅
    have e2 := piece N₂ P₂ hP₂ h₃ h₄ h₆
    linarith
  -- the dominated terms of (12.1)
  have d5 := bigN_term_five_le (σ := σ) hT0 hTN
  have d7 := bigN_term_seven_le hT0 hN1 hTN hσ
  have d8 := bigN_term_eight_le hT0 hN1 hTN hσ
  have hmin := min_le_bigN_term_six (σ := σ) hT0 hN0
  rw [← hu, ← ht6] at hmin
  rw [← ht6] at d5 d7 d8
  have hfb : fullBound N T σ k k = t1 + (N : ℝ) ^ (5 - 6 * σ) + t3 + t4 +
      T ^ (4 / 3 : ℝ) * (N : ℝ) ^ (2 - 4 * σ) + t6 + T * (N : ℝ) ^ (9 / 2 - 7 * σ) +
      T ^ (18 / 19 : ℝ) * (N : ℝ) ^ (72 / 19 - 112 * σ / 19) := by
    rw [ht1, ht3, ht4, ht6]; rfl
  have hA0 : 0 ≤ 2 * C₁ * 2 ^ (13 : ℝ) * T ^ ε := by positivity
  rcases le_total u ((N : ℝ) ^ (5 - 6 * σ)) with hle | hle
  · -- the mean value bound wins
    have hu6 : u ≤ t6 := (min_eq_left hle) ▸ hmin
    refine hfinal 627 (by norm_num) (by linarith) ?_
    have : t1 + t6 ≤ T ^ ε * (t1 + t6 + t3 + t4) := by nlinarith
    linarith
  · -- (12.1) wins
    have h26 : (N : ℝ) ^ (5 - 6 * σ) ≤ t6 := (min_eq_right hle) ▸ hmin
    refine hfinal (5 * (2 * C₁ * 2 ^ (13 : ℝ))) hc1 (by linarith) ?_
    have hfb' : fullBound N T σ k k ≤ 5 * (t1 + t6 + t3 + t4) := by
      rw [hfb]; linarith
    calc (W.card : ℝ) ≤ 2 * C₁ * 2 ^ (13 : ℝ) * T ^ ε * fullBound N T σ k k := hFBW
      _ ≤ 2 * C₁ * 2 ^ (13 : ℝ) * T ^ ε * (5 * (t1 + t6 + t3 + t4)) :=
          mul_le_mul_of_nonneg_left hfb' hA0
      _ = 5 * (2 * C₁ * 2 ^ (13 : ℝ)) * T ^ ε * (t1 + t6 + t3 + t4) := by ring

/-- **Proposition 12.1 from Propositions 6.1 (`j = k`) and 11.2.** -/
theorem propTwelveOne_of_S_bounds (w : CGLUnitRealSmoothBump) {k : ℕ} (hk : 1 ≤ k)
    (hS2 : PropSixOneBound w.toCGLRealSmoothBump k k)
    (hS3 : PropElevenTwoBound w.toCGLRealSmoothBump) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (T T₀ σ : ℝ) (b : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → T ^ (5 / 6 : ℝ) ≤ N → (N : ℝ) ≤ T → 7 / 10 ≤ σ → (∀ n, ‖b n‖ ≤ 1) →
      (∀ t ∈ W, T₀ ≤ t ∧ t ≤ T₀ + T) → (∀ t ∈ W, ∀ t' ∈ W, t ≠ t' → 1 ≤ |t - t'|) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * Complex.exp (Complex.I * t * Real.log n)‖) →
      (W.card : ℝ) ≤ C * T ^ ε * ((N : ℝ) ^ (2 - 2 * σ) + T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * σ) +
        T ^ ((k : ℝ) / (k + 1)) * (N : ℝ) ^ ((4 - 6 * σ) * ((k : ℝ) / (k + 1))) +
        (N : ℝ) ^ ((5 - 6 * σ) * (4 * (k : ℝ) / (4 * k + 3))) * T ^ (2 / (4 * (k : ℝ) + 3))) :=
  propTwelveOne_of_fullBound (fullBoundStatement_of_S_bounds w hk hk hS2 hS3) hε

end

end RHTower.GuthMaynard
