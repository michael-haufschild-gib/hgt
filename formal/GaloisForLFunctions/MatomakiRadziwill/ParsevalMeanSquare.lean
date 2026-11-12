import GaloisForLFunctions.MatomakiRadziwill.ParsevalWindows
import GaloisForLFunctions.RHTower.Sieve.LinearMeanSquareBounded

/-!
# Matomäki–Radziwiłł for `λχ` in additive short windows

For a non-principal Dirichlet character `χ` and every `ε > 0` there is `h₀` such that for every
`h ≥ h₀` there is `X₀` with (`exists_short_sum_mean_square_twLiouville_le`)

`Σ_{X ≤ m < 2X} |Σ_{m < n ≤ m + h} λ(n)χ(n)|² ≤ ε h² X`   for `X ≥ X₀`.

The logarithmic windows of length `δ = log(1 + h/Y)`, `Y ≥ X`, have mean square
(`integral_normSq_window_le`) at most `32h²ε' + 768h + 6`, where `ε'` bounds the
Dirichlet-polynomial mean square at frequencies `|w| ≤ X/√h` (`exists_mean_square_twLiouville_le`):
the window kernel gives `δ² ε'` below `X/√h`, the dyadic tail `≤ 96(√h + h)/X²`
(`integral_normSq_logWindowSum_le_split`), and passing from `f(n)/n` to `f(n)` costs a factor
`(4X)²` and an error `O((h²/X)²)` (`integral_normSq_logWindowSum_le_coefA`).  The corpus block
transfer `Sieve.sum_normSq_window_le_bound` with ratio `1 + 1/N` over `N` blocks converts this into
additive windows at cost `3N(2G + 2(h/N + 1)²/N)`.
-/

open Finset MeasureTheory Set Filter Topology RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem log_four_le_two : Real.log 4 ≤ 2 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [e]; nlinarith

/-- **Logarithmic windows of length `log(1 + h/Y)` from the Dirichlet-polynomial mean square.** -/
theorem integral_normSq_window_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X h : ℕ} (hX1 : 1 ≤ X)
    (hh : 1 ≤ h) (hhX : (4 * (h : ℝ) + 1) * h ≤ X) {εm : ℝ}
    (hMR : (∫ w in Icc (-((X : ℝ) * Real.exp (-(Real.log h / 2))))
        ((X : ℝ) * Real.exp (-(Real.log h / 2))), ‖fullPoly f X w‖ ^ 2) ≤ εm)
    {Y' : ℝ} (hY' : (X : ℝ) ≤ Y') (E : Set ℝ) :
    (∫ u in E, ‖logWindowSum f (Finset.Ioc X (4 * X)) (Real.log (1 + (h : ℝ) / Y')) u‖ ^ 2)
      ≤ 32 * (h : ℝ) ^ 2 * εm + 768 * h + 6 := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hY'0 : 0 < Y' := lt_of_lt_of_le hX0 hY'
  set δ := Real.log (1 + (h : ℝ) / Y') with hδdef
  have hq0 : 0 ≤ (h : ℝ) / Y' := by positivity
  have hhY : (h : ℝ) / Y' ≤ h / X := div_le_div_of_nonneg_left hh0.le hX0 hY'
  have hδ0 : 0 ≤ δ := Real.log_nonneg (by linarith)
  have hδle : δ ≤ h / X := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + (h : ℝ) / Y' by positivity)
    linarith
  have hexpδ : Real.exp δ - 1 ≤ h / X := by
    rw [hδdef, Real.exp_log (by positivity)]; linarith
  -- `e₂ = e^{log h/2} = √h`
  set e2 := Real.exp (Real.log h / 2) with he2
  have he2sq : e2 ^ 2 = h := by
    rw [he2, ← Real.exp_nat_mul]
    push_cast
    rw [show (2 : ℝ) * (Real.log h / 2) = Real.log h by ring, Real.exp_log hh0]
  have he21 : 1 ≤ e2 := Real.one_le_exp (by have := Real.log_nonneg hh1; linarith)
  have he2h : e2 ≤ h := by
    have : e2 ≤ e2 ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) he21
    linarith
  set W := (X : ℝ) * Real.exp (-(Real.log h / 2)) with hWdef
  have hWe : W = X / e2 := by rw [hWdef, Real.exp_neg, ← he2, div_eq_mul_inv]
  have hhXh : (h : ℝ) ≤ X := by
    have : (h : ℝ) ≤ (4 * h + 1) * h := le_mul_of_one_le_left hh0.le (by linarith)
    linarith
  have hW1 : 1 ≤ W := by
    rw [hWe, le_div_iff₀ (by linarith)]; linarith
  -- the three inputs
  have hs0 : (0 : ℕ) ∉ Finset.Ioc X (4 * X) := by simp
  have hsM : ∀ n ∈ Finset.Ioc X (4 * X), n ≤ 4 * X := fun n hn => (Finset.mem_Ioc.mp hn).2
  have hint := integrable_normSq_logWindowSum f (Finset.Ioc X (4 * X)) δ
  have h1 : (∫ u in E, ‖logWindowSum f (Finset.Ioc X (4 * X)) δ u‖ ^ 2)
      ≤ ∫ u, ‖logWindowSum f (Finset.Ioc X (4 * X)) δ u‖ ^ 2 :=
    setIntegral_le_integral hint (ae_of_all _ fun u => sq_nonneg _)
  have h2 := integral_normSq_logWindowSum_le_coefA hf hX1 hδ0
  have h3 := integral_normSq_logWindowSum_le_split (coefA f) hs0 hsM hδ0 hW1
  set I := ∫ w in Icc (-W) W, ‖logPoly (coefA f) (Finset.Ioc X (4 * X)) w‖ ^ 2 with hIdef
  have hMR' : I ≤ εm := hMR
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Icc fun w _ => sq_nonneg _
  set Es := ∑ n ∈ Finset.Ioc X (4 * X), ‖coefA f n‖ ^ 2 with hEsdef
  have hEs0 : 0 ≤ Es := by positivity
  have hEs : Es ≤ 3 / X := by
    have hterm : ∀ n ∈ Finset.Ioc X (4 * X), ‖coefA f n‖ ^ 2 ≤ 1 / (X : ℝ) ^ 2 := by
      intro n hn
      have hnX : (X : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
      have h1n := norm_coefA_le hf n
      have hle : 1 / (n : ℝ) ≤ 1 / X := one_div_le_one_div_of_le hX0 hnX.le
      have := pow_le_pow_left₀ (norm_nonneg _) (le_trans h1n hle) 2
      rwa [div_pow, one_pow] at this
    calc Es ≤ ∑ _n ∈ Finset.Ioc X (4 * X), 1 / (X : ℝ) ^ 2 := sum_le_sum hterm
      _ = 3 * X * (1 / (X : ℝ) ^ 2) := by
          rw [sum_const, nsmul_eq_mul, Nat.card_Ioc]
          push_cast [show X ≤ 4 * X by omega]
          ring
      _ = 3 / X := by field_simp
  -- the main term and the tail
  have hA : δ ^ 2 * I ≤ ((h : ℝ) / X) ^ 2 * εm :=
    mul_le_mul (pow_le_pow_left₀ hδ0 hδle 2) hMR' hI0 (sq_nonneg _)
  have hM4 : (((4 * X : ℕ) : ℝ)) = 4 * X := by push_cast; ring
  have htail0 : 0 ≤ 4 / W + (((4 * X : ℕ) : ℝ)) / W ^ 2 := by positivity
  have hB : Es * (4 / W + (((4 * X : ℕ) : ℝ)) / W ^ 2)
      ≤ 3 / X * (4 / W + (((4 * X : ℕ) : ℝ)) / W ^ 2) :=
    mul_le_mul_of_nonneg_right hEs htail0
  have hBval : 3 / (X : ℝ) * (4 / W + (((4 * X : ℕ) : ℝ)) / W ^ 2)
      = 12 * (e2 + e2 ^ 2) / (X : ℝ) ^ 2 := by
    rw [hM4, hWe]; field_simp; ring
  have hR : (∫ u, ‖logWindowSum (coefA f) (Finset.Ioc X (4 * X)) δ u‖ ^ 2)
      ≤ ((h : ℝ) / X) ^ 2 * εm + 12 * (e2 + e2 ^ 2) / (X : ℝ) ^ 2 := by
    linarith
  have hR' : 2 * (4 * (X : ℝ)) ^ 2
        * (∫ u, ‖logWindowSum (coefA f) (Finset.Ioc X (4 * X)) δ u‖ ^ 2)
      ≤ 32 * (h : ℝ) ^ 2 * εm + 768 * h := by
    have hX2 : (0 : ℝ) ≤ 2 * (4 * (X : ℝ)) ^ 2 := by positivity
    have e : 2 * (4 * (X : ℝ)) ^ 2 * (((h : ℝ) / X) ^ 2 * εm + 12 * (e2 + e2 ^ 2) / (X : ℝ) ^ 2)
        = 32 * (h : ℝ) ^ 2 * εm + 384 * (e2 + e2 ^ 2) := by
      field_simp; ring
    have := mul_le_mul_of_nonneg_left hR hX2
    rw [e] at this
    rw [he2sq] at this
    linarith
  -- the error of passing from `f(n)/n` to `f(n)`
  have hc1 : 0 ≤ 4 * (X : ℝ) * (Real.exp δ - 1) + 1 := by
    have : 0 ≤ Real.exp δ - 1 := by linarith [Real.one_le_exp hδ0]
    positivity
  have hc2 : 4 * (X : ℝ) * (Real.exp δ - 1) + 1 ≤ 4 * h + 1 := by
    have : 4 * (X : ℝ) * (Real.exp δ - 1) ≤ 4 * X * (h / X) :=
      mul_le_mul_of_nonneg_left hexpδ (by positivity)
    have e : 4 * (X : ℝ) * (h / X) = 4 * h := by field_simp
    linarith
  have hc3 : (4 * (X : ℝ) * (Real.exp δ - 1) + 1) * δ ≤ 1 := by
    have : (4 * (X : ℝ) * (Real.exp δ - 1) + 1) * δ ≤ (4 * h + 1) * (h / X) :=
      mul_le_mul hc2 hδle hδ0 (by positivity)
    have e : (4 * (h : ℝ) + 1) * (h / X) ≤ 1 := by
      rw [show (4 * (h : ℝ) + 1) * (h / X) = (4 * h + 1) * h / X by ring, div_le_one hX0]
      exact hhX
    linarith
  have hc4 : ((4 * (X : ℝ) * (Real.exp δ - 1) + 1) * δ) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ (4 * (X : ℝ) * (Real.exp δ - 1) + 1) * δ := mul_nonneg hc1 hδ0
    exact pow_le_one₀ h0 hc3
  have hc5 : Real.log 4 + δ ≤ 3 := by
    have := log_four_le_two
    have : δ ≤ 1 := le_trans hδle (by rw [div_le_one hX0]; exact hhXh)
    linarith
  have hC : 2 * ((4 * (X : ℝ) * (Real.exp δ - 1) + 1) * δ) ^ 2 * (Real.log 4 + δ) ≤ 6 := by
    have hl0 : 0 ≤ Real.log 4 + δ := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
    have := mul_le_mul hc4 hc5 hl0 (by norm_num)
    linarith
  linarith

/-- **Matomäki–Radziwiłł for `λχ` in additive short windows, `χ` non-principal.** -/
theorem exists_short_sum_mean_square_twLiouville_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∑ k ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc (X + k) (X + k + h), twLiouville χ n‖ ^ 2
        ≤ ε * (h : ℝ) ^ 2 * X := by
  set f := twLiouville χ with hfdef
  have hf : ∀ n, ‖f n‖ ≤ 1 := norm_twLiouville_le χ
  -- the number of blocks
  obtain ⟨N, hN⟩ := exists_nat_gt (48 / ε)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hN1 : (1 : ℝ) ≤ N := by
    have : 0 < N := by exact_mod_cast hN0
    exact_mod_cast this
  set εm : ℝ := ε / (768 * N) with hεm
  have hεm0 : 0 < εm := by positivity
  obtain ⟨L₀, hL₀⟩ := exists_mean_square_twLiouville_le χ hχ hεm0
  refine ⟨⌈max (Real.exp L₀) (4 * (4644 * N + 12) / ε + 1)⌉₊, fun h hh₀ => ?_⟩
  have hhreal : max (Real.exp L₀) (4 * (4644 * N + 12) / ε + 1) ≤ h :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hh₀)
  have hhL : Real.exp L₀ ≤ h := le_trans (le_max_left _ _) hhreal
  have hhB : 4 * (4644 * N + 12) / ε + 1 ≤ h := le_trans (le_max_right _ _) hhreal
  have hh1 : (1 : ℝ) ≤ h := by
    have : 0 ≤ 4 * (4644 * (N : ℝ) + 12) / ε := by positivity
    linarith
  have hh1' : 1 ≤ h := by exact_mod_cast hh1
  have hh0 : (0 : ℝ) < h := by linarith
  have hLh : L₀ ≤ Real.log h := by rw [Real.le_log_iff_exp_le hh0]; exact hhL
  obtain ⟨X₁, hX₁⟩ := hL₀ (Real.log h) hLh
  refine ⟨⌈max X₁ ((4 * (h : ℝ) + 1) * h)⌉₊ + 1, fun X hX => ?_⟩
  have hXreal : max X₁ ((4 * (h : ℝ) + 1) * h) + 1 ≤ X := by
    have h1 := Nat.le_ceil (max X₁ ((4 * (h : ℝ) + 1) * h))
    have h2 : ((⌈max X₁ ((4 * (h : ℝ) + 1) * h)⌉₊ + 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hX
    push_cast at h2
    linarith
  have hXX₁ : X₁ ≤ X := by linarith [le_max_left X₁ ((4 * (h : ℝ) + 1) * h)]
  have hhX : (4 * (h : ℝ) + 1) * h ≤ X := by
    linarith [le_max_right X₁ ((4 * (h : ℝ) + 1) * h)]
  have hhh : (h : ℝ) ≤ (4 * h + 1) * h := le_mul_of_one_le_left hh0.le (by linarith)
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ X := by linarith
    exact_mod_cast this
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hhXn : h ≤ X := by
    have : (h : ℝ) ≤ X := by linarith
    exact_mod_cast this
  -- the Dirichlet-polynomial mean square at `|w| ≤ X/√h`
  have hMR := hX₁ X hXX₁ ((X : ℝ) * Real.exp (-(Real.log h / 2))) (by positivity) le_rfl
  -- the block transfer
  set G : ℝ := 32 * (h : ℝ) ^ 2 * εm + 768 * h + 6 with hGdef
  have hG0 : 0 ≤ G := by positivity
  set c : ℕ → ℂ := fun n => if X < n ∧ n ≤ 4 * X then f n else 0 with hcdef
  have hc : ∀ n, ‖c n‖ ≤ 1 := by
    intro n
    simp only [hcdef]
    split_ifs
    · exact hf n
    · simp
  have hcw : ∀ (δ u : ℝ),
      logWindowSum c (Finset.Icc 1 (4 * X)) δ u = logWindowSum f (Finset.Ioc X (4 * X)) δ u := by
    intro δ u
    have hsub : Finset.Ioc X (4 * X) ⊆ Finset.Icc 1 (4 * X) := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      rw [Finset.mem_Icc]
      omega
    unfold logWindowSum
    rw [← Finset.sum_subset hsub fun n _ hn' => ?_]
    · refine sum_congr rfl fun n hn => ?_
      rw [Finset.mem_Ioc] at hn
      simp only [hcdef, if_pos hn]
    · have : ¬ (X < n ∧ n ≤ 4 * X) := by rwa [Finset.mem_Ioc] at hn'
      simp only [hcdef, if_neg this, smul_zero]
  have hG : ∀ Y' : ℝ, (X : ℝ) ≤ Y' → ∀ E : Set ℝ,
      (∫ u in E, ‖logWindowSum c (Finset.Icc 1 (4 * X)) (Real.log (1 + (h : ℝ) / Y')) u‖ ^ 2)
        ≤ G := by
    intro Y' hY' E
    simp_rw [hcw]
    exact integral_normSq_window_le hf hX1 hh1' hhX hMR hY' E
  have hcover : (X : ℝ) + (X : ℝ) ≤ (X : ℝ) * (1 + 1 / (N : ℝ)) ^ N := by
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / N by
      have : 0 ≤ 1 / (N : ℝ) := by positivity
      linarith) N
    have e : (1 : ℝ) + N * (1 / N) = 2 := by field_simp; ring
    rw [e] at hb
    have := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg X : (0 : ℝ) ≤ X)
    linarith
  have hbound := sum_normSq_window_le_bound c zero_le_one hc (L := h) (Y := X) (K := X)
    (M := 4 * X) (K' := N) (ε := 1 / (N : ℝ)) (G := G) (by omega) (by omega) (by positivity) hG0
    (by omega) hcover hG
  -- the windows of `c` are the windows of `f`
  have hwin : ∑ k ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc (X + k) (X + k + h), c n‖ ^ 2
      = ∑ k ∈ Finset.range X, ‖∑ n ∈ Finset.Ioc (X + k) (X + k + h), f n‖ ^ 2 := by
    refine sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    congr 2
    refine sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    have : X < n ∧ n ≤ 4 * X := ⟨by omega, by omega⟩
    simp only [hcdef, if_pos this]
  rw [hwin] at hbound
  refine le_trans hbound ?_
  -- the numerics
  have hpow : (1 + 1 / (N : ℝ)) ^ N ≤ 3 := by
    have h1 : 1 + 1 / (N : ℝ) ≤ Real.exp (1 / N) := by
      linarith [Real.add_one_le_exp (1 / (N : ℝ))]
    have h2 : (1 + 1 / (N : ℝ)) ^ N ≤ Real.exp (1 / N) ^ N :=
      pow_le_pow_left₀ (by positivity) h1 N
    have h3 : Real.exp (1 / (N : ℝ)) ^ N = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; congr 1; field_simp
    rw [h3] at h2
    linarith [Real.exp_one_lt_d9]
  have hpow0 : 0 ≤ (1 + 1 / (N : ℝ)) ^ N := by positivity
  have hlg : Real.log (1 + 1 / (N : ℝ)) ≤ 1 / N := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (N : ℝ) by positivity)
    linarith
  have hlg0 : 0 ≤ Real.log (1 + 1 / (N : ℝ)) := Real.log_nonneg (by
    have : 0 ≤ 1 / (N : ℝ) := by positivity
    linarith)
  set t : ℝ := 1 / (N : ℝ) with ht
  have ht0 : 0 < t := by positivity
  have htN : (N : ℝ) * t = 1 := by rw [ht]; field_simp
  have ht1 : t ≤ 1 := by rw [ht, div_le_one hN0]; exact hN1
  have htε : t ≤ ε / 48 := by
    rw [ht, div_le_div_iff₀ hN0 (by norm_num)]
    have := (div_lt_iff₀ hε).mp hN
    linarith
  -- the block cost
  have hcost : (N : ℝ) * blockCostGC (h : ℝ) t 1 G
      ≤ 2 * N * G + 2 * (t * h + 1) ^ 2 := by
    rw [blockCostGC]
    have hsq0 : 0 ≤ (t * h + 1) ^ 2 := sq_nonneg _
    have : (N : ℝ) * (2 * 1 ^ 2 * (t * h + 1) ^ 2 * Real.log (1 + t))
        ≤ (N : ℝ) * (2 * 1 ^ 2 * (t * h + 1) ^ 2 * t) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlg (by positivity)) hN0.le
    have e : (N : ℝ) * (2 * 1 ^ 2 * (t * h + 1) ^ 2 * t) = 2 * (t * h + 1) ^ 2 := by
      have : (N : ℝ) * (2 * 1 ^ 2 * (t * h + 1) ^ 2 * t) = 2 * (t * h + 1) ^ 2 * (N * t) := by
        ring
      rw [this, htN, mul_one]
    linarith
  have hcost0 : 0 ≤ (N : ℝ) * blockCostGC (h : ℝ) t 1 G :=
    mul_nonneg hN0.le (blockCostGC_nonneg ht0.le hG0)
  -- `2NG = εh²/12 + 1536Nh + 12N`
  have hNG : 2 * (N : ℝ) * G = ε * h ^ 2 / 12 + 1536 * N * h + 12 * N := by
    rw [hGdef, hεm]; field_simp; ring
  have hsq : (t * h + 1) ^ 2 ≤ 2 * t ^ 2 * h ^ 2 + 2 := by linarith [sq_nonneg (t * h - 1)]
  have ht2 : t ^ 2 * (h : ℝ) ^ 2 ≤ ε / 48 * h ^ 2 := by
    have h1 : t ^ 2 ≤ t := by rw [sq]; exact mul_le_of_le_one_left ht0.le ht1
    have : t ^ 2 ≤ ε / 48 := by linarith
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have hlin : 4608 * (N : ℝ) * h + 36 * N + 12 ≤ ε * h ^ 2 / 2 := by
    have hεh : 4 * (4644 * (N : ℝ) + 12) ≤ ε * h := by
      have : 4 * (4644 * (N : ℝ) + 12) / ε ≤ h := by linarith
      rw [div_le_iff₀ hε] at this
      linarith
    have h1 := mul_le_mul_of_nonneg_right hεh hh0.le
    have h2 := mul_le_mul_of_nonneg_left hh1 hN0.le
    linarith
  have hI : 3 * ((N : ℝ) * blockCostGC (h : ℝ) t 1 G) ≤ ε * h ^ 2 := by linarith
  calc (X : ℝ) * (1 + t) ^ N * ((N : ℝ) * blockCostGC (h : ℝ) t 1 G)
      ≤ (X : ℝ) * 3 * ((N : ℝ) * blockCostGC (h : ℝ) t 1 G) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hX0.le) hcost0
    _ = (X : ℝ) * (3 * ((N : ℝ) * blockCostGC (h : ℝ) t 1 G)) := by ring
    _ ≤ (X : ℝ) * (ε * h ^ 2) := mul_le_mul_of_nonneg_left hI hX0.le
    _ = ε * (h : ℝ) ^ 2 * X := by ring

end

end GaloisForLFunctions.MatomakiRadziwill
