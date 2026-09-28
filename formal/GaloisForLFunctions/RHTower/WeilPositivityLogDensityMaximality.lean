import GaloisForLFunctions.RHTower.WeilPositivityMultiplicativeToeplitzBound
import GaloisForLFunctions.RHTower.CriticalGibbsPerronPolarization

/-!
# Weil positivity fixes the log-density of the prime weights at that of `Λ`

The Weil–Toeplitz density ceiling (`weil_log_density_le`: `Σ_{nm ≤ N} lam(n)/(nm) ≤ (1/2 + ε)
(log N)²` for Weil-positive `lam`) is attained by `Λ` itself (`eventually_gibbsEnergy_ge`, from the
Perron–polarization asymptotic `2P(N)/H(N) = log N − γ + o(1)`).  Consequently:

* `weil_supersystem_excess_small`: a Weil-positive `lam ≥ Λ` has excess
  `Σ_{n ≥ 2, nm ≤ N} (lam(n) − Λ(n))/(nm) = o((log N)²)`;
* `vonMangoldt_add_const_not_weilPositive`: for every `c > 0` the weights `Λ(n) + c` are not
  Weil-positive.  This is a heavy perturbation (`Σ c n^{-1/2} = ∞`), excluded by density alone.
-/

open Complex MeasureTheory Filter Topology Set ArithmeticFunction
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

open CriticalGibbs

/-- `Σ_{n ≥ 2, m ≥ 1, nm ≤ N} Λ(n)/(nm)` is the critical Gibbs energy. -/
theorem sum_vonMangoldt_pairs_eq_gibbsEnergy (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then (vonMangoldt n : ℝ) / (n * m) else 0) = gibbsEnergy N := by
  unfold gibbsEnergy
  refine Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun n hn hnot => ?_
  have hn1 : n = 1 := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn hnot
    omega
  subst hn1
  simp [ArithmeticFunction.vonMangoldt_apply_one]

/-- The critical Gibbs energy is at least `(1/2 − ε) (log N)²` for large `N`. -/
theorem eventually_gibbsEnergy_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (1 / 2 - ε) * Real.log N ^ 2 ≤ gibbsEnergy N := by
  set γ := Real.eulerMascheroniConstant
  have hlim := tendsto_gibbs_rayleigh
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hlim) 1 (by norm_num)
  -- `log N ≥ L` for large `N`, with `L` large enough to absorb `γ + 1`
  set L : ℝ := (γ + 1) / (2 * ε) + γ + 2 with hL
  have hγ0 : 0 ≤ γ := by have := Real.one_half_lt_eulerMascheroniConstant; linarith
  refine ⟨max (max N₁ 1) (⌈Real.exp L⌉₊ + 1), fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : L ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hNr]
    have h1 : Real.exp L ≤ ⌈Real.exp L⌉₊ := Nat.le_ceil _
    have h2 : ((⌈Real.exp L⌉₊ : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (le_trans (Nat.le_succ _) (le_trans (le_max_right _ _) hN))
    linarith
  have hL0 : 0 ≤ (γ + 1) / (2 * ε) := by positivity
  have hL1 : 1 ≤ L := by linarith
  have hH := harm_pos hN1
  have hHlog : Real.log N ≤ harm N := by
    have := log_succ_le_harm N
    have : Real.log N ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hNr (by linarith)
    linarith
  have hclose := hN₁ N hNN₁
  rw [Real.dist_eq, sub_zero] at hclose
  have hlow : Real.log N - γ - 1 ≤ 2 * gibbsEnergy N / harm N := by
    have := (abs_lt.mp hclose).1; linarith
  have hlogpos : 0 ≤ Real.log N - γ - 1 := by linarith
  have h2P : (Real.log N - γ - 1) * harm N ≤ 2 * gibbsEnergy N := by
    have := (le_div_iff₀ hH).mp hlow; linarith
  have h2P' : (Real.log N - γ - 1) * Real.log N ≤ 2 * gibbsEnergy N :=
    le_trans (mul_le_mul_of_nonneg_left hHlog hlogpos) h2P
  -- `(γ+1) log N ≤ 2ε (log N)²`
  have hsmall : (γ + 1) * Real.log N ≤ 2 * ε * Real.log N ^ 2 := by
    have hLle : (γ + 1) / (2 * ε) ≤ Real.log N := by linarith
    have : γ + 1 ≤ 2 * ε * Real.log N := by
      rw [div_le_iff₀ (by positivity)] at hLle; linarith
    have hlp : 0 ≤ Real.log N := by linarith
    nlinarith
  nlinarith

/-- **No Weil-positive supersystem of `Λ` has positive log-density excess.**  If `lam ≥ Λ`
pointwise and `lam` is Weil-positive, then `Σ_{n ≥ 2, nm ≤ N} (lam(n) − Λ(n))/(nm) = o((log N)²)`:
the density ceiling `1` of Weil positivity is attained by `Λ` itself. -/
theorem weil_supersystem_excess_small {lam : ℕ → ℝ}
    (hW : ∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 * weilAtomSymbol lam ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then (lam n - vonMangoldt n) / (n * m) else 0) ≤ ε * Real.log N ^ 2 := by
  obtain ⟨N₁, h₁⟩ := weil_log_density_le hW (ε := ε / 2) (by linarith)
  obtain ⟨N₂, h₂⟩ := eventually_gibbsEnergy_ge (ε := ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hu := h₁ N (le_trans (le_max_left _ _) hN)
  have hΛ := h₂ N (le_trans (le_max_right _ _) hN)
  rw [← sum_vonMangoldt_pairs_eq_gibbsEnergy] at hΛ
  have hsplit : ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then (lam n - vonMangoldt n) / (n * m) else 0) =
      (∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then lam n / (n * m) else 0)) -
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then (vonMangoldt n : ℝ) / (n * m) else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  rw [hsplit]
  nlinarith

/-- **Constant shifts are not Weil-positive.**  For every `c > 0`, the weights
`Λ(n) + c` (a heavy perturbation: `Σ c n^{-1/2} = ∞`) violate Weil positivity at some level. -/
theorem vonMangoldt_add_const_not_weilPositive {c : ℝ} (hc : 0 < c) :
    ¬ (∀ a : ℝ, 0 ≤ a → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      paperFT f (I / 2) = 0 → paperFT f (-(I / 2)) = 0 →
      0 ≤ ∫ τ : ℝ, ‖paperFT f τ‖ ^ 2 *
        weilAtomSymbol (fun n => (vonMangoldt n : ℝ) + c) ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π))) := by
  intro hW
  obtain ⟨N₀, hN₀⟩ := weil_supersystem_excess_small hW (ε := c / 16) (by linarith)
  -- lower bound for the excess over the square `n, m ≤ K = ⌊√N⌋`
  set L : ℝ := 8 with hL
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → L ≤ Real.log N := by
    refine ⟨⌈Real.exp L⌉₊ + 1, fun N hN => ?_⟩
    have hNr : (0 : ℝ) < N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast (le_trans (by omega) hN)
      linarith
    rw [Real.le_log_iff_exp_le hNr]
    have h1 : Real.exp L ≤ ⌈Real.exp L⌉₊ := Nat.le_ceil _
    have h2 : ((⌈Real.exp L⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (le_trans (Nat.le_succ _) hN)
    linarith
  set N := max N₀ N₁ with hNdef
  have hex := hN₀ N (le_max_left _ _)
  have hlogN := hN₁ N (le_max_right _ _)
  set K := Nat.sqrt N with hK
  have hKK : K * K ≤ N := Nat.sqrt_le N
  have hNK : N < (K + 1) * (K + 1) := Nat.lt_succ_sqrt N
  have hK1 : 2 ≤ K := by
    by_contra h
    push Not at h
    have : N < 4 := by nlinarith
    have hNr : (N : ℝ) < 4 := by exact_mod_cast this
    have : Real.log N < Real.log 4 := by
      rcases Nat.eq_zero_or_pos N with h0 | hp
      · rw [h0]; simp; positivity
      · exact Real.log_lt_log (by exact_mod_cast hp) hNr
    have : Real.log 4 < 2 := by
      have := Real.log_two_lt_d9
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
    linarith
  have hterm : ∀ n ∈ Finset.Icc 2 N, ∀ m ∈ Finset.Icc 1 N,
      (if n * m ≤ N then (((vonMangoldt n : ℝ) + c) - vonMangoldt n) / (n * m) else 0) =
        (if n * m ≤ N then c / (n * m) else 0) := by
    intro n _ m _; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => hterm n hn m hm] at hex
  -- restrict to `n, m ≤ K`
  have hsub : ∑ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 K, c / ((n : ℝ) * m) ≤
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then c / ((n : ℝ) * m) else 0) := by
    have hKN : K ≤ N := Nat.sqrt_le_self N
    calc ∑ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 K, c / ((n : ℝ) * m)
        = ∑ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 K,
            (if n * m ≤ N then c / ((n : ℝ) * m) else 0) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
          have : n * m ≤ N := by
            have := (Finset.mem_Icc.mp hn).2; have := (Finset.mem_Icc.mp hm).2; nlinarith
          rw [if_pos this]
      _ ≤ ∑ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 N,
            (if n * m ≤ N then c / ((n : ℝ) * m) else 0) := by
          refine Finset.sum_le_sum fun n _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc_right hKN) fun m _ _ => ?_
          split_ifs <;> positivity
      _ ≤ _ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hKN)
            fun n _ _ => Finset.sum_nonneg fun m _ => ?_
          split_ifs <;> positivity
  -- evaluate the square sum
  have hsq : ∑ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 K, c / ((n : ℝ) * m) =
      c * ((harm K - 1) * harm K) := by
    have e : ∀ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 K, c / ((n : ℝ) * m) =
        c / n * harm K := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by
        have := (Finset.mem_Icc.mp hn).1; exact_mod_cast (show 0 < n by omega)
      unfold harm; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm0 : (0 : ℝ) < m := by
        have := (Finset.mem_Icc.mp hm).1; exact_mod_cast (show 0 < m by omega)
      field_simp
    rw [Finset.sum_congr rfl e]
    have hset : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
      ext n; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hH : harm K - 1 = ∑ n ∈ Finset.Icc 2 K, (1 : ℝ) / n := by
      unfold harm
      rw [hset, Finset.sum_insert (by simp)]
      simp
    rw [hH]
    simp only [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have hHK := log_succ_le_harm K
  have hKr : ((N : ℝ)) < ((K : ℝ) + 1) ^ 2 := by exact_mod_cast (by nlinarith : N < (K + 1) ^ 2)
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by
      have := hKK; exact_mod_cast (le_trans (by nlinarith) this)
    linarith
  have hlogK : Real.log N / 2 ≤ Real.log ((K : ℝ) + 1) := by
    have := Real.log_le_log hNpos hKr.le
    rw [Real.log_pow] at this; push_cast at this; linarith
  have hsum_ge : c / 8 * Real.log N ^ 2 ≤
      ∑ n ∈ Finset.Icc 2 N, ∑ m ∈ Finset.Icc 1 N,
        (if n * m ≤ N then c / ((n : ℝ) * m) else 0) := by
    have hA : Real.log N / 2 ≤ harm K := hlogK.trans hHK
    have hB : Real.log N / 2 - 1 ≤ harm K - 1 := by linarith
    have hpos1 : 0 ≤ Real.log N / 2 - 1 := by linarith
    have h3 : (Real.log N / 2 - 1) * (Real.log N / 2) ≤ (harm K - 1) * harm K :=
      mul_le_mul hB hA (by linarith) (by linarith)
    have h4 : Real.log N ^ 2 / 8 ≤ (Real.log N / 2 - 1) * (Real.log N / 2) := by nlinarith
    calc c / 8 * Real.log N ^ 2 ≤ c * ((harm K - 1) * harm K) := by nlinarith
      _ = ∑ n ∈ Finset.Icc 2 K, ∑ m ∈ Finset.Icc 1 K, c / ((n : ℝ) * m) := hsq.symm
      _ ≤ _ := hsub
  have hlog0 : 0 < Real.log N := by linarith
  have hprod := mul_pos hc (pow_pos hlog0 2)
  have hchain := hsum_ge.trans hex
  nlinarith

end

end RHTower
