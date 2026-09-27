import GaloisForLFunctions.RHTower.ZetaWeilNegativeIndexHorizon
import GaloisForLFunctions.RHTower.OffLineClusterWeilUnbounded

/-!
# The finite-level inertia law for the Weil form of `ζ`

Let `weilNegIndex Z a ε` be the largest dimension of a space of polar-constrained `C²` tests
supported in `[-a, a]` on which `Re W(f, f) < -ε ∫|f|²` off `0`.  For `ζ`
(`zeta_weil_inertia_law`):

* **Upper bound** (from `ZetaWeilNegativeIndexHorizon`).  `weilNegIndex(a, ε)` is at most the number
  of off-line pairs with `|γ| ≤ H(A₀, a, ε)`, where `log H = O(e^a + log(1/ε))`.
* **Lower bound.**  If `T` consists of zeros of depth `≥ δ`, pairwise `2R` apart in height, each
  isolated at radius `R` from the other off-line zeros, and visible (`visibleMargin > 0`, which holds
  once `log H_m ≲ e^{2δa}/poly(a)` and `R ≳ e^a`), then `weilNegIndex(a, ε) ≥ |T| - 2` for
  `ε ≤ λ/(|T|(∫s² + 1))`.

So at level `a` the negative squares of the finite Hodge form count the off-line pairs of `ζ`
between the visibility height of isolated pairs and the archimedean horizon.  This is a level-wise,
quantitative form of Bombieri's count, which holds for large enough truncations when there are
finitely many off-line zeros.

**Proof of the lower bound** (`re_W_visible_combination_le`).
* The test at `ρ ∈ T` is `f_ρ = e^{-iγ_ρu} sinh(δu)(a² - u²)₊^{5/2}`.
* **Diagonal.**  By the isolation inequality, `Re W(f_ρ, f_ρ) ≤ -2P² + E_d`
  (`re_W_visible_pair_le`), with the energy monotone in the depth
  (`integral_sinhTest_mul_sinh_mono`).
* **Off-diagonal.**  `|W(f_ρ, f_σ)| ≤ K/(1 + |γ_ρ - γ_σ|)²`.  This follows from
  `(1+d₁)²(1+d₂)² ≥ (1+Δ)²(1+min)²/4` and a power-two window sum under the logarithmic local count
  (`window_tsum_inv_sq_log_le`, using `Σ log(1+|n|)/(1+|n|)² ≤ 12`).  The separation gives
  `Σ_{σ ≠ ρ} (1 + |γ_ρ - γ_σ|)^{-2} ≤ 10/R²` (`sum_separated_inv_sq_le`).
* **Gram expansion.**  `W(Σ c_ρ f_ρ) = Σ c_ρ c̄_σ W(f_ρ, f_σ)` (`W_finset_sum`); the Schur test
  bounds the off-diagonal part by `10K/R² Σ|c|²`.
* **Polar constraints.**  They cut out a subspace of codimension at most `2`
  (`exists_polar_negative_subspace_of_visible_pairs`).  Since
  `|Σ c_ρ f_ρ| ≤ |s| Σ|c_ρ|`, the threshold is explicit.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### A power-two window sum under the logarithmic local count -/

theorem inv_mul_sqrt_succ_le_telescope {m : ℕ} (hm : 1 ≤ m) :
    1 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) ≤
      2 * (1 / Real.sqrt m - 1 / Real.sqrt ((m : ℝ) + 1)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set p := Real.sqrt m with hp
  set q := Real.sqrt ((m : ℝ) + 1) with hq
  have hp0 : 0 < p := Real.sqrt_pos.mpr hm0
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hp2 : p ^ 2 = m := Real.sq_sqrt hm0.le
  have hq2 : q ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hpq : p ≤ q := Real.sqrt_le_sqrt (by linarith)
  -- `2(1/p - 1/q) = 2(q - p)/(pq)` and `q - p = 1/(p + q) ≥ 1/(2q)`
  have hdiff : q - p = 1 / (p + q) := by
    field_simp
    nlinarith
  rw [div_sub_div _ _ hp0.ne' hq0.ne', one_mul, mul_one, mul_div_assoc']
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : q - p ≥ 1 / (2 * q) := by
    rw [hdiff]; exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have h2 : (q - p) * (2 * q) ≥ 1 := by
    rw [ge_iff_le, ← div_le_iff₀ (by positivity)]; linarith
  have : ((m : ℝ) + 1) * q = q ^ 3 := by rw [pow_succ, hq2]
  rw [this]
  nlinarith [mul_pos hp0 hq0, pow_pos hq0 2]

/-- `Σ_{m < M} (m+1)^{-3/2} ≤ 3`. -/
theorem sum_range_inv_mul_sqrt_le (M : ℕ) :
    ∑ m ∈ Finset.range M, 1 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) ≤ 3 := by
  have key : ∀ M : ℕ, 1 ≤ M →
      ∑ m ∈ Finset.range M, 1 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) ≤
        3 - 2 / Real.sqrt M := by
    intro M hM
    induction M with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp; norm_num
      · rw [Finset.sum_range_succ]
        have h := ih hn
        have ht := inv_mul_sqrt_succ_le_telescope hn
        push_cast
        have e : 2 * (1 / Real.sqrt n - 1 / Real.sqrt ((n : ℝ) + 1)) =
            2 / Real.sqrt n - 2 / Real.sqrt ((n : ℝ) + 1) := by ring
        linarith
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · have := key M hM
    have : 0 ≤ 2 / Real.sqrt M := by positivity
    linarith

/-- `log(1 + m) ≤ 2 √(1 + m)`. -/
theorem log_le_two_mul_sqrt_self {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  have e : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [← Real.log_rpow hs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt hx.le]
  linarith

/-- `Σ_{n ∈ S} log(1 + |n|)/(1 + |n|)² ≤ 12` over every finite set of integers. -/
theorem sum_log_one_add_abs_div_sq_le (S : Finset ℤ) :
    ∑ n ∈ S, Real.log (1 + |(n : ℝ)|) / (1 + |(n : ℝ)|) ^ 2 ≤ 12 := by
  classical
  set h : ℕ → ℝ := fun m => 1 / (((m : ℝ) + 1) * Real.sqrt ((m : ℝ) + 1)) with hh
  have hpt : ∀ n : ℤ, Real.log (1 + |(n : ℝ)|) / (1 + |(n : ℝ)|) ^ 2 ≤ 2 * h n.natAbs := by
    intro n
    have habs : |(n : ℝ)| = (n.natAbs : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [habs]
    set m : ℝ := (n.natAbs : ℝ)
    have hm0 : 0 ≤ m := Nat.cast_nonneg _
    have hl := log_le_two_mul_sqrt_self (x := 1 + m) (by linarith)
    have hs := Real.sqrt_pos.mpr (show (0 : ℝ) < 1 + m by linarith)
    have hs2 : Real.sqrt (1 + m) ^ 2 = 1 + m := Real.sq_sqrt (by linarith)
    simp only [hh]
    rw [div_le_iff₀ (by positivity), show m + 1 = 1 + m by ring]
    have e : 2 * (1 / ((1 + m) * Real.sqrt (1 + m))) * (1 + m) ^ 2 = 2 * Real.sqrt (1 + m) := by
      field_simp; nlinarith
    rw [e]; exact hl
  have hnn : ∀ m, 0 ≤ h m := fun m => by simp only [hh]; positivity
  have hsum : ∑ n ∈ S, 2 * h n.natAbs ≤ 2 * (2 * ∑ m ∈ S.image Int.natAbs, h m) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← Finset.sum_fiberwise_of_maps_to (g := Int.natAbs) (t := S.image Int.natAbs)
      (fun n hn => Finset.mem_image_of_mem _ hn), Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    have hcard : (S.filter fun n => n.natAbs = m).card ≤ 2 := by
      have hsub : S.filter (fun n => n.natAbs = m) ⊆ {(m : ℤ), -(m : ℤ)} := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    calc ∑ n ∈ S with n.natAbs = m, h n.natAbs = ∑ n ∈ S with n.natAbs = m, h m :=
          Finset.sum_congr rfl fun n hn => by rw [(Finset.mem_filter.mp hn).2]
      _ = (S.filter fun n => n.natAbs = m).card * h m := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * h m := by
          have : ((S.filter fun n => n.natAbs = m).card : ℝ) ≤ 2 := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right this (hnn m)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ m ∈ S.image Int.natAbs, m < M :=
    ⟨(S.image Int.natAbs).sup id + 1, fun m hm => Nat.lt_succ_of_le (Finset.le_sup (f := id) hm)⟩
  have hsub : ∑ m ∈ S.image Int.natAbs, h m ≤ ∑ m ∈ Finset.range M, h m :=
    Finset.sum_le_sum_of_subset_of_nonneg (fun m hm => Finset.mem_range.mpr (hM m hm))
      (fun m _ _ => hnn m)
  have hr := sum_range_inv_mul_sqrt_le M
  calc ∑ n ∈ S, Real.log (1 + |(n : ℝ)|) / (1 + |(n : ℝ)|) ^ 2 ≤ ∑ n ∈ S, 2 * h n.natAbs :=
        Finset.sum_le_sum fun n _ => hpt n
    _ ≤ 2 * (2 * ∑ m ∈ S.image Int.natAbs, h m) := hsum
    _ ≤ 12 := by nlinarith

/-- **Power-two window sum.**  Under `N(t, t+1] ≤ A₀ log(|t| + 3)`,
`Σ_ρ m_ρ (1 + |γ - t₀|)^{-2} ≤ A₀ (10 log(|t₀| + 3) + 48)`. -/
theorem window_tsum_inv_sq_log_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (t₀ : ℝ) :
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 2) ∧
      ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 2 ≤
        A₀ * (10 * Real.log (|t₀| + 3) + 48) := by
  classical
  have hLC := Tail.LocalCount.ofWindowCount Z hA₀ hloc
  set L₀ := Real.log (|t₀| + 3) with hL₀
  have hL₀1 : 1 ≤ L₀ := one_le_log_abs_add_three t₀
  have hA0 : 0 ≤ A₀ := by linarith
  have hS := hasSum_inv_one_add_abs_sq
  have hpi : π ^ 2 / 3 - 1 ≤ 5 / 2 := by
    have := Real.pi_lt_d2
    have hp : 0 < π := Real.pi_pos
    nlinarith
  have hnonneg : 0 ≤ fun ρ : Z.carrier => (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 2 :=
    fun ρ => div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hfin : ∀ s : Finset Z.carrier,
      ∑ ρ ∈ s, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 2 ≤ A₀ * (10 * L₀ + 48) := by
    intro s
    set κ : Z.carrier → ℤ := fun ρ => WeilEF.key ((ρ : ℂ).im - t₀) with hκ
    rw [← Finset.sum_fiberwise_of_maps_to (g := κ) (t := s.image κ)
      (fun ρ hρ => Finset.mem_image_of_mem κ hρ)]
    have hfiber : ∀ n ∈ s.image κ,
        ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 2 ≤
          4 * A₀ * L₀ * (1 / (1 + |(n : ℝ)|) ^ 2) +
            4 * A₀ * (Real.log (1 + |(n : ℝ)|) / (1 + |(n : ℝ)|) ^ 2) := by
      intro n _
      have hwin := hLC.window (t₀ + n) (s.filter fun ρ => κ ρ = n) (fun ρ hρ => by
        simp only [Finset.mem_filter] at hρ
        have h1 := WeilEF.key_lt ((ρ : ℂ).im - t₀)
        have h2 := WeilEF.le_key_add_one ((ρ : ℂ).im - t₀)
        rw [show WeilEF.key ((ρ : ℂ).im - t₀) = n from hρ.2] at h1 h2
        constructor <;> linarith)
      have hlog : Real.log (|t₀ + n| + 3) ≤ L₀ + Real.log (1 + |(n : ℝ)|) := by
        have hpos : 0 < |t₀| + 3 := by positivity
        have h1 : |t₀ + n| + 3 ≤ (|t₀| + 3) * (1 + |(n : ℝ)|) := by
          have := abs_add_le t₀ (n : ℝ)
          nlinarith [abs_nonneg t₀, abs_nonneg (n : ℝ)]
        rw [hL₀, ← Real.log_mul hpos.ne' (by positivity)]
        exact Real.log_le_log (by positivity) h1
      have hpt : ∀ ρ ∈ s.filter (fun ρ => κ ρ = n),
          (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 2 ≤ (4 / (1 + |(n : ℝ)|) ^ 2) * Z.mult ρ := by
        intro ρ hρ
        simp only [Finset.mem_filter] at hρ
        have h1 := WeilEF.key_lt ((ρ : ℂ).im - t₀)
        have h2 := WeilEF.le_key_add_one ((ρ : ℂ).im - t₀)
        rw [show WeilEF.key ((ρ : ℂ).im - t₀) = n from hρ.2] at h1 h2
        set y := (ρ : ℂ).im - t₀
        have hcmp : 1 + |(n : ℝ)| ≤ 2 * (1 + |y|) := by
          rcases le_or_gt 0 (n : ℝ) with hn | hn
          · rw [abs_of_nonneg hn]
            have : (n : ℝ) ≤ |y| := by rw [abs_of_pos (by linarith)]; linarith
            linarith
          · have hn' : (n : ℝ) ≤ -1 := by
              have : n < 0 := by exact_mod_cast hn
              exact_mod_cast (show n ≤ -1 by omega)
            rw [abs_of_neg hn]
            have : -(n : ℝ) - 1 ≤ |y| := by have := neg_abs_le y; linarith
            linarith
        have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
        have hsq : (1 + |(n : ℝ)|) ^ 2 ≤ 4 * (1 + |y|) ^ 2 := by
          have h0 : 0 ≤ 1 + |(n : ℝ)| := by positivity
          calc (1 + |(n : ℝ)|) ^ 2 ≤ (2 * (1 + |y|)) ^ 2 := pow_le_pow_left₀ h0 hcmp 2
            _ = 4 * (1 + |y|) ^ 2 := by ring
        rw [div_le_iff₀ (by positivity)]
        calc (Z.mult ρ : ℝ) = (Z.mult ρ : ℝ) * (1 + |(n : ℝ)|) ^ 2 / (1 + |(n : ℝ)|) ^ 2 := by
              field_simp
          _ ≤ (Z.mult ρ : ℝ) * (4 * (1 + |y|) ^ 2) / (1 + |(n : ℝ)|) ^ 2 := by gcongr
          _ = 4 / (1 + |(n : ℝ)|) ^ 2 * (Z.mult ρ : ℝ) * (1 + |y|) ^ 2 := by ring
      have hn0 : (0 : ℝ) < 1 + |(n : ℝ)| := by positivity
      calc ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 2
          ≤ ∑ ρ ∈ s with κ ρ = n, (4 / (1 + |(n : ℝ)|) ^ 2) * (Z.mult ρ : ℝ) :=
            Finset.sum_le_sum hpt
        _ = (4 / (1 + |(n : ℝ)|) ^ 2) * ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ (4 / (1 + |(n : ℝ)|) ^ 2) * (A₀ * Real.log (|t₀ + n| + 3)) :=
            mul_le_mul_of_nonneg_left hwin (by positivity)
        _ ≤ (4 / (1 + |(n : ℝ)|) ^ 2) * (A₀ * (L₀ + Real.log (1 + |(n : ℝ)|))) := by
            gcongr
        _ = 4 * A₀ * L₀ * (1 / (1 + |(n : ℝ)|) ^ 2) +
              4 * A₀ * (Real.log (1 + |(n : ℝ)|) / (1 + |(n : ℝ)|) ^ 2) := by ring
    have h1 : ∑ n ∈ s.image κ, 1 / (1 + |(n : ℝ)|) ^ 2 ≤ π ^ 2 / 3 - 1 :=
      sum_le_hasSum _ (fun n _ => by positivity) hS
    have h2 := sum_log_one_add_abs_div_sq_le (s.image κ)
    calc ∑ n ∈ s.image κ, ∑ ρ ∈ s with κ ρ = n, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t₀|) ^ 2
        ≤ ∑ n ∈ s.image κ, (4 * A₀ * L₀ * (1 / (1 + |(n : ℝ)|) ^ 2) +
            4 * A₀ * (Real.log (1 + |(n : ℝ)|) / (1 + |(n : ℝ)|) ^ 2)) :=
          Finset.sum_le_sum hfiber
      _ = 4 * A₀ * L₀ * ∑ n ∈ s.image κ, 1 / (1 + |(n : ℝ)|) ^ 2 +
            4 * A₀ * ∑ n ∈ s.image κ, Real.log (1 + |(n : ℝ)|) / (1 + |(n : ℝ)|) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 4 * A₀ * L₀ * (5 / 2) + 4 * A₀ * 12 := by
          have hL0 : 0 ≤ 4 * A₀ * L₀ := by positivity
          have := mul_le_mul_of_nonneg_left (h1.trans hpi) hL0
          have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * A₀)
          linarith
      _ = A₀ * (10 * L₀ + 48) := by ring
  have hsum := summable_of_sum_le hnonneg hfin
  exact ⟨hsum, hsum.tsum_le_of_sum_le hfin⟩

/-! ### Cross terms between tests at different heights -/

theorem inv_sq_mul_inv_sq_le {d₁ d₂ Δ : ℝ} (h₁ : 0 ≤ d₁) (h₂ : 0 ≤ d₂) (hΔ : 0 ≤ Δ)
    (hle : Δ ≤ d₁ + d₂) :
    1 / ((1 + d₁) ^ 2 * (1 + d₂) ^ 2) ≤
      4 / (1 + Δ) ^ 2 * (1 / (1 + d₁) ^ 2 + 1 / (1 + d₂) ^ 2) := by
  have hmax : (1 + Δ) ^ 2 ≤ 4 * (1 + max d₁ d₂) ^ 2 := by
    have : Δ ≤ 2 * max d₁ d₂ := by
      have := le_max_left d₁ d₂; have := le_max_right d₁ d₂; linarith
    have h0 : 0 ≤ 1 + Δ := by linarith
    calc (1 + Δ) ^ 2 ≤ (2 * (1 + max d₁ d₂)) ^ 2 :=
          pow_le_pow_left₀ h0 (by linarith) 2
      _ = 4 * (1 + max d₁ d₂) ^ 2 := by ring
  rcases le_total d₁ d₂ with h | h
  · rw [max_eq_right h] at hmax
    have e : 1 / ((1 + d₁) ^ 2 * (1 + d₂) ^ 2) ≤ 4 / (1 + Δ) ^ 2 * (1 / (1 + d₁) ^ 2) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos (show (0 : ℝ) < 1 + d₁ by linarith) 2]
    have : 0 ≤ 4 / (1 + Δ) ^ 2 * (1 / (1 + d₂) ^ 2) := by positivity
    rw [mul_add]; linarith
  · rw [max_eq_left h] at hmax
    have e : 1 / ((1 + d₁) ^ 2 * (1 + d₂) ^ 2) ≤ 4 / (1 + Δ) ^ 2 * (1 / (1 + d₂) ^ 2) := by
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos (show (0 : ℝ) < 1 + d₂ by linarith) 2]
    have : 0 ≤ 4 / (1 + Δ) ^ 2 * (1 / (1 + d₁) ^ 2) := by positivity
    rw [mul_add]; linarith

theorem Wsummand_modulatedTest_pair (Z : ZeroConfig) (γ₁ γ₂ : ℝ) (s : ℝ → ℝ) (ρ : ℂ) :
    Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ =
      (Z.mult ρ : ℂ) * paperFT (fun u => (s u : ℂ)) (gammaOf ρ - γ₁) *
        conj (paperFT (fun u => (s u : ℂ)) (conj (gammaOf ρ) - γ₂)) := by
  rw [ZeroConfig.Wsummand]
  unfold modulatedTest
  rw [paperFT_modulate, paperFT_modulate]

/-- The cross summand of two modulated tests decays in the distance of their heights. -/
theorem norm_Wsummand_modulatedTest_pair_le (Z : ZeroConfig) (γ₁ γ₂ : ℝ) {s : ℝ → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (hs : ContDiff ℝ 2 s) (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) {ρ : ℂ}
    (hρ : ρ ∈ Z.carrier) :
    ‖Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ‖ ≤
      64 * Real.exp a * testNorm s ^ 2 / (1 + |γ₁ - γ₂|) ^ 2 *
        ((Z.mult ρ : ℝ) / (1 + |ρ.im - γ₁|) ^ 2 + (Z.mult ρ : ℝ) / (1 + |ρ.im - γ₂|) ^ 2) := by
  have hS : ContDiff ℝ 2 (fun u => (s u : ℂ)) := Complex.ofRealCLM.contDiff.comp hs
  have hSsupp : ∀ u, (fun u => (s u : ℂ)) u ≠ 0 → |u| ≤ a := fun u hu =>
    hsupp u (fun h => hu (by simp [h]))
  have hN := testNorm_nonneg s
  have hst := Z.strip ρ hρ
  have hy : |1 / 2 - ρ.re| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hst.1, hst.2]
  rw [Wsummand_modulatedTest_pair, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_natCast]
  have h1 := norm_paperFT_le_decay hS hSsupp (gammaOf ρ - γ₁)
  have h2 := norm_paperFT_le_decay hS hSsupp (conj (gammaOf ρ) - γ₂)
  have e1 : (gammaOf ρ - γ₁).re = ρ.im - γ₁ := by simp [WeilEF.gammaOf_re]
  have e2 : |(gammaOf ρ - γ₁).im| = |1 / 2 - ρ.re| := by simp [WeilEF.gammaOf_im]
  have e3 : (conj (gammaOf ρ) - γ₂).re = ρ.im - γ₂ := by simp [WeilEF.gammaOf_re]
  have e4 : |(conj (gammaOf ρ) - γ₂).im| = |1 / 2 - ρ.re| := by
    simp only [Complex.sub_im, Complex.conj_im, Complex.ofReal_im, sub_zero, WeilEF.gammaOf_im,
      abs_neg]
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  change _ ≤ Real.exp _ * (4 * testNorm s) / _ at h1 h2
  have hE : Real.exp (|1 / 2 - ρ.re| * a) ≤ Real.exp (a / 2) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg (1 / 2 - ρ.re)])
  have hE2 : Real.exp (a / 2) * Real.exp (a / 2) = Real.exp a := by
    rw [← Real.exp_add]; ring_nf
  set d₁ := |ρ.im - γ₁| with hd₁
  set d₂ := |ρ.im - γ₂| with hd₂
  have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
  have hΔ : |γ₁ - γ₂| ≤ d₁ + d₂ := by
    have := abs_sub_le γ₁ ρ.im γ₂
    rw [abs_sub_comm γ₁ ρ.im] at this
    linarith
  have hkey := inv_sq_mul_inv_sq_le (abs_nonneg (ρ.im - γ₁)) (abs_nonneg (ρ.im - γ₂))
    (abs_nonneg (γ₁ - γ₂)) hΔ
  have hp1 : ‖paperFT (fun u => (s u : ℂ)) (gammaOf ρ - γ₁)‖ ≤
      Real.exp (a / 2) * (4 * testNorm s) / (1 + d₁) ^ 2 :=
    h1.trans (by gcongr)
  have hp2 : ‖paperFT (fun u => (s u : ℂ)) (conj (gammaOf ρ) - γ₂)‖ ≤
      Real.exp (a / 2) * (4 * testNorm s) / (1 + d₂) ^ 2 :=
    h2.trans (by gcongr)
  calc (Z.mult ρ : ℝ) * ‖paperFT (fun u => (s u : ℂ)) (gammaOf ρ - γ₁)‖ *
        ‖paperFT (fun u => (s u : ℂ)) (conj (gammaOf ρ) - γ₂)‖
      ≤ (Z.mult ρ : ℝ) * (Real.exp (a / 2) * (4 * testNorm s) / (1 + d₁) ^ 2) *
          (Real.exp (a / 2) * (4 * testNorm s) / (1 + d₂) ^ 2) := by
        gcongr
    _ = (Z.mult ρ : ℝ) * (16 * Real.exp a * testNorm s ^ 2) *
          (1 / ((1 + d₁) ^ 2 * (1 + d₂) ^ 2)) := by
        rw [← hE2]; field_simp; ring
    _ ≤ (Z.mult ρ : ℝ) * (16 * Real.exp a * testNorm s ^ 2) *
          (4 / (1 + |γ₁ - γ₂|) ^ 2 * (1 / (1 + d₁) ^ 2 + 1 / (1 + d₂) ^ 2)) := by
        gcongr
    _ = 64 * Real.exp a * testNorm s ^ 2 / (1 + |γ₁ - γ₂|) ^ 2 *
          ((Z.mult ρ : ℝ) / (1 + d₁) ^ 2 + (Z.mult ρ : ℝ) / (1 + d₂) ^ 2) := by
        field_simp; ring

/-- The cross Weil value of two modulated tests. -/
theorem norm_W_modulatedTest_pair_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (γ₁ γ₂ : ℝ) {s : ℝ → ℝ}
    {a : ℝ} (ha : 0 ≤ a) (hs : ContDiff ℝ 2 s) (hsupp : ∀ u, s u ≠ 0 → |u| ≤ a) :
    Summable (fun ρ : Z.carrier => Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ) ∧
      ‖Z.W (modulatedTest γ₁ s) (modulatedTest γ₂ s)‖ ≤
        64 * Real.exp a * testNorm s ^ 2 / (1 + |γ₁ - γ₂|) ^ 2 *
          (A₀ * (10 * Real.log (|γ₁| + 3) + 48) + A₀ * (10 * Real.log (|γ₂| + 3) + 48)) := by
  obtain ⟨hs₁, ht₁⟩ := window_tsum_inv_sq_log_le Z hA₀ hloc γ₁
  obtain ⟨hs₂, ht₂⟩ := window_tsum_inv_sq_log_le Z hA₀ hloc γ₂
  set K := 64 * Real.exp a * testNorm s ^ 2 / (1 + |γ₁ - γ₂|) ^ 2 with hK
  have hK0 : 0 ≤ K := by have := testNorm_nonneg s; positivity
  have hb : ∀ ρ : Z.carrier, ‖Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ‖ ≤
      K * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 2 +
        (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₂|) ^ 2) := fun ρ =>
    norm_Wsummand_modulatedTest_pair_le Z γ₁ γ₂ ha hs hsupp ρ.2
  have hbs : Summable (fun ρ : Z.carrier => K * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 2 +
      (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₂|) ^ 2)) := (hs₁.add hs₂).mul_left K
  have hsum := Summable.of_norm_bounded hbs hb
  refine ⟨hsum, ?_⟩
  rw [ZeroConfig.W]
  have hns : Summable (fun ρ : Z.carrier =>
      ‖Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hbs
  calc ‖∑' ρ : Z.carrier, Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ‖
      ≤ ∑' ρ : Z.carrier, ‖Z.Wsummand (modulatedTest γ₁ s) (modulatedTest γ₂ s) ρ‖ :=
        norm_tsum_le_tsum_norm hns
    _ ≤ ∑' ρ : Z.carrier, K * ((Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 2 +
          (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₂|) ^ 2) := Summable.tsum_le_tsum hb hns hbs
    _ = K * (∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₁|) ^ 2 +
          ∑' ρ : Z.carrier, (Z.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - γ₂|) ^ 2) := by
        rw [tsum_mul_left, Summable.tsum_add hs₁ hs₂]
    _ ≤ K * (A₀ * (10 * Real.log (|γ₁| + 3) + 48) + A₀ * (10 * Real.log (|γ₂| + 3) + 48)) :=
        mul_le_mul_of_nonneg_left (add_le_add ht₁ ht₂) hK0

/-- Heights separated by `2R ≥ 2` have `Σ_{σ ≠ ρ} (1 + |γ_ρ - γ_σ|)^{-2} ≤ 10/R²`. -/
theorem sum_separated_inv_sq_le {T : Finset ℂ} {R : ℝ} (hR : 1 ≤ R)
    (hsep : ∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|) {ρ : ℂ} (hρT : ρ ∈ T) :
    ∑ σ ∈ T.erase ρ, 1 / (1 + |ρ.im - σ.im|) ^ 2 ≤ 10 / R ^ 2 := by
  classical
  have hR0 : 0 < R := by linarith
  set γ' : T → ℝ := fun σ => (σ : ℂ).im / (2 * R) with hγ'
  have hwin : ∀ t : ℝ, ∀ s : Finset T, (∀ σ ∈ s, t < γ' σ ∧ γ' σ ≤ t + 1) →
      ∑ σ ∈ s, (1 : ℝ) ≤ 1 := by
    intro t s hs
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcard : s.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro σ hσ σ' hσ'
      by_contra hne
      have hne' : (σ : ℂ) ≠ σ' := fun h => hne (Subtype.ext h)
      have h1 := hsep σ σ.2 σ' σ'.2 hne'
      have hw1 := hs σ hσ
      have hw2 := hs σ' hσ'
      have hlt : |(σ : ℂ).im - (σ' : ℂ).im| < 2 * R := by
        have e : (σ : ℂ).im - (σ' : ℂ).im = 2 * R * (γ' σ - γ' σ') := by
          simp only [hγ']; field_simp
        rw [e, abs_mul, abs_of_pos (by positivity)]
        have : |γ' σ - γ' σ'| < 1 := abs_sub_lt_iff.mpr ⟨by linarith [hw1.1, hw2.2],
          by linarith [hw1.2, hw2.1]⟩
        nlinarith
      linarith
    exact_mod_cast hcard
  obtain ⟨hsum, hle⟩ := window_tsum_inv_sq_le γ' (g := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    hwin (ρ.im / (2 * R))
  have hpt : ∀ σ ∈ T.erase ρ, 1 / (1 + |ρ.im - σ.im|) ^ 2 ≤
      1 / R ^ 2 * (1 / (1 + |σ.im / (2 * R) - ρ.im / (2 * R)|) ^ 2) := by
    intro σ hσ
    have hne : σ ≠ ρ := Finset.ne_of_mem_erase hσ
    have hσT := Finset.mem_of_mem_erase hσ
    have h1 := hsep ρ hρT σ hσT (Ne.symm hne)
    set Δ' := |σ.im / (2 * R) - ρ.im / (2 * R)| with hΔ'
    have hΔ : |ρ.im - σ.im| = 2 * R * Δ' := by
      have e : ρ.im - σ.im = 2 * R * (ρ.im / (2 * R) - σ.im / (2 * R)) := by field_simp
      rw [e, abs_mul, abs_of_pos (by positivity), hΔ', abs_sub_comm]
    have hΔ1 : 1 ≤ Δ' := by rw [hΔ] at h1; nlinarith
    rw [hΔ, div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity), one_mul]
    have : R * (1 + Δ') ≤ 1 + 2 * R * Δ' := by nlinarith
    have h0 : 0 ≤ R * (1 + Δ') := by positivity
    calc R ^ 2 * (1 + Δ') ^ 2 = (R * (1 + Δ')) ^ 2 := by ring
      _ ≤ (1 + 2 * R * Δ') ^ 2 := pow_le_pow_left₀ h0 this 2
      _ = 1 * (1 + 2 * R * Δ') ^ 2 := by ring
  have hall : ∑ σ ∈ T, 1 / (1 + |σ.im / (2 * R) - ρ.im / (2 * R)|) ^ 2 ≤ 10 := by
    have e : ∑ σ ∈ T, 1 / (1 + |σ.im / (2 * R) - ρ.im / (2 * R)|) ^ 2 =
        ∑ σ : T, (1 : ℝ) / (1 + |γ' σ - ρ.im / (2 * R)|) ^ 2 := by
      rw [← Finset.sum_coe_sort T]
    rw [e]
    refine (hsum.sum_le_tsum Finset.univ fun σ _ => by positivity).trans ?_
    simpa using hle
  calc ∑ σ ∈ T.erase ρ, 1 / (1 + |ρ.im - σ.im|) ^ 2
      ≤ ∑ σ ∈ T.erase ρ, 1 / R ^ 2 * (1 / (1 + |σ.im / (2 * R) - ρ.im / (2 * R)|) ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 1 / R ^ 2 * ∑ σ ∈ T.erase ρ, 1 / (1 + |σ.im / (2 * R) - ρ.im / (2 * R)|) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ 1 / R ^ 2 * ∑ σ ∈ T, 1 / (1 + |σ.im / (2 * R) - ρ.im / (2 * R)|) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset ρ T)
        intro σ _ _; positivity
    _ ≤ 1 / R ^ 2 * 10 := by gcongr
    _ = 10 / R ^ 2 := by ring

/-- The deep-pair energy grows with the depth: `∫ s_δ sinh(δu) ≤ ∫ s_δ sinh(δ'u)` for `δ ≤ δ'`. -/
theorem integral_sinhTest_mul_sinh_mono {a δ δ' : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ') :
    ∫ u, sinhTest a δ u * Real.sinh (δ * u) ≤ ∫ u, sinhTest a δ u * Real.sinh (δ' * u) := by
  have hcont : ∀ c : ℝ, Continuous (fun u => sinhTest a δ u * Real.sinh (c * u)) := fun c =>
    (sinhTest_contDiff a δ).continuous.mul
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
  have hcs : ∀ c : ℝ, HasCompactSupport (fun u => sinhTest a δ u * Real.sinh (c * u)) := fun c =>
    (hasCompactSupport_of_support_subset_abs (sinhTest_supp (δ := δ) ha)).mul_right
  refine integral_mono ((hcont δ).integrable_of_hasCompactSupport (hcs δ))
    ((hcont δ').integrable_of_hasCompactSupport (hcs δ')) fun u => ?_
  simp only [sinhTest]
  have hw := sinhTestWeight_nonneg a u
  rcases le_total 0 u with hu | hu
  · have h1 : Real.sinh (δ * u) ≤ Real.sinh (δ' * u) :=
      Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right hδδ' hu)
    have h0 : 0 ≤ Real.sinh (δ * u) := Real.sinh_nonneg_iff.mpr (mul_nonneg hδ hu)
    have := mul_le_mul_of_nonneg_left h1 (mul_nonneg h0 hw)
    nlinarith
  · have h1 : Real.sinh (δ' * u) ≤ Real.sinh (δ * u) :=
      Real.sinh_le_sinh.mpr (mul_le_mul_of_nonpos_right hδδ' hu)
    have h0 : Real.sinh (δ * u) ≤ 0 := by
      rw [← Real.sinh_zero]; exact Real.sinh_le_sinh.mpr (mul_nonpos_of_nonneg_of_nonpos hδ hu)
    have := mul_le_mul_of_nonpos_left h1 h0
    nlinarith

/-! ### Negative directions from separated visible pairs -/

theorem paperFT_finset_sum {ι : Type*} (T : Finset ι) (c : ι → ℂ) {f : ι → ℝ → ℂ}
    (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i)) (z : ℂ) :
    paperFT (fun u => ∑ i ∈ T, c i * f i u) z = ∑ i ∈ T, c i * paperFT (f i) z := by
  rw [paperFT_def]
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [paperFT_def, ← integral_const_mul]
    congr 1 with u; ring
  · intro i _
    have := integrable_mul_cexp (hf i) (hfc i) z
    simpa [mul_assoc] using this.const_mul (c i)

/-- The Weil form of a combination `Σ c_ρ f_ρ` is the Hermitian form of the Gram matrix
`W(f_ρ, f_σ)`, when all cross zero sums converge. -/
theorem W_finset_sum {ι : Type*} (Z : ZeroConfig) (T : Finset ι) (c : ι → ℂ) {f : ι → ℝ → ℂ}
    (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i))
    (hsum : ∀ i j, Summable (fun ρ : Z.carrier => Z.Wsummand (f i) (f j) ρ)) :
    Z.W (fun u => ∑ i ∈ T, c i * f i u) (fun u => ∑ i ∈ T, c i * f i u) =
      ∑ i ∈ T, ∑ j ∈ T, c i * conj (c j) * Z.W (f i) (f j) := by
  have hpt : ∀ ρ : ℂ, Z.Wsummand (fun u => ∑ i ∈ T, c i * f i u)
      (fun u => ∑ i ∈ T, c i * f i u) ρ =
      ∑ i ∈ T, ∑ j ∈ T, c i * conj (c j) * Z.Wsummand (f i) (f j) ρ := by
    intro ρ
    rw [ZeroConfig.Wsummand, paperFT_finset_sum T c hf hfc, paperFT_finset_sum T c hf hfc,
      map_sum, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ZeroConfig.Wsummand, map_mul]
    ring
  rw [ZeroConfig.W]
  simp_rw [hpt]
  rw [Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => (hsum i j).mul_left _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum fun j _ => (hsum i j).mul_left _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left, ZeroConfig.W]

/-- The diagonal Gram entry of a visible isolated pair. -/
theorem re_W_visible_pair_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a δ R Hm : ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (hR : 0 ≤ R) {ρ : ℂ} (hρ : ρ ∈ Z.carrier) (hre : 1 / 2 + δ ≤ ρ.re)
    (hHm : |ρ.im| ≤ Hm)
    (hiso : ∀ σ ∈ Z.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R → σ.re = 1 / 2) :
    (Z.W (modulatedTest ρ.im (sinhTest a δ)) (modulatedTest ρ.im (sinhTest a δ))).re ≤
      -2 * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 +
        384 * A₀ * Real.log (Hm + 3) * testNorm (sinhTest a δ) ^ 2 *
          (1 + Real.exp a / (1 + R)) := by
  set δ' := ρ.re - 1 / 2 with hδ'
  have hδ'0 : 0 < δ' := by linarith
  have hmaster := re_W_modulatedTest_le_of_isolated Z hA₀ hloc hρ hδ'0 (by rw [hδ']; ring) ha hR
    hiso (sinhTest_contDiff a δ) (sinhTest_odd a δ) (sinhTest_supp ha)
  have hP0 : 0 ≤ ∫ u, sinhTest a δ u * Real.sinh (δ * u) := by
    refine integral_nonneg fun u => ?_
    show 0 ≤ sinhTest a δ u * Real.sinh (δ * u)
    simp only [sinhTest]
    have := mul_nonneg (mul_self_nonneg (Real.sinh (δ * u))) (sinhTestWeight_nonneg a u)
    nlinarith
  have hmono := integral_sinhTest_mul_sinh_mono (a := a) ha hδ.le (show δ ≤ δ' by linarith)
  have hsq : (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 ≤
      (∫ u, sinhTest a δ u * Real.sinh (δ' * u)) ^ 2 := pow_le_pow_left₀ hP0 hmono 2
  have hm : (1 : ℝ) ≤ Z.mult ρ := by exact_mod_cast Z.one_le_mult ρ hρ
  have hlog : Real.log (|ρ.im| + 3) ≤ Real.log (Hm + 3) :=
    Real.log_le_log (by positivity) (by linarith)
  have hN := sq_nonneg (testNorm (sinhTest a δ))
  have hK : 0 ≤ 1 + Real.exp a / (1 + R) := by positivity
  have hA0 : 0 ≤ A₀ := by linarith
  have h1 : -2 * (Z.mult ρ : ℝ) * (∫ u, sinhTest a δ u * Real.sinh (δ' * u)) ^ 2 ≤
      -2 * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 := by
    have := sq_nonneg (∫ u, sinhTest a δ u * Real.sinh (δ' * u))
    nlinarith
  have h2 : 384 * A₀ * Real.log (|ρ.im| + 3) * testNorm (sinhTest a δ) ^ 2 *
      (1 + Real.exp a / (1 + R)) ≤ 384 * A₀ * Real.log (Hm + 3) * testNorm (sinhTest a δ) ^ 2 *
        (1 + Real.exp a / (1 + R)) := by gcongr
  linarith

/-- **Separated visible pairs give independent negative directions.**  Let `T` be a finite set of
zeros of depth at least `δ` and height at most `H_m`, pairwise `2R` apart in height with `R ≥ 1`,
and each isolated: every other zero within height `R` of `ρ ∈ T`, apart from `1 - ρ̄`, lies on the
critical line.  Suppose the visibility condition holds:
`384A₀ log(H_m + 3)N²(1 + e^a/(1+R)) + 64e^aN² · 2A₀(10 log(H_m + 3) + 48) · 10/R² < 2P²`,
with `N = ‖s‖₁ + ‖s''‖₁`, `P = ∫ s sinh(δu)`, `s = sinh(δu)(a² - u²)₊^{5/2}`.  Then every nonzero
combination `Σ_ρ c_ρ e^{-iγ_ρu}s(u)` has negative Weil form.  So the modulated tests at the
heights of `T` span a `|T|`-dimensional negative subspace. -/
theorem re_W_visible_combination_le (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a δ R Hm : ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (hR : 1 ≤ R) (T : Finset ℂ)
    (hT : ∀ ρ ∈ T, ρ ∈ Z.carrier ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ Hm)
    (hsep : ∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|)
    (hiso : ∀ ρ ∈ T, ∀ σ ∈ Z.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R → σ.re = 1 / 2)
    (hlog : 0 ≤ Real.log (Hm + 3)) (c : ℂ → ℂ) :
    (Z.W (fun u => ∑ ρ ∈ T, c ρ * modulatedTest ρ.im (sinhTest a δ) u)
      (fun u => ∑ ρ ∈ T, c ρ * modulatedTest ρ.im (sinhTest a δ) u)).re ≤
      (-(2 * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2) +
        (384 * A₀ * Real.log (Hm + 3) * testNorm (sinhTest a δ) ^ 2 * (1 + Real.exp a / (1 + R)) +
          64 * Real.exp a * testNorm (sinhTest a δ) ^ 2 *
            (2 * (A₀ * (10 * Real.log (Hm + 3) + 48))) * (10 / R ^ 2))) *
        ∑ ρ ∈ T, ‖c ρ‖ ^ 2 := by
  classical
  set s := sinhTest a δ with hsdef
  set N := testNorm s with hN
  set P := ∫ u, s u * Real.sinh (δ * u) with hP
  set f : ℂ → ℝ → ℂ := fun ρ => modulatedTest ρ.im s with hf
  have hs := sinhTest_contDiff a δ
  have hsupp : ∀ u, s u ≠ 0 → |u| ≤ a := sinhTest_supp ha
  have hfc : ∀ ρ, Continuous (f ρ) := fun ρ => continuous_modulatedTest _ hs.continuous
  have hfcs : ∀ ρ, HasCompactSupport (f ρ) := fun ρ => hasCompactSupport_modulatedTest _ hsupp
  have hpair := fun ρ σ : ℂ => norm_W_modulatedTest_pair_le Z hA₀ hloc ρ.im σ.im ha hs hsupp
  have hexp := W_finset_sum Z T c hfc hfcs (fun ρ σ => (hpair ρ σ).1)
  rw [hexp, Complex.re_sum]
  set Ed := 384 * A₀ * Real.log (Hm + 3) * N ^ 2 * (1 + Real.exp a / (1 + R)) with hEd
  set K := 64 * Real.exp a * N ^ 2 * (2 * (A₀ * (10 * Real.log (Hm + 3) + 48))) with hKdef
  have hA0 : 0 ≤ A₀ := by linarith
  have hlog0 : 0 ≤ Real.log (Hm + 3) := hlog
  have hK0 : 0 ≤ K := by positivity
  set κ : ℂ → ℂ → ℝ := fun ρ σ => if ρ = σ then 0 else K / (1 + |ρ.im - σ.im|) ^ 2 with hκ
  have hκ0 : ∀ ρ σ, 0 ≤ κ ρ σ := fun ρ σ => by simp only [hκ]; split_ifs <;> positivity
  -- termwise bounds
  have hdiag : ∀ ρ ∈ T, (Z.W (f ρ) (f ρ)).re ≤ -2 * P ^ 2 + Ed := fun ρ hρ =>
    re_W_visible_pair_le Z hA₀ hloc ha hδ (by linarith) (hT ρ hρ).1 (hT ρ hρ).2.1 (hT ρ hρ).2.2
      (hiso ρ hρ)
  have hoff : ∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → ‖Z.W (f ρ) (f σ)‖ ≤ K / (1 + |ρ.im - σ.im|) ^ 2 := by
    intro ρ hρ σ hσ _
    refine (hpair ρ σ).2.trans ?_
    have h1 : Real.log (|ρ.im| + 3) ≤ Real.log (Hm + 3) :=
      Real.log_le_log (by positivity) (by linarith [(hT ρ hρ).2.2])
    have h2 : Real.log (|σ.im| + 3) ≤ Real.log (Hm + 3) :=
      Real.log_le_log (by positivity) (by linarith [(hT σ hσ).2.2])
    have e : K / (1 + |ρ.im - σ.im|) ^ 2 = 64 * Real.exp a * N ^ 2 / (1 + |ρ.im - σ.im|) ^ 2 *
        (A₀ * (10 * Real.log (Hm + 3) + 48) + A₀ * (10 * Real.log (Hm + 3) + 48)) := by
      rw [hKdef]; ring
    rw [e]
    have : 0 ≤ 64 * Real.exp a * N ^ 2 / (1 + |ρ.im - σ.im|) ^ 2 := by positivity
    gcongr
  have hterm : ∀ ρ ∈ T, ∀ σ ∈ T, (c ρ * conj (c σ) * Z.W (f ρ) (f σ)).re ≤
      (if ρ = σ then ‖c ρ‖ ^ 2 * (-2 * P ^ 2 + Ed) else 0) +
        1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ := by
    intro ρ hρ σ hσ
    by_cases hrs : ρ = σ
    · subst hrs
      rw [if_pos rfl]
      simp only [hκ, if_pos rfl, mul_zero, add_zero]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.re_ofReal_mul]
      exact mul_le_mul_of_nonneg_left (hdiag ρ hρ) (sq_nonneg _)
    · rw [if_neg hrs, zero_add]
      simp only [hκ, if_neg hrs, one_mul]
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left (hoff ρ hρ σ hσ hrs) (by positivity)
  -- Schur bound on the off-diagonal part
  have hrow : ∀ ρ ∈ T, ∑ σ ∈ T, (1 : ℝ) * κ ρ σ ≤ K * (10 / R ^ 2) := by
    intro ρ hρ
    have e : ∑ σ ∈ T, (1 : ℝ) * κ ρ σ = K * ∑ σ ∈ T.erase ρ, 1 / (1 + |ρ.im - σ.im|) ^ 2 := by
      rw [← Finset.add_sum_erase T _ hρ]
      simp only [hκ, if_pos rfl, one_mul, zero_add]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hσ))]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (sum_separated_inv_sq_le hR hsep hρ) hK0
  have hcol : ∀ σ ∈ T, ∑ ρ ∈ T, (1 : ℝ) * κ ρ σ ≤ K * (10 / R ^ 2) := by
    intro σ hσ
    have e : ∑ ρ ∈ T, (1 : ℝ) * κ ρ σ = K * ∑ ρ ∈ T.erase σ, 1 / (1 + |σ.im - ρ.im|) ^ 2 := by
      rw [← Finset.add_sum_erase T _ hσ]
      simp only [hκ, if_pos rfl, one_mul, zero_add]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      rw [if_neg (Finset.ne_of_mem_erase hρ), abs_sub_comm]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (sum_separated_inv_sq_le hR hsep hσ) hK0
  have hschur := double_sum_le_of_row_col T (m := fun _ => (1 : ℝ)) (x := fun ρ => ‖c ρ‖)
    (fun _ => zero_le_one) hκ0 hrow hcol
  have hsum_le : ∑ ρ ∈ T, (∑ σ ∈ T, c ρ * conj (c σ) * Z.W (f ρ) (f σ)).re ≤
      ∑ ρ ∈ T, ∑ σ ∈ T, ((if ρ = σ then ‖c ρ‖ ^ 2 * (-2 * P ^ 2 + Ed) else 0) +
        1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ) := by
    refine Finset.sum_le_sum fun ρ hρ => ?_
    rw [Complex.re_sum]
    exact Finset.sum_le_sum fun σ hσ => hterm ρ hρ σ hσ
  have hsplit : ∑ ρ ∈ T, ∑ σ ∈ T, ((if ρ = σ then ‖c ρ‖ ^ 2 * (-2 * P ^ 2 + Ed) else 0) +
        1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ) =
      (∑ ρ ∈ T, ‖c ρ‖ ^ 2) * (-2 * P ^ 2 + Ed) +
        ∑ ρ ∈ T, ∑ σ ∈ T, 1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ := by
    simp_rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun ρ hρ => by rw [if_pos hρ]
  have hS' : ∑ σ ∈ T, (1 : ℝ) * ‖c σ‖ ^ 2 = ∑ ρ ∈ T, ‖c ρ‖ ^ 2 := by simp
  rw [hS'] at hschur
  calc ∑ ρ ∈ T, (∑ σ ∈ T, c ρ * conj (c σ) * Z.W (f ρ) (f σ)).re
      ≤ (∑ ρ ∈ T, ‖c ρ‖ ^ 2) * (-2 * P ^ 2 + Ed) +
          ∑ ρ ∈ T, ∑ σ ∈ T, 1 * 1 * (‖c ρ‖ * ‖c σ‖) * κ ρ σ := hsum_le.trans (le_of_eq hsplit)
    _ ≤ (∑ ρ ∈ T, ‖c ρ‖ ^ 2) * (-2 * P ^ 2 + Ed) + K * (10 / R ^ 2) * ∑ ρ ∈ T, ‖c ρ‖ ^ 2 := by
        linarith
    _ = _ := by rw [hEd, hKdef]; ring

/-- The strict form: every nonzero combination has negative Weil form. -/
theorem re_W_visible_combination_neg (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a δ R Hm : ℝ} (ha : 0 ≤ a)
    (hδ : 0 < δ) (hR : 1 ≤ R) (T : Finset ℂ)
    (hT : ∀ ρ ∈ T, ρ ∈ Z.carrier ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ Hm)
    (hsep : ∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|)
    (hiso : ∀ ρ ∈ T, ∀ σ ∈ Z.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R → σ.re = 1 / 2)
    (hvis : 384 * A₀ * Real.log (Hm + 3) * testNorm (sinhTest a δ) ^ 2 * (1 + Real.exp a / (1 + R)) +
        64 * Real.exp a * testNorm (sinhTest a δ) ^ 2 *
          (2 * (A₀ * (10 * Real.log (Hm + 3) + 48))) * (10 / R ^ 2) <
      2 * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2)
    (c : ℂ → ℂ) (hc : ∃ ρ ∈ T, c ρ ≠ 0) :
    (Z.W (fun u => ∑ ρ ∈ T, c ρ * modulatedTest ρ.im (sinhTest a δ) u)
      (fun u => ∑ ρ ∈ T, c ρ * modulatedTest ρ.im (sinhTest a δ) u)).re < 0 := by
  obtain ⟨ρ₀, hρ₀, hc₀⟩ := hc
  have hlog : 0 ≤ Real.log (Hm + 3) :=
    Real.log_nonneg (by linarith [abs_nonneg ρ₀.im, (hT ρ₀ hρ₀).2.2])
  have h := re_W_visible_combination_le Z hA₀ hloc ha hδ hR T hT hsep hiso hlog c
  have hS : 0 < ∑ ρ ∈ T, ‖c ρ‖ ^ 2 := by
    have h1 : 0 < ‖c ρ₀‖ ^ 2 := by positivity
    have := Finset.single_le_sum (f := fun ρ => ‖c ρ‖ ^ 2) (fun _ _ => sq_nonneg _) hρ₀
    linarith
  have hneg : -(2 * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2) +
      (384 * A₀ * Real.log (Hm + 3) * testNorm (sinhTest a δ) ^ 2 * (1 + Real.exp a / (1 + R)) +
        64 * Real.exp a * testNorm (sinhTest a δ) ^ 2 *
          (2 * (A₀ * (10 * Real.log (Hm + 3) + 48))) * (10 / R ^ 2)) < 0 := by linarith
  exact lt_of_le_of_lt h (mul_neg_of_neg_of_pos hneg hS)

/-! ### The polar-constrained negative subspace -/

/-- The combination `Σ_ρ c_ρ e^{-iγ_ρu} s(u)` over a finite set of heights. -/
def visibleCombination (T : Finset ℂ) (s : ℝ → ℝ) (c : T → ℂ) : ℝ → ℂ :=
  fun u => ∑ ρ : T, c ρ * modulatedTest (ρ : ℂ).im s u

/-- Coefficients on `T`, extended by zero. -/
def extendCoeff (T : Finset ℂ) (c : T → ℂ) : ℂ → ℂ :=
  fun ρ => if h : ρ ∈ T then c ⟨ρ, h⟩ else 0

theorem visibleCombination_eq (T : Finset ℂ) (s : ℝ → ℝ) (c : T → ℂ) :
    visibleCombination T s c =
      fun u => ∑ ρ ∈ T, extendCoeff T c ρ * modulatedTest ρ.im s u := by
  funext u
  unfold visibleCombination
  rw [← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp [extendCoeff, ρ.2]

theorem sum_norm_sq_extendCoeff (T : Finset ℂ) (c : T → ℂ) :
    ∑ ρ ∈ T, ‖extendCoeff T c ρ‖ ^ 2 = ∑ ρ : T, ‖c ρ‖ ^ 2 := by
  rw [← Finset.sum_coe_sort T]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp [extendCoeff, ρ.2]

theorem exists_extendCoeff_ne {T : Finset ℂ} {c : T → ℂ} (hc : c ≠ 0) :
    ∃ ρ ∈ T, extendCoeff T c ρ ≠ 0 := by
  obtain ⟨ρ, hρ⟩ := Function.ne_iff.mp hc
  exact ⟨ρ, ρ.2, by simpa [extendCoeff, ρ.2] using hρ⟩

theorem norm_sq_visibleCombination_le (T : Finset ℂ) (s : ℝ → ℝ) (c : T → ℂ) (u : ℝ) :
    ‖visibleCombination T s c u‖ ^ 2 ≤ T.card * (∑ ρ : T, ‖c ρ‖ ^ 2) * s u ^ 2 := by
  have h1 : ‖visibleCombination T s c u‖ ≤ (∑ ρ : T, ‖c ρ‖) * |s u| := by
    unfold visibleCombination
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [norm_mul]
    unfold modulatedTest
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    simp
  have h2 : (∑ ρ : T, ‖c ρ‖) ^ 2 ≤ (Finset.univ : Finset T).card * ∑ ρ : T, ‖c ρ‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [Finset.card_univ, Fintype.card_coe] at h2
  have h0 : 0 ≤ (∑ ρ : T, ‖c ρ‖) * |s u| := by positivity
  calc ‖visibleCombination T s c u‖ ^ 2 ≤ ((∑ ρ : T, ‖c ρ‖) * |s u|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (∑ ρ : T, ‖c ρ‖) ^ 2 * s u ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ T.card * (∑ ρ : T, ‖c ρ‖ ^ 2) * s u ^ 2 :=
        mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-- The visibility margin `λ = 2P² - (E_d + 10K/R²)` of `re_W_visible_combination_le`. -/
def visibleMargin (A₀ a δ R Hm : ℝ) : ℝ :=
  2 * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 -
    (384 * A₀ * Real.log (Hm + 3) * testNorm (sinhTest a δ) ^ 2 * (1 + Real.exp a / (1 + R)) +
      64 * Real.exp a * testNorm (sinhTest a δ) ^ 2 *
        (2 * (A₀ * (10 * Real.log (Hm + 3) + 48))) * (10 / R ^ 2))

/-- **Visible pairs give negative squares of the polar-constrained form.**  Under the hypotheses
of `re_W_visible_combination_neg`, the polar-constrained `C²` tests on `[-a, a]` contain a subspace
`V` of dimension at least `|T| - 2` on which
`Re W(f, f) < -λ/(|T|(∫s² + 1)) ∫|f|²`, with `λ = visibleMargin > 0`. -/
theorem exists_polar_negative_subspace_of_visible_pairs (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) {a δ R Hm : ℝ} (ha : 0 < a)
    (hδ : 0 < δ) (hR : 1 ≤ R) (T : Finset ℂ) (hTne : T.Nonempty)
    (hT : ∀ ρ ∈ T, ρ ∈ Z.carrier ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ Hm)
    (hsep : ∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|)
    (hiso : ∀ ρ ∈ T, ∀ σ ∈ Z.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R → σ.re = 1 / 2)
    (hvis : 0 < visibleMargin A₀ a δ R Hm) :
    ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧ T.card ≤ Module.finrank ℂ V + 2 ∧
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) ∧
      ∀ f ∈ V, f ≠ 0 → (Z.W f f).re <
        -(visibleMargin A₀ a δ R Hm / (T.card * ((∫ u, sinhTest a δ u ^ 2) + 1)) *
          ∫ u, ‖f u‖ ^ 2) := by
  classical
  set s := sinhTest a δ with hsdef
  set fr : T → ℝ → ℂ := fun ρ => modulatedTest (ρ : ℂ).im s with hfr
  have hs := sinhTest_contDiff a δ
  have hsupp : ∀ u, s u ≠ 0 → |u| ≤ a := sinhTest_supp ha.le
  have hlog : 0 ≤ Real.log (Hm + 3) := by
    obtain ⟨ρ, hρ⟩ := hTne
    exact Real.log_nonneg (by linarith [abs_nonneg ρ.im, (hT ρ hρ).2.2])
  have hvis' : 384 * A₀ * Real.log (Hm + 3) * testNorm (sinhTest a δ) ^ 2 *
      (1 + Real.exp a / (1 + R)) + 64 * Real.exp a * testNorm (sinhTest a δ) ^ 2 *
        (2 * (A₀ * (10 * Real.log (Hm + 3) + 48))) * (10 / R ^ 2) <
      2 * (∫ u, sinhTest a δ u * Real.sinh (δ * u)) ^ 2 := by
    unfold visibleMargin at hvis; linarith
  -- the synthesis map `c ↦ Σ c_ρ f_ρ`
  let Γ : (T → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
    { toFun := visibleCombination T s
      map_add' := fun c d => by
        funext u; simp only [visibleCombination, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun k c => by
        funext u
        simp only [visibleCombination, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum, mul_assoc] }
  -- the polar map
  let Φ : (T → ℂ) →ₗ[ℂ] ℂ × ℂ :=
    { toFun := fun c => (∑ ρ : T, c ρ * paperFT (fr ρ) (I / 2),
        ∑ ρ : T, c ρ * paperFT (fr ρ) (-(I / 2)))
      map_add' := fun c d => by
        ext <;> simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun k c => by
        ext <;> simp [Finset.mul_sum, mul_assoc] }
  have hfrc : ∀ ρ, Continuous (fr ρ) := fun ρ => continuous_modulatedTest _ hs.continuous
  have hfrs : ∀ ρ, HasCompactSupport (fr ρ) := fun ρ => hasCompactSupport_modulatedTest _ hsupp
  have hΓFT : ∀ c z, paperFT (Γ c) z = ∑ ρ : T, c ρ * paperFT (fr ρ) z := fun c z =>
    paperFT_finset_sum Finset.univ c hfrc hfrs z
  -- negativity on nonzero coefficients
  have hW0 : Z.W 0 0 = 0 := by
    rw [ZeroConfig.W]
    have : ∀ ρ : Z.carrier, Z.Wsummand 0 0 ρ = 0 := fun ρ => by
      simp [ZeroConfig.Wsummand, paperFT_def]
    simp [this]
  have hneg : ∀ c : T → ℂ, c ≠ 0 → (Z.W (Γ c) (Γ c)).re < 0 := by
    intro c hc
    have h := re_W_visible_combination_neg Z hA₀ hloc ha.le hδ hR T hT hsep hiso hvis'
      (extendCoeff T c) (exists_extendCoeff_ne hc)
    change (Z.W (visibleCombination T s c) (visibleCombination T s c)).re < 0
    rwa [visibleCombination_eq]
  have hinj : Function.Injective Γ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    by_contra hc0
    have := hneg c hc0
    rw [hc, hW0, Complex.zero_re] at this
    exact lt_irrefl _ this
  set V := (LinearMap.ker Φ).map Γ with hV
  have hequiv := Submodule.equivMapOfInjective Γ hinj (LinearMap.ker Φ)
  have hfinV : FiniteDimensional ℂ V := LinearEquiv.finiteDimensional hequiv
  have hdimV : Module.finrank ℂ V = Module.finrank ℂ (LinearMap.ker Φ) := hequiv.finrank_eq.symm
  have hrank := LinearMap.finrank_range_add_finrank_ker Φ
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrank
  have hrange : Module.finrank ℂ (LinearMap.range Φ) ≤ 2 := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    rw [Module.finrank_prod, Module.finrank_self] at this
    exact this
  refine ⟨V, hfinV, by omega, ?_, ?_⟩
  · intro f hf
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hf
    rw [LinearMap.mem_ker] at hc
    have hc1 : ∑ ρ : T, c ρ * paperFT (fr ρ) (I / 2) = 0 := congrArg Prod.fst hc
    have hc2 : ∑ ρ : T, c ρ * paperFT (fr ρ) (-(I / 2)) = 0 := congrArg Prod.snd hc
    refine ⟨?_, ?_, by rw [hΓFT]; exact hc1, by rw [hΓFT]; exact hc2⟩
    · change ContDiff ℝ 2 (fun u => ∑ ρ : T, c ρ * modulatedTest (ρ : ℂ).im s u)
      exact ContDiff.sum fun ρ _ => contDiff_const.mul (modulatedTest_contDiff _ hs)
    · refine tsupport_subset_of_support_subset_abs fun u hu => ?_
      change (∑ ρ : T, c ρ * modulatedTest (ρ : ℂ).im s u) ≠ 0 at hu
      obtain ⟨ρ, -, hρ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
      have : s u ≠ 0 := by
        intro h0; apply hρ; simp [modulatedTest, h0]
      exact hsupp u this
  · intro f hf hf0
    obtain ⟨c, -, rfl⟩ := Submodule.mem_map.mp hf
    have hc0 : c ≠ 0 := by
      intro h; apply hf0; rw [h, map_zero]
    have hle := re_W_visible_combination_le Z hA₀ hloc ha.le hδ hR T hT hsep hiso hlog
      (extendCoeff T c)
    rw [sum_norm_sq_extendCoeff, ← visibleCombination_eq] at hle
    change (Z.W (visibleCombination T s c) (visibleCombination T s c)).re < _
    set S := ∑ ρ : T, ‖c ρ‖ ^ 2 with hS
    have hSpos : 0 < S := by
      obtain ⟨ρ, hρ⟩ := Function.ne_iff.mp hc0
      have h1 : 0 < ‖c ρ‖ ^ 2 := by positivity
      have := Finset.single_le_sum (f := fun ρ => ‖c ρ‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ ρ)
      linarith
    set Q := ∫ u, s u ^ 2 with hQ
    have hQ0 : 0 ≤ Q := integral_nonneg fun _ => sq_nonneg _
    have hL2 : ∫ u, ‖visibleCombination T s c u‖ ^ 2 ≤ T.card * S * Q := by
      have iS := integrable_sq_of_supp hs.continuous hsupp
      have hcont : Continuous (visibleCombination T s c) := by
        unfold visibleCombination
        exact continuous_finsetSum _ fun ρ _ => continuous_const.mul (hfrc ρ)
      have hcs : HasCompactSupport (visibleCombination T s c) :=
        hasCompactSupport_of_support_subset_abs fun u hu => by
          obtain ⟨ρ, -, hρ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hu
          have : s u ≠ 0 := by intro h0; apply hρ; simp [modulatedTest, h0]
          exact hsupp u this
      have iF : Integrable (fun u => ‖visibleCombination T s c u‖ ^ 2) := by
        have h2 : HasCompactSupport (fun u => ‖visibleCombination T s c u‖ *
            ‖visibleCombination T s c u‖) := hcs.norm.mul_right
        have : HasCompactSupport (fun u => ‖visibleCombination T s c u‖ ^ 2) := by
          rw [show (fun u => ‖visibleCombination T s c u‖ ^ 2) =
            fun u => ‖visibleCombination T s c u‖ * ‖visibleCombination T s c u‖ from
              funext fun u => sq _]
          exact h2
        exact (hcont.norm.pow 2).integrable_of_hasCompactSupport this
      calc ∫ u, ‖visibleCombination T s c u‖ ^ 2 ≤ ∫ u, T.card * S * s u ^ 2 :=
            integral_mono iF (iS.const_mul _) (norm_sq_visibleCombination_le T s c)
        _ = T.card * S * Q := by rw [integral_const_mul]
    have hcard : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
    set lam := visibleMargin A₀ a δ R Hm with hlam
    have hle' : (Z.W (visibleCombination T s c) (visibleCombination T s c)).re ≤ -lam * S := by
      refine hle.trans (le_of_eq ?_)
      rw [hlam]; unfold visibleMargin; ring
    have hkey : lam / (T.card * (Q + 1)) * ∫ u, ‖visibleCombination T s c u‖ ^ 2 < lam * S := by
      have hden : 0 < (T.card : ℝ) * (Q + 1) := by positivity
      calc lam / (T.card * (Q + 1)) * ∫ u, ‖visibleCombination T s c u‖ ^ 2
          ≤ lam / (T.card * (Q + 1)) * (T.card * S * Q) :=
            mul_le_mul_of_nonneg_left hL2 (by positivity)
        _ = lam * S * (Q / (Q + 1)) := by field_simp
        _ < lam * S := by
            have : Q / (Q + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
            have hlS : 0 < lam * S := mul_pos hvis hSpos
            nlinarith
    have e : (∫ u, ‖Γ c u‖ ^ 2) = ∫ u, ‖visibleCombination T s c u‖ ^ 2 := rfl
    rw [e]
    linarith

/-! ### The finite-level inertia of `ζ` -/

/-- The `ε`-negative index of the level-`a` Weil form: the largest dimension of a space of
polar-constrained `C²` tests on `[-a, a]` on which `Re W(f, f) < -ε ∫|f|²` off `0`. -/
def weilNegIndex (Z : ZeroConfig) (a ε : ℝ) : ℕ :=
  sSup {n : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ), FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n ∧
    (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
      paperFT f (-(I / 2)) = 0) ∧
    ∀ f ∈ V, f ≠ 0 → (Z.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)}

/-- **The finite-level inertia law for `ζ`.**  There is `A₀ ≥ 1` such that, at every level `a > 0`:

* **(upper)** for `0 < ε ≤ 1`, the `ε`-negative index is at most the number of off-line pairs with
  `|γ| ≤ H(A₀, a, ε)`, where `log H ≤ 7000 e^a + 7 log A₀ + 7 log(1/ε) + 150`;
* **(lower)** if `T` is a nonempty set of zeros of depth `≥ δ` and height `≤ H_m`, pairwise `2R`
  apart (`R ≥ 1`), isolated at radius `R` from other off-line zeros, and visible
  (`visibleMargin A₀ a δ R H_m > 0`), then for every `ε ≤ λ/(|T|(∫s² + 1))` the `ε`-negative index
  is at least `|T| - 2`.

The negative squares of the finite-level Hodge form are the off-line pairs of `ζ`, counted between
the visibility height `exp(e^{2δa - O(log a)})` of isolated pairs and the archimedean horizon
`exp(O(e^a))`. -/
theorem zeta_weil_inertia_law :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧
      (∀ a ε : ℝ, 0 < a → 0 < ε → ε ≤ 1 →
        weilNegIndex zetaZeroConfig a ε ≤
          (offLinePairsBelow zetaZeroConfig (inertiaHorizonHeight A₀ a ε)).card) ∧
      (∀ (a δ R Hm ε : ℝ) (T : Finset ℂ), 0 < a → 0 < δ → 1 ≤ R → T.Nonempty →
        (∀ ρ ∈ T, ρ ∈ zetaZeroConfig.carrier ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ Hm) →
        (∀ ρ ∈ T, ∀ σ ∈ T, ρ ≠ σ → 2 * R ≤ |ρ.im - σ.im|) →
        (∀ ρ ∈ T, ∀ σ ∈ zetaZeroConfig.carrier, σ ≠ ρ → σ ≠ reflect ρ → |σ.im - ρ.im| ≤ R →
          σ.re = 1 / 2) →
        0 < visibleMargin A₀ a δ R Hm → 0 < ε → ε ≤ 1 →
        ε ≤ visibleMargin A₀ a δ R Hm / (T.card * ((∫ u, sinhTest a δ u ^ 2) + 1)) →
        T.card ≤ weilNegIndex zetaZeroConfig a ε + 2) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  have hupper := zeta_weil_negative_index_le_of_local_count hA₀ hloc
  have hbdd : ∀ a ε : ℝ, 0 < a → 0 < ε → ε ≤ 1 → BddAbove {n : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ),
      FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n ∧
      (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
        paperFT f (-(I / 2)) = 0) ∧
      ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)} := by
    intro a ε ha hε hε1
    refine ⟨(offLinePairsBelow zetaZeroConfig (inertiaHorizonHeight A₀ a ε)).card, ?_⟩
    rintro n ⟨V, hVf, rfl, hV, hneg⟩
    exact hupper a ε ha hε hε1 V hVf hV hneg
  refine ⟨A₀, hA₀, fun a ε ha hε hε1 => ?_, fun a δ R Hm ε T ha hδ hR hTne hT hsep hiso hvis
    hε hε1 hεT => ?_⟩
  · unfold weilNegIndex
    refine csSup_le ⟨0, ⊥, inferInstance, finrank_bot ℂ (ℝ → ℂ), fun f hf => ?_,
      fun f hf hf0 => absurd ((Submodule.mem_bot ℂ).mp hf) hf0⟩ ?_
    · rw [(Submodule.mem_bot ℂ).mp hf]
      refine ⟨contDiff_const, by simp [tsupport, Function.support], by simp [paperFT_def],
        by simp [paperFT_def]⟩
    · rintro n ⟨V, hVf, rfl, hV, hneg⟩
      exact hupper a ε ha hε hε1 V hVf hV hneg
  · obtain ⟨V, hVf, hdim, hV, hneg⟩ := exists_polar_negative_subspace_of_visible_pairs
      zetaZeroConfig hA₀ hloc ha hδ hR T hTne hT hsep hiso hvis
    have hmem : Module.finrank ℂ V ∈ {n : ℕ | ∃ V : Submodule ℂ (ℝ → ℂ),
        FiniteDimensional ℂ V ∧ Module.finrank ℂ V = n ∧
        (∀ f ∈ V, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ paperFT f (I / 2) = 0 ∧
          paperFT f (-(I / 2)) = 0) ∧
        ∀ f ∈ V, f ≠ 0 → (zetaZeroConfig.W f f).re < -(ε * ∫ u, ‖f u‖ ^ 2)} := by
      refine ⟨V, hVf, rfl, hV, fun f hf hf0 => ?_⟩
      have h := hneg f hf hf0
      have hF : 0 ≤ ∫ u, ‖f u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
      have := mul_le_mul_of_nonneg_right hεT hF
      linarith
    have hle := le_csSup (hbdd a ε ha hε hε1) hmem
    unfold weilNegIndex
    omega

end RHTower
