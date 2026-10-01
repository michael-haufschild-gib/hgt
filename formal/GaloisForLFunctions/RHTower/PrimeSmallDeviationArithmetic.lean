import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import GaloisForLFunctions.RHTower.VonMangoldtRpowTail
import Zeta23.Chebyshev
import Zeta23.FromPNTPlus.Mertens

/-!
# Arithmetic sizes of `o(Λ)` deviations

Let `d : ℕ → ℝ` satisfy `|d(n)| ≤ η Λ(n)` for all large `n`, for every `η > 0`
(`IsLittleOVonMangoldt d`). Then, by Mertens' first theorem and the square-root Chebyshev bound:
- `Σ_{n≤N} |d(n)|/n ≤ A_η + η(log N + log 4 + 4)` (`exists_sum_abs_div_le`);
- `Σ_{n≤N} |d(n)|/√n ≤ A_η + η (2 log 4 + 16) √N` (`exists_sum_abs_div_sqrt_le`);
- `Σ_n |d(n)| n^{−σ} < ∞` for every `σ > 1` (`summable_abs_mul_rpow`);
- `Σ_{N<n≤M} |d(n)| n^{−3/2} ≤ η C_T N^{−1/2}` for large `N` (`exists_sum_Ioc_abs_rpow_le`), from
  the dyadic Chebyshev tail `Σ_{N<n≤M} Λ(n) n^{−3/2} ≤ C_T N^{−1/2}`.

These four bounds define the class `NotchSmall`. It contains every `o(Λ)` deviation and every null
sequence (`notchSmall_of_tendsto_zero`), and it is closed under sums and under domination.
-/

noncomputable section

open Finset Filter Topology ArithmeticFunction

namespace RHTower.PrimeSmallDeviation

/-- `d = o(Λ)`: for every `η > 0`, `|d(n)| ≤ η Λ(n)` for all large `n`. -/
def IsLittleOVonMangoldt (d : ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ P₀ : ℕ, ∀ n : ℕ, P₀ ≤ n → |d n| ≤ η * Λ n

theorem sum_range_vonMangoldt_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ range (N + 1), (Λ n : ℝ) / n ≤ Real.log N + (Real.log 4 + 4) := by
  have h := Mertens.sum_mangoldt_div_eq_log (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at h
  have e : ∑ n ∈ range (N + 1), (Λ n : ℝ) / n = ∑ n ∈ Ioc 0 N, (Λ n : ℝ) / n := by
    refine (Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)).symm
    · rw [Finset.mem_Ioc] at hn; exact Finset.mem_range.mpr (by omega)
    · have : n = 0 := by rw [Finset.mem_range] at hn; rw [Finset.mem_Ioc] at hn'; omega
      subst this; simp
  rw [e]
  linarith [(abs_le.mp h).2]

theorem sum_range_vonMangoldt_div_sqrt_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ range (N + 1), (Λ n : ℝ) / Real.sqrt n ≤ (2 * Real.log 4 + 16) * Real.sqrt N := by
  have h := Zeta23.Cheb.sum_vonMangoldt_div_sqrt_le (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at h
  have e : ∑ n ∈ range (N + 1), (Λ n : ℝ) / Real.sqrt n =
      ∑ n ∈ Ioc 0 N, (Λ n : ℝ) / Real.sqrt n := by
    refine (Finset.sum_subset (fun n hn => ?_) (fun n hn hn' => ?_)).symm
    · rw [Finset.mem_Ioc] at hn; exact Finset.mem_range.mpr (by omega)
    · have : n = 0 := by rw [Finset.mem_range] at hn; rw [Finset.mem_Ioc] at hn'; omega
      subst this; simp
  rw [e]; exact h

variable {d : ℕ → ℝ}

/-- A weighted sum of `|d|` against a nonnegative weight is at most a fixed head plus `η` times the
same sum of `Λ`. -/
theorem sum_abs_mul_le_head (hd : IsLittleOVonMangoldt d) {η : ℝ} (hη : 0 < η) :
    ∃ P₀ : ℕ, ∀ (w : ℕ → ℝ), (∀ n, 0 ≤ w n) → ∀ N : ℕ,
      ∑ n ∈ range (N + 1), |d n| * w n ≤
        ∑ n ∈ range P₀, |d n| * w n + η * ∑ n ∈ range (N + 1), (Λ n : ℝ) * w n := by
  obtain ⟨P₀, hP₀⟩ := hd η hη
  refine ⟨P₀, fun w hw N => ?_⟩
  have hsplit : ∑ n ∈ range (N + 1), |d n| * w n ≤
      ∑ n ∈ range P₀, |d n| * w n + ∑ n ∈ range (N + 1), (η * Λ n) * w n := by
    calc ∑ n ∈ range (N + 1), |d n| * w n
        = ∑ n ∈ range (N + 1), ((if n < P₀ then |d n| * w n else 0) +
            (if n < P₀ then 0 else |d n| * w n)) :=
          Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
      _ = ∑ n ∈ range (N + 1), (if n < P₀ then |d n| * w n else 0) +
            ∑ n ∈ range (N + 1), (if n < P₀ then 0 else |d n| * w n) := Finset.sum_add_distrib
      _ ≤ ∑ n ∈ range P₀, |d n| * w n + ∑ n ∈ range (N + 1), (η * Λ n) * w n := by
          refine add_le_add ?_ (Finset.sum_le_sum fun n _ => ?_)
          · rw [← Finset.sum_filter]
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
              (fun n _ _ => mul_nonneg (abs_nonneg _) (hw n))
            rw [Finset.mem_filter] at hn; exact Finset.mem_range.mpr hn.2
          · split_ifs with h
            · exact mul_nonneg (mul_nonneg hη.le vonMangoldt_nonneg) (hw n)
            · exact mul_le_mul_of_nonneg_right (hP₀ n (not_lt.mp h)) (hw n)
  refine hsplit.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Harmonic mass `o(log N)`.** -/
theorem exists_sum_abs_div_le (hd : IsLittleOVonMangoldt d) {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ range (N + 1), |d n| / n ≤ A + η * (Real.log N + (Real.log 4 + 4)) := by
  obtain ⟨P₀, h⟩ := sum_abs_mul_le_head hd hη
  refine ⟨∑ n ∈ range P₀, |d n| * (n : ℝ)⁻¹,
    Finset.sum_nonneg fun n _ => by positivity, fun N hN => ?_⟩
  have h1 := h (fun n => (n : ℝ)⁻¹) (fun n => by positivity) N
  have h2 := sum_range_vonMangoldt_div_le hN
  simp only [div_eq_mul_inv] at h2 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h2 hη.le]

/-- **Square-root mass `o(√N)`.** -/
theorem exists_sum_abs_div_sqrt_le (hd : IsLittleOVonMangoldt d) {η : ℝ} (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N →
      ∑ n ∈ range (N + 1), |d n| / Real.sqrt n ≤ A + η * ((2 * Real.log 4 + 16) * Real.sqrt N) := by
  obtain ⟨P₀, h⟩ := sum_abs_mul_le_head hd hη
  refine ⟨∑ n ∈ range P₀, |d n| * (Real.sqrt n)⁻¹,
    Finset.sum_nonneg fun n _ => by positivity, fun N hN => ?_⟩
  have h1 := h (fun n => (Real.sqrt n)⁻¹) (fun n => by positivity) N
  have h2 := sum_range_vonMangoldt_div_sqrt_le hN
  simp only [div_eq_mul_inv] at h2 ⊢
  nlinarith [mul_le_mul_of_nonneg_left h2 hη.le]

/-- **Absolute convergence past `σ = 1`.** -/
theorem summable_abs_mul_rpow (hd : IsLittleOVonMangoldt d) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n : ℕ => |d n| * (n : ℝ) ^ (-σ) := by
  obtain ⟨P₀, hP₀⟩ := hd 1 one_pos
  have hs := GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow hσ
  refine (summable_nat_add_iff P₀).mp (Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) ((summable_nat_add_iff P₀).mpr hs))
  have := hP₀ (n + P₀) (by omega)
  rw [one_mul] at this
  exact mul_le_mul_of_nonneg_right this (by positivity)

/-- The constant of the `Λ(n) n^{−3/2}` tail. -/
def vonMangoldtThreeHalvesTail : ℝ := RHTower.vonMangoldtRpowTailConstant (1 / 2) * Real.sqrt 2

theorem vonMangoldtThreeHalvesTail_nonneg : 0 ≤ vonMangoldtThreeHalvesTail :=
  mul_nonneg (RHTower.vonMangoldtRpowTailConstant_nonneg (by norm_num)) (Real.sqrt_nonneg _)

/-- **The `Λ(n) n^{−3/2}` tail**: `Σ_{N<n≤M} Λ(n) n^{−3/2} ≤ C_T N^{−1/2}`. -/
theorem sum_Ioc_vonMangoldt_rpow_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ n ∈ Ioc N M, (Λ n : ℝ) * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) ≤
      vonMangoldtThreeHalvesTail * (Real.sqrt N)⁻¹ := by
  set m := Nat.log 2 (N + 1) with hm
  have h2m : 2 ^ m ≤ N + 1 := Nat.pow_log_le_self 2 (by omega)
  have h2m' : N + 1 < 2 ^ (m + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hsub : Ioc N M ⊆ {n ∈ Icc 1 M | 2 ^ m ≤ n} := by
    intro n hn
    rw [mem_Ioc] at hn
    rw [mem_filter, mem_Icc]
    exact ⟨⟨by omega, hn.2⟩, by omega⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
    mul_nonneg vonMangoldt_nonneg (by positivity)).trans ?_
  refine (RHTower.sum_vonMangoldt_rpow_dyadic_tail_le (by norm_num : (0 : ℝ) < 1 / 2) m M).trans ?_
  have e : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ m = (Real.sqrt ((2 : ℝ) ^ m))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow,
      ← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; ring
  rw [e, vonMangoldtThreeHalvesTail, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (RHTower.vonMangoldtRpowTailConstant_nonneg (by norm_num))
  have hN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have h2 : (0 : ℝ) < Real.sqrt ((2 : ℝ) ^ m) := Real.sqrt_pos.mpr (by positivity)
  rw [← div_eq_mul_inv, le_div_iff₀ hN0, inv_mul_le_iff₀ h2, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have : ((N + 1 : ℕ) : ℝ) < ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast h2m'
  push_cast at this
  rw [pow_succ] at this
  linarith

/-- **The `|d(n)| n^{−3/2}` tail**: for large `N`, `Σ_{N<n≤M} |d(n)| n^{−3/2} ≤ η C_T N^{−1/2}`. -/
theorem exists_sum_Ioc_abs_rpow_le (hd : IsLittleOVonMangoldt d) {η : ℝ} (hη : 0 < η) :
    ∃ P₀ : ℕ, ∀ N : ℕ, P₀ ≤ N → 1 ≤ N → ∀ M : ℕ,
      ∑ n ∈ Ioc N M, |d n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) ≤
        η * (vonMangoldtThreeHalvesTail * (Real.sqrt N)⁻¹) := by
  obtain ⟨P₀, hP₀⟩ := hd η hη
  refine ⟨P₀, fun N hPN hN M => ?_⟩
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (sum_Ioc_vonMangoldt_rpow_le hN M) hη.le)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [mem_Ioc] at hn
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hP₀ n (by omega)) (by positivity)

/-! ## The notch-small class -/

/-- **Notch-small deviations**: the four size conditions under which the refined notch controls
every error term. -/
structure NotchSmall (d : ℕ → ℝ) : Prop where
  harm : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ range (N + 1), |d n| / n ≤ A + η * (Real.log N + (Real.log 4 + 4))
  sqrt : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ range (N + 1), |d n| / Real.sqrt n ≤ A + η * ((2 * Real.log 4 + 16) * Real.sqrt N)
  tail : ∀ η : ℝ, 0 < η → ∃ P₀ : ℕ, ∀ N : ℕ, P₀ ≤ N → 1 ≤ N → ∀ M : ℕ,
    ∑ n ∈ Ioc N M, |d n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) ≤
      η * (vonMangoldtThreeHalvesTail * (Real.sqrt N)⁻¹)
  summable : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |d n| * (n : ℝ) ^ (-σ)

theorem IsLittleOVonMangoldt.notchSmall (hd : IsLittleOVonMangoldt d) : NotchSmall d :=
  ⟨fun _ hη => exists_sum_abs_div_le hd hη, fun _ hη => exists_sum_abs_div_sqrt_le hd hη,
    fun _ hη => exists_sum_Ioc_abs_rpow_le hd hη, fun _ hσ => summable_abs_mul_rpow hd hσ⟩

/-- Domination preserves notch-smallness. -/
theorem NotchSmall.mono {d' : ℕ → ℝ} (h : NotchSmall d') (hle : ∀ n, |d n| ≤ |d' n|) :
    NotchSmall d := by
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_, fun σ hσ => ?_⟩
  · obtain ⟨A, hA, hb⟩ := h.harm η hη
    exact ⟨A, hA, fun N hN => (Finset.sum_le_sum fun n _ =>
      div_le_div_of_nonneg_right (hle n) (Nat.cast_nonneg n)).trans (hb N hN)⟩
  · obtain ⟨A, hA, hb⟩ := h.sqrt η hη
    exact ⟨A, hA, fun N hN => (Finset.sum_le_sum fun n _ =>
      div_le_div_of_nonneg_right (hle n) (Real.sqrt_nonneg _)).trans (hb N hN)⟩
  · obtain ⟨P₀, hb⟩ := h.tail η hη
    exact ⟨P₀, fun N h1 h2 M => (Finset.sum_le_sum fun n _ =>
      mul_le_mul_of_nonneg_right (hle n) (by positivity)).trans (hb N h1 h2 M)⟩
  · exact (h.summable σ hσ).of_nonneg_of_le (fun n => by positivity)
      fun n => mul_le_mul_of_nonneg_right (hle n) (by positivity)

/-- Sums of notch-small deviations are notch-small. -/
theorem NotchSmall.add {d₁ d₂ : ℕ → ℝ} (h₁ : NotchSmall d₁) (h₂ : NotchSmall d₂) :
    NotchSmall (d₁ + d₂) := by
  have hab : ∀ n, |(d₁ + d₂) n| ≤ |d₁ n| + |d₂ n| := fun n => abs_add_le _ _
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_, fun σ hσ => ?_⟩
  · obtain ⟨A₁, hA₁, hb₁⟩ := h₁.harm (η / 2) (by linarith)
    obtain ⟨A₂, hA₂, hb₂⟩ := h₂.harm (η / 2) (by linarith)
    refine ⟨A₁ + A₂, by linarith, fun N hN => ?_⟩
    have h : ∑ n ∈ range (N + 1), |(d₁ + d₂) n| / n ≤
        ∑ n ∈ range (N + 1), |d₁ n| / n + ∑ n ∈ range (N + 1), |d₂ n| / n := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun n _ => by
        rw [← add_div]; exact div_le_div_of_nonneg_right (hab n) (Nat.cast_nonneg n)
    have := hb₁ N hN; have := hb₂ N hN
    linarith
  · obtain ⟨A₁, hA₁, hb₁⟩ := h₁.sqrt (η / 2) (by linarith)
    obtain ⟨A₂, hA₂, hb₂⟩ := h₂.sqrt (η / 2) (by linarith)
    refine ⟨A₁ + A₂, by linarith, fun N hN => ?_⟩
    have h : ∑ n ∈ range (N + 1), |(d₁ + d₂) n| / Real.sqrt n ≤
        ∑ n ∈ range (N + 1), |d₁ n| / Real.sqrt n + ∑ n ∈ range (N + 1), |d₂ n| / Real.sqrt n := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun n _ => by
        rw [← add_div]; exact div_le_div_of_nonneg_right (hab n) (Real.sqrt_nonneg _)
    have := hb₁ N hN; have := hb₂ N hN
    linarith
  · obtain ⟨P₁, hb₁⟩ := h₁.tail (η / 2) (by linarith)
    obtain ⟨P₂, hb₂⟩ := h₂.tail (η / 2) (by linarith)
    refine ⟨max P₁ P₂, fun N hN hN1 M => ?_⟩
    have h : ∑ n ∈ Ioc N M, |(d₁ + d₂) n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) ≤
        ∑ n ∈ Ioc N M, |d₁ n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) +
          ∑ n ∈ Ioc N M, |d₂ n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun n _ => by
        rw [← add_mul]; exact mul_le_mul_of_nonneg_right (hab n) (by positivity)
    have := hb₁ N (le_of_max_le_left hN) hN1 M
    have := hb₂ N (le_of_max_le_right hN) hN1 M
    linarith
  · exact ((h₁.summable σ hσ).add (h₂.summable σ hσ)).of_nonneg_of_le (fun n => by positivity)
      fun n => by rw [← add_mul]; exact mul_le_mul_of_nonneg_right (hab n) (by positivity)

/-! ## Null sequences are notch-small -/

theorem sum_range_inv_le (N : ℕ) : ∑ n ∈ range (N + 1), (n : ℝ)⁻¹ ≤ 1 + Real.log N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hstep : ((N + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log ((N + 1 : ℕ) : ℝ) - Real.log N := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < N / (N + 1) by positivity)
      rw [Real.log_div hN0.ne' (by positivity)] at h
      push_cast
      have e : (N : ℝ) / (N + 1) - 1 = -(N + 1 : ℝ)⁻¹ := by field_simp; ring
      linarith
    linarith

theorem sum_range_inv_sqrt_le_two_mul_sqrt (N : ℕ) :
    ∑ n ∈ range (N + 1), (Real.sqrt n)⁻¹ ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hs : 0 < Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hle : Real.sqrt N ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
    have hstep : (Real.sqrt ((N + 1 : ℕ) : ℝ))⁻¹ ≤
        2 * (Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt N) := by
      have h1 : Real.sqrt ((N + 1 : ℕ) : ℝ) ^ 2 = (N : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have h2 : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
      rw [inv_le_iff_one_le_mul₀ hs]
      nlinarith [Real.sqrt_nonneg (N : ℝ)]
    linarith

theorem rpow_neg_one_add_half_eq_inv {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 + 1 / 2 : ℝ)) = (x * Real.sqrt x)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_add hx, Real.rpow_one, Real.sqrt_eq_rpow]

theorem sum_Ioc_rpow_three_halves_le {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ n ∈ Ioc N M, (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) ≤ 2 * (Real.sqrt N)⁻¹ := by
  have key : ∀ M, N ≤ M → ∑ n ∈ Ioc N M, (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) ≤
      2 * ((Real.sqrt N)⁻¹ - (Real.sqrt M)⁻¹) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ M hNM ih =>
      rw [Finset.sum_Ioc_succ_top hNM]
      have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
      have hs : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM0
      have hs1 : 0 < Real.sqrt ((M + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hle : Real.sqrt M ≤ Real.sqrt ((M + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by push_cast; linarith)
      have h1 : Real.sqrt ((M + 1 : ℕ) : ℝ) ^ 2 = (M : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have h2 : Real.sqrt (M : ℝ) ^ 2 = M := Real.sq_sqrt (Nat.cast_nonneg M)
      rw [rpow_neg_one_add_half_eq_inv (by positivity)]
      have hstep : (((M + 1 : ℕ) : ℝ) * Real.sqrt ((M + 1 : ℕ) : ℝ))⁻¹ ≤
          2 * ((Real.sqrt M)⁻¹ - (Real.sqrt ((M + 1 : ℕ) : ℝ))⁻¹) := by
        set a := Real.sqrt (M : ℝ) with ha
        set b := Real.sqrt ((M + 1 : ℕ) : ℝ) with hb
        have key : (b - a) * (b + a) = 1 := by nlinarith [h1, h2]
        have hnum : a ≤ 2 * (b - a) * ((M : ℝ) + 1) := by
          nlinarith [key, sq_nonneg (b - a), hs, hs1]
        have hc : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
        rw [hc, inv_sub_inv hs.ne' hs1.ne']
        have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
        calc (((M : ℝ) + 1) * b)⁻¹ = a / (a * b * ((M : ℝ) + 1)) := by
              field_simp
          _ ≤ 2 * (b - a) * ((M : ℝ) + 1) / (a * b * ((M : ℝ) + 1)) :=
              div_le_div_of_nonneg_right hnum (by positivity)
          _ = 2 * ((b - a) / (a * b)) := by
              field_simp
      linarith
  rcases le_or_gt N M with hNM | hMN
  · have := key M hNM
    have : 0 ≤ (Real.sqrt M)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    linarith
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity

theorem two_le_vonMangoldtThreeHalvesTail : 2 ≤ vonMangoldtThreeHalvesTail := by
  unfold vonMangoldtThreeHalvesTail RHTower.vonMangoldtRpowTailConstant
  have h1 : (0 : ℝ) < (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have h3 : 14 ≤ 14 / (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have h4 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  nlinarith

/-- A null sequence `e(n) → 0` is notch-small. -/
theorem notchSmall_of_tendsto_zero {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0)) : NotchSmall e := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ n, |e n| ≤ B := by
    obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto e he).subset_closedBall 0
    exact ⟨B, fun n => by
      have := hB ⟨n, rfl⟩
      simpa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using this⟩
  have hsmall : ∀ η : ℝ, 0 < η → ∃ n₁ : ℕ, ∀ n, n₁ ≤ n → |e n| ≤ η := fun η hη => by
    obtain ⟨n₁, h⟩ := Metric.tendsto_atTop.mp he η hη
    exact ⟨n₁, fun n hn => by have := h n hn; rw [Real.dist_eq, sub_zero] at this; exact this.le⟩
  have head : ∀ η : ℝ, 0 < η → ∀ (w : ℕ → ℝ), (∀ n, 0 ≤ w n) → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      ∑ n ∈ range (N + 1), |e n| * w n ≤ A + η * ∑ n ∈ range (N + 1), w n := by
    intro η hη w hw
    obtain ⟨n₁, hn₁⟩ := hsmall η hη
    refine ⟨∑ n ∈ range n₁, |e n| * w n, Finset.sum_nonneg fun n _ =>
      mul_nonneg (abs_nonneg _) (hw n), fun N => ?_⟩
    rw [Finset.mul_sum]
    calc ∑ n ∈ range (N + 1), |e n| * w n
        = ∑ n ∈ range (N + 1), ((if n < n₁ then |e n| * w n else 0) +
            (if n < n₁ then 0 else |e n| * w n)) :=
          Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
      _ = ∑ n ∈ range (N + 1), (if n < n₁ then |e n| * w n else 0) +
            ∑ n ∈ range (N + 1), (if n < n₁ then 0 else |e n| * w n) := Finset.sum_add_distrib
      _ ≤ ∑ n ∈ range n₁, |e n| * w n + ∑ n ∈ range (N + 1), η * w n := by
          refine add_le_add ?_ (Finset.sum_le_sum fun n _ => ?_)
          · rw [← Finset.sum_filter]
            refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_)
              (fun n _ _ => mul_nonneg (abs_nonneg _) (hw n))
            rw [Finset.mem_filter] at hn; exact Finset.mem_range.mpr hn.2
          · split_ifs with h
            · exact mul_nonneg hη.le (hw n)
            · exact mul_le_mul_of_nonneg_right (hn₁ n (not_lt.mp h)) (hw n)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨fun η hη => ?_, fun η hη => ?_, fun η hη => ?_, fun σ hσ => ?_⟩
  · obtain ⟨A, hA, hb⟩ := head η hη (fun n => (n : ℝ)⁻¹) fun n => by positivity
    refine ⟨A, hA, fun N hN => ?_⟩
    have h1 := hb N
    have h2 := sum_range_inv_le N
    simp only [div_eq_mul_inv] at h1 ⊢
    nlinarith [mul_le_mul_of_nonneg_left h2 hη.le]
  · obtain ⟨A, hA, hb⟩ := head η hη (fun n => (Real.sqrt n)⁻¹) fun n => by positivity
    refine ⟨A, hA, fun N hN => ?_⟩
    have h1 := hb N
    have h2 := sum_range_inv_sqrt_le_two_mul_sqrt N
    have hsq := Real.sqrt_nonneg (N : ℝ)
    simp only [div_eq_mul_inv] at h1 ⊢
    have h3 : η * (2 * Real.sqrt N) ≤ η * ((2 * Real.log 4 + 16) * Real.sqrt N) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hsq) hη.le
    linarith [mul_le_mul_of_nonneg_left h2 hη.le]
  · obtain ⟨n₁, hn₁⟩ := hsmall η hη
    refine ⟨n₁, fun N hN hN1 M => ?_⟩
    have hsum : ∑ n ∈ Ioc N M, |e n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) ≤
        η * ∑ n ∈ Ioc N M, (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [Finset.mem_Ioc] at hn
      exact mul_le_mul_of_nonneg_right (hn₁ n (by omega)) (by positivity)
    have h2 := sum_Ioc_rpow_three_halves_le hN1 M
    have h3 := two_le_vonMangoldtThreeHalvesTail
    have h4 : 0 ≤ (Real.sqrt N)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have h5 : 2 * (Real.sqrt N)⁻¹ ≤ vonMangoldtThreeHalvesTail * (Real.sqrt N)⁻¹ :=
      mul_le_mul_of_nonneg_right h3 h4
    nlinarith [mul_le_mul_of_nonneg_left (h2.trans h5) hη.le]
  · have hs := Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)
    exact (hs.mul_left B).of_nonneg_of_le (fun n => by positivity)
      fun n => mul_le_mul_of_nonneg_right (hB n) (by positivity)

/-! ## Notch-boundedness at a fixed level -/

/-- **Notch-boundedness at level `η`**: the four size bounds of `NotchSmall` at one fixed `η`. -/
structure NotchBounded (d : ℕ → ℝ) (η : ℝ) : Prop where
  harm : ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ range (N + 1), |d n| / n ≤ A + η * (Real.log N + (Real.log 4 + 4))
  sqrt : ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ range (N + 1), |d n| / Real.sqrt n ≤ A + η * ((2 * Real.log 4 + 16) * Real.sqrt N)
  tail : ∃ P₀ : ℕ, ∀ N : ℕ, P₀ ≤ N → 1 ≤ N → ∀ M : ℕ,
    ∑ n ∈ Ioc N M, |d n| * (n : ℝ) ^ (-(1 + 1 / 2 : ℝ)) ≤
      η * (vonMangoldtThreeHalvesTail * (Real.sqrt N)⁻¹)
  summable : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |d n| * (n : ℝ) ^ (-σ)

/-- A notch-small sequence is notch-bounded at every level `η > 0`. -/
theorem NotchSmall.notchBounded {d : ℕ → ℝ} (h : NotchSmall d) {η : ℝ} (hη : 0 < η) :
    NotchBounded d η :=
  ⟨h.harm η hη, h.sqrt η hη, h.tail η hη, h.summable⟩

/-- **Deviations of size `C(1 + Λ)` are notch-bounded at level `2C`.** -/
theorem notchBounded_of_abs_le {d : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, |d n| ≤ C * (1 + Λ n)) : NotchBounded d (2 * C) := by
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hpt : ∀ (w : ℕ → ℝ), (∀ n, 0 ≤ w n) → ∀ F : Finset ℕ,
      ∑ n ∈ F, |d n| * w n ≤ C * (∑ n ∈ F, w n + ∑ n ∈ F, (Λ n : ℝ) * w n) := by
    intro w hw F
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => by
      have := mul_le_mul_of_nonneg_right (hd n) (hw n)
      linarith
  refine ⟨⟨C, hC, fun N hN => ?_⟩, ⟨0, le_rfl, fun N hN => ?_⟩, ⟨0, fun N _ hN M => ?_⟩,
    fun σ hσ => ?_⟩
  · have h1 := hpt (fun n => (n : ℝ)⁻¹) (fun n => by positivity) (range (N + 1))
    have h2 := sum_range_inv_le N
    have h3 := sum_range_vonMangoldt_div_le hN
    simp only [div_eq_mul_inv] at h1 h3 ⊢
    have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add h2 h3) hC]
  · have h1 := hpt (fun n => (Real.sqrt n)⁻¹) (fun n => by positivity) (range (N + 1))
    have h2 := sum_range_inv_sqrt_le_two_mul_sqrt N
    have h3 := sum_range_vonMangoldt_div_sqrt_le hN
    simp only [div_eq_mul_inv] at h1 h3 ⊢
    have hsq := Real.sqrt_nonneg (N : ℝ)
    have h4 : 2 * Real.sqrt N ≤ (2 * Real.log 4 + 16) * Real.sqrt N :=
      mul_le_mul_of_nonneg_right (by linarith) hsq
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add (h2.trans h4) h3) hC]
  · have h1 := hpt (fun n => (n : ℝ) ^ (-(1 + 1 / 2 : ℝ))) (fun n => by positivity) (Ioc N M)
    have h2 := sum_Ioc_rpow_three_halves_le hN M
    have h3 := sum_Ioc_vonMangoldt_rpow_le hN M
    have h4 := two_le_vonMangoldtThreeHalvesTail
    have h5 : 0 ≤ (Real.sqrt N)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
    have h6 : 2 * (Real.sqrt N)⁻¹ ≤ vonMangoldtThreeHalvesTail * (Real.sqrt N)⁻¹ :=
      mul_le_mul_of_nonneg_right h4 h5
    nlinarith [mul_le_mul_of_nonneg_left (add_le_add (h2.trans h6) h3) hC]
  · have hs1 := Real.summable_nat_rpow.mpr (show -σ < -1 by linarith)
    have hs2 := GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow hσ
    refine ((hs1.add hs2).mul_left C).of_nonneg_of_le (fun n => by positivity) fun n => ?_
    have := mul_le_mul_of_nonneg_right (hd n) (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (-σ))
    linarith

end RHTower.PrimeSmallDeviation
