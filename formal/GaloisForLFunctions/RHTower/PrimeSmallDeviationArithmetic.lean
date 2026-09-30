import GaloisForLFunctions.HTGeometry.RealDirichletSeries
import Zeta23.Chebyshev
import Zeta23.FromPNTPlus.Mertens

/-!
# Arithmetic sizes of `o(Λ)` deviations

Let `d : ℕ → ℝ` satisfy `|d(n)| ≤ η Λ(n)` for all large `n`, for every `η > 0`
(`IsLittleOVonMangoldt d`). Then, by Mertens' first theorem and the square-root Chebyshev bound:
- `Σ_{n≤N} |d(n)|/n ≤ A_η + η(log N + log 4 + 4)` (`exists_sum_abs_div_le`);
- `Σ_{n≤N} |d(n)|/√n ≤ A_η + η (2 log 4 + 16) √N` (`exists_sum_abs_div_sqrt_le`);
- `Σ_n |d(n)| n^{−σ} < ∞` for every `σ > 1` (`summable_abs_mul_rpow`).
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

end RHTower.PrimeSmallDeviation
