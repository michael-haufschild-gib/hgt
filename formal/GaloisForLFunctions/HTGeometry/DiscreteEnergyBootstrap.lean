import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# An abstract discrete Liouville--Green bootstrap

A normalized energy `F` whose increment is, up to a controlled remainder, the drift `Dr` times an
exact discrete derivative `ΔP`, and whose primitive `P` is dominated by `F`, stays within a factor
two of its initial size as soon as the drift is small and the total control is summable with small
sum.  One discrete Abel summation converts the non-summable `ΔP` term into a boundary term plus a
summable one, and a Gronwall bootstrap finishes.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- **Discrete Abel summation.** -/
theorem abel_sum_Ico (D P : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, D (k + 1) * (P (k + 1) - P k)
      = D b * P b - D a * P a - ∑ k ∈ Finset.Ico a b, (D (k + 1) - D k) * P k := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      rw [Finset.sum_Ico_succ_top hb, Finset.sum_Ico_succ_top hb, ih]
      ring

/-- Telescoping over an `Ico` range. -/
theorem telescope_Ico (g : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Finset.Ico a b, (g (k + 1) - g k) = g b - g a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      rw [Finset.sum_Ico_succ_top hb, ih]
      ring

variable {F P Dr ctrl : ℕ → ℝ}

/-- **The abstract window estimate.** -/
theorem abstract_window_estimate {N₀ K : ℕ} (hK : N₀ ≤ K)
    (hPF : ∀ n, N₀ ≤ n → |P n| ≤ 4 * F n)
    (hstep : ∀ k, N₀ ≤ k →
      |F (k + 2) - F (k + 1) - Dr (k + 1) * (P (k + 1) - P k) / 2|
        ≤ ctrl k * (F k + F (k + 1)))
    (hctrl0 : ∀ k, N₀ ≤ k → 0 ≤ ctrl k)
    {S : ℝ} (hS : ∀ m, N₀ ≤ m → m ≤ K → F m ≤ S) (hS0 : 0 ≤ S)
    (hbdry : ∀ n, N₀ ≤ n → 2 * |Dr n| ≤ 1 / 8)
    (hsum : ∑ k ∈ Finset.Ico N₀ K, (2 * |Dr (k + 1) - Dr k| + 2 * ctrl k) ≤ 1 / 8) :
    |F (K + 1) - F (N₀ + 1)| ≤ 3 / 8 * S := by
  have hPb : ∀ m, N₀ ≤ m → m ≤ K → |P m| ≤ 4 * S := by
    intro m hm hmK
    have h1 := hPF m hm
    have h2 := hS m hm hmK
    linarith
  have htel : F (K + 1) - F (N₀ + 1)
      = ∑ k ∈ Finset.Ico N₀ K, (F (k + 2) - F (k + 1)) := by
    have := telescope_Ico (fun m => F (m + 1)) hK
    simpa using this.symm
  have hsplit : ∀ k, F (k + 2) - F (k + 1)
      = Dr (k + 1) * (P (k + 1) - P k) / 2
        + (F (k + 2) - F (k + 1) - Dr (k + 1) * (P (k + 1) - P k) / 2) := by
    intro k; ring
  have hA : F (K + 1) - F (N₀ + 1)
      = (Dr K * P K - Dr N₀ * P N₀
          - ∑ k ∈ Finset.Ico N₀ K, (Dr (k + 1) - Dr k) * P k) / 2
        + ∑ k ∈ Finset.Ico N₀ K,
            (F (k + 2) - F (k + 1) - Dr (k + 1) * (P (k + 1) - P k) / 2) := by
    have hdiv : ∑ k ∈ Finset.Ico N₀ K, Dr (k + 1) * (P (k + 1) - P k) / 2
        = (∑ k ∈ Finset.Ico N₀ K, Dr (k + 1) * (P (k + 1) - P k)) / 2 := by
      rw [eq_div_iff (by norm_num : (2:ℝ) ≠ 0), Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [htel, Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib, hdiv,
      abel_sum_Ico Dr P hK]
  have hT : |∑ k ∈ Finset.Ico N₀ K, (Dr (k + 1) - Dr k) * P k| / 2
      ≤ ∑ k ∈ Finset.Ico N₀ K, 2 * |Dr (k + 1) - Dr k| * S := by
    have hb1 : |∑ k ∈ Finset.Ico N₀ K, (Dr (k + 1) - Dr k) * P k|
        ≤ ∑ k ∈ Finset.Ico N₀ K, 4 * |Dr (k + 1) - Dr k| * S := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [abs_mul]
      calc |Dr (k + 1) - Dr k| * |P k|
          ≤ |Dr (k + 1) - Dr k| * (4 * S) :=
            mul_le_mul_of_nonneg_left (hPb k hk.1 (le_of_lt hk.2)) (abs_nonneg _)
        _ = 4 * |Dr (k + 1) - Dr k| * S := by ring
    have hb2 : ∑ k ∈ Finset.Ico N₀ K, 4 * |Dr (k + 1) - Dr k| * S
        = 2 * ∑ k ∈ Finset.Ico N₀ K, 2 * |Dr (k + 1) - Dr k| * S := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hb2] at hb1
    linarith
  have hU : |∑ k ∈ Finset.Ico N₀ K,
        (F (k + 2) - F (k + 1) - Dr (k + 1) * (P (k + 1) - P k) / 2)|
      ≤ ∑ k ∈ Finset.Ico N₀ K, 2 * ctrl k * S := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : N₀ ≤ k + 1 := le_trans hk.1 (Nat.le_succ k)
    refine (hstep k hk.1).trans ?_
    have hsum2 : F k + F (k + 1) ≤ 2 * S := by
      have h1 := hS k hk.1 (le_of_lt hk.2)
      have h2 := hS _ hk1 hk.2
      linarith
    calc ctrl k * (F k + F (k + 1)) ≤ ctrl k * (2 * S) :=
          mul_le_mul_of_nonneg_left hsum2 (hctrl0 k hk.1)
      _ = 2 * ctrl k * S := by ring
  have hBK : |Dr K * P K| / 2 ≤ 1 / 8 * S := by
    rw [abs_mul]
    have h1 : |Dr K| * |P K| ≤ |Dr K| * (4 * S) :=
      mul_le_mul_of_nonneg_left (hPb K hK le_rfl) (abs_nonneg _)
    have h2 := hbdry K hK
    nlinarith [abs_nonneg (Dr K)]
  have hB0 : |Dr N₀ * P N₀| / 2 ≤ 1 / 8 * S := by
    rw [abs_mul]
    have h1 : |Dr N₀| * |P N₀| ≤ |Dr N₀| * (4 * S) :=
      mul_le_mul_of_nonneg_left (hPb N₀ le_rfl hK) (abs_nonneg _)
    have h2 := hbdry N₀ le_rfl
    nlinarith [abs_nonneg (Dr N₀)]
  have hcomb : (∑ k ∈ Finset.Ico N₀ K, 2 * |Dr (k + 1) - Dr k| * S)
      + (∑ k ∈ Finset.Ico N₀ K, 2 * ctrl k * S) ≤ 1 / 8 * S := by
    rw [← Finset.sum_add_distrib]
    have hrw : ∀ k ∈ Finset.Ico N₀ K,
        2 * |Dr (k + 1) - Dr k| * S + 2 * ctrl k * S
          = (2 * |Dr (k + 1) - Dr k| + 2 * ctrl k) * S := fun k _ => by ring
    rw [Finset.sum_congr rfl hrw, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsum hS0
  rw [hA]
  have hfinal := abs_add_le
      ((Dr K * P K - Dr N₀ * P N₀
          - ∑ k ∈ Finset.Ico N₀ K, (Dr (k + 1) - Dr k) * P k) / 2)
      (∑ k ∈ Finset.Ico N₀ K,
          (F (k + 2) - F (k + 1) - Dr (k + 1) * (P (k + 1) - P k) / 2))
  have hnum : |(Dr K * P K - Dr N₀ * P N₀
          - ∑ k ∈ Finset.Ico N₀ K, (Dr (k + 1) - Dr k) * P k) / 2|
      ≤ |Dr K * P K| / 2 + |Dr N₀ * P N₀| / 2
        + |∑ k ∈ Finset.Ico N₀ K, (Dr (k + 1) - Dr k) * P k| / 2 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hs : |Dr K * P K - Dr N₀ * P N₀
          - ∑ k ∈ Finset.Ico N₀ K, (Dr (k + 1) - Dr k) * P k|
        ≤ |Dr K * P K| + |Dr N₀ * P N₀|
          + |∑ k ∈ Finset.Ico N₀ K, (Dr (k + 1) - Dr k) * P k| := by
      have h1 := abs_sub (Dr K * P K - Dr N₀ * P N₀)
        (∑ k ∈ Finset.Ico N₀ K, (Dr (k + 1) - Dr k) * P k)
      have h2 := abs_sub (Dr K * P K) (Dr N₀ * P N₀)
      linarith
    linarith
  linarith

/-- **The abstract bootstrap.** -/
theorem abstract_energy_bootstrap {N₀ : ℕ}
    (hF0 : ∀ n, N₀ ≤ n → 0 ≤ F n)
    (hPF : ∀ n, N₀ ≤ n → |P n| ≤ 4 * F n)
    (hstep : ∀ k, N₀ ≤ k →
      |F (k + 2) - F (k + 1) - Dr (k + 1) * (P (k + 1) - P k) / 2|
        ≤ ctrl k * (F k + F (k + 1)))
    (hctrl0 : ∀ k, N₀ ≤ k → 0 ≤ ctrl k)
    (hbdry : ∀ n, N₀ ≤ n → 2 * |Dr n| ≤ 1 / 8)
    (hsum : ∀ K, ∑ k ∈ Finset.Ico N₀ K, (2 * |Dr (k + 1) - Dr k| + 2 * ctrl k) ≤ 1 / 8)
    {m : ℕ} (hm : N₀ ≤ m) :
    F m ≤ 2 * max (F N₀) (F (N₀ + 1)) := by
  set C : ℝ := max (F N₀) (F (N₀ + 1)) with hC
  have hC0 : 0 ≤ C := le_trans (hF0 N₀ le_rfl) (le_max_left _ _)
  have hCa : F N₀ ≤ C := le_max_left _ _
  have hCb : F (N₀ + 1) ≤ C := le_max_right _ _
  have main : ∀ K, N₀ ≤ K → ∀ j, N₀ ≤ j → j ≤ K → F j ≤ 2 * C := by
    intro K hKle
    induction K, hKle using Nat.le_induction with
    | base =>
        intro j hj1 hj2
        have : j = N₀ := le_antisymm hj2 hj1
        subst this
        linarith
    | succ K hK ih =>
        intro j hj1 hj2
        rcases Nat.lt_or_ge j (K + 1) with hlt | hge
        · exact ih j hj1 (Nat.lt_succ_iff.mp hlt)
        · have hjeq : j = K + 1 := le_antisymm hj2 hge
          subst hjeq
          have hwin := abstract_window_estimate hK hPF hstep hctrl0
            (S := 2 * C) ih (by linarith) hbdry (hsum K)
          have := (abs_le.mp hwin).2
          linarith
  exact main m hm m hm le_rfl

end GaloisForLFunctions.HTGeometry
