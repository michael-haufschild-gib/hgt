import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.ShiftedProductRigidity
import GaloisForLFunctions.HTGeometry.LogFrequencySeparation

/-!
# Logarithmic collision cells

Two translated product readings determine an unordered pair even at finite
resolution. In `[1,N]`, a cell of radius `ε` contains at most two ordered
pairs when `2ε(N+1)² < |t|`. The cell is in the real logarithmic lift,
not on the circle: distinct winding numbers are not identified.
-/

noncomputable section

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

open Finset

/-- Simultaneous real cells for the unshifted and shifted logarithmic products. -/
def InLogPairCell (t ε u v : ℝ) (a b : ℕ) : Prop :=
  |t * Real.log (a * b : ℕ) - u| ≤ ε ∧
    |t * Real.log ((a + 1) * (b + 1) : ℕ) - v| ≤ ε

private theorem eq_of_common_log_cell {a b M : ℕ} {t ε u : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haM : a ≤ M) (hbM : b ≤ M)
    (hres : 2 * ε * M < |t|)
    (hau : |t * Real.log a - u| ≤ ε) (hbu : |t * Real.log b - u| ≤ ε) :
    a = b := by
  by_contra hab
  have hM : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le ha haM
  have hgap := HTGeometry.inv_le_abs_log_sub_log_of_le ha hb hab haM hbM
  have hsep : |t| / M ≤ |t * Real.log a - t * Real.log b| := by
    rw [← mul_sub, abs_mul, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hgap (abs_nonneg t)
  have hclose : |t * Real.log a - t * Real.log b| ≤ 2 * ε := by
    calc
      _ = |(t * Real.log a - u) - (t * Real.log b - u)| := by congr 1; ring
      _ ≤ |t * Real.log a - u| + |t * Real.log b - u| := abs_sub _ _
      _ ≤ 2 * ε := by linarith only [hau, hbu]
  have h := (div_le_iff₀ hM).mp (hsep.trans hclose)
  linarith only [h, hres]

/-- Real product cells below the integer gap contain only permutations. -/
theorem pair_eq_or_swap_of_common_cell {a b c d N : ℕ} {t ε u v : ℝ}
    (ha : a ∈ Icc 1 N) (hb : b ∈ Icc 1 N)
    (hc : c ∈ Icc 1 N) (hd : d ∈ Icc 1 N)
    (hres : 2 * ε * ((N + 1 : ℕ) : ℝ) ^ 2 < |t|)
    (hab : InLogPairCell t ε u v a b) (hcd : InLogPairCell t ε u v c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  obtain ⟨ha0, haN⟩ := mem_Icc.mp ha
  obtain ⟨hb0, hbN⟩ := mem_Icc.mp hb
  obtain ⟨hc0, hcN⟩ := mem_Icc.mp hc
  obtain ⟨hd0, hdN⟩ := mem_Icc.mp hd
  have hres' : 2 * ε * (((N + 1) ^ 2 : ℕ) : ℝ) < |t| := by
    exact_mod_cast hres
  have hprod : ∀ x y : ℕ, x ≤ N + 1 → y ≤ N + 1 → x * y ≤ (N + 1) ^ 2 := by
    intro x y hx hy
    simpa only [pow_two] using Nat.mul_le_mul hx hy
  apply (pairSignature_eq_iff a b c d).mp
  apply Prod.ext
  · exact eq_of_common_log_cell (Nat.mul_pos ha0 hb0) (Nat.mul_pos hc0 hd0)
      (hprod a b (by omega) (by omega)) (hprod c d (by omega) (by omega))
      hres' hab.1 hcd.1
  · exact eq_of_common_log_cell
      (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))
      (Nat.mul_pos (Nat.succ_pos c) (Nat.succ_pos d))
      (hprod (a + 1) (b + 1) (by omega) (by omega))
      (hprod (c + 1) (d + 1) (by omega) (by omega)) hres' hab.2 hcd.2

/-- Actual pairs in the interval whose two lifted readings lie in the given cell. -/
def logPairCell (N : ℕ) (t ε u v : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Icc 1 N) ×ˢ (Icc 1 N)).filter fun p => InLogPairCell t ε u v p.1 p.2

/-- A finite-resolution mixed collision bound, uniform in both cell centres. -/
theorem card_logPairCell_le_two (N : ℕ) (t ε u v : ℝ)
    (hres : 2 * ε * ((N + 1 : ℕ) : ℝ) ^ 2 < |t|) :
    (logPairCell N t ε u v).card ≤ 2 := by
  classical
  by_cases he : (logPairCell N t ε u v).Nonempty
  · obtain ⟨⟨a, b⟩, hab⟩ := he
    obtain ⟨habN, habcell⟩ := mem_filter.mp hab
    obtain ⟨ha, hb⟩ := mem_product.mp habN
    have hsub : logPairCell N t ε u v ⊆ {(a, b), (b, a)} := by
      rintro ⟨c, d⟩ hcd
      obtain ⟨hcdN, hcdcell⟩ := mem_filter.mp hcd
      obtain ⟨hc, hd⟩ := mem_product.mp hcdN
      have h := pair_eq_or_swap_of_common_cell hc hd ha hb hres hcdcell habcell
      simpa only [mem_insert, mem_singleton, Prod.mk.injEq] using h
    refine (card_le_card hsub).trans ?_
    by_cases heq : (a, b) = (b, a)
    · simp [heq]
    · rw [card_pair heq]
  · simp only [not_nonempty_iff_eq_empty.mp he, card_empty, Nat.zero_le]

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
