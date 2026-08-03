import GaloisForLFunctions.RHTower.Sieve.LogLogTelescope
import Mathlib.Data.Nat.Squarefree

/-!
# The squarefree part of the harmonic sum

Every positive integer factors as `n = m² l` with `l` squarefree, so the harmonic sum is dominated
by the product of the squarefree reciprocal sum and `∑ 1/m²`.  Since the latter is at most `2`
(by the telescoping bound `1/m² ≤ 1/(m(m-1))`), one gets

`∑_{n ≤ Y} 1/n ≤ 2 · ∑_{l ≤ Y, l squarefree} 1/l`.

This converts a lower bound for the harmonic sum into a lower bound for the squarefree reciprocal
sum, which is what the Selberg mass of an interval sieve dominates.
-/

namespace RHTower.Sieve

open Finset Nat

/-- `∑_{m ≤ Y} 1/m² ≤ 2`, by telescoping `1/m² ≤ 1/(m(m-1))`. -/
theorem sum_inv_sq_le_two (Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 Y, (1 : ℝ) / (m : ℝ) ^ 2 ≤ 2 := by
  classical
  rcases Nat.lt_or_ge Y 1 with hY | hY
  · have : Finset.Icc 1 Y = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    norm_num
  have hsplit : Finset.Icc 1 Y = insert 1 (Finset.Ico 2 (Y + 1)) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnot : (1 : ℕ) ∉ Finset.Ico 2 (Y + 1) := by simp
  rw [hsplit, Finset.sum_insert hnot]
  have htail : ∑ m ∈ Finset.Ico 2 (Y + 1), (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 := by
    have hterm : ∀ m ∈ Finset.Ico 2 (Y + 1),
        (1 : ℝ) / (m : ℝ) ^ 2 ≤ 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
      intro m hm
      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Ico.1 hm).1
      have hpos : (0 : ℝ) < (m : ℝ) * ((m : ℝ) - 1) := by nlinarith
      have hsq : (0 : ℝ) < (m : ℝ) ^ 2 := by nlinarith
      rw [div_le_div_iff₀ hsq hpos]
      nlinarith
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hcong : ∀ m ∈ Finset.Ico 2 (Y + 1),
        (fun k : ℕ => -(1 / ((k : ℝ) - 1))) (m + 1) - (fun k : ℕ => -(1 / ((k : ℝ) - 1))) m
          = 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
      intro m hm
      have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Ico.1 hm).1
      have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have h0 : (m : ℝ) ≠ 0 := by intro h; rw [h] at hmR; linarith
      have h1 : (m : ℝ) - 1 ≠ 0 := by intro h; linarith [h]
      have hkey : -(1 / ((m : ℝ))) - (-(1 / ((m : ℝ) - 1)))
          = 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
        field_simp
        ring
      simp only [hc, add_sub_cancel_right]
      exact hkey
    have hz1 : 2 ≤ Y + 1 := by omega
    have htel := sum_Ico_telescope (fun k : ℕ => -(1 / ((k : ℝ) - 1))) hz1
    rw [Finset.sum_congr rfl hcong] at htel
    rw [htel]
    have hc2 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
    have hcY : ((Y + 1 : ℕ) : ℝ) - 1 = (Y : ℝ) := by push_cast; ring
    rw [hc2, hcY, div_one]
    have hYR : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    have hinvpos : (0 : ℝ) < 1 / (Y : ℝ) := by positivity
    linarith
  have hone : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
  rw [hone]
  linarith [htail]

/-- A choice of squarefree factorisation `n = m² l`. -/
noncomputable def sqfreeSplit (n : ℕ) : ℕ × ℕ :=
  if h : 0 < n then
    ((Nat.sq_mul_squarefree_of_pos h).choose,
      (Nat.sq_mul_squarefree_of_pos h).choose_spec.choose)
  else (1, 1)

theorem sqfreeSplit_spec {n : ℕ} (hn : 0 < n) :
    0 < (sqfreeSplit n).1 ∧ 0 < (sqfreeSplit n).2
      ∧ (sqfreeSplit n).2 ^ 2 * (sqfreeSplit n).1 = n ∧ Squarefree (sqfreeSplit n).1 := by
  unfold sqfreeSplit
  rw [dif_pos hn]
  exact (Nat.sq_mul_squarefree_of_pos hn).choose_spec.choose_spec

/-- **Squarefree domination of the harmonic sum.** -/
theorem sum_inv_le_two_mul_sum_inv_squarefree (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, (1 : ℝ) / n
      ≤ 2 * ∑ l ∈ {l ∈ Finset.Icc 1 Y | Squarefree l}, (1 : ℝ) / l := by
  classical
  set A : Finset ℕ := {l ∈ Finset.Icc 1 Y | Squarefree l} with hA
  set B : Finset ℕ := Finset.Icc 1 Y with hB
  have hmaps : ∀ n ∈ Finset.Icc 1 Y, sqfreeSplit n ∈ A ×ˢ B := by
    intro n hn
    obtain ⟨hn1, hnY⟩ := Finset.mem_Icc.1 hn
    obtain ⟨ha, hb, hab, hsq⟩ := sqfreeSplit_spec (by omega : 0 < n)
    have hale : (sqfreeSplit n).1 ≤ n := by
      calc (sqfreeSplit n).1 ≤ (sqfreeSplit n).2 ^ 2 * (sqfreeSplit n).1 := by
            refine Nat.le_mul_of_pos_left _ ?_
            positivity
        _ = n := hab
    have hble : (sqfreeSplit n).2 ≤ n := by
      calc (sqfreeSplit n).2 ≤ (sqfreeSplit n).2 ^ 2 := by nlinarith
        _ ≤ (sqfreeSplit n).2 ^ 2 * (sqfreeSplit n).1 := by
            refine Nat.le_mul_of_pos_right _ ha
        _ = n := hab
    exact Finset.mem_product.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨ha, le_trans hale hnY⟩, hsq⟩,
        Finset.mem_Icc.2 ⟨hb, le_trans hble hnY⟩⟩
  have hinj : ∀ x ∈ Finset.Icc 1 Y, ∀ y ∈ Finset.Icc 1 Y,
      sqfreeSplit x = sqfreeSplit y → x = y := by
    intro x hx y hy hxy
    obtain ⟨hx1, -⟩ := Finset.mem_Icc.1 hx
    obtain ⟨hy1, -⟩ := Finset.mem_Icc.1 hy
    obtain ⟨-, -, hx3, -⟩ := sqfreeSplit_spec (by omega : 0 < x)
    obtain ⟨-, -, hy3, -⟩ := sqfreeSplit_spec (by omega : 0 < y)
    rw [hxy] at hx3
    exact hx3.symm.trans hy3
  have hval : ∀ n ∈ Finset.Icc 1 Y,
      (1 : ℝ) / n = (1 : ℝ) / (sqfreeSplit n).1 * ((1 : ℝ) / ((sqfreeSplit n).2 : ℝ) ^ 2) := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Icc.1 hn
    obtain ⟨ha, hb, hab, -⟩ := sqfreeSplit_spec (by omega : 0 < n)
    have hcast : (n : ℝ) = ((sqfreeSplit n).2 : ℝ) ^ 2 * ((sqfreeSplit n).1 : ℝ) := by
      have hc := congrArg (fun k : ℕ => (k : ℝ)) hab
      push_cast at hc
      exact hc.symm
    have haR : (0 : ℝ) < ((sqfreeSplit n).1 : ℝ) := by exact_mod_cast ha
    have hbR : (0 : ℝ) < ((sqfreeSplit n).2 : ℝ) := by exact_mod_cast hb
    rw [hcast]
    field_simp
  rw [Finset.sum_congr rfl hval]
  have hstep : ∑ n ∈ Finset.Icc 1 Y,
      (1 : ℝ) / (sqfreeSplit n).1 * ((1 : ℝ) / ((sqfreeSplit n).2 : ℝ) ^ 2)
      ≤ ∑ x ∈ A ×ˢ B, (1 : ℝ) / (x.1 : ℝ) * ((1 : ℝ) / (x.2 : ℝ) ^ 2) := by
    rw [← Finset.sum_image (f := fun x : ℕ × ℕ =>
      (1 : ℝ) / (x.1 : ℝ) * ((1 : ℝ) / (x.2 : ℝ) ^ 2)) hinj]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
      exact hmaps n hn
    · intro x _ _
      positivity
  refine le_trans hstep ?_
  rw [Finset.sum_product]
  have hfactor : ∑ l ∈ A, ∑ m ∈ B,
      (1 : ℝ) / (l : ℝ) * ((1 : ℝ) / (m : ℝ) ^ 2)
      = (∑ l ∈ A, (1 : ℝ) / l) * ∑ m ∈ B, (1 : ℝ) / (m : ℝ) ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => (Finset.mul_sum _ _ _).symm
  rw [hfactor]
  have hsq := sum_inv_sq_le_two Y
  have hApos : (0 : ℝ) ≤ ∑ l ∈ A, (1 : ℝ) / l :=
    Finset.sum_nonneg fun l _ => by positivity
  nlinarith [hsq, hApos]

end RHTower.Sieve
