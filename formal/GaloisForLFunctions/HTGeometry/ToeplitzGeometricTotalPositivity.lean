import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityTwoTerm

/-!
# Geometric sequences are Pólya frequency sequences of every order

The sequence `ρⁿ` with `ρ ≥ 0` (coefficients of `1/(1 − ρy)`) is `PF_k` for every `k`
(`PFSeq.geometric`).  For `ρ = 0` it is the two-term sequence `(1, 0, …)`.  For `ρ > 0` expand a
Toeplitz minor along its first column.  The entries `ρ^{j₀ − i_r}` are nonzero exactly for the
initial rows with `i_r ≤ j₀`.  With no such row the column vanishes.  With two such rows, rows `0`
and `1` are proportional (`row₀ = ρ^{i₁ − i₀} row₁`), so the determinant vanishes.  With exactly one,
the minor is `ρ^{j₀ − i₀}` times the tail minor.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem zext_geometric {ρ : ℝ} (z : ℤ) :
    zext (fun n : ℕ => ρ ^ n) z = if 0 ≤ z then ρ ^ z.toNat else 0 := rfl

/-- Two proportional rows force a vanishing determinant. -/
theorem det_eq_zero_of_row_eq_smul {m : ℕ} (M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (c : ℝ)
    (h : ∀ k, M 0 k = c * M 1 k) : M.det = 0 := by
  have hrow : M = M.updateRow 0 (c • M 1) := by
    ext r k
    by_cases hr : r = 0
    · subst hr
      simp [h]
    · simp [Matrix.updateRow_ne hr]
  rw [hrow, Matrix.det_updateRow_smul]
  have : (M.updateRow 0 (M 1)).det = 0 := by
    have h01 : (0 : Fin (m + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    apply Matrix.det_zero_of_row_eq h01
    simp
  rw [this, mul_zero]

/-- All consecutive Toeplitz minors of a positive geometric sequence are nonnegative. -/
theorem seqMinor_geometric_nonneg {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ (m : ℕ) (i j : ℕ → ℕ), StrictMono i → StrictMono j →
      0 ≤ seqMinor (fun n : ℕ => ρ ^ n) m i j := by
  intro m
  induction m with
  | zero =>
    intro i j _ _
    rw [seqMinor_zero]
    exact zero_le_one
  | succ m ih =>
    intro i j hi hj
    have htail := ih (fun l => i (l + 1)) (fun l => j (l + 1)) (fun a b h => hi (by omega))
      (fun a b h => hj (by omega))
    by_cases h0 : (i 0 : ℤ) ≤ j 0
    · by_cases h1 : 1 ≤ m ∧ (i 1 : ℤ) ≤ j 0
      · -- two rows meet the first column: rows `0` and `1` are proportional
        obtain ⟨hm1, hi1⟩ := h1
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        unfold seqMinor
        rw [det_eq_zero_of_row_eq_smul _ (ρ ^ (i 1 - i 0))]
        intro k
        simp only [Matrix.of_apply, Fin.val_zero, Fin.val_one]
        have hi01 : i 0 < i 1 := hi (by norm_num)
        have hjk : j 0 ≤ j k := hj.monotone (Nat.zero_le _)
        rw [zext_geometric, zext_geometric, if_pos (by omega), if_pos (by omega), ← pow_add]
        congr 1
        omega
      · -- only row `0` meets the first column
        have hcol : ∀ r : ℕ, 1 ≤ r → r ≤ m → zext (fun n : ℕ => ρ ^ n) ((j 0 : ℤ) - i r) = 0 := by
          intro r hr hrm
          apply zext_of_neg
          have hir : i 1 ≤ i r := hi.monotone hr
          push Not at h1
          have := h1 (by omega)
          omega
        rw [seqMinor_succ_of_col _ m i j hcol, zext_geometric, if_pos (by omega)]
        exact mul_nonneg (pow_nonneg hρ.le _) htail
    · -- no row meets the first column
      push Not at h0
      have hcol : ∀ r : ℕ, 1 ≤ r → r ≤ m → zext (fun n : ℕ => ρ ^ n) ((j 0 : ℤ) - i r) = 0 := by
        intro r hr _
        apply zext_of_neg
        have : i 0 < i r := hi (by omega)
        omega
      rw [seqMinor_succ_of_col _ m i j hcol, zext_of_neg _ (by omega), zero_mul]

namespace PFSeq

/-- **Geometric sequences `ρⁿ`, `ρ ≥ 0`, are `PF_k` for every `k`.** -/
theorem geometric {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) : PFSeq k (fun n : ℕ => ρ ^ n) := by
  rcases hρ.eq_or_lt with h | h
  · subst h
    convert PFSeq.twoTerm (zero_le_one : (0 : ℝ) ≤ 1) le_rfl k using 1
    funext n
    unfold twoTermSeq
    rcases n with _ | _ | n <;> simp
  · intro m _ i j hi hj
    rw [toeplitzMinor_eq_seqMinor]
    exact seqMinor_geometric_nonneg h m _ _ (strictMono_finExtend hi) (strictMono_finExtend hj)

end PFSeq

end

end GaloisForLFunctions.HTGeometry
