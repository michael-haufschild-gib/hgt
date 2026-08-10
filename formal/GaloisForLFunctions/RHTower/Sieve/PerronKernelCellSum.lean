import GaloisForLFunctions.RHTower.Sieve.PerronTripleCellBound
import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTail

/-!
# The Perron kernel is summable over the cells

The cell aggregate carries the kernel `1/‖σ + iy‖²` at one point of each cell.  Those weights are
summable: the cells far from the real axis are damped quadratically, so

```text
∑_{k < m} 1/‖σ + i·v_k‖²  ≤  7/σ² + 1
```

*uniformly in the number of cells*, whenever `v_k` lies in the `k`-th unit cell of a range whose
left endpoint is an integer.  Seven cells sit within distance three of the axis and pay `1/σ²`
each; the rest telescope.

This is the quantitative content of the cell decomposition.  The route it replaces bounds the
vertical integral by `sup‖f‖ · ∫ dt/‖σ+it‖ ≍ sup‖f‖ · log T`, which grows with the height.  Against
a uniform bound `V` for the long factor the aggregate is `≤ V²·x^{2σ}·(7/σ² + 1)` — the logarithm
of the height is gone.
-/

noncomputable section

namespace RHTower.Sieve

open Complex Finset

/-- The modulus squared on a vertical line. -/
theorem normSq_line_eq (σ y : ℝ) : ‖(σ : ℂ) + (y : ℝ) * I‖ ^ 2 = σ ^ 2 + y ^ 2 := by
  have hre : ((σ : ℂ) + (y : ℝ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (y : ℝ) * I).im = y := by simp
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
  ring

/-- **The Perron kernel is summable over unit cells, uniformly in their number.** -/
theorem sum_cells_inv_normSq_le {σ : ℝ} (hσ : 0 < σ) {n m : ℕ} {v : ℕ → ℝ}
    (hv : ∀ k, k < m →
      v k ∈ Set.Icc (-(n : ℝ) + (k : ℝ) * 1) (-(n : ℝ) + ((k : ℝ) + 1) * 1)) :
    ∑ k ∈ Finset.range m, 1 / ‖(σ : ℂ) + (v k : ℝ) * I‖ ^ 2 ≤ 7 / σ ^ 2 + 1 := by
  classical
  have hσ2 : (0 : ℝ) < σ ^ 2 := by positivity
  set g : ℕ → ℝ := fun k => 1 / ‖(σ : ℂ) + (v k : ℝ) * I‖ ^ 2 with hg
  have hgeq : ∀ k, g k = 1 / (σ ^ 2 + (v k) ^ 2) := by
    intro k; rw [hg]; simp only; rw [normSq_line_eq]
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    rw [hgeq]; positivity
  have hgσ : ∀ k, g k ≤ 1 / σ ^ 2 := fun k => by
    rw [hgeq]
    exact one_div_le_one_div_of_le hσ2 (by nlinarith [sq_nonneg (v k)])
  -- the far terms are dominated by the squares of their distance to the axis
  have hgfar : ∀ (k : ℕ) (d : ℕ), 0 < d → ((d : ℝ)) ^ 2 ≤ (v k) ^ 2 →
      g k ≤ 1 / ((d : ℝ)) ^ 2 := by
    intro k d hd hsq
    rw [hgeq]
    have hd0 : (0 : ℝ) < (d : ℝ) ^ 2 := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
      positivity
    exact one_div_le_one_div_of_le hd0 (by linarith)
  set P : ℕ → Prop := fun k => k + 3 < n ∨ n + 3 < k with hP
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range m) P g]
  -- the near cells
  have hnear : ∑ k ∈ (Finset.range m).filter (fun k => ¬ P k), g k ≤ 7 / σ ^ 2 := by
    have hsub : (Finset.range m).filter (fun k => ¬ P k) ⊆ Finset.Icc (n - 3) (n + 3) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have h := hk.2
      rw [hP] at h
      simp only [not_or, not_lt] at h
      rw [Finset.mem_Icc]
      omega
    have hcard : #((Finset.range m).filter (fun k => ¬ P k)) ≤ 7 := by
      refine le_trans (Finset.card_le_card hsub) ?_
      rw [Nat.card_Icc]
      omega
    have hc : (#((Finset.range m).filter (fun k => ¬ P k)) : ℝ) ≤ 7 := by exact_mod_cast hcard
    have hinv : (0 : ℝ) ≤ 1 / σ ^ 2 := by positivity
    calc ∑ k ∈ (Finset.range m).filter (fun k => ¬ P k), g k
        ≤ ∑ _k ∈ (Finset.range m).filter (fun k => ¬ P k), (1 / σ ^ 2) :=
          Finset.sum_le_sum fun k _ => hgσ k
      _ = #((Finset.range m).filter (fun k => ¬ P k)) * (1 / σ ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 7 * (1 / σ ^ 2) := by nlinarith [hc, hinv]
      _ = 7 / σ ^ 2 := by ring
  -- the far cells
  have hfar : ∑ k ∈ (Finset.range m).filter P, g k ≤ 1 := by
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range m).filter P)
      (fun k => k + 3 < n) g]
    have hleft : ∑ k ∈ ((Finset.range m).filter P).filter (fun k => k + 3 < n), g k ≤ 1 / 2 := by
      set L := ((Finset.range m).filter P).filter (fun k => k + 3 < n) with hL
      have hmemL : ∀ k ∈ L, k + 3 < n ∧ k < m := by
        intro k hk
        rw [hL, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hk
        exact ⟨hk.2, hk.1.1⟩
      have hstep : ∀ k ∈ L, g k ≤ 1 / (((n - k - 1 : ℕ) : ℝ)) ^ 2 := by
        intro k hk
        obtain ⟨hk3, hkm⟩ := hmemL k hk
        have hd3 : 3 ≤ n - k - 1 := by omega
        have hcast : ((n - k - 1 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) - 1 := by
          have h1 : n - k - 1 = n - (k + 1) := by omega
          rw [h1, Nat.cast_sub (by omega : k + 1 ≤ n)]
          push_cast
          ring
        have hvk : v k ≤ -(n : ℝ) + (k : ℝ) + 1 := by
          have := (hv k hkm).2
          simpa using (by linarith [this] : v k ≤ -(n : ℝ) + (k : ℝ) + 1)
        have hneg : v k ≤ -((n - k - 1 : ℕ) : ℝ) := by rw [hcast]; linarith
        have hd0 : (3 : ℝ) ≤ ((n - k - 1 : ℕ) : ℝ) := by exact_mod_cast hd3
        refine hgfar k (n - k - 1) (by omega) ?_
        nlinarith [hneg, hd0]
      have hinj : Set.InjOn (fun k => n - k - 1) L := by
        intro a ha b hb hab
        obtain ⟨ha3, _⟩ := hmemL a ha
        obtain ⟨hb3, _⟩ := hmemL b hb
        simp only at hab
        omega
      have himg : L.image (fun k => n - k - 1) ⊆ Finset.Icc 3 n := by
        intro d hd
        rw [Finset.mem_image] at hd
        obtain ⟨k, hk, rfl⟩ := hd
        obtain ⟨hk3, _⟩ := hmemL k hk
        rw [Finset.mem_Icc]
        omega
      calc ∑ k ∈ L, g k
          ≤ ∑ k ∈ L, 1 / (((n - k - 1 : ℕ) : ℝ)) ^ 2 := Finset.sum_le_sum hstep
        _ = ∑ d ∈ L.image (fun k => n - k - 1), 1 / ((d : ℕ) : ℝ) ^ 2 := by
            rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
        _ ≤ ∑ d ∈ Finset.Icc 3 n, 1 / ((d : ℕ) : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun d _ _ => by positivity)
        _ ≤ 1 / 2 := by
            have := sum_Icc_inv_sq_le (R := 2) (by norm_num) n
            norm_num at this ⊢
            linarith
    have hright : ∑ k ∈ ((Finset.range m).filter P).filter (fun k => ¬ (k + 3 < n)), g k
        ≤ 1 / 2 := by
      set R := ((Finset.range m).filter P).filter (fun k => ¬ (k + 3 < n)) with hR
      have hmemR : ∀ k ∈ R, n + 3 < k ∧ k < m := by
        intro k hk
        rw [hR, Finset.mem_filter, Finset.mem_filter, Finset.mem_range] at hk
        have hPk := hk.1.2
        rw [hP] at hPk
        have := hk.2
        rcases hPk with h | h
        · omega
        · exact ⟨h, hk.1.1⟩
      have hstep : ∀ k ∈ R, g k ≤ 1 / (((k - n : ℕ) : ℝ)) ^ 2 := by
        intro k hk
        obtain ⟨hk3, hkm⟩ := hmemR k hk
        have hd3 : 3 ≤ k - n := by omega
        have hcast : ((k - n : ℕ) : ℝ) = (k : ℝ) - (n : ℝ) := by
          rw [Nat.cast_sub (by omega : n ≤ k)]
        have hvk : -(n : ℝ) + (k : ℝ) ≤ v k := by
          have := (hv k hkm).1
          simpa using (by linarith [this] : -(n : ℝ) + (k : ℝ) ≤ v k)
        have hpos : ((k - n : ℕ) : ℝ) ≤ v k := by rw [hcast]; linarith
        have hd0 : (3 : ℝ) ≤ ((k - n : ℕ) : ℝ) := by exact_mod_cast hd3
        refine hgfar k (k - n) (by omega) ?_
        nlinarith [hpos, hd0]
      have hinj : Set.InjOn (fun k => k - n) R := by
        intro a ha b hb hab
        obtain ⟨ha3, _⟩ := hmemR a ha
        obtain ⟨hb3, _⟩ := hmemR b hb
        simp only at hab
        omega
      have himg : R.image (fun k => k - n) ⊆ Finset.Icc 3 m := by
        intro d hd
        rw [Finset.mem_image] at hd
        obtain ⟨k, hk, rfl⟩ := hd
        obtain ⟨hk3, hkm⟩ := hmemR k hk
        rw [Finset.mem_Icc]
        omega
      calc ∑ k ∈ R, g k
          ≤ ∑ k ∈ R, 1 / (((k - n : ℕ) : ℝ)) ^ 2 := Finset.sum_le_sum hstep
        _ = ∑ d ∈ R.image (fun k => k - n), 1 / ((d : ℕ) : ℝ) ^ 2 := by
            rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
        _ ≤ ∑ d ∈ Finset.Icc 3 m, 1 / ((d : ℕ) : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg himg (fun d _ _ => by positivity)
        _ ≤ 1 / 2 := by
            have := sum_Icc_inv_sq_le (R := 2) (by norm_num) m
            norm_num at this ⊢
            linarith
    linarith [hleft, hright]
  linarith [hnear, hfar]

end RHTower.Sieve

end
