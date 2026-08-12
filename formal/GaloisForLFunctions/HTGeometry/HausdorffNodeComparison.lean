import GaloisForLFunctions.HTGeometry.HausdorffQuadratureMeasure

/-!
# Comparing the node powers with the falling-factorial ratios

The quadrature reproduces the falling-factorial moments exactly, so its ordinary moments differ from
`b m` only through

`(k/N)^m − (k)_m/(N)_m`.

For `m ≤ k ≤ N` the ratio is the product of the fractions `(k−i)/(N−i)`, each of which lies between
`(k−m+1)/N` and `k/N`; hence the ratio is squeezed between `((k−m+1)/N)^m` and `(k/N)^m`, whose
difference is at most `m(m−1)/N`.  Below the diagonal the ratio vanishes and the node power is at
most `k/N < m/N`.  Either way the difference is at most `m²/N`.
-/

open MeasureTheory Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `a^m − b^m ≤ m (a − b)` for `0 ≤ b ≤ a ≤ 1`. -/
theorem pow_sub_pow_le_nsmul_sub {a b : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (ha : a ≤ 1) (m : ℕ) :
    a ^ m - b ^ m ≤ (m : ℝ) * (a - b) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have ha0 : 0 ≤ a := le_trans hb hba
      have hbm : 0 ≤ b ^ m := pow_nonneg hb m
      have hbm1 : b ^ m ≤ 1 := pow_le_one₀ hb (le_trans hba ha)
      have hnn : 0 ≤ a ^ m - b ^ m := by
        have := pow_le_pow_left₀ hb hba m
        linarith
      have hstep : a ^ (m + 1) - b ^ (m + 1) = a * (a ^ m - b ^ m) + (a - b) * b ^ m := by
        ring
      have h1 : a * (a ^ m - b ^ m) ≤ a ^ m - b ^ m := by nlinarith
      have h2 : (a - b) * b ^ m ≤ (a - b) * 1 :=
        mul_le_mul_of_nonneg_left hbm1 (by linarith)
      rw [hstep]
      push_cast
      linarith

/-- The real form of the falling factorial. -/
theorem cast_descFactorial_eq_prod {n m : ℕ} (h : m ≤ n) :
    ((n.descFactorial m : ℕ) : ℝ) = ∏ i ∈ range m, ((n : ℝ) - (i : ℝ)) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hin : i ≤ n := le_trans (le_of_lt (Finset.mem_range.mp hi)) h
  exact Nat.cast_sub hin

/-- The falling-factorial ratio as a product of node-like fractions. -/
theorem descFactorial_ratio_eq_prod {N m k : ℕ} (hmk : m ≤ k) (hkN : k ≤ N) :
    ((k.descFactorial m : ℕ) : ℝ) / ((N.descFactorial m : ℕ) : ℝ)
      = ∏ i ∈ range m, (((k : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ))) := by
  rw [Finset.prod_div_distrib, cast_descFactorial_eq_prod hmk,
    cast_descFactorial_eq_prod (le_trans hmk hkN)]

/-- **The uniform comparison bound.** -/
theorem abs_node_pow_sub_ratio_le {N m k : ℕ} (hm : m ≤ N) (hk : k ≤ N) (hN : 0 < N) :
    |((k : ℝ) / (N : ℝ)) ^ m - ((k.descFactorial m : ℕ) : ℝ) / ((N.descFactorial m : ℕ) : ℝ)|
      ≤ ((m : ℝ) * (m : ℝ)) / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hx0 : (0 : ℝ) ≤ (k : ℝ) / (N : ℝ) := by positivity
  have hx1 : (k : ℝ) / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNR]
    exact_mod_cast hk
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp
  rcases Nat.lt_or_ge k m with hlt | hge
  · -- below the diagonal the falling factorial vanishes
    have hzero : k.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hlt
    have hpow : ((k : ℝ) / (N : ℝ)) ^ m ≤ (k : ℝ) / (N : ℝ) := by
      calc ((k : ℝ) / (N : ℝ)) ^ m ≤ ((k : ℝ) / (N : ℝ)) ^ 1 :=
            pow_le_pow_of_le_one hx0 hx1 hmpos
        _ = (k : ℝ) / (N : ℝ) := pow_one _
    have hkm : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_of_lt hlt
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hbound : (k : ℝ) / (N : ℝ) ≤ ((m : ℝ) * (m : ℝ)) / (N : ℝ) := by
      rw [div_le_div_iff_of_pos_right hNR]
      nlinarith
    rw [hzero]
    simp only [Nat.cast_zero, zero_div, sub_zero, abs_of_nonneg (pow_nonneg hx0 m)]
    linarith
  · -- above the diagonal, squeeze the ratio between two powers
    have hmk : m ≤ k := hge
    have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
    have hkNR : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
    have hmNR : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hratio := descFactorial_ratio_eq_prod hmk hk
    set x : ℝ := (k : ℝ) / (N : ℝ) with hxdef
    set y : ℝ := ((k : ℝ) - (m : ℝ) + 1) / (N : ℝ) with hydef
    have hfac_pos : ∀ i ∈ range m, (0 : ℝ) < (N : ℝ) - (i : ℝ) := by
      intro i hi
      have : (i : ℝ) < (m : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
      linarith
    have hy0 : (0 : ℝ) ≤ y := by
      rw [hydef]
      apply div_nonneg _ hNR.le
      linarith
    have hyx : y ≤ x := by
      rw [hydef, hxdef, div_le_div_iff_of_pos_right hNR]
      linarith
    have hlow : ∀ i ∈ range m, y ≤ ((k : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ)) := by
      intro i hi
      have hiR : (i : ℝ) ≤ (m : ℝ) - 1 := by
        have hlt : (i : ℕ) < m := Finset.mem_range.mp hi
        have : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hlt
        linarith
      have hpos := hfac_pos i hi
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      rw [hydef, div_le_div_iff₀ hNR hpos]
      nlinarith
    have hhigh : ∀ i ∈ range m, ((k : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ)) ≤ x := by
      intro i hi
      have hpos := hfac_pos i hi
      have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
      rw [hxdef, div_le_div_iff₀ hpos hNR]
      nlinarith
    have hprodlow : y ^ m ≤ ∏ i ∈ range m, (((k : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ))) := by
      have := Finset.prod_le_prod (f := fun _ : ℕ => y)
        (g := fun i : ℕ => ((k : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ)))
        (s := range m) (fun i _ => hy0) hlow
      simpa [Finset.prod_const, Finset.card_range] using this
    have hnonneg : ∀ i ∈ range m, (0 : ℝ) ≤ ((k : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ)) :=
      fun i hi => le_trans hy0 (hlow i hi)
    have hprodhigh : ∏ i ∈ range m, (((k : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ))) ≤ x ^ m := by
      have := Finset.prod_le_prod (f := fun i : ℕ => ((k : ℝ) - (i : ℝ)) / ((N : ℝ) - (i : ℝ)))
        (g := fun _ : ℕ => x) (s := range m) hnonneg hhigh
      simpa [Finset.prod_const, Finset.card_range] using this
    have hgap := pow_sub_pow_le_nsmul_sub hy0 hyx hx1 m
    have hxy : x - y = ((m : ℝ) - 1) / (N : ℝ) := by
      rw [hxdef, hydef, div_sub_div_same]
      congr 1
      ring
    rw [hratio]
    rw [abs_of_nonneg (by linarith)]
    have hfinal : x ^ m - y ^ m ≤ ((m : ℝ) * (m : ℝ)) / (N : ℝ) := by
      rw [hxy] at hgap
      have hmm : (m : ℝ) * (((m : ℝ) - 1) / (N : ℝ)) ≤ ((m : ℝ) * (m : ℝ)) / (N : ℝ) := by
        rw [mul_div_assoc', div_le_div_iff_of_pos_right hNR]
        nlinarith
      linarith
    linarith

end

end GaloisForLFunctions.HTGeometry
