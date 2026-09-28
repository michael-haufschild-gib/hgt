import Mathlib

/-!
# First-order Riemann sums over a proportional tail

For `0 < θ < 1` and `φ` bounded by `M` and `L`-Lipschitz on `[θ, 1]`, the right-endpoint samples
`N⁻¹ Σ_{θN < k ≤ N} φ(k/N)` approximate `∫_θ¹ φ` within `(M + L)/N`.

With `k₀ = ⌊θN⌋` the nodes `b_i = max(θ, (k₀ + i)/N)` run from `θ` to `1`.  Every cell except the
first has length exactly `1/N` and its right endpoint is the sample point, costing at most `L/N²`;
the first cell is shorter than `1/N` and costs at most `M/N + L/N²`.
-/

open Set MeasureTheory Filter

namespace RHTower

/-- The tail sample sum `Σ_{θN < k ≤ N} φ(k/N)`. -/
noncomputable def tailSampleSum (θ : ℝ) (N : ℕ) (φ : ℝ → ℂ) : ℂ :=
  ∑ k ∈ Finset.Ioc 0 N, if θ * N < k then φ (k / N) else 0

theorem tailSampleSum_eq_sum_range {θ : ℝ} (hθ0 : 0 ≤ θ) (N : ℕ) (φ : ℝ → ℂ) :
    tailSampleSum θ N φ =
      ∑ i ∈ Finset.range (N - ⌊θ * N⌋₊), φ (((⌊θ * N⌋₊ + 1 + i : ℕ) : ℝ) / N) := by
  classical
  set k₀ := ⌊θ * N⌋₊ with hk₀
  have hθN : 0 ≤ θ * N := mul_nonneg hθ0 (Nat.cast_nonneg N)
  have hfilter : ∀ k : ℕ, (θ * N < k ↔ k₀ < k) := fun k => (Nat.floor_lt hθN).symm
  rw [tailSampleSum]
  rw [← Finset.sum_filter]
  have hset : (Finset.Ioc 0 N).filter (fun k : ℕ => θ * N < k) = Finset.Ico (k₀ + 1) (N + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico, hfilter]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range, show N + 1 - (k₀ + 1) = N - k₀ by omega]

/-- **The tail Riemann estimate.** -/
theorem norm_tailSampleSum_sub_integral_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {φ : ℝ → ℂ}
    {M L : ℝ} (hM : ∀ x ∈ Icc θ 1, ‖φ x‖ ≤ M)
    (hL : ∀ x ∈ Icc θ 1, ∀ y ∈ Icc θ 1, ‖φ x - φ y‖ ≤ L * |x - y|)
    (hint : IntervalIntegrable φ volume θ 1) {N : ℕ} (hN : 0 < N) :
    ‖(1 / (N : ℂ)) * tailSampleSum θ N φ - ∫ x in θ..1, φ x‖ ≤ (M + L) / N := by
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hLnn : 0 ≤ L := by
    have h := hL 1 ⟨hθ1.le, le_rfl⟩ θ ⟨le_rfl, hθ1.le⟩
    have hpos : 0 < |1 - θ| := abs_pos.mpr (by linarith)
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (φ 1 - φ θ)]
  have hMnn : 0 ≤ M := (norm_nonneg _).trans (hM θ ⟨le_rfl, hθ1.le⟩)
  set k₀ := ⌊θ * N⌋₊ with hk₀
  have hθN : 0 ≤ θ * N := by positivity
  have hk₀le : (k₀ : ℝ) ≤ θ * N := Nat.floor_le hθN
  have hk₀lt : θ * N < k₀ + 1 := Nat.lt_floor_add_one _
  have hk₀N : k₀ < N := by
    have : θ * N < N := by nlinarith
    exact_mod_cast (Nat.floor_lt hθN).mpr (by exact_mod_cast this)
  set n := N - k₀ with hn
  have hnN : (k₀ : ℝ) + n = N := by
    rw [hn]; push_cast [hk₀N.le]; ring
  -- the nodes
  set b : ℕ → ℝ := fun i => max θ (((k₀ : ℝ) + i) / N) with hb
  have hb0 : b 0 = θ := by
    simp only [hb, Nat.cast_zero, add_zero]
    exact max_eq_left ((div_le_iff₀ hNpos).mpr (by linarith))
  have hbn : b n = 1 := by
    simp only [hb]
    rw [hnN, div_self hNpos.ne']
    exact max_eq_right hθ1.le
  have hbsucc : ∀ i, b (i + 1) = ((k₀ : ℝ) + (i + 1)) / N := by
    intro i
    simp only [hb, Nat.cast_add, Nat.cast_one]
    refine max_eq_right ?_
    rw [le_div_iff₀ hNpos]
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  have hbmono : ∀ i, b i ≤ b (i + 1) := by
    intro i
    simp only [hb]
    refine max_le_max le_rfl ?_
    apply div_le_div_of_nonneg_right _ hNpos.le
    push_cast; linarith
  have hbmem : ∀ i ≤ n, b i ∈ Icc θ 1 := by
    intro i hi
    refine ⟨le_max_left _ _, max_le hθ1.le ?_⟩
    rw [div_le_iff₀ hNpos, one_mul]
    have : (i : ℝ) ≤ n := by exact_mod_cast hi
    linarith
  have hcell_len : ∀ i, b (i + 1) - b i ≤ 1 / N := by
    intro i
    rw [hbsucc]
    have : ((k₀ : ℝ) + i) / N ≤ b i := le_max_right _ _
    have e : ((k₀ : ℝ) + (i + 1)) / N - ((k₀ : ℝ) + i) / N = 1 / N := by field_simp; ring
    linarith
  have hcell_full : ∀ i, 1 ≤ i → b (i + 1) - b i = 1 / N := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hbsucc, hbsucc]
    push_cast
    field_simp
    ring
  -- the integral as a sum over cells
  have hint_cell : ∀ i < n, IntervalIntegrable φ volume (b i) (b (i + 1)) := by
    intro i hi
    refine hint.mono_set ?_
    rw [uIcc_of_le hθ1.le, uIcc_of_le (hbmono i)]
    exact Icc_subset_Icc (hbmem i hi.le).1 (hbmem (i + 1) hi).2
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := φ) hint_cell
  rw [hb0, hbn] at hsplit
  -- the sample sum as a sum over cells
  have hsample : (1 / (N : ℂ)) * tailSampleSum θ N φ =
      ∑ i ∈ Finset.range n, ((1 / N : ℝ) : ℂ) * φ (b (i + 1)) := by
    rw [tailSampleSum_eq_sum_range hθ0.le, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbsucc]
    push_cast
    congr 2
    ring
  rw [hsample, ← hsplit, ← Finset.sum_sub_distrib]
  -- per-cell estimate
  have hcell : ∀ i ∈ Finset.range n,
      ‖((1 / N : ℝ) : ℂ) * φ (b (i + 1)) - ∫ x in b i..b (i + 1), φ x‖ ≤
        (if i = 0 then M / N else 0) + L / N ^ 2 := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hr := hbmem (i + 1) hi'
    set ℓ := b (i + 1) - b i with hℓ
    have hℓ0 : 0 ≤ ℓ := sub_nonneg.mpr (hbmono i)
    have hsplit_cell : ((1 / N : ℝ) : ℂ) * φ (b (i + 1)) - ∫ x in b i..b (i + 1), φ x =
        ((1 / N - ℓ : ℝ) : ℂ) * φ (b (i + 1)) +
          ∫ x in b i..b (i + 1), (φ (b (i + 1)) - φ x) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint_cell i hi'),
        intervalIntegral.integral_const, hℓ]
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [hsplit_cell]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hcell_len i))]
      split_ifs with h0
      · have hM0 : ‖φ (b (i + 1))‖ ≤ M := hM _ hr
        calc (1 / N - ℓ) * ‖φ (b (i + 1))‖ ≤ (1 / N) * M :=
              mul_le_mul (by linarith) hM0 (norm_nonneg _) (by positivity)
          _ = M / N := by ring
      · rw [hcell_full i (Nat.one_le_iff_ne_zero.mpr h0), sub_self, zero_mul]
    · have hbound : ∀ x ∈ uIoc (b i) (b (i + 1)), ‖φ (b (i + 1)) - φ x‖ ≤ L * ℓ := by
        intro x hx
        rw [uIoc_of_le (hbmono i)] at hx
        have hxmem : x ∈ Icc θ 1 :=
          ⟨(hbmem i hi'.le).1.trans hx.1.le, hx.2.trans hr.2⟩
        refine (hL _ hr x hxmem).trans (mul_le_mul_of_nonneg_left ?_ hLnn)
        rw [abs_of_nonneg (by linarith [hx.2])]; linarith [hx.1]
      calc ‖∫ x in b i..b (i + 1), (φ (b (i + 1)) - φ x)‖
          ≤ L * ℓ * |b (i + 1) - b i| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
        _ = L * ℓ * ℓ := by rw [abs_of_nonneg hℓ0]
        _ ≤ L / N ^ 2 := by
            have hℓN : ℓ ≤ 1 / N := hcell_len i
            calc L * ℓ * ℓ ≤ L * (1 / N) * (1 / N) := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_left hℓN hLnn) hℓN hℓ0 (by positivity)
              _ = L / N ^ 2 := by ring
  calc ‖∑ i ∈ Finset.range n, (((1 / N : ℝ) : ℂ) * φ (b (i + 1)) - ∫ x in b i..b (i + 1), φ x)‖
      ≤ ∑ i ∈ Finset.range n, ((if i = 0 then M / N else 0) + L / N ^ 2) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hcell)
    _ = (if 0 < n then M / N else 0) + n * (L / N ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range n) 0, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        simp [Finset.mem_range]
    _ ≤ M / N + N * (L / N ^ 2) := by
        have hnN' : (n : ℝ) ≤ N := by linarith [(Nat.cast_nonneg k₀ : (0 : ℝ) ≤ k₀)]
        have h1 : (if 0 < n then M / N else 0) ≤ M / N := by
          split_ifs
          · exact le_rfl
          · exact div_nonneg hMnn hNpos.le
        have h2 : (n : ℝ) * (L / N ^ 2) ≤ N * (L / N ^ 2) :=
          mul_le_mul_of_nonneg_right hnN' (by positivity)
        linarith
    _ = (M + L) / N := by field_simp

end RHTower
