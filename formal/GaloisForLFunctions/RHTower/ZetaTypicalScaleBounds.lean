import GaloisForLFunctions.RHTower.ZetaTypicalHeightSup
import GaloisForLFunctions.RHTower.ZetaDisplacedLittlewoodFloor
import GaloisForLFunctions.RHTower.ZetaCriticalScaleTailMoment
import GaloisForLFunctions.RHTower.OuterLawMollifiedProductEquivalence

/-!
# Typical bounds for `ζ` at a scale `R` near the critical line

Three density statements at a scale `0 < R ≤ 1/8`, for heights `t ∈ [T, 2T]`:

* **large values** (`volume_zetaLargeNearScale_le`): the heights near which some `z` with
  `½ ≤ Re z ≤ ½ + 4R`, `|Im z − t| ≤ 4R` has `|ζ(z)| > V (4T)^{cR} (1 + log 4T)²` have measure
  `O(T/(c²V²))`. Area mean value on discs of radius `cR`, cells of length `R` with eleven-fold
  overlap, the column bound of `ZetaTypicalHeightSup` (reflection left of the line);
* **small values** (`volume_logZeta_lt_neg_le`): on a vertical line `Re s = x ∈ [½, 1]`, the
  heights with `log|ζ(x + it)| < −W` have measure `O(T log log T / W)`: the positive part of
  `log|ζ|` by the tangent-line (Jensen) bound against the mean square, the signed integral by the
  displaced Littlewood floor;
* **zero shadows** (`volume_zetaZeroShadowScaled_le`): heights within `κ (Re ρ − ½)` of a zero `ρ`
  with `Re ρ ≥ ½ + a` have measure `O(κ T/(a log T))`, by the critical-scale tail moment.
-/

noncomputable section

open Complex Set MeasureTheory Filter

namespace RHTower

/-! ## Cells of length `h` -/

/-- **Cell Markov at length `h`.** -/
theorem volume_setOf_le_of_cells_scaled {P : ℝ → Prop} {Φ : ℕ → ℝ} {A T h : ℝ} (hA : 0 < A)
    (hh : 0 < h) (hΦ : ∀ k, 0 ≤ Φ k)
    (hbad : ∀ t ∈ Icc T (2 * T), P t → ∀ k : ℕ, T + k * h ≤ t → t ≤ T + (k + 1) * h → A ≤ Φ k) :
    volume {t | t ∈ Icc T (2 * T) ∧ P t} ≤
      ENNReal.ofReal (h * (∑ k ∈ Finset.range (⌈T / h⌉₊ + 1), Φ k) / A) := by
  set m := ⌈T / h⌉₊ + 1 with hm
  set Bk := (Finset.range m).filter (fun k => A ≤ Φ k) with hBk
  have hsub : {t | t ∈ Icc T (2 * T) ∧ P t} ⊆ ⋃ k ∈ Bk, Icc (T + k * h) (T + (k + 1) * h) := by
    rintro t ⟨ht, hP⟩
    have h0 : 0 ≤ (t - T) / h := div_nonneg (by linarith [ht.1]) hh.le
    set k := ⌊(t - T) / h⌋₊ with hk
    have hk1 : (k : ℝ) ≤ (t - T) / h := Nat.floor_le h0
    have hk2 : (t - T) / h < k + 1 := Nat.lt_floor_add_one _
    rw [le_div_iff₀ hh] at hk1
    rw [div_lt_iff₀ hh] at hk2
    have hkm : k < m := by
      have h3 : (t - T) / h ≤ T / h := div_le_div_of_nonneg_right (by linarith [ht.2]) hh.le
      have : (k : ℝ) < (⌈T / h⌉₊ : ℝ) + 1 := by
        have := Nat.le_ceil (T / h)
        have h4 : (k : ℝ) ≤ (t - T) / h := Nat.floor_le h0
        linarith
      rw [hm]; exact_mod_cast this
    refine mem_iUnion₂.mpr ⟨k, ?_, ⟨by linarith, by linarith⟩⟩
    rw [hBk, Finset.mem_filter]
    exact ⟨Finset.mem_range.mpr hkm, hbad t ht hP k (by linarith) (by linarith)⟩
  have hcard : (Bk.card : ℝ) * A ≤ ∑ k ∈ Finset.range m, Φ k := by
    calc (Bk.card : ℝ) * A = ∑ _k ∈ Bk, A := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ Bk, Φ k := Finset.sum_le_sum fun k hk => (Finset.mem_filter.mp hk).2
      _ ≤ ∑ k ∈ Finset.range m, Φ k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => hΦ k
  calc volume {t | t ∈ Icc T (2 * T) ∧ P t}
      ≤ volume (⋃ k ∈ Bk, Icc (T + k * h) (T + (k + 1) * h)) := measure_mono hsub
    _ ≤ ∑ k ∈ Bk, volume (Icc (T + k * h) (T + (k + 1) * h)) := measure_biUnion_finset_le _ _
    _ = ∑ _k ∈ Bk, ENNReal.ofReal h := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Real.volume_Icc]; congr 1; ring
    _ = ENNReal.ofReal (Bk.card * h) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (h * (∑ k ∈ Finset.range m, Φ k) / A) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc, mul_comm (Bk.card : ℝ) h]
        exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hA).mpr hcard) hh.le

/-- **Sliding windows of length `(a + b) h`.** The windows `[s + (k − a)h, s + (k + b)h]`,
`k < m`, cover every point at most `a + b` times. -/
theorem sum_integral_sliding_scaled_le {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ y, 0 ≤ g y)
    (s h : ℝ) (hh : 0 ≤ h) (a b m : ℕ) :
    ∑ k ∈ Finset.range m, ∫ y in (s + ((k : ℝ) - a) * h)..(s + ((k : ℝ) + b) * h), g y ≤
      (a + b) * ∫ y in (s - a * h)..(s + ((m : ℝ) + b) * h), g y := by
  have hsplit : ∀ k : ℕ, ∫ y in (s + ((k : ℝ) - a) * h)..(s + ((k : ℝ) + b) * h), g y =
      ∑ j ∈ Finset.range (a + b),
        ∫ y in (s + ((j : ℝ) - a) * h + k * h)..(s + ((j : ℝ) - a) * h + k * h + h), g y := by
    intro k
    have hs := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun j : ℕ => s + ((j : ℝ) - a) * h + k * h) (n := a + b)
      (fun j _ => hg.intervalIntegrable _ _)
    simp only [CharP.cast_eq_zero, zero_sub] at hs
    rw [show s + ((k : ℝ) - a) * h = s + -(a : ℝ) * h + k * h by ring,
      show s + ((k : ℝ) + b) * h = s + (((a + b : ℕ) : ℝ) - a) * h + k * h by push_cast; ring, ← hs]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast; ring
  have hrow : ∀ j : ℕ, ∑ k ∈ Finset.range m,
      ∫ y in (s + ((j : ℝ) - a) * h + k * h)..(s + ((j : ℝ) - a) * h + k * h + h), g y =
      ∫ y in (s + ((j : ℝ) - a) * h)..(s + ((j : ℝ) - a) * h + m * h), g y := by
    intro j
    have hs := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun k : ℕ => s + ((j : ℝ) - a) * h + k * h) (n := m)
      (fun k _ => hg.intervalIntegrable _ _)
    simp only [CharP.cast_eq_zero, zero_mul, add_zero] at hs
    rw [← hs]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring_nf
  have hmono : ∀ j ∈ Finset.range (a + b),
      ∫ y in (s + ((j : ℝ) - a) * h)..(s + ((j : ℝ) - a) * h + m * h), g y ≤
        ∫ y in (s - a * h)..(s + ((m : ℝ) + b) * h), g y := by
    intro j hj
    have hjab : (j : ℝ) + 1 ≤ a + b := by
      have := Finset.mem_range.mp hj; exact_mod_cast (by omega : j + 1 ≤ a + b)
    have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
    have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
    refine intervalIntegral.integral_mono_interval ?_ ?_ ?_
      (Filter.Eventually.of_forall fun y => hg0 y) (hg.intervalIntegrable _ _)
    · nlinarith
    · nlinarith
    · nlinarith
  calc ∑ k ∈ Finset.range m, ∫ y in (s + ((k : ℝ) - a) * h)..(s + ((k : ℝ) + b) * h), g y
      = ∑ j ∈ Finset.range (a + b), ∑ k ∈ Finset.range m,
          ∫ y in (s + ((j : ℝ) - a) * h + k * h)..(s + ((j : ℝ) - a) * h + k * h + h), g y := by
        simp_rw [hsplit]; exact Finset.sum_comm
    _ = ∑ j ∈ Finset.range (a + b),
          ∫ y in (s + ((j : ℝ) - a) * h)..(s + ((j : ℝ) - a) * h + m * h), g y :=
        Finset.sum_congr rfl fun j _ => hrow j
    _ ≤ ∑ _j ∈ Finset.range (a + b), ∫ y in (s - a * h)..(s + ((m : ℝ) + b) * h), g y :=
        Finset.sum_le_sum hmono
    _ = (a + b) * ∫ y in (s - a * h)..(s + ((m : ℝ) + b) * h), g y := by simp

/-! ## Large values at scale `R` -/

/-- Heights `t ∈ [T, 2T]` near which, at scale `R`, `ζ` exceeds `M`: some `z` with
`½ ≤ Re z ≤ ½ + 4R` and `|Im z − t| ≤ 4R` has `|ζ(z)| > M`. -/
def zetaLargeNearScale (T R M : ℝ) : Set ℝ :=
  {t | t ∈ Icc T (2 * T) ∧ ∃ z : ℂ, 1 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 + 4 * R ∧ |z.im - t| ≤ 4 * R ∧
    M < ‖riemannZeta z‖}

/-- **Large values at scale `R`, quantitative.** With the constants `C` of the vertical mean square
and `K` of the `χ`-bound, an area radius `0 < r ≤ R ≤ 1/8`, `T ≥ 8` and `M > 0`, the heights in
`[T, 2T]` near which `|ζ| > M` at scale `R` have measure at most
`R · 11 (4R + 2r) Q / (π r² (T/2)² M²)`, where `Q` is the column bound. -/
theorem volume_zetaLargeNearScale_le_aux {C K R r : ℝ} (hC : 0 < C) (hK0 : 0 ≤ K) (hr0 : 0 < r)
    (hrR : r ≤ R) (hR8 : R ≤ 1 / 8)
    (hA1 : ∀ T : ℝ, 2 ≤ T → ∀ σ : ℝ, 1 / 2 ≤ σ → σ ≤ 3 →
      ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ C * T * (1 + Real.log T) ^ 3)
    (hχ : ∀ d : ℝ, 0 ≤ d → d ≤ 1 / 4 → ∀ t : ℝ,
      ‖zetaChi (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ K * (max 1 |t|) ^ d)
    {T M : ℝ} (hT : 8 ≤ T) (hM : 0 < M) :
    volume (zetaLargeNearScale T R M) ≤ ENNReal.ofReal (R * (11 * ((4 * R + 2 * r)
      * ((4 * T + 2) ^ 2 * ((K * (4 * T) ^ r) ^ 2 + 1) * (4 * C * T * (1 + Real.log (4 * T)) ^ 3))))
        / (Real.pi * r ^ 2 * (T / 2) ^ 2 * M ^ 2)) := by
  have hR0 : 0 < R := lt_of_lt_of_le hr0 hrR
  set Q := (4 * T + 2) ^ 2 * ((K * (4 * T) ^ r) ^ 2 + 1) * (4 * C * T * (1 + Real.log (4 * T)) ^ 3)
    with hQ
  set A := Real.pi * r ^ 2 * (T / 2) ^ 2 * M ^ 2 with hAdef
  have hA : 0 < A := by rw [hAdef]; have := Real.pi_pos; positivity
  set Φ : ℕ → ℝ := fun k => ∫ x in (1 / 2 - r)..(1 / 2 + 4 * R + r),
    ∫ y in (T + ((k : ℝ) - (5 : ℕ)) * R)..(T + ((k : ℝ) + (6 : ℕ)) * R),
      ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 with hΦdef
  have hΦ0 : ∀ k, 0 ≤ Φ k := fun k =>
    intervalIntegral.integral_nonneg (by linarith) fun x _ =>
      intervalIntegral.integral_nonneg (by push_cast; nlinarith) fun y _ => by positivity
  have hbad : ∀ t ∈ Icc T (2 * T),
      (∃ z : ℂ, 1 / 2 ≤ z.re ∧ z.re ≤ 1 / 2 + 4 * R ∧ |z.im - t| ≤ 4 * R ∧ M < ‖riemannZeta z‖) →
      ∀ k : ℕ, T + k * R ≤ t → t ≤ T + (k + 1) * R → A ≤ Φ k := by
    rintro t ht ⟨z, hz1, hz2, hzt, hzM⟩ k hk1 hk2
    have hzt' := abs_le.mp hzt
    have hmean := normSq_mul_area_le_box differentiable_zetaEntire (z := z) hr0
      (a := 1 / 2 - r) (b := 1 / 2 + 4 * R + r) (c := T + ((k : ℝ) - (5 : ℕ)) * R)
      (d := T + ((k : ℝ) + (6 : ℕ)) * R) (by linarith) (by linarith) (by push_cast; nlinarith)
      (by push_cast; nlinarith)
    have hzim : T / 2 ≤ z.im := by linarith [ht.1]
    have hne : z ≠ 1 := by intro h; rw [h] at hzim; simp at hzim; linarith
    have hn1 : T / 2 ≤ ‖z - 1‖ := by
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      rw [Complex.sub_im, Complex.one_im, sub_zero, abs_of_pos (by linarith)]; exact hzim
    have hE : T / 2 * M ≤ ‖zetaEntire z‖ := by
      rw [zetaEntire_eq hne, norm_mul]
      exact mul_le_mul hn1 hzM.le hM.le (norm_nonneg _)
    have hE2 : (T / 2) ^ 2 * M ^ 2 ≤ ‖zetaEntire z‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hE 2
    calc A = Real.pi * r ^ 2 * ((T / 2) ^ 2 * M ^ 2) := by rw [hAdef]; ring
      _ ≤ Real.pi * r ^ 2 * ‖zetaEntire z‖ ^ 2 := by gcongr
      _ ≤ Φ k := hmean
  have hvol := volume_setOf_le_of_cells_scaled hA hR0 hΦ0 hbad
  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  set m := ⌈T / R⌉₊ + 1 with hm
  have hm1 : (m : ℝ) * R ≤ T + 2 * R := by
    rw [hm]; push_cast
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ T / R)
    have h2 : (⌈T / R⌉₊ : ℝ) * R ≤ (T / R + 1) * R := mul_le_mul_of_nonneg_right this.le hR0.le
    rw [add_mul, div_mul_cancel₀ _ hR0.ne'] at h2
    nlinarith
  have hsum : ∑ k ∈ Finset.range m, Φ k ≤ 11 * ((4 * R + 2 * r) * Q) := by
    have hswap : ∑ k ∈ Finset.range m, Φ k = ∫ x in (1 / 2 - r)..(1 / 2 + 4 * R + r),
        ∑ k ∈ Finset.range m, ∫ y in (T + ((k : ℝ) - (5 : ℕ)) * R)..(T + ((k : ℝ) + (6 : ℕ)) * R),
          ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 := by
      rw [intervalIntegral.integral_finsetSum]
      intro k _
      exact (continuous_integral_normSq_zetaEntire_column (by push_cast; nlinarith)).intervalIntegrable
        _ _
    rw [hswap]
    have hQ0 : 0 ≤ Q := by
      rw [hQ]
      have : 0 ≤ 1 + Real.log (4 * T) := by
        linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T)]
      have := hC.le
      positivity
    have hpt : ∀ x ∈ uIoc (1 / 2 - r) (1 / 2 + 4 * R + r), ‖∑ k ∈ Finset.range m,
        ∫ y in (T + ((k : ℝ) - (5 : ℕ)) * R)..(T + ((k : ℝ) + (6 : ℕ)) * R),
          ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2‖ ≤ 11 * Q := by
      intro x hx
      rw [uIoc_of_le (by linarith)] at hx
      have hg : Continuous fun y : ℝ => ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
        (differentiable_zetaEntire.continuous.comp (by fun_prop)).norm.pow 2
      have hsl := sum_integral_sliding_scaled_le hg (fun y => by positivity) T R hR0.le 5 6 m
      have hcol := integral_normSq_zetaEntire_column_le hC hK0 hr0 (by linarith) hA1 hχ (T := T)
        (x := x) (Y₁ := T - (5 : ℕ) * R) (Y₂ := T + ((m : ℝ) + (6 : ℕ)) * R) (by linarith)
        hx.1.le (by linarith [hx.2]) (by push_cast; linarith) (by push_cast; nlinarith)
        (by push_cast; nlinarith)
      have h0 : 0 ≤ ∑ k ∈ Finset.range m,
          ∫ y in (T + ((k : ℝ) - (5 : ℕ)) * R)..(T + ((k : ℝ) + (6 : ℕ)) * R),
            ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2 :=
        Finset.sum_nonneg fun k _ =>
          intervalIntegral.integral_nonneg (by push_cast; nlinarith) fun y _ => by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      have h11 : ((5 : ℕ) : ℝ) + (6 : ℕ) = 11 := by norm_num
      rw [h11] at hsl
      nlinarith
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [abs_of_pos (by linarith)] at hn
    calc _ ≤ ‖∫ x in (1 / 2 - r)..(1 / 2 + 4 * R + r), ∑ k ∈ Finset.range m,
          ∫ y in (T + ((k : ℝ) - (5 : ℕ)) * R)..(T + ((k : ℝ) + (6 : ℕ)) * R),
            ‖zetaEntire ((x : ℂ) + (y : ℂ) * I)‖ ^ 2‖ := Real.le_norm_self _
      _ ≤ 11 * Q * (1 / 2 + 4 * R + r - (1 / 2 - r)) := hn
      _ = 11 * ((4 * R + 2 * r) * Q) := by ring
  rw [mul_div_assoc, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum hA.le) hR0.le

/-- **Large values at scale `R`.** There is `C₁` such that for `0 < c ≤ 1`, `0 < R ≤ 1/8`,
`T ≥ 8` and `V > 0`, the heights `t ∈ [T, 2T]` near which `|ζ| > V (4T)^{cR} (1 + log 4T)²` at
scale `R` have measure at most `C₁ T/(c² V²)`. -/
theorem exists_volume_zetaLargeNearScale_le :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ c R T V : ℝ, 0 < c → c ≤ 1 → 0 < R → R ≤ 1 / 8 → 8 ≤ T → 0 < V →
      volume (zetaLargeNearScale T R (V * (4 * T) ^ (c * R) * (1 + Real.log (4 * T)) ^ 2))
        ≤ ENNReal.ofReal (C₁ * T / (c ^ 2 * V ^ 2)) := by
  obtain ⟨C, hC, hA1⟩ := exists_integral_normSq_zeta_vertical_le
  obtain ⟨K, hK0, hχ⟩ :=
    exists_norm_zetaChi_moving_left_line_le_rpow (d₀ := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨26400 * (K ^ 2 + 1) * C / Real.pi, by have := Real.pi_pos; positivity, ?_⟩
  intro c R T V hc hc1 hR hR8 hT hV
  have hr0 : 0 < c * R := mul_pos hc hR
  have hrR : c * R ≤ R := mul_le_of_le_one_left hR.le hc1
  set r := c * R with hrdef
  set ℓ := 1 + Real.log (4 * T) with hℓ
  have hℓ1 : 1 ≤ ℓ := by rw [hℓ]; linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T)]
  set P := (4 * T) ^ r with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) hr0.le
  set M := V * P * ℓ ^ 2 with hM
  have hM0 : 0 < M := by positivity
  have h := volume_zetaLargeNearScale_le_aux hC hK0 hr0 hrR hR8 hA1
    (fun d hd0 hd t => hχ d hd0 hd t) hT hM0
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hT0 : 0 < T := by linarith
  have hpi := Real.pi_pos
  have hden : 0 < Real.pi * r ^ 2 * (T / 2) ^ 2 * M ^ 2 := by positivity
  rw [div_le_div_iff₀ hden (by positivity)]
  have hQ : (4 * T + 2) ^ 2 * ((K * P) ^ 2 + 1) * (4 * C * T * ℓ ^ 3)
      ≤ 25 * T ^ 2 * ((K ^ 2 + 1) * P ^ 2) * (4 * C * T * ℓ ^ 3) := by
    have h1 : (4 * T + 2) ^ 2 ≤ 25 * T ^ 2 := by nlinarith
    have h2 : (K * P) ^ 2 + 1 ≤ (K ^ 2 + 1) * P ^ 2 := by
      have : 1 ≤ P ^ 2 := one_le_pow₀ hP1
      nlinarith [sq_nonneg K]
    gcongr
  have hwidth : 4 * R + 2 * r ≤ 6 * R := by linarith
  have hℓ4 : ℓ ^ 3 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ1 (by norm_num)
  have hRc : R * c = r := by rw [hrdef]; ring
  have hQ0 : 0 ≤ 25 * T ^ 2 * ((K ^ 2 + 1) * P ^ 2) * (4 * C * T * ℓ ^ 3) := by
    have := hC.le; positivity
  calc R * (11 * ((4 * R + 2 * r) * ((4 * T + 2) ^ 2 * ((K * P) ^ 2 + 1)
        * (4 * C * T * ℓ ^ 3)))) * (c ^ 2 * V ^ 2)
      ≤ R * (11 * (6 * R * (25 * T ^ 2 * ((K ^ 2 + 1) * P ^ 2) * (4 * C * T * ℓ ^ 3))))
        * (c ^ 2 * V ^ 2) := by
        gcongr
    _ = 6600 * (K ^ 2 + 1) * C * T ^ 3 * (R * c) ^ 2 * V ^ 2 * P ^ 2 * ℓ ^ 3 := by ring
    _ ≤ 6600 * (K ^ 2 + 1) * C * T ^ 3 * (R * c) ^ 2 * V ^ 2 * P ^ 2 * ℓ ^ 4 := by
        have := hC.le
        gcongr
    _ = 26400 * (K ^ 2 + 1) * C / Real.pi * T * (Real.pi * r ^ 2 * (T / 2) ^ 2 * M ^ 2) := by
        rw [hM, hRc]; field_simp; ring

/-! ## Small values on vertical lines -/

/-- The tangent-line (Jensen) bound: `max(0, log y) ≤ ½ log(1 + A) + (y² − A)/(2(1 + A))`. -/
theorem max_zero_log_le_tangent {y A : ℝ} (hy : 0 ≤ y) (hA : 0 ≤ A) :
    max 0 (Real.log y) ≤ Real.log (1 + A) / 2 + (y ^ 2 - A) / (2 * (1 + A)) := by
  have h1 : max 0 (Real.log y) ≤ Real.log (1 + y ^ 2) / 2 := by
    have h0 : 0 ≤ Real.log (1 + y ^ 2) := Real.log_nonneg (by nlinarith)
    rcases le_or_gt y 1 with hy1 | hy1
    · have : Real.log y ≤ 0 := Real.log_nonpos hy hy1
      exact max_le (by linarith) (by linarith)
    · have hlog : Real.log y = Real.log (y ^ 2) / 2 := by rw [Real.log_pow]; push_cast; ring
      have : Real.log (y ^ 2) ≤ Real.log (1 + y ^ 2) :=
        Real.log_le_log (by positivity) (by linarith)
      exact max_le (by linarith) (by linarith)
  have h2 : Real.log (1 + y ^ 2) ≤ Real.log (1 + A) + (y ^ 2 - A) / (1 + A) := by
    have hpos : 0 < (1 + y ^ 2) / (1 + A) := by positivity
    have := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by positivity) (by positivity)] at this
    have e : (1 + y ^ 2) / (1 + A) - 1 = (y ^ 2 - A) / (1 + A) := by field_simp; ring
    linarith
  have e : (y ^ 2 - A) / (2 * (1 + A)) = (y ^ 2 - A) / (1 + A) / 2 := by
    rw [div_div, mul_comm]
  linarith

/-- The negative part of `log|ζ|` on a vertical segment: with `A` the mean of `|ζ|²` and the
Littlewood floor `∫ log|ζ| ≥ −B`, `∫ max(0, −log|ζ|) ≤ (T₂ − T₁) log(1 + A)/2 + B`. -/
theorem integral_negPart_log_norm_le {x T₁ T₂ B : ℝ} (hT₁ : 20 ≤ T₁)
    (hT : T₁ < T₂)
    (hfl : -B ≤ ∫ t in T₁..T₂, Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) :
    ∫ t in T₁..T₂, max 0 (-Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖)
      ≤ (T₂ - T₁) * (Real.log (1 + (∫ t in T₁..T₂,
          ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ ^ 2) / (T₂ - T₁)) / 2) + B := by
  set f : ℝ → ℝ := fun t => Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ with hfdef
  set D := T₂ - T₁ with hD
  have hDpos : 0 < D := by linarith
  set S := ∫ t in T₁..T₂, ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ ^ 2 with hSdef
  set A := S / D with hAdef
  have hS0 : 0 ≤ S := intervalIntegral.integral_nonneg hT.le fun t _ => by positivity
  have hA0 : 0 ≤ A := div_nonneg hS0 hDpos.le
  have hne1 : ∀ t : ℝ, 20 ≤ t → (x : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro t ht h; have := congrArg Complex.im h; simp at this; linarith
  have hfi : IntervalIntegrable f volume T₁ T₂ :=
    intervalIntegrable_log_norm_vertical_of_analyticAt fun t ht => by
      rw [uIcc_of_le hT.le] at ht
      exact analyticAt_riemannZeta_of_ne_one (hne1 t (by linarith [ht.1]))
  have hg : (fun t => max 0 (-f t)) = fun t => (|f t| - f t) / 2 := by
    funext t
    rcases le_total 0 (f t) with h | h
    · rw [max_eq_left (by linarith), abs_of_nonneg h]; ring
    · rw [max_eq_right (by linarith), abs_of_nonpos h]; ring
  have hgi : IntervalIntegrable (fun t => max 0 (-f t)) volume T₁ T₂ := by
    rw [hg]; exact (hfi.abs.sub hfi).div_const 2
  have hsq : IntervalIntegrable (fun t : ℝ => ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ ^ 2)
      volume T₁ T₂ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hT.le]; exact continuousOn_normSq_zeta_vertical x (by linarith)
  set h : ℝ → ℝ := fun t => Real.log (1 + A) / 2
    + (‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ ^ 2 - A) / (2 * (1 + A)) - f t with hhdef
  have hhi : IntervalIntegrable h volume T₁ T₂ :=
    (intervalIntegrable_const.add ((hsq.sub intervalIntegrable_const).div_const _)).sub hfi
  have hpt : ∀ t ∈ Set.Icc T₁ T₂, max 0 (-f t) ≤ h t := by
    intro t _
    have hm := max_zero_log_le_tangent (norm_nonneg (riemannZeta ((x : ℂ) + (t : ℂ) * I))) hA0
    have e : max 0 (-f t) = max 0 (f t) - f t := by
      rcases le_total 0 (f t) with h | h
      · rw [max_eq_left (by linarith), max_eq_right h]; ring
      · rw [max_eq_right (by linarith), max_eq_left h]; ring
    rw [e]; simp only [hhdef, hfdef] at hm ⊢; linarith
  have hmono := intervalIntegral.integral_mono_on hT.le hgi hhi hpt
  have hcalc : ∫ t in T₁..T₂, h t = D * (Real.log (1 + A) / 2) + (S - D * A) / (2 * (1 + A))
      - ∫ t in T₁..T₂, f t := by
    simp only [hhdef]
    rw [intervalIntegral.integral_sub (intervalIntegrable_const.add
        ((hsq.sub intervalIntegrable_const).div_const _)) hfi,
      intervalIntegral.integral_add intervalIntegrable_const
        ((hsq.sub intervalIntegrable_const).div_const _),
      intervalIntegral.integral_const, intervalIntegral.integral_div,
      intervalIntegral.integral_sub hsq intervalIntegrable_const, intervalIntegral.integral_const]
    simp only [smul_eq_mul, ← hD, ← hSdef]
  have hDA : S - D * A = 0 := by rw [hAdef]; field_simp; ring
  rw [hcalc, hDA, zero_div, add_zero] at hmono
  show ∫ t in T₁..T₂, max 0 (-f t) ≤ D * (Real.log (1 + A) / 2) + B
  linarith

/-- Markov for the negative part of `log|ζ|` on `[T, 2T] ⊆ (T₁, T₂)`. -/
theorem volume_log_norm_lt_neg_le_of_integral {x T T₁ T₂ W I₀ : ℝ}
    (hT₁20 : 20 ≤ T₁) (hT₁ : T₁ < T) (hT₂ : 2 * T < T₂) (hW : 0 < W)
    (hI : ∫ t in T₁..T₂, max 0 (-Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) ≤ I₀) :
    volume {t | t ∈ Icc T (2 * T) ∧ Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ < -W}
      ≤ ENNReal.ofReal (I₀ / W) := by
  have hT₁₂ : T₁ < T₂ := by linarith
  set g : ℝ → ℝ := fun t => max 0 (-Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) with hgdef
  have hne1 : ∀ t : ℝ, 20 ≤ t → (x : ℂ) + (t : ℂ) * I ≠ 1 := by
    intro t ht h; have := congrArg Complex.im h; simp at this; linarith
  have hfi : IntervalIntegrable (fun t => Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖)
      volume T₁ T₂ :=
    intervalIntegrable_log_norm_vertical_of_analyticAt fun t ht => by
      rw [uIcc_of_le hT₁₂.le] at ht
      exact analyticAt_riemannZeta_of_ne_one (hne1 t (by linarith [ht.1]))
  have hgi : IntervalIntegrable g volume T₁ T₂ := by
    have : g = fun t : ℝ => (|Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖|
        - Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) / 2 := by
      funext t; simp only [hgdef]
      rcases le_total 0 (Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖) with h | h
      · rw [max_eq_left (by linarith), abs_of_nonneg h]; ring
      · rw [max_eq_right (by linarith), abs_of_nonpos h]; ring
    rw [this]; exact (hfi.abs.sub hfi).div_const 2
  have hsub : {t | t ∈ Icc T (2 * T) ∧ Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ < -W} ⊆
      {t | W ≤ g t} ∩ Ioc T₁ T₂ := by
    rintro t ⟨ht, hlt⟩
    refine ⟨?_, by linarith [ht.1], by linarith [ht.2]⟩
    show W ≤ max 0 (-Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖)
    exact le_max_of_le_right (by linarith)
  have hgint : Integrable g (volume.restrict (Ioc T₁ T₂)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT₁₂.le).mp hgi
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Ioc T₁ T₂))
    (Filter.Eventually.of_forall fun t => le_max_left 0 _) hgint W
  rw [← intervalIntegral.integral_of_le hT₁₂.le] at hmark
  have hfin : volume.restrict (Ioc T₁ T₂) {t | W ≤ g t} ≠ ⊤ :=
    measure_ne_top_of_subset (Set.subset_univ _) (by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  calc volume {t | t ∈ Icc T (2 * T) ∧ Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ < -W}
      ≤ ENNReal.ofReal ((volume.restrict (Ioc T₁ T₂)).real {t | W ≤ g t}) := by
        rw [Measure.real, ENNReal.ofReal_toReal hfin, Measure.restrict_apply' measurableSet_Ioc]
        exact measure_mono hsub
    _ ≤ ENNReal.ofReal (I₀ / W) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ hW, mul_comm]
        exact hmark.trans hI

/-- The numerical budget of the small-value bound. -/
theorem small_value_budget {C Cf Kf T T₁ T₂ S : ℝ} (hC : 0 < C) (hCf : 0 < Cf) (hKf : 0 < Kf)
    (hT : 40 ≤ T) (hT₁ : T₁ ∈ Ioo (T - 1) T) (hT₂ : T₂ ∈ Ioo (2 * T) (2 * T + 1)) (hS0 : 0 ≤ S)
    (hS : S ≤ 4 * C * T * (1 + Real.log (4 * T)) ^ 3) :
    (T₂ - T₁) * (Real.log (1 + S / (T₂ - T₁)) / 2) + (Cf + Kf * Real.log T₂)
      ≤ ((Real.log (1 + 4 * C) + 3 * Real.log (3 / 2)) / Real.log 2 + 3
          + (Cf + 3 * Kf) / Real.log 2) * T * Real.log (2 + Real.log T) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set a₁ : ℝ := Real.log (1 + 4 * C) + 3 * Real.log (3 / 2) with ha₁
  have ha₁0 : 0 ≤ a₁ := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + 4 * C)
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2)
    linarith
  have hT0 : 0 < T := by linarith
  set D := T₂ - T₁ with hD
  have hD0 : T ≤ D := by rw [hD]; linarith [hT₁.2, hT₂.1]
  have hDle : D ≤ T + 2 := by rw [hD]; linarith [hT₁.1, hT₂.2]
  have hDpos : 0 < D := by linarith
  have hLL : Real.log 2 ≤ Real.log (2 + Real.log T) :=
    Real.log_le_log (by norm_num) (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)])
  have hA : S / D ≤ 4 * C * (1 + Real.log (4 * T)) ^ 3 := by
    rw [div_le_iff₀ hDpos]
    have h0 : 0 ≤ 4 * C * (1 + Real.log (4 * T)) ^ 3 := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T); have := hC.le; positivity
    nlinarith
  have hA0 : 0 ≤ S / D := div_nonneg hS0 hDpos.le
  have hlogA : Real.log (1 + S / D) ≤ a₁ + 3 * Real.log (2 + Real.log T) := by
    have h1l : 1 ≤ 1 + Real.log (4 * T) := by
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * T)]
    have hstep : 1 + S / D ≤ (1 + 4 * C) * (1 + Real.log (4 * T)) ^ 3 := by
      have : 1 ≤ (1 + Real.log (4 * T)) ^ 3 := one_le_pow₀ h1l
      nlinarith
    have h4 : 1 + Real.log (4 * T) ≤ 3 / 2 * (2 + Real.log T) := by
      rw [Real.log_mul (by norm_num) hT0.ne']
      have : Real.log 4 < 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        have := Real.log_two_lt_d9; push_cast; linarith
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)]
    calc Real.log (1 + S / D) ≤ Real.log ((1 + 4 * C) * (1 + Real.log (4 * T)) ^ 3) :=
          Real.log_le_log (by linarith) hstep
      _ = Real.log (1 + 4 * C) + 3 * Real.log (1 + Real.log (4 * T)) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ Real.log (1 + 4 * C) + 3 * Real.log (3 / 2 * (2 + Real.log T)) := by
          gcongr
      _ = a₁ + 3 * Real.log (2 + Real.log T) := by
          rw [Real.log_mul (by norm_num) (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ T)]),
            ha₁]
          ring
  have hlog2T : Real.log T₂ ≤ 3 * T := by
    have := Real.log_le_sub_one_of_pos (by linarith [hT₂.1] : (0 : ℝ) < T₂)
    linarith [hT₂.2]
  have hlogA0 : 0 ≤ Real.log (1 + S / D) := Real.log_nonneg (by linarith)
  have hL0 : 0 ≤ Real.log (2 + Real.log T) := le_trans hl2.le hLL
  have h1 : D * (Real.log (1 + S / D) / 2) ≤ T * (a₁ + 3 * Real.log (2 + Real.log T)) := by
    have e1 : D * (Real.log (1 + S / D) / 2) ≤ T * Real.log (1 + S / D) := by nlinarith
    have e3 : T * Real.log (1 + S / D) ≤ T * (a₁ + 3 * Real.log (2 + Real.log T)) :=
      mul_le_mul_of_nonneg_left hlogA hT0.le
    linarith
  have h2 : Cf + Kf * Real.log T₂ ≤ (Cf + 3 * Kf) * T := by nlinarith
  have h3 : T * (a₁ + 3 * Real.log (2 + Real.log T)) ≤
      T * Real.log (2 + Real.log T) * (a₁ / Real.log 2 + 3) := by
    have : a₁ ≤ a₁ / Real.log 2 * Real.log (2 + Real.log T) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hLL ha₁0
    nlinarith
  have h4 : (Cf + 3 * Kf) * T ≤ T * Real.log (2 + Real.log T) * ((Cf + 3 * Kf) / Real.log 2) := by
    have : (Cf + 3 * Kf) ≤ (Cf + 3 * Kf) / Real.log 2 * Real.log (2 + Real.log T) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hLL (by positivity)
    nlinarith
  calc D * (Real.log (1 + S / D) / 2) + (Cf + Kf * Real.log T₂)
      ≤ T * Real.log (2 + Real.log T) * (a₁ / Real.log 2 + 3)
        + T * Real.log (2 + Real.log T) * ((Cf + 3 * Kf) / Real.log 2) := by linarith
    _ = (a₁ / Real.log 2 + 3 + (Cf + 3 * Kf) / Real.log 2) * T * Real.log (2 + Real.log T) := by
        ring

/-- **Small values on vertical lines.** There is `C₂` such that for `T ≥ 40`, `½ ≤ x ≤ 1` and
`W > 0`, the heights `t ∈ [T, 2T]` with `log|ζ(x + it)| < −W` have measure at most
`C₂ T log(2 + log T)/W`. -/
theorem exists_volume_logZeta_lt_neg_le :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ T : ℝ, 40 ≤ T → ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 1 → ∀ W : ℝ, 0 < W →
      volume {t | t ∈ Icc T (2 * T) ∧ Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ < -W}
        ≤ ENNReal.ofReal (C₂ * T * Real.log (2 + Real.log T) / W) := by
  obtain ⟨C, hC, hA1⟩ := exists_integral_normSq_zeta_vertical_le
  obtain ⟨Cf, Kf, hCf, hKf, hfloor⟩ := exists_zetaDisplacedLine_logMean_floor
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log (1 + 4 * C) + 3 * Real.log (3 / 2)) / Real.log 2 + 3
    + (Cf + 3 * Kf) / Real.log 2, ?_, ?_⟩
  · have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + 4 * C)
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3 / 2)
    positivity
  intro T hT x hx1 hx2 W hW
  have hdense := countable_zetaZeroHeights.dense_compl ℝ
  obtain ⟨T₁, hT₁B, hT₁⟩ := hdense.exists_between (by linarith : T - 1 < T)
  obtain ⟨T₂, hT₂B, hT₂⟩ := hdense.exists_between (by linarith : 2 * T < 2 * T + 1)
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT₁₂ : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  have hne : ∀ S : ℝ, 20 ≤ S → S ∉ {T : ℝ | 20 ≤ T ∧ ∃ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ),
      riemannZeta ((x : ℂ) + (T : ℂ) * I) = 0} →
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) (15 / 2 : ℝ), riemannZeta ((x : ℂ) + (S : ℂ) * I) ≠ 0 :=
    fun S hS hSB y hy h0 => hSB ⟨hS, y, hy, h0⟩
  have hfl := hfloor x hx1 hx2 T₁ T₂ hT₁20 hT₁₂ (hne T₁ hT₁20 hT₁B)
    (hne T₂ (by linarith [hT₂.1]) hT₂B)
  have hms := integral_normSq_zeta_span_le hC hA1 (T := T) (σ := x) (Y₁ := T₁) (Y₂ := T₂)
    (by linarith) hx1 (by linarith) (by linarith [hT₁.1]) hT₁₂.le (by linarith [hT₂.2])
  have hint := integral_negPart_log_norm_le (x := x) hT₁20 hT₁₂ hfl
  have hS0 : 0 ≤ ∫ t in T₁..T₂, ‖riemannZeta ((x : ℂ) + (t : ℂ) * I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hT₁₂.le fun t _ => by positivity
  have hbud := small_value_budget hC hCf hKf hT hT₁ hT₂ hS0 hms
  exact volume_log_norm_lt_neg_le_of_integral hT₁20 hT₁.2 hT₂.1 hW (hint.trans hbud)

/-! ## Zero shadows at scale -/

/-- Heights within `κ (Re ρ − ½)` of a zero `ρ` with `Re ρ ≥ ½ + a`. -/
def zetaZeroShadowScaled (a κ : ℝ) : Set ℝ :=
  {t | ∃ w : ℂ, riemannZeta w = 0 ∧ 1 / 2 + a ≤ w.re ∧ |w.im - t| ≤ κ * (w.re - 1 / 2)}

/-- **Scaled zero shadows.** For all large `U`, for every `a ≥ 2/log U` and `κ > 0`, the heights
in `[U/4 + κ + 1, U/2 − κ − 1]` within `κ (Re ρ − ½)` of a zero with `Re ρ ≥ ½ + a` have measure
at most `2κ (D U/(4 a log U) + K log² U)`. -/
theorem exists_volume_zetaZeroShadowScaled_le :
    ∃ D K : ℝ, 0 ≤ D ∧ 0 ≤ K ∧ ∀ᶠ U in atTop, ∀ a κ : ℝ, 2 / Real.log U ≤ a → 0 < κ →
      volume (zetaZeroShadowScaled a κ ∩ Icc (U / 4 + κ + 1) (U / 2 - κ - 1))
        ≤ ENNReal.ofReal (2 * κ * (D / (a * Real.log U) * (U / 4) + K * Real.log U ^ 2)) := by
  classical
  obtain ⟨D, K, hD, hK, htail⟩ := exists_offLineTailMoment_window_le
  refine ⟨D, K, hD, hK, ?_⟩
  filter_upwards [htail, eventually_ge_atTop (100 : ℝ)] with U hU hU100
  obtain ⟨T₁, hT₁, T₂, hT₂, hc⟩ := hU
  intro a κ ha hκ
  have hL0 : 0 < Real.log U := Real.log_pos (by linarith)
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hT₁20 : 20 ≤ T₁ := by linarith [hT₁.1]
  have hT12 : T₁ < T₂ := by linarith [hT₁.2, hT₂.1]
  obtain ⟨Z, hZ⟩ := exists_zetaRectangleZeros_finset hT₁20 hT12
  set Zc := Z.filter (fun w => 1 / 2 + a * Real.log U / Real.log U ≤ w.re) with hZc
  have hsub : zetaZeroShadowScaled a κ ∩ Icc (U / 4 + κ + 1) (U / 2 - κ - 1) ⊆
      ⋃ w ∈ Zc, Icc (w.im - κ * (w.re - 1 / 2)) (w.im + κ * (w.re - 1 / 2)) := by
    rintro t ⟨⟨w, hw0, hwa, hwt⟩, ht⟩
    have hw1 : w.re < 1 := by
      by_contra h
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hw0
    have hwt' := abs_le.mp hwt
    have hκw : κ * (w.re - 1 / 2) ≤ κ := by nlinarith
    have hZw : w ∈ Z := by
      rw [hZ, Complex.mem_reProdIm, Set.uIcc_of_le (by norm_num), Set.uIcc_of_le hT12.le]
      refine ⟨⟨⟨by linarith, by linarith⟩, ⟨by linarith [ht.1, hT₁.2], by linarith [ht.2, hT₂.1]⟩⟩,
        hw0⟩
    have hwa' : 1 / 2 + a * Real.log U / Real.log U ≤ w.re := by
      rw [mul_div_assoc, div_self hL0.ne', mul_one]; exact hwa
    exact mem_iUnion₂.mpr ⟨w, Finset.mem_filter.mpr ⟨hZw, hwa'⟩, ⟨by linarith, by linarith⟩⟩
  have hvol : volume (zetaZeroShadowScaled a κ ∩ Icc (U / 4 + κ + 1) (U / 2 - κ - 1))
      ≤ ENNReal.ofReal (∑ w ∈ Zc, 2 * κ * (w.re - 1 / 2)) := by
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
    rw [ENNReal.ofReal_sum_of_nonneg fun w hw => by
      have := (Finset.mem_filter.mp hw).2
      have : 0 < a * Real.log U / Real.log U := by positivity
      nlinarith]
    refine Finset.sum_le_sum fun w _ => ?_
    rw [Real.volume_Icc]; apply le_of_eq; congr 1; ring
  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  have hmass := hc Z hZ (a * Real.log U) (by rw [div_le_iff₀ hL0] at ha; linarith)
  have hm : ∑ w ∈ Zc, 2 * κ * (w.re - 1 / 2) ≤
      2 * κ * ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    obtain ⟨hwZ, hwa⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwbox, hw0⟩ := (hZ w).mp hwZ
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hwbox
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hT12.le] at hwbox
      simp at hwbox
      linarith [hwbox.2.1]
    have hord : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) := by
      exact_mod_cast one_le_toNat_analyticOrderAt_riemannZeta hw1 hw0
    have hre : 0 ≤ w.re - 1 / 2 := by
      have : 0 < a * Real.log U / Real.log U := by positivity
      linarith
    have := mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * κ) hre)
      (by linarith : (0 : ℝ) ≤ ((analyticOrderAt riemannZeta w).toNat : ℝ) - 1)
    nlinarith
  have hTT : T₂ - T₁ ≤ U / 4 := by linarith [hT₁.1, hT₂.2]
  have hDc : D / (a * Real.log U) * (T₂ - T₁) ≤ D / (a * Real.log U) * (U / 4) :=
    mul_le_mul_of_nonneg_left hTT (by positivity)
  calc ∑ w ∈ Zc, 2 * κ * (w.re - 1 / 2)
      ≤ 2 * κ * ∑ w ∈ Zc, ((analyticOrderAt riemannZeta w).toNat : ℝ) * (w.re - 1 / 2) := hm
    _ ≤ 2 * κ * (D / (a * Real.log U) * (T₂ - T₁) + K * Real.log U ^ 2) := by gcongr
    _ ≤ 2 * κ * (D / (a * Real.log U) * (U / 4) + K * Real.log U ^ 2) := by gcongr

end RHTower

end
