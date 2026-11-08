import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheRowsOfANearPairSum

/-!
# Uniform row means on logarithmic annuli

Lattice quadrature and local Lipschitz bounds give an explicit `O(1/n)` error
for either side of a logarithmic annulus. The integral mean is independent of
its receiving index, including annuli crossing that index.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Set
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- A Lipschitz row on a positive real interval is approximated by its lattice sum;
only the two fractional end intervals contribute the supremum term. -/
theorem abs_sum_Ioc_floor_sub_integral_le {f : ℝ → ℝ} {a b A lam : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hA : 0 ≤ A) (hlam : 0 ≤ lam)
    (hfA : ∀ x ∈ Set.Icc a b, |f x| ≤ A)
    (hfl : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤ lam * |x - y|) :
    |∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n - ∫ x in a..b, f x| ≤ lam * (b - a) + 3 * A := by
  have hb : 0 ≤ b := ha.trans hab
  have hcont : ContinuousOn f (Set.Icc a b) := continuousOn_of_abs_sub_le hfl
  have hii : ∀ u v, u ∈ Set.Icc a b → v ∈ Set.Icc a b → IntervalIntegrable f volume u v :=
    fun u v hu hv => (hcont.mono (Set.uIcc_subset_Icc hu hv)).intervalIntegrable
  have hi_bound : ∀ u v, u ∈ Set.Icc a b → v ∈ Set.Icc a b → u ≤ v →
      |∫ x in u..v, f x| ≤ A * (v - u) := by
    intro u v hu hv huv
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
      (f := f) (C := A) (fun x hx => by
        rw [uIoc_of_le huv] at hx
        exact hfA x ⟨hu.1.trans hx.1.le, hx.2.trans hv.2⟩)
    rwa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] at h
  have ha_mem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  by_cases hnon : ⌊a⌋₊ + 1 ≤ ⌊b⌋₊
  · let a₀ : ℕ := ⌊a⌋₊ + 1
    let M : ℕ := ⌊b⌋₊ - a₀
    have heq : ⌊b⌋₊ = a₀ + M := by dsimp only [a₀, M]; omega
    have hal : a < (a₀ : ℝ) := by dsimp only [a₀]; push_cast; exact Nat.lt_floor_add_one a
    have hau : (a₀ : ℝ) ≤ a + 1 := by
      dsimp only [a₀]; push_cast; linarith only [Nat.floor_le ha]
    have hbu : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb
    have hbl : b < (⌊b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one b
    have hcast : (a₀ : ℝ) + M = ⌊b⌋₊ := by exact_mod_cast heq.symm
    have hMba : (M : ℝ) ≤ b - a := by linarith only [hcast, hal, hbu]
    have hma : (a₀ : ℝ) ∈ Set.Icc a b :=
      ⟨hal.le, by linarith only [hcast, hbu, Nat.cast_nonneg (α := ℝ) M]⟩
    have hmb : (⌊b⌋₊ : ℝ) ∈ Set.Icc a b :=
      ⟨by linarith only [hcast, hal, Nat.cast_nonneg (α := ℝ) M], hbu⟩
    have hfin : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ =
        (range (M + 1)).map ⟨fun i => a₀ + i, fun _ _ h => Nat.add_left_cancel h⟩ := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨hlo, hhi⟩
        refine ⟨n - a₀, ?_, ?_⟩ <;> dsimp only [a₀, M] at * <;> omega
      · rintro ⟨i, hi, rfl⟩
        dsimp only [a₀, M] at *
        omega
    have hsum : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n) =
        (∑ i ∈ range M, f ((a₀ : ℝ) + i)) + f ⌊b⌋₊ := by
      rw [hfin, sum_map, Finset.sum_range_succ]
      simp only [Function.Embedding.coeFn_mk, Nat.cast_add, ← hcast]
    have hr := abs_sum_range_sub_integral_le (f := f) (lam := lam) (a₀ : ℝ) M
      (fun x hx y hy => hfl x ⟨hma.1.trans hx.1, hx.2.trans (by linarith only [hcast, hbu])⟩
        y ⟨hma.1.trans hy.1, hy.2.trans (by linarith only [hcast, hbu])⟩)
    have hthree : (∫ x in a..b, f x) = (∫ x in a..(a₀ : ℝ), f x) +
        (∫ x in (a₀ : ℝ)..(a₀ : ℝ) + M, f x) + (∫ x in (⌊b⌋₊ : ℝ)..b, f x) := by
      rw [hcast, intervalIntegral.integral_add_adjacent_intervals (hii _ _ ha_mem hma)
        (hii _ _ hma hmb), intervalIntegral.integral_add_adjacent_intervals
        (hii _ _ ha_mem hmb) (hii _ _ hmb hb_mem)]
    have hlo : |∫ x in a..(a₀ : ℝ), f x| ≤ A :=
      (hi_bound _ _ ha_mem hma hal.le).trans
        ((mul_le_mul_of_nonneg_left (by linarith only [hau] : (a₀ : ℝ) - a ≤ 1) hA).trans_eq (mul_one A))
    have hhi : |∫ x in (⌊b⌋₊ : ℝ)..b, f x| ≤ A :=
      (hi_bound _ _ hmb hb_mem hbu).trans
        ((mul_le_mul_of_nonneg_left (by linarith only [hbl] : b - (⌊b⌋₊ : ℝ) ≤ 1) hA).trans_eq (mul_one A))
    rw [hsum, hthree]
    have hlast := hfA _ hmb
    have habs : |(∑ i ∈ range M, f ((a₀ : ℝ) + i)) + f ⌊b⌋₊ -
        ((∫ x in a..(a₀ : ℝ), f x) + (∫ x in (a₀ : ℝ)..(a₀ : ℝ) + M, f x) +
          (∫ x in (⌊b⌋₊ : ℝ)..b, f x))| ≤
        |(∑ i ∈ range M, f ((a₀ : ℝ) + i)) - (∫ x in (a₀ : ℝ)..(a₀ : ℝ) + M, f x)| +
          |f ⌊b⌋₊| + |∫ x in a..(a₀ : ℝ), f x| + |∫ x in (⌊b⌋₊ : ℝ)..b, f x| := by
      let X := (∑ i ∈ range M, f ((a₀ : ℝ) + i)) -
        (∫ x in (a₀ : ℝ)..(a₀ : ℝ) + M, f x)
      let Y := f ⌊b⌋₊
      let Z := -(∫ x in a..(a₀ : ℝ), f x)
      let W := -(∫ x in (⌊b⌋₊ : ℝ)..b, f x)
      have he : (∑ i ∈ range M, f ((a₀ : ℝ) + i)) + f ⌊b⌋₊ -
          ((∫ x in a..(a₀ : ℝ), f x) + (∫ x in (a₀ : ℝ)..(a₀ : ℝ) + M, f x) +
            (∫ x in (⌊b⌋₊ : ℝ)..b, f x)) = X + Y + Z + W := by
        dsimp only [X, Y, Z, W]; ring
      rw [he]
      simpa only [X, Y, Z, W, abs_neg] using
        (abs_add_le (X + Y + Z) W).trans
          (add_le_add ((abs_add_le (X + Y) Z).trans
            (add_le_add (abs_add_le X Y) le_rfl)) le_rfl)
    have hm := mul_le_mul_of_nonneg_left hMba hlam
    linarith only [habs, hr, hlast, hlo, hhi, hm]
  · have hempty : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    have hlen : b - a ≤ 1 := by
      have hfa := Nat.floor_le ha
      have hfb := Nat.lt_floor_add_one b
      have hcast : (⌊b⌋₊ : ℝ) ≤ ⌊a⌋₊ := by exact_mod_cast (show ⌊b⌋₊ ≤ ⌊a⌋₊ by omega)
      linarith only [hfa, hfb, hcast]
    rw [hempty, sum_empty, zero_sub, abs_neg]
    have hi := hi_bound a b ha_mem hb_mem hab
    have hm := mul_le_mul_of_nonneg_left hlen hA
    have hLamNonneg := mul_nonneg hlam (sub_nonneg.mpr hab)
    linarith only [hi, hm, hLamNonneg, hA]


/-- On a fixed multiplicative neighborhood of its receiving index, a logarithmic row kernel
has Lipschitz constant of order `(L/w + A)/n²`. -/
theorem abs_logarithmic_row_sub_le {K : ℝ → ℝ} {n w x y A L : ℝ}
    (hn : 0 < n) (hw : 0 < w) (hx : n / 4 ≤ x) (hy : n / 4 ≤ y) (hL0 : 0 ≤ L)
    (hKy : |K (Real.log (y / n) / w)| ≤ A)
    (hKL : |K (Real.log (x / n) / w) - K (Real.log (y / n) / w)| ≤
      L * |Real.log (x / n) / w - Real.log (y / n) / w|) :
    |K (Real.log (x / n) / w) / Real.sqrt (n * x) -
      K (Real.log (y / n) / w) / Real.sqrt (n * y)| ≤
      ((8 * L / w + 4 * A) / n ^ 2) * |x - y| := by
  have hη : 0 < n / 4 := by positivity
  have hx0 : 0 < x := hη.trans_le hx
  have hy0 : 0 < y := hη.trans_le hy
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hKy
  have hlog : |Real.log (x / n) - Real.log (y / n)| ≤ 4 * |x - y| / n := by
    have h := abs_log_one_add_div_sub_le hη (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
    have hex : 1 + (x - n / 4) / (n / 4) = x / (n / 4) := by field_simp; ring
    have hey : 1 + (y - n / 4) / (n / 4) = y / (n / 4) := by field_simp; ring
    rw [hex, hey, Real.log_div hx0.ne' hη.ne', Real.log_div hy0.ne' hη.ne',
      sub_sub_sub_cancel_right] at h
    rw [show (x - n / 4) - (y - n / 4) = x - y by ring] at h
    rw [Real.log_div hx0.ne' hn.ne', Real.log_div hy0.ne' hn.ne', sub_sub_sub_cancel_right]
    exact h.trans_eq (by ring)
  have hlogw : |Real.log (x / n) / w - Real.log (y / n) / w| ≤
      4 * |x - y| / (n * w) := by
    rw [← sub_div, abs_div, abs_of_pos hw]
    exact (div_le_div_of_nonneg_right hlog hw.le).trans_eq (by ring)
  have hs (z : ℝ) (hz : 0 ≤ z) : Real.sqrt (n * z) = 2 * Real.sqrt ((n / 4) * z) := by
    rw [show n * z = 4 * ((n / 4) * z) by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hrec : |1 / Real.sqrt (n * x) - 1 / Real.sqrt (n * y)| ≤
      4 * |x - y| / n ^ 2 := by
    have h := abs_inv_sqrt_sub_le hη (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
    rw [add_sub_cancel, add_sub_cancel,
      show (x - n / 4) - (y - n / 4) = x - y by ring] at h
    have he : 1 / Real.sqrt (n * x) - 1 / Real.sqrt (n * y) =
        (1 / 2 : ℝ) * (1 / Real.sqrt ((n / 4) * x) - 1 / Real.sqrt ((n / 4) * y)) := by
      rw [hs x hx0.le, hs y hy0.le]; ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring)
  have hbound : 1 / Real.sqrt (n * x) ≤ 2 / n := by
    have hsq : n / 2 ≤ Real.sqrt (n * x) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      have h := mul_le_mul_of_nonneg_left hx hn.le
      nlinarith only [h]
    exact (one_div_le_one_div_of_le (by positivity : 0 < n / 2) hsq).trans_eq (by ring)
  have he : K (Real.log (x / n) / w) / Real.sqrt (n * x) -
      K (Real.log (y / n) / w) / Real.sqrt (n * y) =
      (K (Real.log (x / n) / w) - K (Real.log (y / n) / w)) * (1 / Real.sqrt (n * x)) +
        K (Real.log (y / n) / w) * (1 / Real.sqrt (n * x) - 1 / Real.sqrt (n * y)) := by ring
  rw [he]
  calc
    _ ≤ |K (Real.log (x / n) / w) - K (Real.log (y / n) / w)| * (1 / Real.sqrt (n * x)) +
        |K (Real.log (y / n) / w)| * |1 / Real.sqrt (n * x) - 1 / Real.sqrt (n * y)| := by
      simpa only [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (n * x))] using
        abs_add_le ((K (Real.log (x / n) / w) - K (Real.log (y / n) / w)) * (1 / Real.sqrt (n * x)))
          (K (Real.log (y / n) / w) * (1 / Real.sqrt (n * x) - 1 / Real.sqrt (n * y)))
    _ ≤ (L * (4 * |x - y| / (n * w))) * (2 / n) + A * (4 * |x - y| / n ^ 2) :=
      add_le_add
        (mul_le_mul (hKL.trans (mul_le_mul_of_nonneg_left hlogw hL0)) hbound (by positivity) (by positivity))
        (mul_le_mul hKy hrec (abs_nonneg _) hA0)
    _ = _ := by ring


/-- A logarithmic annulus has a row-independent Riemann mean, with an error of order `1/n`.
The interval may lie on either side of its receiving row. -/
theorem abs_logarithmic_row_sum_sub_mean_le {K : ℝ → ℝ} {α β T A L w : ℝ}
    (_hT : 0 < T) (hα : -T ≤ α) (hαβ : α ≤ β) (hβ : β ≤ T)
    (hw : 0 < w) (hTw : T * w ≤ 1 / 2) (hL0 : 0 ≤ L)
    (hA : ∀ t ∈ Set.Icc α β, |K t| ≤ A)
    (hL : ∀ s ∈ Set.Icc α β, ∀ t ∈ Set.Icc α β, |K s - K t| ≤ L * |s - t|)
    {n : ℕ} (hn : 1 ≤ n) :
    |(∑ j ∈ Finset.Ioc ⌊(n : ℝ) * Real.exp (α * w)⌋₊
        ⌊(n : ℝ) * Real.exp (β * w)⌋₊,
      K (Real.log ((j : ℝ) / n) / w) / Real.sqrt ((n : ℝ) * j)) -
        ∫ t in α..β, K t * (w * Real.exp (w * t / 2))| ≤
      (32 * T * L + 14 * A) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA α ⟨le_rfl, hαβ⟩)
  let a : ℝ := n * Real.exp (α * w)
  let b : ℝ := n * Real.exp (β * w)
  let f : ℝ → ℝ := fun x => K (Real.log (x / n) / w) / Real.sqrt ((n : ℝ) * x)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hab : a ≤ b := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hαβ hw.le)) hn0.le
  have halower : (n : ℝ) / 2 ≤ a := by
    have hαw := mul_le_mul_of_nonneg_right hα hw.le
    have he := Real.add_one_le_exp (α * w)
    have hh : (1 / 2 : ℝ) ≤ Real.exp (α * w) := by linarith only [hαw, hTw, he]
    calc
      (n : ℝ) / 2 = n * (1 / 2 : ℝ) := by ring
      _ ≤ n * Real.exp (α * w) := mul_le_mul_of_nonneg_left hh hn0.le
      _ = a := rfl
  have hquarter (x : ℝ) (hx : x ∈ Set.Icc a b) : (n : ℝ) / 4 ≤ x := by
    linarith only [halower, hx.1, hn0]
  have hmem (x : ℝ) (hx : x ∈ Set.Icc a b) : Real.log (x / n) / w ∈ Set.Icc α β := by
    have hx0 : 0 < x := ha.trans_le hx.1
    constructor
    · rw [le_div_iff₀ hw, Real.le_log_iff_exp_le (div_pos hx0 hn0), le_div_iff₀ hn0]
      simpa only [a, mul_comm] using hx.1
    · rw [div_le_iff₀ hw, Real.log_le_iff_le_exp (div_pos hx0 hn0), div_le_iff₀ hn0]
      simpa only [b, mul_comm] using hx.2
  have hfA : ∀ x ∈ Set.Icc a b, |f x| ≤ 2 * A / n := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    have hs : (n : ℝ) / 2 ≤ Real.sqrt ((n : ℝ) * x) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left (hquarter x hx) hn0.le
      nlinarith only [hh]
    dsimp only [f]
    rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr (mul_pos hn0 hx0))]
    exact (div_le_div₀ hA0 (hA _ (hmem x hx)) (by positivity) hs).trans_eq (by ring)
  have hfl : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |f x - f y| ≤
      ((8 * L / w + 4 * A) / (n : ℝ) ^ 2) * |x - y| := by
    intro x hx y hy
    exact abs_logarithmic_row_sub_le hn0 hw (hquarter x hx) (hquarter y hy) hL0
      (hA _ (hmem y hy)) (hL _ (hmem x hx) _ (hmem y hy))
  have hlen : b - a ≤ 4 * T * w * n := by
    have he (t : ℝ) (ht : -T ≤ t ∧ t ≤ T) : |Real.exp (t * w) - 1| ≤ 2 * T * w := by
      have htT : |t| ≤ T := abs_le.mpr ht
      have htw : |t * w| ≤ T * w := by
        rw [abs_mul, abs_of_pos hw]
        exact mul_le_mul_of_nonneg_right htT hw.le
      exact (Real.abs_exp_sub_one_le (htw.trans (by linarith only [hTw]))).trans
        ((mul_le_mul_of_nonneg_left htw (by norm_num)).trans_eq (by ring))
    have heα := abs_le.mp (he α ⟨hα, hαβ.trans hβ⟩)
    have heβ := abs_le.mp (he β ⟨hα.trans hαβ, hβ⟩)
    have hh : Real.exp (β * w) - Real.exp (α * w) ≤ 4 * T * w := by
      linarith only [heα.1, heβ.2]
    calc
      b - a = n * (Real.exp (β * w) - Real.exp (α * w)) := by dsimp only [a, b]; ring
      _ ≤ n * (4 * T * w) := mul_le_mul_of_nonneg_left hh hn0.le
      _ = _ := by ring
  have hquad := abs_sum_Ioc_floor_sub_integral_le ha.le hab
    (by positivity : 0 ≤ 2 * A / (n : ℝ)) (by positivity) hfA hfl
  have hbudget : ((8 * L / w + 4 * A) / (n : ℝ) ^ 2) * (b - a) + 3 * (2 * A / n) ≤
      (32 * T * L + 14 * A) / n := by
    calc
      _ ≤ ((8 * L / w + 4 * A) / (n : ℝ) ^ 2) * (4 * T * w * n) + 3 * (2 * A / n) :=
        add_le_add (mul_le_mul_of_nonneg_left hlen
          (show 0 ≤ (8 * L / w + 4 * A) / (n : ℝ) ^ 2 by positivity)) le_rfl
      _ = (32 * T * L + 16 * A * (T * w) + 6 * A) / n := by
        field_simp [hn0.ne', hw.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_right (by
        have hh := mul_le_mul_of_nonneg_left hTw (show 0 ≤ 16 * A by positivity)
        linarith only [hh]) hn0.le
  have hint : (∫ x in a..b, f x) = ∫ t in α..β, K t * (w * Real.exp (w * t / 2)) := by
    have h := integral_rowKernel_eq hw hαβ (continuousOn_of_abs_sub_le hL) hn
    have hshift := intervalIntegral.integral_comp_add_right (f := f)
      (a := a - n) (b := b - n) (n : ℝ)
    rw [sub_add_cancel, sub_add_cancel] at hshift
    rw [← hshift]
    have hea : a - n = n * (Real.exp (α * w) - 1) := by dsimp only [a]; ring
    have heb : b - n = n * (Real.exp (β * w) - 1) := by dsimp only [b]; ring
    rw [hea, heb]
    refine (intervalIntegral.integral_congr fun x _ => ?_).trans h
    dsimp only [f, rowKernel]
    have he : (x + n) / n = 1 + x / n := by field_simp [hn0.ne']; ring
    rw [he, add_comm x (n : ℝ)]
  rw [hint] at hquad
  exact hquad.trans hbudget

/-- Including a possible lattice point at the left endpoint changes a logarithmic interval
sum by at most one supremum bound. -/
lemma abs_sum_Icc_ceil_floor_sub_sum_Ioc_floor_le {f : ℝ → ℝ} {a b A : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hA : 0 ≤ A)
    (hf : ∀ x ∈ Set.Icc a b, |f x| ≤ A) :
    |(∑ n ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, f n) -
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n| ≤ A := by
  let S := Finset.Icc ⌈a⌉₊ ⌊b⌋₊
  let T := Finset.Ioc ⌊a⌋₊ ⌊b⌋₊
  have hsub : T ⊆ S := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hn
    have hal : a ≤ (n : ℝ) := (Nat.lt_floor_add_one a).le.trans
      (by exact_mod_cast Nat.succ_le_of_lt hlo)
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hal, hhi⟩
  have hdiff : S \ T ⊆ {⌊a⌋₊} := by
    intro n hn
    obtain ⟨hnS, hnT⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hnS
    have hnlo : n ≤ ⌊a⌋₊ := le_of_not_gt (fun h => hnT (Finset.mem_Ioc.mpr ⟨h, hhi⟩))
    have haN : a ≤ (n : ℝ) := (Nat.le_ceil a).trans (by exact_mod_cast hlo)
    have hfn : (⌊a⌋₊ : ℝ) ≤ n := (Nat.floor_le ha).trans haN
    have hn : n = ⌊a⌋₊ := le_antisymm hnlo (by exact_mod_cast hfn)
    simpa only [Finset.mem_singleton] using hn
  have hcard : ((S \ T).card : ℝ) ≤ 1 := by
    exact_mod_cast (show (S \ T).card ≤ 1 by simpa using Finset.card_le_card hdiff)
  have hbound : |∑ n ∈ S \ T, f n| ≤ A := by
    calc
      _ ≤ ∑ n ∈ S \ T, |f n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ S \ T, A := Finset.sum_le_sum fun n hn => by
        obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1
        have haN : a ≤ (n : ℝ) := (Nat.le_ceil a).trans (by exact_mod_cast hlo)
        have hb : 0 ≤ b := ha.trans hab
        exact hf n ⟨haN, (by exact_mod_cast hhi : (n : ℝ) ≤ ⌊b⌋₊).trans (Nat.floor_le hb)⟩
      _ = ((S \ T).card : ℝ) * A := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ A := (mul_le_mul_of_nonneg_right hcard hA).trans_eq (one_mul A)
  have hs := Finset.sum_sdiff hsub (f := fun n : ℕ => f n)
  have he : (∑ n ∈ S, f n) - ∑ n ∈ T, f n = ∑ n ∈ S \ T, f n := by linarith only [hs]
  change |(∑ n ∈ S, f n) - ∑ n ∈ T, f n| ≤ A
  rw [he]
  exact hbound


/-- Closed logarithmic annuli obey the same uniform mean estimate; a possible left endpoint
contributes one extra lattice value. -/
theorem abs_closed_logarithmic_row_sum_sub_mean_le {K : ℝ → ℝ} {α β T A L w : ℝ}
    (hT : 0 < T) (hα : -T ≤ α) (hαβ : α ≤ β) (hβ : β ≤ T)
    (hw : 0 < w) (hTw : T * w ≤ 1 / 2) (hL0 : 0 ≤ L)
    (hA : ∀ t ∈ Set.Icc α β, |K t| ≤ A)
    (hL : ∀ s ∈ Set.Icc α β, ∀ t ∈ Set.Icc α β, |K s - K t| ≤ L * |s - t|)
    {n : ℕ} (hn : 1 ≤ n) :
    |(∑ j ∈ Finset.Icc ⌈(n : ℝ) * Real.exp (α * w)⌉₊
        ⌊(n : ℝ) * Real.exp (β * w)⌋₊,
      K (Real.log ((j : ℝ) / n) / w) / Real.sqrt ((n : ℝ) * j)) -
        ∫ t in α..β, K t * (w * Real.exp (w * t / 2))| ≤
      (32 * T * L + 16 * A) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA α ⟨le_rfl, hαβ⟩)
  let a : ℝ := n * Real.exp (α * w)
  let b : ℝ := n * Real.exp (β * w)
  let f : ℝ → ℝ := fun x => K (Real.log (x / n) / w) / Real.sqrt ((n : ℝ) * x)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hab : a ≤ b := mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hαβ hw.le)) hn0.le
  have halower : (n : ℝ) / 2 ≤ a := by
    have hαw := mul_le_mul_of_nonneg_right hα hw.le
    have he := Real.add_one_le_exp (α * w)
    have hh : (1 / 2 : ℝ) ≤ Real.exp (α * w) := by linarith only [hαw, hTw, he]
    calc
      (n : ℝ) / 2 = n * (1 / 2 : ℝ) := by ring
      _ ≤ n * Real.exp (α * w) := mul_le_mul_of_nonneg_left hh hn0.le
      _ = a := rfl
  have hfA : ∀ x ∈ Set.Icc a b, |f x| ≤ 2 * A / n := by
    intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    have hmem : Real.log (x / n) / w ∈ Set.Icc α β := by
      constructor
      · rw [le_div_iff₀ hw, Real.le_log_iff_exp_le (div_pos hx0 hn0), le_div_iff₀ hn0]
        simpa only [a, mul_comm] using hx.1
      · rw [div_le_iff₀ hw, Real.log_le_iff_le_exp (div_pos hx0 hn0), div_le_iff₀ hn0]
        simpa only [b, mul_comm] using hx.2
    have hs : (n : ℝ) / 2 ≤ Real.sqrt ((n : ℝ) * x) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      have hh := mul_le_mul_of_nonneg_left (halower.trans hx.1) hn0.le
      nlinarith only [hh, sq_nonneg (n : ℝ)]
    dsimp only [f]
    rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr (mul_pos hn0 hx0))]
    exact (div_le_div₀ hA0 (hA _ hmem) (by positivity) hs).trans_eq (by ring)
  have hclosed := abs_sum_Icc_ceil_floor_sub_sum_Ioc_floor_le ha.le hab (by positivity) hfA
  have hopen := abs_logarithmic_row_sum_sub_mean_le hT hα hαβ hβ hw hTw hL0 hA hL hn
  have htri := (abs_sub_le
    (∑ j ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, f j)
    (∑ j ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f j)
    (∫ t in α..β, K t * (w * Real.exp (w * t / 2)))).trans
      (add_le_add hclosed hopen)
  exact htri.trans_eq (by ring)


/-- A terminal multiplicative strip of logarithmic width `t` contains at most `Nt + 1`
lattice points. -/
lemma card_terminal_exponential_strip_le {N : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    (((Finset.Icc 1 N).filter (fun n : ℕ => (N : ℝ) < (n : ℝ) * Real.exp t)).card : ℝ) ≤ N * t + 1 := by
  let a : ℝ := N * Real.exp (-t)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have haN : a ≤ N := by
    have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
    exact (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)).trans_eq (mul_one _)
  have hfN : ⌊a⌋₊ ≤ N := Nat.floor_le_of_le haN
  have hset : (Finset.Icc 1 N).filter (fun n : ℕ => (N : ℝ) < (n : ℝ) * Real.exp t) = Finset.Ioc ⌊a⌋₊ N := by
    ext n
    simp only [mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    have hmul : (N : ℝ) < n * Real.exp t ↔ a < n := by
      rw [← div_lt_iff₀ (Real.exp_pos t)]
      have he : (N : ℝ) / Real.exp t = a := by
        dsimp only [a]
        rw [div_eq_mul_inv, ← Real.exp_neg]
      rw [he]
    rw [hmul, ← Nat.floor_lt ha]
    omega
  rw [hset, Nat.card_Ioc, Nat.cast_sub hfN]
  have hlo := Nat.sub_one_lt_floor a
  have hexp := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-t)) (Nat.cast_nonneg (α := ℝ) N)
  dsimp only [a] at hlo ⊢
  nlinarith only [hlo, hexp]

/-- An interior uniform estimate and a terminal-strip envelope control the normalized square
mean on any fixed terminal fraction. -/
lemma normalized_sum_le_of_terminal_strip {N : ℕ} (hN : 1 ≤ N)
    {δ t a b : ℝ} (ht : 0 ≤ t) {E : ℕ → ℝ}
    (he : ∀ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N, E n ≤ b ^ 2)
    (hi : ∀ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (n : ℝ) * Real.exp t ≤ N → E n ≤ a ^ 2) :
    (∑ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N, E n) / N ≤
      a ^ 2 + (t + 1 / N) * b ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let S := Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N
  let T := (Finset.Icc 1 N).filter (fun n : ℕ => (N : ℝ) < (n : ℝ) * Real.exp t)
  have hpoint : ∀ n ∈ S, E n ≤ a ^ 2 + if n ∈ T then b ^ 2 else 0 := by
    intro n hn
    have hnI : n ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr
      ⟨by have := (Finset.mem_Ioc.mp hn).1; omega, (Finset.mem_Ioc.mp hn).2⟩
    by_cases hlate : n ∈ T
    · rw [if_pos hlate]
      exact (he n hn).trans (le_add_of_nonneg_left (sq_nonneg a))
    · rw [if_neg hlate, add_zero]
      exact hi n hn (le_of_not_gt (fun h => hlate (mem_filter.mpr ⟨hnI, h⟩)))
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, ← sum_filter, sum_const, nsmul_eq_mul] at hsum
  have hcardS : (S.card : ℝ) ≤ N := by
    dsimp only [S]
    rw [Nat.card_Ioc]
    exact_mod_cast Nat.sub_le N ⌊δ * (N : ℝ)⌋₊
  have hcardT : ((S.filter (fun n => n ∈ T)).card : ℝ) ≤ N * t + 1 := by
    have hsub : S.filter (fun n => n ∈ T) ⊆ T := fun _ h => (mem_filter.mp h).2
    exact (by exact_mod_cast Finset.card_le_card hsub : ((S.filter (fun n => n ∈ T)).card : ℝ) ≤ T.card).trans
      (card_terminal_exponential_strip_le ht)
  have hb := hsum.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcardS (sq_nonneg a))
    (mul_le_mul_of_nonneg_right hcardT (sq_nonneg b)))
  exact (div_le_div_of_nonneg_right hb hN0.le).trans_eq (by field_simp [hN0.ne'])

#print axioms abs_closed_logarithmic_row_sum_sub_mean_le
#print axioms normalized_sum_le_of_terminal_strip
#print axioms abs_sum_Ioc_floor_sub_integral_le
#print axioms abs_logarithmic_row_sub_le
#print axioms abs_logarithmic_row_sum_sub_mean_le
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
