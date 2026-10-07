import GaloisForLFunctions.RHTower.WeilConeBoundaryMobiusAveraging
import GaloisForLFunctions.RHTower.WeilZetaSquareRegularPartRigidity
import GaloisForLFunctions.RHTower.AbsolutelyConvergentZetaSignRigidity
import GaloisForLFunctions.RHTower.WeilConeBoundaryDilationRigidity

/-!
# Uniqueness of Weil-positive systems in the boundary class with a Möbius part

Let `a, f, v : ℕ → ℝ` with `Σ (|a(n)| + |f(n)|) n^{−½} (1 + log n) < ∞`, `Σ |v(n)| n^{−½} < ∞`,
`f(1) = 0` and `v(0) = v(1) = 0`. The Dirichlet series `A`, `F`, `V` converge absolutely on
`Re s ≥ ½` and need not continue past the critical line.

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_mobius_boundary`). If
`λ = Λ ⋆ a + μ ⋆ f + v` is full-cone Weil-positive, then `a = δ₁`, `f = 0`, `v = 0`, so `λ = Λ`.
Hence RH holds (`riemannHypothesis_of_weilPositiveFull_mobius_boundary`), and within the class a
Weil-positive system exists iff RH (`exists_mobiusBoundary_weilPositive_iff`).

**Proof.**
* *`a = δ₁`.* For `m ≥ 1` and `c = ±1`, the averaged boundary inequality gives
  `∫ ω_L W (1 − Re A) |ζ|² ≥ −K L` with `W = |1 + c m^{it}|²` (`exists_averaged_ge_boundary`).
  Truncate `Re A` at `N`; the tail costs `4 τ_N ∫ ω_L |ζ|²` with `τ_N = Σ_{n ≥ N} |a(n)| n^{−½}`.
  The twisted second moments of `ζ` turn the truncated integral into `B(c, m) W(L) + O(L)`,
  where `B(c, m) = (1 + c²)(1 − A(1)) + c m^{−½}(2 − Σ a(n)(1 + gcd(m, n))/n)`. Since
  `W(L) ≥ L log L`, this forces `B(c, m) ≥ 0`. With `A(1) = 1` and `c = ±1`, this says
  `Σ a(n) gcd(m, n)/n = 1` for all `m`. Gcd inversion applied to `a − δ₁` then gives `a = δ₁`.
* *`v = 0`.* With `A ≡ 1` the boundary inequality reads `Re V |ζ|² + Re(F ζ̄) ≤ 0` on the line;
  the Möbius de-tilted second moments give `v = 0`
  (`WeilZetaSquare.eq_zero_of_re_regular_le_of_summable`).
* *`f = 0`.* Then `Re(F ζ̄) ≤ 0` on the line, and the `K!`-Möbius weight together with the
  uniform twisted first moment gives `f = 0`
  (`ZetaUniformMoment.eq_zero_of_re_mul_conj_zeta_nonpos`).

No step uses analyticity across the critical line, zero counting or discrete moments of `ζ′`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open RHTower.WeilSpectral RHTower.WeilHerglotz RHTower.WeilFiniteType RHTower.WeilInfiniteDilation
open RHTower.WeilZetaSquare

namespace RHTower.WeilBoundaryMobius

open RHTower.WeilBoundaryDilation (HalfSummable BoundaryRegular regSeries)

variable {a f v : ℕ → ℝ}

/-! ## The real part of the dilation series on the line -/

theorem summable_abs_div_sqrt_of_half {x : ℕ → ℝ}
    (h : LSeriesSummable (fun n => (x n : ℂ)) (1 / 2)) :
    Summable fun n => |x n| / Real.sqrt n := by
  refine (summable_norm_iff.mpr h).congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [LSeries.norm_term_eq, if_neg hn.ne', Complex.norm_real, Real.norm_eq_abs,
    Real.sqrt_eq_rpow]
  norm_num

theorem summable_coeff_half (ha : HalfSummable a) : Summable fun n => |a n / Real.sqrt n| :=
  (summable_abs_div_sqrt_of_half ha.half).congr fun n => by
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]

/-- `Re A(½+it) = Σ a(n) n^{−1/2} cos(t log n)`. -/
theorem re_dilSeries_line_boundary (ha : HalfSummable a) (t : ℝ) :
    (dilSeries a (linePt t)).re = ∑' n, a n / Real.sqrt n * Real.cos (Real.log n * t) := by
  have hs : LSeriesSummable (fun n => (a n : ℂ)) (linePt t) :=
    WeilBoundaryDilation.summable_of_half ha (by rw [linePt_re])
  unfold dilSeries LSeries
  rw [Complex.re_tsum hs]
  exact tsum_congr fun n => re_term_line a t n

theorem tendsto_tailN_boundary (a : ℕ → ℝ) : Tendsto (tailN a) atTop (𝓝 0) :=
  tendsto_sum_nat_add (f := fun n => |a n / Real.sqrt n|)

theorem abs_re_sub_reAN_le_boundary (ha : HalfSummable a) (N : ℕ) (t : ℝ) :
    |(dilSeries a (linePt t)).re - reAN a N t| ≤ tailN a N := by
  have hs := summable_coeff_half ha
  have hsc : Summable fun n => a n / Real.sqrt n * Real.cos (Real.log n * t) :=
    Summable.of_norm_bounded hs fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [re_dilSeries_line_boundary ha, reAN, ← hsc.sum_add_tsum_nat_add N, add_sub_cancel_left]
  have hs' : Summable fun n => |a (n + N) / Real.sqrt ((n + N : ℕ) : ℝ)| :=
    (summable_nat_add_iff N).mpr hs
  have hFG : ∀ n, ‖a (n + N) / Real.sqrt ((n + N : ℕ) : ℝ) *
      Real.cos (Real.log ((n + N : ℕ) : ℝ) * t)‖ ≤ |a (n + N) / Real.sqrt ((n + N : ℕ) : ℝ)| := by
    intro n
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hF : Summable fun n => ‖a (n + N) / Real.sqrt ((n + N : ℕ) : ℝ) *
      Real.cos (Real.log ((n + N : ℕ) : ℝ) * t)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hFG hs'
  rw [← Real.norm_eq_abs]
  exact (norm_tsum_le_tsum_norm hF).trans (Summable.tsum_le_tsum hFG hF hs')

theorem abs_coeffB_sub_coeffBN_le_boundary (ha : HalfSummable a) {c : ℝ} (hc : |c| ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) (N : ℕ) : |coeffB a c m - coeffBN a c m N| ≤ 4 * tailN a N := by
  have hs := summable_coeff_half ha
  have hbound : ∀ n, |a n / Real.sqrt n * coeffTerm c m n| ≤ 4 * |a n / Real.sqrt n| := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_coeffTerm_le hc hm hn) (abs_nonneg _)
  have hsc : Summable fun n => a n / Real.sqrt n * coeffTerm c m n :=
    Summable.of_norm_bounded (hs.mul_left 4) fun n => by rw [Real.norm_eq_abs]; exact hbound n
  unfold coeffB coeffBN
  rw [← hsc.sum_add_tsum_nat_add N]
  have e : 1 + c ^ 2 + 2 * c / Real.sqrt m - (∑ n ∈ Finset.range N, a n / Real.sqrt n *
      coeffTerm c m n + ∑' n, a (n + N) / Real.sqrt (n + N : ℕ) * coeffTerm c m (n + N)) -
      (1 + c ^ 2 + 2 * c / Real.sqrt m - ∑ n ∈ Finset.range N, a n / Real.sqrt n *
        coeffTerm c m n) = -∑' n, a (n + N) / Real.sqrt (n + N : ℕ) * coeffTerm c m (n + N) := by
    ring
  rw [e, abs_neg, tailN, ← tsum_mul_left]
  have hs' := (summable_nat_add_iff N).mpr hs
  refine (norm_tsum_le_tsum_norm ((summable_nat_add_iff N).mpr hsc).norm).trans ?_
  exact Summable.tsum_le_tsum (fun n => hbound (n + N)) ((summable_nat_add_iff N).mpr hsc).norm
    (hs'.mul_left 4)

/-- `|∫ ω W (1 − Re A) Z − ∫ ω W (1 − A_N) Z| ≤ 4 τ_N ∫ ω Z`. -/
theorem abs_integral_sub_truncated_le_boundary (ha : HalfSummable a) {L : ℝ} (hL : 0 < L)
    {c : ℝ} (hc : |c| ≤ 1) (m N : ℕ) :
    |(∫ t, win L t * (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) * zsq t)) -
        ∫ t, win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t)| ≤
      4 * tailN a N * ∫ t, win L t * zsq t := by
  have cR : Continuous fun t : ℝ => (dilSeries a (linePt t)).re :=
    Complex.continuous_re.comp (WeilBoundaryDilation.continuous_lineSeries ha)
  have cW := continuous_twoPointWeight c m
  have i1 : Integrable fun t => win L t *
      (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) * zsq t) :=
    integrable_win_mul hL ((cW.mul (continuous_const.sub cR)).mul continuous_zsq)
  have i2 : Integrable fun t => win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t) :=
    integrable_win_mul hL ((cW.mul (continuous_const.sub (continuous_reAN a N))).mul
      continuous_zsq)
  have i3 : Integrable fun t => 4 * tailN a N * (win L t * zsq t) :=
    (integrable_win_mul hL continuous_zsq).const_mul _
  rw [← integral_sub i1 i2, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono (i1.sub i2).abs i3 fun t => ?_)
  have hw := blockWindow_nonneg L (2 * L) (L / 2) t
  have hW0 := twoPointWeight_nonneg hc m t
  have hW1 := twoPointWeight_le hc m t
  have hz := zsq_nonneg t
  have hd := abs_re_sub_reAN_le_boundary ha N t
  have e : win L t * (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) * zsq t) -
      win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t) =
      win L t * twoPointWeight c m t * zsq t * (reAN a N t - (dilSeries a (linePt t)).re) := by
    ring
  rw [e, abs_mul, abs_of_nonneg (by positivity), abs_sub_comm]
  have hτ := tailN_nonneg a N
  calc win L t * twoPointWeight c m t * zsq t * |(dilSeries a (linePt t)).re - reAN a N t|
      ≤ win L t * 4 * zsq t * tailN a N := by gcongr
    _ = 4 * tailN a N * (win L t * zsq t) := by ring

/-! ## `B(c, m) ≥ 0` and `a = δ₁` -/

/-- **`B(c, m) ≥ 0`** for `|c| ≤ 1`, `m ≥ 1`. -/
theorem coeffB_nonneg_boundary (ha : HalfSummable a) (hla : LogHalfSummable a)
    (hf : HalfSummable f) (hf1 : f 1 = 0)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) {c : ℝ} (hc : |c| ≤ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ coeffB a c m := by
  by_contra hneg
  push Not at hneg
  set β := -coeffB a c m with hβdef
  have hβ : 0 < β := by linarith
  obtain ⟨K, hK⟩ := exists_averaged_ge_boundary ha hla hf hf1 hv hW hc hm
  obtain ⟨C, hC, hmainN⟩ := exists_abs_integral_truncated_sub_le
  obtain ⟨K₀, hK₀, hmom⟩ := exists_momentRe_zero_le
  have hτpos : 0 < β / (16 * (4 + K₀)) := by positivity
  obtain ⟨N, hN⟩ := ((tendsto_order.1 (tendsto_tailN_boundary a)).2 _ hτpos).exists
  set τ := tailN a N with hτdef
  have hτ0 : 0 ≤ τ := tailN_nonneg a N
  set E := errN a m N
  have hE0 : 0 ≤ E := errN_nonneg a m N
  -- a large aperture
  obtain ⟨L, hL32, hLlog⟩ : ∃ L : ℝ, 32 ≤ L ∧ (4 * (K + C * E) + 1) / β < Real.log L := by
    obtain ⟨L, hL⟩ := ((Real.tendsto_log_atTop.eventually_gt_atTop ((4 * (K + C * E) + 1) / β)).and
      (eventually_ge_atTop (32 : ℝ))).exists
    exact ⟨L, hL.2, hL.1⟩
  have hL0 : 0 < L := by linarith
  have hL16 : 16 ≤ L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos (by linarith)
  set Wl := (ZetaNotch.logWindow L).re
  have hWl : L * Real.log L ≤ Wl := WeilFiniteSupport.re_logWindow_ge (by linarith)
  have hI := hK hL32
  have hTr := abs_integral_sub_truncated_le_boundary ha hL0 hc m N
  have hMain : |(∫ t, win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t)) -
      coeffBN a c m N * (ZetaNotch.logWindow L).re| ≤ C * L * errN a m N := hmainN a hc hm N hL16
  have hBN := abs_coeffB_sub_coeffBN_le_boundary ha hc hm N
  have hM0 : ∫ t, win L t * zsq t ≤ K₀ * L * Real.log L := by
    rw [← momentRe_zero_eq]; exact hmom hL16
  set I := ∫ t, win L t * (twoPointWeight c m t * (1 - (dilSeries a (linePt t)).re) * zsq t)
  set IN := ∫ t, win L t * (twoPointWeight c m t * (1 - reAN a N t) * zsq t)
  have h1 : I ≤ IN + 4 * τ * (K₀ * L * Real.log L) := by
    have := (abs_le.mp hTr).2
    have h4 : 4 * τ * ∫ t, win L t * zsq t ≤ 4 * τ * (K₀ * L * Real.log L) :=
      mul_le_mul_of_nonneg_left hM0 (by positivity)
    linarith
  have h2 : IN ≤ coeffBN a c m N * Wl + C * L * E := by
    have := (abs_le.mp hMain).2; linarith
  have h3 : coeffBN a c m N ≤ -β + 4 * τ := by
    have := (abs_le.mp hBN).1; linarith
  have hτ1 : 4 * τ ≤ β / 2 := by
    have : τ ≤ β / (16 * (4 + K₀)) := hN.le
    have h' : β / (16 * (4 + K₀)) ≤ β / 64 :=
      div_le_div_of_nonneg_left hβ.le (by norm_num) (by nlinarith)
    linarith
  have hτ2 : 4 * τ * K₀ ≤ β / 4 := by
    have : τ ≤ β / (16 * (4 + K₀)) := hN.le
    have h' : 4 * τ * K₀ ≤ 4 * (β / (16 * (4 + K₀))) * K₀ := by
      have := mul_le_mul_of_nonneg_right this hK₀; nlinarith
    have h'' : 4 * (β / (16 * (4 + K₀))) * K₀ ≤ β / 4 := by
      rw [show 4 * (β / (16 * (4 + K₀))) * K₀ = β / 4 * (K₀ / (4 + K₀)) by field_simp; ring]
      have : K₀ / (4 + K₀) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
      nlinarith
    linarith
  have hWl0 : 0 ≤ Wl := le_trans (by positivity) hWl
  have h4 : coeffBN a c m N * Wl ≤ -(β / 2) * (L * Real.log L) := by
    have : coeffBN a c m N ≤ -(β / 2) := by linarith
    have hb2 : 0 ≤ β / 2 := by positivity
    nlinarith
  have hLL : 0 < L * Real.log L := by positivity
  have hfin : β / 4 * (L * Real.log L) ≤ (K + C * E) * L := by
    have := hI
    have hτK : 4 * τ * (K₀ * L * Real.log L) ≤ β / 4 * (L * Real.log L) := by
      have := mul_le_mul_of_nonneg_right hτ2 hLL.le
      nlinarith
    nlinarith
  have hcontra : β / 4 * Real.log L ≤ K + C * E := by
    have := hfin
    rw [show β / 4 * (L * Real.log L) = (β / 4 * Real.log L) * L by ring] at this
    exact le_of_mul_le_mul_right this hL0
  have hlog' : 4 * (K + C * E) + 1 < β * Real.log L := by
    rw [div_lt_iff₀ hβ] at hLlog; linarith
  linarith

theorem summable_a_div_boundary (ha : HalfSummable a) :
    Summable fun n => |a n| / Real.sqrt n := by
  refine (summable_coeff_half ha).congr fun n => ?_
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem summable_a_gcd_div_boundary (ha : HalfSummable a) {m : ℕ} (hm : 0 < m) :
    Summable fun n => a n * (Nat.gcd m n : ℝ) / n := by
  refine Summable.of_norm_bounded ((summable_a_div_boundary ha).mul_left (m + 1 : ℝ)) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hg : (Nat.gcd m n : ℝ) ≤ m + 1 := by
    have : Nat.gcd m n ≤ m + 1 := (Nat.gcd_le_left n hm).trans (Nat.le_succ m)
    exact_mod_cast this
  rw [Real.norm_eq_abs, abs_div, abs_mul, Nat.abs_cast, Nat.abs_cast]
  have hsn : Real.sqrt n ≤ n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  calc |a n| * (Nat.gcd m n : ℝ) / n ≤ |a n| * (m + 1) / Real.sqrt n := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hg (abs_nonneg _)) hsn0 hsn
    _ = (m + 1 : ℝ) * (|a n| / Real.sqrt n) := by ring

theorem summable_a_div_n_boundary (ha : HalfSummable a) :
    Summable fun n => a n / n := by
  refine (summable_a_gcd_div_boundary ha one_pos).congr fun n => ?_
  simp

/-- `A(1) = Σ a(n)/n = 1`. -/
theorem tsum_a_div_eq_one_boundary (ha : HalfSummable a)
    (hf : HalfSummable f) (hf1 : f 1 = 0)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) :
    ∑' n, a n / n = 1 := by
  have h := dilSeries_one_eq_one_boundary ha hf hf1 hv hW
  have hs : LSeriesSummable (fun n => (a n : ℂ)) 1 := summable_of_le_re ha (by norm_num)
  have hre := congrArg Complex.re h
  unfold dilSeries LSeries at hre
  rw [Complex.re_tsum hs, Complex.one_re] at hre
  rw [← hre]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn.ne', Complex.cpow_one, ← Complex.ofReal_natCast,
    ← Complex.ofReal_div, Complex.ofReal_re]

/-- `B(c, m) = (1 + c²)(1 − Σ a(n)/n) + (c/√m)(2 − Σ a(n)/n − Σ a(n) gcd(m,n)/n)`. -/
theorem coeffB_eq_boundary (ha : HalfSummable a) (c : ℝ) {m : ℕ}
    (hm : 1 ≤ m) :
    coeffB a c m = (1 + c ^ 2) * (1 - ∑' n, a n / n) +
      c / Real.sqrt m * (2 - ∑' n, a n / n - ∑' n, a n * (Nat.gcd m n : ℝ) / n) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hmR
  have hpt : ∀ n, a n / Real.sqrt n * coeffTerm c m n =
      (1 + c ^ 2) * (a n / n) + c / Real.sqrt m * (a n / n + a n * (Nat.gcd m n : ℝ) / n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
    have hnn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnR.le
    unfold coeffTerm
    rw [Real.sqrt_mul hmR.le]
    generalize Real.sqrt (n : ℝ) = r at hnn hsn ⊢
    rw [← hnn]
    field_simp
    ring
  have hu := summable_a_div_n_boundary ha
  have hg := summable_a_gcd_div_boundary ha (by omega : 0 < m)
  unfold coeffB
  rw [tsum_congr hpt, Summable.tsum_add (hu.mul_left _) ((hu.add hg).mul_left _), tsum_mul_left,
    tsum_mul_left, Summable.tsum_add hu hg]
  field_simp
  ring

/-- **`Σ_n a(n) gcd(m, n)/n = 1`** for every `m ≥ 1`. -/
theorem tsum_a_gcd_div_eq_one_boundary (ha : HalfSummable a) (hla : LogHalfSummable a)
    (hf : HalfSummable f) (hf1 : f 1 = 0)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) {m : ℕ} (hm : 1 ≤ m) :
    ∑' n, a n * (Nat.gcd m n : ℝ) / n = 1 := by
  have hS1 := tsum_a_div_eq_one_boundary ha hf hf1 hv hW
  have h1 := coeffB_nonneg_boundary ha hla hf hf1 hv hW (c := 1) (by norm_num) hm
  have h2 := coeffB_nonneg_boundary ha hla hf hf1 hv hW (c := -1) (by norm_num) hm
  rw [coeffB_eq_boundary ha _ hm, hS1] at h1 h2
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  set G := ∑' n, a n * (Nat.gcd m n : ℝ) / n
  have h1' : 0 ≤ 1 - G := by
    have : 0 ≤ 1 / Real.sqrt m * (2 - 1 - G) := by linarith
    have := (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 1 / Real.sqrt m)).mp this
    linarith
  have h2' : 0 ≤ G - 1 := by
    have : 0 ≤ 1 / Real.sqrt m * (G - 1) := by
      have e : (1 + (-1 : ℝ) ^ 2) * (1 - 1) + -1 / Real.sqrt m * (2 - 1 - G) =
          1 / Real.sqrt m * (G - 1) := by ring
      linarith
    exact (mul_nonneg_iff_of_pos_left (by positivity : (0 : ℝ) < 1 / Real.sqrt m)).mp this
  linarith

/-- **Dilation rigidity in the boundary class with a Möbius part.** If `Λ ⋆ a + μ ⋆ f + v` is
full-cone Weil-positive, with `Σ |a(n)| n^{−½}(1 + log n) < ∞`, `Σ |f(n)| n^{−½} < ∞`,
`f(1) = 0` and `v` regular on `Re s ≥ ½`, then `a = δ₁`. -/
theorem eq_delta_of_weilPositiveFull_boundary (ha : HalfSummable a) (hla : LogHalfSummable a)
    (hf : HalfSummable f) (hf1 : f 1 = 0)
    (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) :
    a 1 = 1 ∧ ∀ n, 2 ≤ n → a n = 0 := by
  classical
  set b : ℕ → ℝ := fun n => a n - if n = 1 then 1 else 0 with hb
  have hbs : Summable fun n => |b n| / Real.sqrt n := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_a_div_boundary ha).add (summable_of_ne_finset_zero (s := {1})
        (f := fun n : ℕ => if n = 1 then (1 : ℝ) else 0) fun n hn => by simp at hn; simp [hn]))
    by_cases h1 : n = 1
    · subst h1
      simp only [hb, ite_true, Nat.cast_one, Real.sqrt_one, div_one]
      have := abs_sub (a 1) 1
      rw [abs_one] at this
      linarith
    · simp only [hb, if_neg h1, sub_zero, add_zero, le_refl]
  have hzero : ∀ m, 0 < m → ∑' n, b n * (Nat.gcd m n : ℝ) / n = 0 := by
    intro m hm
    have hG := tsum_a_gcd_div_eq_one_boundary ha hla hf hf1 hv hW (m := m) hm
    have hδs : Summable fun n : ℕ => (if n = 1 then (1 : ℝ) else 0) * (Nat.gcd m n : ℝ) / n :=
      summable_of_ne_finset_zero (s := {1}) fun n hn => by simp at hn; simp [hn]
    have e : (fun n => b n * (Nat.gcd m n : ℝ) / n) = fun n =>
        a n * (Nat.gcd m n : ℝ) / n - (if n = 1 then (1 : ℝ) else 0) * (Nat.gcd m n : ℝ) / n := by
      funext n; simp only [hb]; ring
    rw [e, Summable.tsum_sub (summable_a_gcd_div_boundary ha hm) hδs, hG,
      tsum_eq_single 1 (fun n hn => by simp [hn])]
    simp
  have hb0 := eq_zero_of_tsum_gcd_mul_div_eq_zero hbs hzero
  refine ⟨?_, fun n hn => ?_⟩
  · have := hb0 1 one_pos
    simp only [hb, ite_true] at this
    linarith
  · have := hb0 n (by omega)
    simp only [hb, if_neg (show n ≠ 1 by omega), sub_zero] at this
    exact this


/-! ## The regular and Möbius parts -/

theorem halfSummable_delta : HalfSummable (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) := by
  refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
  have : n ≠ 1 := by simpa using hn
  simp [LSeries.term, this]

theorem dilSeries_delta (s : ℂ) :
    dilSeries (fun n : ℕ => if n = 1 then (1 : ℝ) else 0) s = 1 := by
  unfold dilSeries LSeries
  rw [tsum_eq_single 1 fun n hn => by simp [LSeries.term, hn]]
  simp [LSeries.term]

/-- `Σ |x(n)| n^{−½} < ∞` and `Σ |x(n)| log n · n^{−½} < ∞` give the log moment. -/
theorem logMomentSummable_of_half {x : ℕ → ℝ}
    (hx : LSeriesSummable (fun n => (x n : ℂ)) (1 / 2))
    (hlx : LSeriesSummable (LSeries.logMul fun n => (x n : ℂ)) (1 / 2)) :
    ZetaUniformMoment.LogMomentSummable x := by
  refine (hx.norm.add hlx.norm).congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn.ne', if_neg hn.ne']
  simp only [LSeries.logMul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    ← Complex.natCast_log, abs_of_nonneg hlog]
  rw [show ((1 / 2 : ℂ)).re = 1 / 2 by norm_num, Real.rpow_neg hn0.le]
  field_simp

theorem halfSummable_of_half {x : ℕ → ℝ} (hx : LSeriesSummable (fun n => (x n : ℂ)) (1 / 2)) :
    HalfSummable x := by
  have e : ((1 / 2 - 0 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
  show LSeriesSummable _ _
  rw [e]; exact hx

/-- **The regular and Möbius parts vanish once `a = δ₁`.** -/
theorem moebiusPart_regularPart_eq_zero_boundary (hlf : ZetaUniformMoment.LogMomentSummable f)
    (hf : HalfSummable f) (hf1 : f 1 = 0) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (finiteTypeSeq (fun n => if n = 1 then 1 else 0) f v)) :
    (∀ n, 1 ≤ n → f n = 0) ∧ ∀ n, v n = 0 := by
  have hb : ∀ t, (regSeries v (linePt t)).re * zsq t +
      (dilSeries f (linePt t) * conj (riemannZeta (linePt t))).re ≤ 0 := by
    intro t
    have h := re_boundary_ge_boundary halfSummable_delta hf hf1 hv hW t
    rw [dilSeries_delta, sub_self, zero_mul, zero_mul, Complex.zero_re] at h
    exact h
  have hv1 : ∀ n, 1 ≤ n → v n = 0 :=
    eq_zero_of_re_regular_le_of_summable (summable_abs_div_sqrt_of_half hv.summable) hv.one
      (summable_abs_div_sqrt_of_half hf.half) fun t _ => hb t
  have hv0 : ∀ n, v n = 0 := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hv.zero
    · exact hv1 n hn
  have hV : ∀ t, regSeries v (linePt t) = 0 := by
    intro t
    have : (fun n => (v n : ℂ)) = 0 := funext fun n => by simp [hv0 n]
    simp only [regSeries, this, LSeries_zero, Pi.zero_apply]
  refine ⟨ZetaUniformMoment.eq_zero_of_re_mul_conj_zeta_nonpos hlf hf1 fun y _ => ?_, hv0⟩
  have h := hb y
  rw [hV, Complex.zero_re, zero_mul, zero_add] at h
  have hl : linePt y = (1 / 2 : ℂ) + y * I := by simp [linePt]
  rw [hl] at h
  exact h

/-! ## Uniqueness and RH -/

/-- **Uniqueness in the boundary class with a Möbius part.** If `Λ ⋆ a + μ ⋆ f + v` is full-cone
Weil-positive, with `Σ (|a(n)| + |f(n)|) n^{−½}(1 + log n) < ∞`, `f(1) = 0` and `v` regular on
the closed half-plane `Re s ≥ ½`, then it equals `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_mobius_boundary
    (ha : LSeriesSummable (fun n => (a n : ℂ)) (1 / 2)) (hla : LogHalfSummable a)
    (hf : LSeriesSummable (fun n => (f n : ℂ)) (1 / 2)) (hlf : LogHalfSummable f)
    (hf1 : f 1 = 0) (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) :
    finiteTypeSeq a f v = fun n => (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have ha' := halfSummable_of_half ha
  have hf' := halfSummable_of_half hf
  obtain ⟨h1, h2⟩ := eq_delta_of_weilPositiveFull_boundary ha' hla hf' hf1 hv hW
  rw [finiteTypeSeq_eq_delta_left h1 h2] at hW ⊢
  obtain ⟨hf0, hv0⟩ := moebiusPart_regularPart_eq_zero_boundary (logMomentSummable_of_half hf hlf)
    hf' hf1 hv hW
  have he : finiteTypeSeq (fun n => if n = 1 then 1 else 0) f v =
      finiteTypeSeq (fun n => if n = 1 then 1 else 0) (fun _ => 0) (fun _ => 0) := by
    funext n
    unfold finiteTypeSeq
    rw [hv0 n]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp2 : 1 ≤ p.2 := by
      obtain ⟨hmul, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      rcases Nat.eq_zero_or_pos p.2 with h | h
      · rw [h, mul_zero] at hmul; exact absurd hmul.symm hn
      · exact h
    rw [hf0 _ hp2]
  rw [he, WeilFiniteType.finiteTypeSeq_delta_zero_zero]

/-- **A boundary-class Weil-positive system with a Möbius part forces RH.** -/
theorem riemannHypothesis_of_weilPositiveFull_mobius_boundary
    (ha : LSeriesSummable (fun n => (a n : ℂ)) (1 / 2)) (hla : LogHalfSummable a)
    (hf : LSeriesSummable (fun n => (f n : ℂ)) (1 / 2)) (hlf : LogHalfSummable f)
    (hf1 : f 1 = 0) (hv : BoundaryRegular v) (hW : WeilPositiveFull (finiteTypeSeq a f v)) :
    RiemannHypothesis := by
  rw [eq_vonMangoldt_of_weilPositiveFull_mobius_boundary ha hla hf hlf hf1 hv hW] at hW
  exact riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr hW

/-- **Within the boundary class with a Möbius part, a Weil-positive system exists iff RH.** The
class consists of `Λ ⋆ a + μ ⋆ f + v` with `Σ (|a(n)| + |f(n)|) n^{−½}(1 + log n) < ∞`,
`f(1) = 0`, `v(0) = v(1) = 0` and `Σ |v(n)| n^{−½} < ∞`. -/
theorem exists_mobiusBoundary_weilPositive_iff :
    (∃ a f v : ℕ → ℝ, LSeriesSummable (fun n => (a n : ℂ)) (1 / 2) ∧ LogHalfSummable a ∧
      LSeriesSummable (fun n => (f n : ℂ)) (1 / 2) ∧ LogHalfSummable f ∧ f 1 = 0 ∧
      BoundaryRegular v ∧ WeilPositiveFull (finiteTypeSeq a f v)) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨a, f, v, ha, hla, hf, hlf, hf1, hv, hW⟩
    exact riemannHypothesis_of_weilPositiveFull_mobius_boundary ha hla hf hlf hf1 hv hW
  · intro hRH
    have hW := riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH
    refine ⟨fun n => if n = 1 then 1 else 0, 0, 0, ?_, ?_, ?_, ?_, rfl,
      WeilBoundaryDilation.boundaryRegular_zero, ?_⟩
    · refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, this]
    · refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
      have : n ≠ 1 := by simpa using hn
      simp [LSeries.term, LSeries.logMul, this]
    · have h : (fun n => (((0 : ℕ → ℝ) n : ℝ) : ℂ)) = 0 := by funext n; simp
      rw [h]; exact LSeriesSummable_zero
    · have h : (fun n => (((0 : ℕ → ℝ) n : ℝ) : ℂ)) = 0 := by funext n; simp
      show LSeriesSummable (LSeries.logMul fun n => (((0 : ℕ → ℝ) n : ℝ) : ℂ)) (1 / 2)
      rw [h]
      have h0 : LSeries.logMul (0 : ℕ → ℂ) = 0 := by funext n; simp [LSeries.logMul]
      rw [h0]; exact LSeriesSummable_zero
    · have e0 : (0 : ℕ → ℝ) = fun _ => 0 := rfl
      rw [e0, WeilFiniteType.finiteTypeSeq_delta_zero_zero]
      exact hW

end RHTower.WeilBoundaryMobius
