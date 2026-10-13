import GaloisForLFunctions.RHTower.CosDilationCumulativeAutocorrRigidity

/-!
# Cumulative Autocorrelation Excursion Rigidity and General Window Unfolding

Let `f : ℝ → ℝ` be a continuous core supported in `[α, β] ⊂ (0, ∞)` (`0 < α ≤ β`) with zero
mean `∫_{y > 0} f(y) dy = 0`, and let `C_f(u) := ∫ r in 0..u, A_f(r) dr` be its cumulative
dilation autocorrelation.

In `CosDilationCumulativeAutocorrRigidity` we proved the exact weighted cumulative laws
`∫ u in α/β..1, C_f(u) / u² du = -2 * C_f(1)` and `∫ u in 1..β/α, C_f(u) / u² du = 2 * C_f(1)`.
Combining these with the exact weight integrals `∫ u in α/β..1, 1 / u² du = β / α - 1` and
`∫ u in 1..β/α, 1 / u² du = 1 - α / β < 1` yields sharp excursion bounds that hold for
arbitrary support ratio `β / α`:

* **Upper excursion bound on `[1, β/α]`** (`two_mul_intervalIntegral_zero_one_le_of_forall_le_on_Icc`):
  if `C_f(u) ≤ M` for all `u ∈ [1, β/α]`, then `2 * C_f(1) ≤ (1 - α / β) * M`.
* **Universal `2 C_f(1)` excursion rigidity** (`eq_zero_of_intervalIntegral_dilationAutocorr_le_two_mul_on_Icc`):
  although `C_f(1) = ∫_0^1 A_f` at `u = 1` and `C_f(β/α) = 0` at `u = β/α`, if
  `C_f(u) ≤ 2 * C_f(1)` (equivalently `∫ r in 1..u, A_f(r) dr ≤ ∫ r in 0..1, A_f(r) dr`) for all
  `u ∈ [1, β/α]`, then `f = 0` everywhere—for **any** `0 < α ≤ β` without support-ratio restriction.
* **Lower excursion bound on `[α/β, 1]`** (`two_mul_intervalIntegral_zero_one_le_of_forall_neg_le_on_Icc`):
  if `-M ≤ C_f(u)` for all `u ∈ [α/β, 1]`, then `2 * C_f(1) ≤ (β / α - 1) * M`.
* **Lower excursion rigidity for `β < 3α`**
  (`eq_zero_of_neg_intervalIntegral_zero_one_le_on_Icc_of_lt_three_mul`):
  if `β < 3α` and `-C_f(1) ≤ C_f(u)` for all `u ∈ [α/β, 1]`, then `f = 0` everywhere.
* **General symmetric window unfolding** (`cosDilationKernel_one_mul_sin_div_pi_eq_intervalIntegral`):
  for any blind core `f` with `Ψ_f(0) = 0` and any `c ∈ [0, 1/2]` satisfying `c ≤ α / β` and
  `β / α ≤ 3 - c`,
  `Ψ_f(1) * sin(2π c) / π = (∫ r in (1 - c)..(1 + c), A_f(r) dr) + (∫ r in (2 - c)..(2 + c), A_f(r) dr)`.
* **Complementary quarter-period unfolding on `[1/4, 1/2]`**
  (`neg_cosDilationKernel_one_div_pi_eq_intervalIntegral_of_le_nine_fourths`):
  for any blind core `f` with `Ψ_f(0) = 0` and `β ≤ (9/4) α`,
  `-Ψ_f(1) / π = (∫ r in 0..(3/4), A_f(r) dr) + (∫ r in (5/4)..(7/4), A_f(r) dr)`.
-/

open MeasureTheory Set Real Filter Topology

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### Exact `u⁻²` weight integrals and zero-mean excursion identities -/

/-- **Integral of `1 / u²` on `[a, b] ⊂ (0, ∞)`.** -/
theorem intervalIntegral_one_div_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u in a..b, (1 : ℝ) / u ^ 2 = a⁻¹ - b⁻¹ := by
  have hu_pos : ∀ u ∈ uIcc a b, 0 < u := fun u hu =>
    lt_of_lt_of_le (lt_min ha hb) hu.1
  have h_cont : ContinuousOn (fun u : ℝ => (1 : ℝ) / u ^ 2) (uIcc a b) :=
    continuousOn_const.div (continuousOn_id.pow 2) fun u hu =>
      pow_ne_zero 2 (hu_pos u hu).ne'
  have hderiv : ∀ u ∈ uIcc a b, HasDerivAt (fun x : ℝ => -x⁻¹) ((1 : ℝ) / u ^ 2) u := by
    intro u hu
    have hd := (hasDerivAt_inv (hu_pos u hu).ne').neg
    rw [neg_neg, one_div] at *
    exact hd
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv h_cont.intervalIntegrable
  linarith

/-- **Excursion upper bound on `[1, β/α]`.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
if `∫ r in 0..u, A_f(r) dr ≤ M` for all `u ∈ [1, β/α]`, then
`2 * ∫ r in 0..1, A_f(r) dr ≤ (1 - α / β) * M`. -/
theorem two_mul_intervalIntegral_zero_one_le_of_forall_le_on_Icc (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {M : ℝ}
    (hM : ∀ u ∈ Icc 1 (β / α), ∫ r in (0 : ℝ)..u, dilationAutocorr f r ≤ M) :
    2 * ∫ r in (0 : ℝ)..1, dilationAutocorr f r ≤ (1 - α / β) * M := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hle1 : 1 ≤ β / α := (one_le_div hα).mpr hαβ
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have hC_cont : Continuous fun u : ℝ => ∫ r in (0 : ℝ)..u, dilationAutocorr f r :=
    intervalIntegral.continuous_primitive hA_cont.intervalIntegrable 0
  have hu_pos : ∀ u ∈ uIcc 1 (β / α), 0 < u := by
    intro u hu
    rw [uIcc_of_le hle1] at hu
    exact lt_of_lt_of_le zero_lt_one hu.1
  have hi1 : IntervalIntegrable
      (fun u : ℝ => (∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2) volume 1 (β / α) :=
    (hC_cont.continuousOn.div (continuousOn_id.pow 2) fun u hu =>
      pow_ne_zero 2 (hu_pos u hu).ne').intervalIntegrable
  have hi2 : IntervalIntegrable (fun u : ℝ => M * ((1 : ℝ) / u ^ 2)) volume 1 (β / α) :=
    (continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2) fun u hu =>
      pow_ne_zero 2 (hu_pos u hu).ne')).intervalIntegrable
  have h_mono : ∫ u in (1 : ℝ)..(β / α), (∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2 ≤
      ∫ u in (1 : ℝ)..(β / α), M * ((1 : ℝ) / u ^ 2) := by
    refine intervalIntegral.integral_mono_on hle1 hi1 hi2 fun u hu => ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (hM u hu) (sq_nonneg u)
  rw [intervalIntegral_one_beta_div_alpha_div_sq_dilationAutocorr hf hα hαβ hsupp hmean,
    intervalIntegral.integral_const_mul,
    intervalIntegral_one_div_sq zero_lt_one (div_pos hβ0 hα), inv_one, inv_div] at h_mono
  linarith

/-- **Universal `2 C_f(1)` cumulative excursion rigidity on `[1, β/α]`.**
For **any** continuous core `f` supported in `[α, β]` (`0 < α ≤ β`, with no upper bound on `β / α`)
and `∫_{y > 0} f(y) dy = 0`, if `∫ r in 0..u, A_f(r) dr ≤ 2 * ∫ r in 0..1, A_f(r) dr` for all
`u ∈ [1, β/α]`, then `f = 0` everywhere. -/
theorem eq_zero_of_intervalIntegral_dilationAutocorr_le_two_mul_on_Icc (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    (hle : ∀ u ∈ Icc 1 (β / α),
      ∫ r in (0 : ℝ)..u, dilationAutocorr f r ≤ 2 * ∫ r in (0 : ℝ)..1, dilationAutocorr f r)
    (y : ℝ) : f y = 0 := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have h_bound := two_mul_intervalIntegral_zero_one_le_of_forall_le_on_Icc
    hf hα hαβ hsupp hmean hle
  have h_pos : 0 < α / β := div_pos hα hβ0
  have h_nonpos : ∫ r in (0 : ℝ)..1, dilationAutocorr f r ≤ 0 := by
    by_contra hgt
    have hC1_pos : 0 < ∫ r in (0 : ℝ)..1, dilationAutocorr f r := not_le.mp hgt
    have : 0 < (α / β) * (2 * ∫ r in (0 : ℝ)..1, dilationAutocorr f r) := by positivity
    linarith
  exact eq_zero_of_intervalIntegral_zero_one_dilationAutocorr_nonpos hf hα hαβ hsupp h_nonpos y

/-- **Equivalent right-excursion rigidity on `[1, β/α]`.**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
and `∫ r in 1..u, A_f(r) dr ≤ ∫ r in 0..1, A_f(r) dr` for all `u ∈ [1, β/α]`, then `f = 0`
everywhere. -/
theorem eq_zero_of_intervalIntegral_one_le_intervalIntegral_zero_one_on_Icc (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    (hle : ∀ u ∈ Icc 1 (β / α),
      ∫ r in (1 : ℝ)..u, dilationAutocorr f r ≤ ∫ r in (0 : ℝ)..1, dilationAutocorr f r)
    (y : ℝ) : f y = 0 := by
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  refine eq_zero_of_intervalIntegral_dilationAutocorr_le_two_mul_on_Icc
    hf hα hαβ hsupp hmean (fun u hu => ?_) y
  have h_adj := (intervalIntegral.integral_add_adjacent_intervals
    (hA_cont.intervalIntegrable (μ := volume) 0 1)
    (hA_cont.intervalIntegrable (μ := volume) 1 u)).symm
  have h_u := hle u hu
  linarith

/-- **Excursion lower bound on `[α/β, 1]`.**
For any continuous core `f` supported in `[α, β]` (`0 < α ≤ β`) with `∫_{y > 0} f(y) dy = 0`,
if `-M ≤ ∫ r in 0..u, A_f(r) dr` for all `u ∈ [α/β, 1]`, then
`2 * ∫ r in 0..1, A_f(r) dr ≤ (β / α - 1) * M`. -/
theorem two_mul_intervalIntegral_zero_one_le_of_forall_neg_le_on_Icc (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0) {M : ℝ}
    (hM : ∀ u ∈ Icc (α / β) 1, -M ≤ ∫ r in (0 : ℝ)..u, dilationAutocorr f r) :
    2 * ∫ r in (0 : ℝ)..1, dilationAutocorr f r ≤ (β / α - 1) * M := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hle1 : α / β ≤ 1 := (div_le_one hβ0).mpr hαβ
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have hC_cont : Continuous fun u : ℝ => ∫ r in (0 : ℝ)..u, dilationAutocorr f r :=
    intervalIntegral.continuous_primitive hA_cont.intervalIntegrable 0
  have hu_pos : ∀ u ∈ uIcc (α / β) 1, 0 < u := by
    intro u hu
    rw [uIcc_of_le hle1] at hu
    exact lt_of_lt_of_le (div_pos hα hβ0) hu.1
  have hi1 : IntervalIntegrable (fun u : ℝ => (-M) * ((1 : ℝ) / u ^ 2)) volume (α / β) 1 :=
    (continuousOn_const.mul (continuousOn_const.div (continuousOn_id.pow 2) fun u hu =>
      pow_ne_zero 2 (hu_pos u hu).ne')).intervalIntegrable
  have hi2 : IntervalIntegrable
      (fun u : ℝ => (∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2) volume (α / β) 1 :=
    (hC_cont.continuousOn.div (continuousOn_id.pow 2) fun u hu =>
      pow_ne_zero 2 (hu_pos u hu).ne').intervalIntegrable
  have h_mono : ∫ u in (α / β)..1, (-M) * ((1 : ℝ) / u ^ 2) ≤
      ∫ u in (α / β)..1, (∫ r in (0 : ℝ)..u, dilationAutocorr f r) / u ^ 2 := by
    refine intervalIntegral.integral_mono_on hle1 hi1 hi2 fun u hu => ?_
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (hM u hu) (sq_nonneg u)
  rw [intervalIntegral_alpha_div_beta_one_div_sq_dilationAutocorr hf hα hαβ hsupp hmean,
    intervalIntegral.integral_const_mul,
    intervalIntegral_one_div_sq (div_pos hα hβ0) zero_lt_one, inv_one, inv_div] at h_mono
  linarith

/-- **Lower excursion rigidity on `[α/β, 1]` for `β < 3α`.**
If `f` is continuous and supported in `[α, β]` (`0 < α ≤ β < 3α`) with `∫_{y > 0} f(y) dy = 0`,
and `-(∫ r in 0..1, A_f(r) dr) ≤ ∫ r in 0..u, A_f(r) dr` for all `u ∈ [α/β, 1]`, then `f = 0`
everywhere. -/
theorem eq_zero_of_neg_intervalIntegral_zero_one_le_on_Icc_of_lt_three_mul (hf : Continuous f)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < 3 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    (hle : ∀ u ∈ Icc (α / β) 1,
      -(∫ r in (0 : ℝ)..1, dilationAutocorr f r) ≤ ∫ r in (0 : ℝ)..u, dilationAutocorr f r)
    (y : ℝ) : f y = 0 := by
  have h_bound := two_mul_intervalIntegral_zero_one_le_of_forall_neg_le_on_Icc
    hf hα hαβ hsupp hmean hle
  have h_ratio : β / α < 3 := (div_lt_iff₀ hα).mpr hβ
  have h_nonpos : ∫ r in (0 : ℝ)..1, dilationAutocorr f r ≤ 0 := by
    by_contra hgt
    have hC1_pos : 0 < ∫ r in (0 : ℝ)..1, dilationAutocorr f r := not_le.mp hgt
    have : 0 < (3 - β / α) * ∫ r in (0 : ℝ)..1, dilationAutocorr f r :=
      mul_pos (by linarith) hC1_pos
    linarith
  exact eq_zero_of_intervalIntegral_zero_one_dilationAutocorr_nonpos hf hα hαβ hsupp h_nonpos y

/-! ### General symmetric window unfolding and complementary quarter-period unfolding -/

/-- **Pointwise four-term collapse on `[0, c]` when `c ≤ α / β` and `β / α ≤ 3 - c`.** -/
theorem tsum_dilationAutocorr_abs_eq_four_terms_on_Icc (hf : Continuous f)
    {α β c : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hc_lo : c ≤ α / β) (hc_hi : β / α ≤ 3 - c) (hc_half : c ≤ 1 / 2)
    {x : ℝ} (hx0 : 0 ≤ x) (hxc : x ≤ c) :
    (∑' k : ℤ, dilationAutocorr f |x + (k : ℝ)|) =
      dilationAutocorr f (1 - x) + dilationAutocorr f (1 + x) +
        dilationAutocorr f (2 - x) + dilationAutocorr f (2 + x) := by
  have hZ : ∀ r : ℝ, (r ≤ c ∨ 3 - c ≤ r) → dilationAutocorr f r = 0 := by
    intro r hr
    refine dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp fun h => ?_
    rcases hr with hr | hr
    · linarith [h.1]
    · linarith [h.2]
  rw [tsum_eq_sum (s := ({-2, -1, 1, 2} : Finset ℤ)) fun k hk => ?_]
  · rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    have h_m2 : |x + ((-2 : ℤ) : ℝ)| = 2 - x := by
      push_cast; rw [abs_of_neg (by linarith)]; ring
    have h_m1 : |x + ((-1 : ℤ) : ℝ)| = 1 - x := by
      push_cast; rw [abs_of_neg (by linarith)]; ring
    have h_p1 : |x + ((1 : ℤ) : ℝ)| = 1 + x := by
      push_cast; rw [abs_of_pos (by linarith)]; ring
    have h_p2 : |x + ((2 : ℤ) : ℝ)| = 2 + x := by
      push_cast; rw [abs_of_pos (by linarith)]; ring
    rw [h_m2, h_m1, h_p1, h_p2]
    ring
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    refine hZ |x + (k : ℝ)| ?_
    by_cases hk0 : k = 0
    · left
      subst hk0
      simp only [Int.cast_zero, add_zero, abs_of_nonneg hx0]
      exact hxc
    · right
      rcases le_or_gt 3 k with hk3 | hk3
      · have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
        rw [abs_of_pos (by linarith)]
        linarith
      · have hk_le : k ≤ -3 := by omega
        have : (k : ℝ) ≤ -3 := by exact_mod_cast hk_le
        rw [abs_of_neg (by linarith)]
        linarith

/-- **General symmetric window unfolding of `Ψ_f(1) * sin(2π c) / π`.**
For any continuous blind core `f` supported in `[α, β]` (`0 < α ≤ β`) with `Ψ_f(0) = 0` and any
`c ∈ [0, 1/2]` satisfying `c ≤ α / β` and `β / α ≤ 3 - c`,
`Ψ_f(1) * sin(2π c) / π = (∫ r in (1 - c)..(1 + c), A_f(r) dr) + (∫ r in (2 - c)..(2 + c), A_f(r) dr)`. -/
theorem cosDilationKernel_one_mul_sin_div_pi_eq_intervalIntegral
    (hf : Continuous f) {α β c : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (h0 : cosDilationKernel f 0 = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0)
    (hc0 : 0 ≤ c) (hc_half : c ≤ 1 / 2) (hc_lo : c ≤ α / β) (hc_hi : β / α ≤ 3 - c) :
    cosDilationKernel f 1 * Real.sin (2 * π * c) / π =
      (∫ r in (1 - c)..(1 + c), dilationAutocorr f r) +
        (∫ r in (2 - c)..(2 + c), dilationAutocorr f r) := by
  have hInt := intervalIntegral_tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp h0 hblind 0 c
  rw [mul_zero, Real.sin_zero, sub_zero, ← mul_div_right_comm] at hInt
  rw [← hInt]
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have h_congr : ∫ x in (0 : ℝ)..c, (∑' k : ℤ, dilationAutocorr f |x + (k : ℝ)|) =
      ∫ x in (0 : ℝ)..c,
        ((dilationAutocorr f (1 - x) + dilationAutocorr f (1 + x)) +
          (dilationAutocorr f (2 - x) + dilationAutocorr f (2 + x))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hc0] at hx
    rw [tsum_dilationAutocorr_abs_eq_four_terms_on_Icc hf hα hαβ hsupp hc_lo hc_hi hc_half
      hx.1 hx.2]
    ring
  rw [h_congr]
  have hi1m : IntervalIntegrable (fun x => dilationAutocorr f (1 - x)) volume 0 c :=
    (hA_cont.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hi1p : IntervalIntegrable (fun x => dilationAutocorr f (1 + x)) volume 0 c :=
    (hA_cont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hi2m : IntervalIntegrable (fun x => dilationAutocorr f (2 - x)) volume 0 c :=
    (hA_cont.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
  have hi2p : IntervalIntegrable (fun x => dilationAutocorr f (2 + x)) volume 0 c :=
    (hA_cont.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (hi1m.add hi1p) (hi2m.add hi2p),
    intervalIntegral.integral_add hi1m hi1p,
    intervalIntegral.integral_add hi2m hi2p]
  have h1m : ∫ x in (0 : ℝ)..c, dilationAutocorr f (1 - x) =
      ∫ r in (1 - c)..1, dilationAutocorr f r := by
    rw [intervalIntegral.integral_comp_sub_left (dilationAutocorr f) 1, sub_zero]
  have h1p : ∫ x in (0 : ℝ)..c, dilationAutocorr f (1 + x) =
      ∫ r in (1 : ℝ)..(1 + c), dilationAutocorr f r := by
    have h_eq : (fun x : ℝ => dilationAutocorr f (1 + x)) =
        fun x : ℝ => dilationAutocorr f (x + 1) := by funext x; ring_nf
    rw [h_eq, intervalIntegral.integral_comp_add_right (dilationAutocorr f) 1,
      zero_add, add_comm c 1]
  have h2m : ∫ x in (0 : ℝ)..c, dilationAutocorr f (2 - x) =
      ∫ r in (2 - c)..2, dilationAutocorr f r := by
    rw [intervalIntegral.integral_comp_sub_left (dilationAutocorr f) 2, sub_zero]
  have h2p : ∫ x in (0 : ℝ)..c, dilationAutocorr f (2 + x) =
      ∫ r in (2 : ℝ)..(2 + c), dilationAutocorr f r := by
    have h_eq : (fun x : ℝ => dilationAutocorr f (2 + x)) =
        fun x : ℝ => dilationAutocorr f (x + 2) := by funext x; ring_nf
    rw [h_eq, intervalIntegral.integral_comp_add_right (dilationAutocorr f) 2,
      zero_add, add_comm c 2]
  rw [h1m, h1p, h2m, h2p,
    intervalIntegral.integral_add_adjacent_intervals (hA_cont.intervalIntegrable _ _)
      (hA_cont.intervalIntegrable _ _),
    intervalIntegral.integral_add_adjacent_intervals (hA_cont.intervalIntegrable _ _)
      (hA_cont.intervalIntegrable _ _)]

/-- **Complementary quarter-period unfolding on `[1/4, 1/2]` for `β ≤ (9/4) α`.**
If `f` is a continuous blind core supported in `[α, β]` (`0 < α ≤ β ≤ (9/4) α`) with
`∫_{y > 0} f(y) dy = 0`, then
`-Ψ_f(1) / π = (∫ r in 0..(3/4), A_f(r) dr) + (∫ r in (5/4)..(7/4), A_f(r) dr)`. -/
theorem neg_cosDilationKernel_one_div_pi_eq_intervalIntegral_of_le_nine_fourths
    (hf : Continuous f) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β ≤ 9 / 4 * α)
    (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hmean : ∫ y in Ioi (0 : ℝ), f y = 0)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) :
    -cosDilationKernel f 1 / π =
      (∫ r in (0 : ℝ)..(3 / 4), dilationAutocorr f r) +
        (∫ r in (5 / 4 : ℝ)..(7 / 4), dilationAutocorr f r) := by
  have h0 : cosDilationKernel f 0 = 0 := cosDilationKernel_zero_of_integral_eq_zero hmean
  have hQ := cosDilationKernel_one_div_pi_eq_intervalIntegral_of_le_eleven_fourths
    hf hα hαβ (by linarith) hsupp h0 hblind
  have hA_cont : Continuous (dilationAutocorr f) := continuous_dilationAutocorr hf hα hsupp
  have h_tot : ∫ r in (0 : ℝ)..(9 / 4), dilationAutocorr f r = 0 :=
    intervalIntegral_dilationAutocorr_eq_zero_of_ge hf hα hαβ hsupp hmean
      ((div_le_iff₀ hα).mpr hβ)
  have h_split1 := intervalIntegral.integral_add_adjacent_intervals
    (hA_cont.intervalIntegrable (μ := volume) 0 (3 / 4))
    (hA_cont.intervalIntegrable (μ := volume) (3 / 4) (5 / 4))
  have h_split2 := intervalIntegral.integral_add_adjacent_intervals
    (hA_cont.intervalIntegrable (μ := volume) 0 (5 / 4))
    (hA_cont.intervalIntegrable (μ := volume) (5 / 4) (7 / 4))
  have h_split3 := intervalIntegral.integral_add_adjacent_intervals
    (hA_cont.intervalIntegrable (μ := volume) 0 (7 / 4))
    (hA_cont.intervalIntegrable (μ := volume) (7 / 4) (9 / 4))
  rw [neg_div, hQ]
  linarith

end

end RHTower
