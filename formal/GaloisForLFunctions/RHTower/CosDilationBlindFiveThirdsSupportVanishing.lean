import GaloisForLFunctions.RHTower.CosDilationBlindGoldenSupportVanishing

/-!
# Blind cores of support ratio below `5/3` vanish: the Gauss branch of the Farey recursion

Let `f` be continuous and supported in `[α, β]` with `0 < α ≤ β < 2α`, dilation autocorrelation
`A_f`, and cosine–dilation kernel `Ψ_f` vanishing at every integer `n ≥ 2`.  Put
`H(v) = A_f(1 − 1/v)/v` and `τ(v) = 2 + 1/(v − 1)` (`gaussBranch`).

**The Gauss–Farey equation** (`dilationAutocorr_gauss_farey_equation`).  For every `v ≥ 2`,

`H(v) + H(v + 1) + H(τ(v))/(v − 1) = (Ψ_f(0) + 2Ψ_f(1) cos(2π/v))/v`.

Poisson periodization at `x = 1 − 1/v` keeps the translates `1 − 1/v`, `1 + 1/v` and `2 − 1/v`.
The inversion law sends `1 + 1/v` to `1 − 1/(v + 1)` (the parabolic Farey branch `v ↦ v + 1`) and
`2 − 1/v` to `1 − 1/τ(v)` (the Gauss branch, whose fixed point is `φ² = (3 + √5)/2`).

**Theorem** (`eq_zero_of_cosDilationKernel_blind_of_lt_five_thirds_mul`).  If `3β < 5α`, then
`f = 0`.  This extends `eq_zero_of_cosDilationKernel_blind_of_golden` (support ratio below the
golden ratio) by one level of the Farey tree.

**Proof** for `φ ≤ β/α < 5/3`, with `a = Ψ_f(0) + 2Ψ_f(1)`, `b = 2Ψ_f(1)` and
`F = fareySeriesR a b`.
* `H = F` on `[v*, ∞)`, `v* = α/(2α − β) < 3` (`dilationAutocorr_profile_eq_fareySeriesR`), and
  `H = 0` on `[2, β/(β − α)]`.  For `v` slightly above `2` the equation gives the Lewis-type
  identity `(v − 1)F(v) = F(τ(v))`.
* Both sides are holomorphic on `Re z > 1`, so the identity holds for every real `v > 1`.
* As `v → ∞`, `(v − 1)F(v) → a/2` (`tendsto_sub_one_mul_altHarmonicR`,
  `tendsto_sub_one_mul_altCosDefectR`) and `F(τ(v)) → F(2)`.  With `F(2) = F(3)` (the identity at
  `v = 2`) and `F(2) + F(3) = (a − 2b)/2` this forces `a = −2b`.
* Then `F = −b(2P − E)` with `2P − E = Σ_m (κ(v + 2m) − κ(v + 2m + 1)) > 0`, where
  `κ(x) = (3 − cos(2π/x))/x` decreases on `[2, ∞)` (`two_altHarmonicR_sub_altCosDefectR_pos`).  At
  the fixed point `φ²` the identity reads `(φ² − 2)F(φ²) = 0`, so `b = 0`, hence `a = 0`, and the
  short-core rigidity theorem finishes.
-/

open MeasureTheory Set Real Filter Topology

namespace RHTower

noncomputable section

variable {f : ℝ → ℝ}

/-! ### Bounds on the two series -/

theorem altHarmonicR_antitone {v w : ℝ} (hv : 0 < v) (hvw : v ≤ w) :
    altHarmonicR w ≤ altHarmonicR v := by
  refine (summable_altHarmonicR (lt_of_lt_of_le hv hvw)).tsum_le_tsum (fun k => ?_)
    (summable_altHarmonicR hv)
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have h1 : 0 < v + 2 * (k : ℝ) := by linarith
  have h2 : 0 < v + 2 * (k : ℝ) + 1 := by linarith
  exact one_div_le_one_div_of_le (mul_pos h1 h2)
    (mul_le_mul (by linarith) (by linarith) h2.le (by linarith))

theorem altHarmonicR_bounds {v : ℝ} (hv : 2 ≤ v) :
    1 / (2 * v) ≤ altHarmonicR v ∧ altHarmonicR v ≤ 1 / (2 * (v - 1)) := by
  have h1 := altHarmonicR_add_one (show 0 < v by linarith)
  have h2 := altHarmonicR_add_one (show 0 < v - 1 by linarith)
  rw [sub_add_cancel] at h2
  have m1 := altHarmonicR_antitone (show 0 < v by linarith) (show v ≤ v + 1 by linarith)
  have m2 := altHarmonicR_antitone (show 0 < v - 1 by linarith) (show v - 1 ≤ v by linarith)
  have e1 : (1 / v) / 2 = 1 / (2 * v) := by rw [div_div, mul_comm]
  have e2 : (1 / (v - 1)) / 2 = 1 / (2 * (v - 1)) := by rw [div_div, mul_comm]
  constructor
  · rw [← e1]; linarith
  · rw [← e2]; linarith

theorem tendsto_sub_one_mul_altHarmonicR :
    Tendsto (fun v : ℝ => (v - 1) * altHarmonicR v) atTop (𝓝 (1 / 2)) := by
  have hlo : Tendsto (fun v : ℝ => 1 / 2 - 1 / (2 * v)) atTop (𝓝 (1 / 2)) := by
    have : Tendsto (fun v : ℝ => 1 / (2 * v)) atTop (𝓝 0) := by
      refine (tendsto_inv_atTop_zero.comp
        (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).congr fun v => ?_
      simp [one_div]
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with v hv
    have hb := (altHarmonicR_bounds hv).1
    have hv1 : 0 ≤ v - 1 := by linarith
    have : (v - 1) * (1 / (2 * v)) ≤ (v - 1) * altHarmonicR v := mul_le_mul_of_nonneg_left hb hv1
    have e : (v - 1) * (1 / (2 * v)) = 1 / 2 - 1 / (2 * v) := by
      field_simp
    linarith
  · filter_upwards [eventually_ge_atTop 2] with v hv
    have hb := (altHarmonicR_bounds hv).2
    have hv1 : 0 < v - 1 := by linarith
    calc (v - 1) * altHarmonicR v ≤ (v - 1) * (1 / (2 * (v - 1))) :=
          mul_le_mul_of_nonneg_left hb hv1.le
      _ = 1 / 2 := by field_simp

theorem hasSum_sub_succ_of_antitone {t : ℕ → ℝ} (hmono : ∀ i, t (i + 1) ≤ t i)
    (ht : Tendsto t atTop (𝓝 0)) : HasSum (fun i => t i - t (i + 1)) (t 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun i => sub_nonneg.mpr (hmono i))]
  have hsum : ∀ n : ℕ, ∑ i ∈ Finset.range n, (t i - t (i + 1)) = t 0 - t n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  simp_rw [hsum]
  simpa using (tendsto_const_nhds (x := t 0)).sub ht

theorem abs_cosDefectR_le_cube {x : ℝ} (hx : 0 < x) :
    |(Real.cos (2 * π / x) - 1) / x| ≤ 2 * π ^ 2 / x ^ 3 := by
  have hc1 := Real.cos_le_one (2 * π / x)
  have hc2 := Real.one_sub_sq_div_two_le_cos (x := 2 * π / x)
  rw [abs_div, abs_of_pos hx, abs_of_nonpos (by linarith), div_le_div_iff₀ hx (by positivity)]
  have : -(Real.cos (2 * π / x) - 1) ≤ (2 * π / x) ^ 2 / 2 := by linarith
  calc -(Real.cos (2 * π / x) - 1) * x ^ 3 ≤ (2 * π / x) ^ 2 / 2 * x ^ 3 :=
        mul_le_mul_of_nonneg_right this (by positivity)
    _ = 2 * π ^ 2 * x := by field_simp

/-- `|altCosDefectR v| ≤ 2π²/(v − 1)²` for `v ≥ 2`. -/
theorem abs_altCosDefectR_le_sq {v : ℝ} (hv : 2 ≤ v) :
    |altCosDefectR v| ≤ 2 * π ^ 2 / (v - 1) ^ 2 := by
  have hv1 : (1 : ℝ) ≤ v := by linarith
  have hs := summable_altCosDefectR hv1
  set t : ℕ → ℝ := fun i => 1 / (v + i - 1) ^ 2 with ht
  have hmono : ∀ i, t (i + 1) ≤ t i := by
    intro i
    simp only [ht]
    have hi : (0 : ℝ) ≤ i := i.cast_nonneg
    have hp : 0 < v + (i : ℝ) - 1 := by linarith
    apply one_div_le_one_div_of_le (pow_pos hp 2)
    push_cast
    nlinarith
  have htt : Tendsto t atTop (𝓝 0) := by
    have : Tendsto (fun i : ℕ => (v + (i : ℝ) - 1) ^ 2) atTop atTop := by
      have h1 : Tendsto (fun i : ℕ => v - 1 + (i : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
      have h2 := (tendsto_pow_atTop (n := 2) (by norm_num)).comp h1
      refine h2.congr fun i => ?_
      simp only [Function.comp]; ring
    refine (tendsto_inv_atTop_zero.comp this).congr fun i => ?_
    simp [ht, one_div]
  have htel := hasSum_sub_succ_of_antitone hmono htt
  have hbound : ∀ i : ℕ, ‖(-1 : ℝ) ^ i * ((Real.cos (2 * π / (v + i)) - 1) / (v + i))‖ ≤
      2 * π ^ 2 * (t i - t (i + 1)) := by
    intro i
    have hi : (0 : ℝ) ≤ i := i.cast_nonneg
    have hx : 2 ≤ v + i := by linarith
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    refine (abs_cosDefectR_le_cube (by linarith)).trans ?_
    simp only [ht]
    push_cast
    rw [show v + ((i : ℝ) + 1) - 1 = v + i by ring]
    have hx1 : 0 < v + (i : ℝ) - 1 := by linarith
    have hx0 : 0 < v + (i : ℝ) := by linarith
    have key : 1 / (v + i) ^ 3 ≤ 1 / (v + i - 1) ^ 2 - 1 / (v + i) ^ 2 := by
      rw [div_sub_div _ _ (pow_pos hx1 2).ne' (pow_pos hx0 2).ne',
        div_le_div_iff₀ (pow_pos hx0 3) (mul_pos (pow_pos hx1 2) (pow_pos hx0 2))]
      have hq : 0 ≤ (v + (i : ℝ)) ^ 2 + (v + i) - 1 := by nlinarith
      nlinarith [mul_nonneg (sq_nonneg (v + (i : ℝ))) hq]
    calc 2 * π ^ 2 / (v + i) ^ 3 = 2 * π ^ 2 * (1 / (v + i) ^ 3) := by ring
      _ ≤ 2 * π ^ 2 * (1 / (v + i - 1) ^ 2 - 1 / (v + i) ^ 2) :=
          mul_le_mul_of_nonneg_left key (by positivity)
  have hsum := (htel.mul_left (2 * π ^ 2))
  calc |altCosDefectR v| = ‖∑' i : ℕ, (-1 : ℝ) ^ i *
        ((Real.cos (2 * π / (v + i)) - 1) / (v + i))‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ 2 * π ^ 2 * t 0 := tsum_of_norm_bounded hsum hbound
    _ = 2 * π ^ 2 / (v - 1) ^ 2 := by simp only [ht]; push_cast; ring

theorem tendsto_sub_one_mul_altCosDefectR :
    Tendsto (fun v : ℝ => (v - 1) * altCosDefectR v) atTop (𝓝 0) := by
  have hup : Tendsto (fun v : ℝ => 2 * π ^ 2 / (v - 1)) atTop (𝓝 0) := by
    have : Tendsto (fun v : ℝ => v - 1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
    have h := this.inv_tendsto_atTop.const_mul (2 * π ^ 2)
    rw [mul_zero] at h
    exact h.congr fun v => by simp [div_eq_mul_inv]
  refine squeeze_zero_norm' ?_ hup
  filter_upwards [eventually_ge_atTop 2] with v hv
  have hv1 : 0 < v - 1 := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hv1]
  calc (v - 1) * |altCosDefectR v| ≤ (v - 1) * (2 * π ^ 2 / (v - 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (abs_altCosDefectR_le_sq hv) hv1.le
    _ = 2 * π ^ 2 / (v - 1) := by field_simp

/-! ### Positivity of `2P − E` -/

/-- `κ(x) = (3 − cos(2π/x))/x` strictly decreases on `[2, ∞)`. -/
theorem kappa_strictAnti {x y : ℝ} (hx : 2 ≤ x) (hxy : x < y) :
    (3 - Real.cos (2 * π / y)) / y < (3 - Real.cos (2 * π / x)) / x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hc : Real.cos (2 * π / x) ≤ Real.cos (2 * π / y) := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
    · rw [div_le_iff₀ hx0]; nlinarith [Real.pi_pos]
    · exact div_le_div_of_nonneg_left (by positivity) hx0 hxy.le
  have hcy := Real.cos_le_one (2 * π / y)
  rw [div_lt_div_iff₀ hy0 hx0]
  nlinarith

theorem two_altHarmonicR_sub_altCosDefectR_pos {v : ℝ} (hv : 2 ≤ v) :
    0 < 2 * altHarmonicR v - altCosDefectR v := by
  have hv0 : 0 < v := by linarith
  have hv1 : (1 : ℝ) ≤ v := by linarith
  set e : ℕ → ℝ := fun i => (-1 : ℝ) ^ i * ((Real.cos (2 * π / (v + i)) - 1) / (v + i)) with he
  have hs : Summable e := summable_altCosDefectR hv1
  have hsE : Summable fun m : ℕ => e (2 * m) :=
    hs.comp_injective (fun a b h => by simpa using h)
  have hsO : Summable fun m : ℕ => e (2 * m + 1) :=
    hs.comp_injective (fun a b h => by simpa using h)
  have hsplit := tsum_even_add_odd hsE hsO
  set κ : ℝ → ℝ := fun x => (3 - Real.cos (2 * π / x)) / x with hκ
  have hterm : ∀ m : ℕ, 2 * (1 / ((v + 2 * m) * (v + 2 * m + 1))) - (e (2 * m) + e (2 * m + 1)) =
      κ (v + 2 * m) - κ (v + 2 * m + 1) := by
    intro m
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    have h1 : (0 : ℝ) < v + 2 * m := by linarith
    have h2 : (0 : ℝ) < v + 2 * m + 1 := by linarith
    have p1 : (-1 : ℝ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
    have p2 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    simp only [he, hκ, p1, p2]
    push_cast
    field_simp
    ring_nf
  have hP := summable_altHarmonicR hv0
  have hsum : HasSum (fun m : ℕ => κ (v + 2 * m) - κ (v + 2 * m + 1))
      (2 * altHarmonicR v - altCosDefectR v) := by
    have hA := (hP.hasSum.mul_left 2).sub (hsE.hasSum.add hsO.hasSum)
    rw [hsplit] at hA
    refine (hA.congr_fun fun m => (hterm m).symm).congr_fun fun m => rfl |>.trans ?_
    rfl
  rw [← hsum.tsum_eq]
  refine hsum.summable.tsum_pos (fun m => ?_) 0 ?_
  · have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    exact sub_nonneg.mpr (kappa_strictAnti (x := v + 2 * m) (by linarith) (by linarith)).le
  · simp only [Nat.cast_zero, mul_zero, add_zero]
    exact sub_pos.mpr (kappa_strictAnti hv (by linarith))

/-! ### The Gauss–Farey equation -/

/-- The Gauss branch `τ(v) = 2 + 1/(v − 1)`. -/
def gaussBranch (v : ℝ) : ℝ := 2 + 1 / (v - 1)

/-- **Three-term periodization** for `β < 2α` and `v ≥ 2`. -/
theorem dilationAutocorr_three_term_periodization (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hβ2 : β < 2 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) {v : ℝ} (hv2 : 2 ≤ v) :
    dilationAutocorr f (1 - 1 / v) + dilationAutocorr f (1 + 1 / v) +
        dilationAutocorr f (2 - 1 / v) =
      cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π / v) := by
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hv0 : 0 < v := by linarith
  have hlo : 1 / 2 ≤ α / β := by rw [le_div_iff₀ hβ0]; linarith
  have hhi : β / α < 2 := by rw [div_lt_iff₀ hα]; linarith
  have hinvv : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv2
  have hinvv0 : 0 < 1 / v := by positivity
  have hblindℤ := cosDilationKernel_int_eq_zero hf hα hαβ hsupp hblind
  have h := tsum_dilationAutocorr_abs_eq hf hα hαβ hsupp hblindℤ (1 - 1 / v)
  rw [tsum_eq_sum (s := {0, -2, 1}) fun k hk => ?_] at h
  · rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
      Finset.sum_singleton] at h
    have a0 : |1 - 1 / v + ((0 : ℤ) : ℝ)| = 1 - 1 / v := by
      rw [Int.cast_zero, add_zero, abs_of_pos (by linarith)]
    have a2 : |1 - 1 / v + ((-2 : ℤ) : ℝ)| = 1 + 1 / v := by
      rw [abs_of_neg (by push_cast; linarith)]; push_cast; ring
    have a1 : |1 - 1 / v + ((1 : ℤ) : ℝ)| = 2 - 1 / v := by
      rw [abs_of_pos (by push_cast; linarith)]; push_cast; ring
    have hcos : Real.cos (2 * π * (1 - 1 / v)) = Real.cos (2 * π / v) := by
      rw [show 2 * π * (1 - 1 / v) = 2 * π - 2 * π / v by ring, Real.cos_two_pi_sub]
    rw [a0, a2, a1, hcos] at h
    have h' : dilationAutocorr f (1 - 1 / v) + (dilationAutocorr f (1 + 1 / v) +
        dilationAutocorr f (2 - 1 / v)) =
        cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π / v) := by
      exact_mod_cast h
    linarith
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rw [dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp, Complex.ofReal_zero]
    intro hm
    rcases le_or_gt 2 k with hk2 | hk2
    · have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      rw [abs_of_pos (by linarith)] at hm
      linarith [hm.2]
    rcases le_or_gt (-1) k with hkm | hkm
    · have : k = -1 := by omega
      subst this
      rw [abs_of_neg (by push_cast; linarith)] at hm
      push_cast at hm
      linarith [hm.1]
    · have hk3 : k ≤ -3 := by omega
      have : (k : ℝ) ≤ -3 := by exact_mod_cast hk3
      rw [abs_of_neg (by linarith)] at hm
      linarith [hm.2]

/-- **The Gauss–Farey equation** `H(v) + H(v + 1) + H(τ(v))/(v − 1) = g(v)`. -/
theorem dilationAutocorr_gauss_farey_equation (hf : Continuous f) {α β : ℝ} (hα : 0 < α)
    (hαβ : α ≤ β) (hβ2 : β < 2 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) {v : ℝ} (hv2 : 2 ≤ v) :
    dilationAutocorr f (1 - 1 / v) / v + dilationAutocorr f (1 - 1 / (v + 1)) / (v + 1) +
        dilationAutocorr f (1 - 1 / gaussBranch v) / gaussBranch v / (v - 1) =
      (cosDilationKernel f 0 + 2 * cosDilationKernel f 1 * Real.cos (2 * π / v)) / v := by
  have hv0 : 0 < v := by linarith
  have hv1 : 0 < v - 1 := by linarith
  have hv1' : v - 1 ≠ 0 := hv1.ne'
  have hv0' : v ≠ 0 := hv0.ne'
  have hvp : v + 1 ≠ 0 := by linarith
  have h2v : 2 * v - 1 ≠ 0 := ne_of_gt (by linarith)
  have hp := dilationAutocorr_three_term_periodization hf hα hαβ hβ2 hsupp hblind hv2
  have hs1 : 1 - 1 / (v + 1) = v / (v + 1) := by field_simp; ring
  have hr1 : 0 < 1 - 1 / (v + 1) := by rw [hs1]; positivity
  have hinv1 := dilationAutocorr_inv f hr1
  have e1 : (1 - 1 / (v + 1))⁻¹ = 1 + 1 / v := by
    rw [hs1, inv_div]; field_simp
  rw [e1] at hinv1
  have hτ : gaussBranch v = (2 * v - 1) / (v - 1) := by unfold gaussBranch; field_simp; ring
  have hs2 : 1 - 1 / gaussBranch v = v / (2 * v - 1) := by rw [hτ]; field_simp; ring
  have hr2 : 0 < 1 - 1 / gaussBranch v := by rw [hs2]; exact div_pos hv0 (by linarith)
  have hinv2 := dilationAutocorr_inv f hr2
  have e2 : (1 - 1 / gaussBranch v)⁻¹ = 2 - 1 / v := by
    rw [hs2, inv_div]; field_simp
  rw [e2] at hinv2
  rw [hinv1, hinv2] at hp
  set X := dilationAutocorr f (1 - 1 / v) with hX
  set Y := dilationAutocorr f (1 - 1 / (v + 1)) with hY
  set Z := dilationAutocorr f (1 - 1 / gaussBranch v) with hZ
  rw [hs1, hs2] at hp
  rw [← hp, hτ]
  field_simp

/-- **The Lewis identity forces the trivial Farey series.**  If `F = fareySeriesR a b` satisfies
`(v − 1)F(v) = F(τ(v))` on an interval `(2, q)`, then `a = b = 0`.

Both sides are holomorphic on `Re z > 1`, so the identity holds for every real `v > 1`.  As
`v → ∞`, `(v − 1)F(v) → a/2` and `F(τ(v)) → F(2)`; with `F(2) = F(3)` (the identity at `v = 2`)
and `F(2) + F(3) = (a − 2b)/2` this forces `a = −2b`.  Then `F = −b(2P − E)` with `2P − E > 0`,
and the identity at the fixed point `φ²` of `τ` gives `F(φ²) = 0`, so `b = 0`. -/
theorem eq_zero_of_fareySeriesR_lewis_identity {a b q : ℝ} (hq2 : 2 < q)
    (hlewis : ∀ v, 2 < v → v < q →
      (v - 1) * fareySeriesR a b v = fareySeriesR a b (gaussBranch v)) :
    a = 0 ∧ b = 0 := by
  set F := fareySeriesR a b with hF
  -- analytic continuation of the Lewis identity
  set Φ : ℂ → ℂ := fun z => (z - 1) * fareySeries a b z - fareySeries a b (2 + 1 / (z - 1)) with hΦ
  set U₁ : Set ℂ := {z | 1 < z.re} with hU₁
  have hU₁o : IsOpen U₁ := isOpen_lt continuous_const Complex.continuous_re
  have hmaps : ∀ z ∈ U₁, 2 + 1 / (z - 1) ∈ halfPlaneHalf := by
    intro z hz
    have hz' : 1 < z.re := hz
    show 1 / 2 < (2 + 1 / (z - 1)).re
    rw [Complex.add_re, show ((2 : ℂ)).re = 2 by norm_num]
    have hre : 0 < (1 / (z - 1)).re := by
      rw [one_div, Complex.inv_re]
      apply div_pos (by simp; linarith)
      rw [Complex.normSq_pos]
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith
    linarith
  have hsub : U₁ ⊆ halfPlaneHalf := fun z hz => by
    show 1 / 2 < z.re; have : 1 < z.re := hz; linarith
  have hΦd : DifferentiableOn ℂ Φ U₁ := by
    refine ((differentiableOn_id.sub_const 1).mul
      ((differentiableOn_fareySeries a b).mono hsub)).sub ?_
    refine (differentiableOn_fareySeries a b).comp ?_ hmaps
    refine (differentiableOn_const 2).add ((differentiableOn_const 1).div
      (differentiableOn_id.sub_const 1) fun z hz => ?_)
    intro h0
    have := congrArg Complex.re h0
    have hz' : 1 < z.re := hz
    simp at this
    linarith
  have hΦzero := eqOn_zero_of_real_interval (hΦd.analyticOnNhd hU₁o)
    (convex_halfSpace_re_gt 1).isPreconnected hq2
    (by show 1 < (((2 + q) / 2 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith)
    fun x hx1 hx2 => by
      simp only [hΦ]
      have h2 : ((2 : ℂ) + 1 / ((x : ℂ) - 1)) = ((gaussBranch x : ℝ) : ℂ) := by
        unfold gaussBranch; push_cast; ring
      rw [h2, fareySeries_ofReal, fareySeries_ofReal, ← hF, ← hlewis x hx1 hx2]
      push_cast
      ring
  have hlewis_all : ∀ v : ℝ, 1 < v → (v - 1) * F v = F (gaussBranch v) := by
    intro v hv
    have hvU : ((v : ℝ) : ℂ) ∈ U₁ := by show 1 < ((v : ℝ) : ℂ).re; rw [Complex.ofReal_re]; exact hv
    have := hΦzero hvU
    simp only [hΦ, Pi.zero_apply] at this
    have h2 : ((2 : ℂ) + 1 / ((v : ℂ) - 1)) = ((gaussBranch v : ℝ) : ℂ) := by
      unfold gaussBranch; push_cast; ring
    rw [h2, fareySeries_ofReal, fareySeries_ofReal, ← hF] at this
    have : (((v - 1) * F v - F (gaussBranch v) : ℝ) : ℂ) = 0 := by push_cast; exact this
    have := Complex.ofReal_eq_zero.mp this
    linarith
  -- the limit `v → ∞`
  have hlim1 : Tendsto (fun v : ℝ => (v - 1) * F v) atTop (𝓝 (a / 2)) := by
    have h := (tendsto_sub_one_mul_altHarmonicR.const_mul a).add
      (tendsto_sub_one_mul_altCosDefectR.const_mul b)
    rw [show a * (1 / 2) + b * 0 = a / 2 by ring] at h
    refine h.congr fun v => ?_
    simp only [hF, fareySeriesR]; ring
  have hcont : ContinuousAt F 2 := by
    have hc : ContinuousAt (fareySeries a b) ((2 : ℝ) : ℂ) :=
      ((differentiableOn_fareySeries a b).differentiableAt
        (isOpen_halfPlaneHalf.mem_nhds
          (by show 1 / 2 < ((2 : ℝ) : ℂ).re; simp; norm_num))).continuousAt
    have hcomp := Complex.continuous_re.continuousAt.comp
      (hc.comp Complex.continuous_ofReal.continuousAt)
    refine hcomp.congr (Eventually.of_forall fun v => ?_)
    simp only [Function.comp, fareySeries_ofReal, Complex.ofReal_re, hF]
  have hτlim : Tendsto gaussBranch atTop (𝓝 2) := by
    have : Tendsto (fun v : ℝ => 1 / (v - 1)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun v : ℝ => v - 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_id
      exact h1.inv_tendsto_atTop.congr fun v => by simp [one_div]
    have h3 := (tendsto_const_nhds (x := (2 : ℝ))).add this
    rw [add_zero] at h3
    exact h3.congr fun v => rfl
  have hlim2 : Tendsto (fun v => F (gaussBranch v)) atTop (𝓝 (F 2)) := hcont.tendsto.comp hτlim
  have hF2 : F 2 = a / 2 := by
    refine tendsto_nhds_unique hlim2 (hlim1.congr' ?_)
    filter_upwards [eventually_gt_atTop 1] with v hv
    exact hlewis_all v hv
  -- `F(2) = F(3)` and the recursion at `2`
  have hF23 : F 2 = F 3 := by
    have := hlewis_all 2 (by norm_num)
    rw [show gaussBranch 2 = 3 by unfold gaussBranch; norm_num] at this
    linarith
  have hrec2 := fareySeriesR_add_one a b (v := 2) (by norm_num)
  rw [← hF, show (2 : ℝ) + 1 = 3 by norm_num,
    show Real.cos (2 * π / 2) = -1 by rw [show 2 * π / 2 = π by ring, Real.cos_pi]] at hrec2
  have hab : a = -2 * b := by
    rw [← hF23, hF2] at hrec2
    linarith
  -- the fixed point of the Gauss branch
  set vf := (3 + Real.sqrt 5) / 2 with hvf
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5pos : 2 < Real.sqrt 5 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hvf2 : 2 < vf := by rw [hvf]; linarith
  have hfix : gaussBranch vf = vf := by
    unfold gaussBranch
    rw [hvf]
    have h1 : (3 + Real.sqrt 5) / 2 - 1 = (1 + Real.sqrt 5) / 2 := by ring
    have hpos : 0 < 1 + Real.sqrt 5 := by positivity
    have key : 1 / ((1 + Real.sqrt 5) / 2) = (Real.sqrt 5 - 1) / 2 := by
      rw [one_div_div, div_eq_div_iff hpos.ne' two_ne_zero]
      nlinarith
    rw [h1, key]
    ring
  have hFvf : F vf = 0 := by
    have := hlewis_all vf (by linarith)
    rw [hfix] at this
    have h : (vf - 2) * F vf = 0 := by linarith
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact h
  have hb0 : b = 0 := by
    have hpos := two_altHarmonicR_sub_altCosDefectR_pos hvf2.le
    have : F vf = -b * (2 * altHarmonicR vf - altCosDefectR vf) := by
      simp only [hF, fareySeriesR]; rw [hab]; ring
    rw [hFvf] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · linarith
    · linarith
  exact ⟨by rw [hab, hb0]; ring, hb0⟩

/-! ### The theorem -/

/-- **Blind cores of support ratio below `5/3` vanish.** -/
theorem eq_zero_of_cosDilationKernel_blind_of_lt_five_thirds_mul (hf : Continuous f) {α β : ℝ}
    (hα : 0 < α) (hαβ : α ≤ β) (h53 : 3 * β < 5 * α) (hsupp : ∀ y, f y ≠ 0 → α ≤ y ∧ y ≤ β)
    (hblind : ∀ n : ℕ, 2 ≤ n → cosDilationKernel f n = 0) (y : ℝ) : f y = 0 := by
  rcases lt_or_ge (β ^ 2) (α * β + α ^ 2) with hg | hg
  · exact eq_zero_of_cosDilationKernel_blind_of_golden hf hα hαβ hg hsupp hblind y
  have hβ0 : 0 < β := lt_of_lt_of_le hα hαβ
  have hβ2 : β < 2 * α := by linarith
  have h32 : 3 * α < 2 * β := by nlinarith
  have hβα : α < β := by linarith
  have h2ab : 0 < 2 * α - β := by linarith
  set Ψ0 := cosDilationKernel f 0 with hΨ0
  set Ψ1 := cosDilationKernel f 1 with hΨ1
  set a := Ψ0 + 2 * Ψ1 with ha
  set b := 2 * Ψ1 with hb
  set F := fareySeriesR a b with hF
  set vs := α / (2 * α - β) with hvs
  have hvs2 : 2 < vs := by rw [hvs, lt_div_iff₀ h2ab]; linarith
  have hvs3 : vs < 3 := by rw [hvs, div_lt_iff₀ h2ab]; linarith
  have hmax : max 2 vs = vs := max_eq_right hvs2.le
  have hHF : ∀ v, vs ≤ v → dilationAutocorr f (1 - 1 / v) / v = F v := by
    intro v hv
    have := dilationAutocorr_profile_eq_fareySeriesR hf hα hαβ hβ2 hsupp hblind
      (v := v) (by rw [hmax]; exact hv)
    rw [this]
  set w₂ := β / (β - α) with hw₂
  have hβα' : 0 < β - α := by linarith
  have hw₂2 : 2 < w₂ := by rw [hw₂, lt_div_iff₀ hβα']; linarith
  have hHzero : ∀ v, 2 ≤ v → v ≤ w₂ → dilationAutocorr f (1 - 1 / v) / v = 0 := by
    intro v hv1 hv2
    have hv0 : 0 < v := by linarith
    rw [dilationAutocorr_eq_zero_of_not_mem_Ioo hf hα hαβ hsupp, zero_div]
    intro hm
    have : 1 - 1 / v ≤ α / β := by
      rw [hw₂, le_div_iff₀ hβα'] at hv2
      rw [show 1 - 1 / v = (v - 1) / v by field_simp, div_le_div_iff₀ hv0 hβ0]
      nlinarith
    linarith [hm.1]
  -- the Lewis identity on an interval
  set q := min w₂ (1 + 1 / (vs - 2)) with hq
  have hq2 : 2 < q := by
    rw [hq, lt_min_iff]
    refine ⟨hw₂2, ?_⟩
    have : 1 < 1 / (vs - 2) := by rw [lt_div_iff₀ (by linarith)]; linarith
    linarith
  have hlewis : ∀ v, 2 < v → v < q → (v - 1) * F v = F (gaussBranch v) := by
    intro v hv2 hvq
    have hvw : v ≤ w₂ := (hvq.le.trans (min_le_left _ _))
    have hv1 : 0 < v - 1 := by linarith
    have hτ : vs ≤ gaussBranch v := by
      have hvq' : v ≤ 1 + 1 / (vs - 2) := hvq.le.trans (min_le_right _ _)
      unfold gaussBranch
      have : v - 1 ≤ 1 / (vs - 2) := by linarith
      rw [le_div_iff₀ (by linarith)] at this
      have : vs - 2 ≤ 1 / (v - 1) := by rw [le_div_iff₀ hv1]; linarith
      linarith
    have e := dilationAutocorr_gauss_farey_equation hf hα hαβ hβ2 hsupp hblind hv2.le
    rw [hHzero v hv2.le hvw, hHF (v + 1) (by linarith), hHF (gaussBranch v) hτ, zero_add] at e
    have hrec := fareySeriesR_add_one a b (v := v) (by linarith)
    rw [← hF] at hrec
    have hg : (Ψ0 + 2 * Ψ1 * Real.cos (2 * π / v)) / v =
        (a + b * (Real.cos (2 * π / v) - 1)) / v := by
      rw [ha, hb]; ring
    rw [hg, ← hrec] at e
    field_simp at e
    linarith
  obtain ⟨ha0, hb0⟩ := eq_zero_of_fareySeriesR_lewis_identity hq2 hlewis
  have hΨ1z : Ψ1 = 0 := by rw [hb] at hb0; linarith
  have hΨ0z : Ψ0 = 0 := by rw [ha] at ha0; linarith
  exact eq_zero_of_cosDilationKernel_blind_of_le_two_mul hf hα hαβ hβ2.le hsupp hΨ0z hblind y

end

end RHTower
