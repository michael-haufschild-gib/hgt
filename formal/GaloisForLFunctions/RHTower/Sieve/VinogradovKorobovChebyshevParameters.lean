import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovLogDeriv

/-!
# Parameters of the Vinogradov–Korobov Chebyshev contour

With `σ(x) = (log x)^{3/5}(log log x)^{-5/3}` and `κ = 1/(12·10⁸)` the contour is run at

```text
T = exp(κ·σ(N)),      s = log T / 2,      H = N·exp(-s/6).
```

Write `L = log N`, `p = L^{2/5}`, `q = (log L)^{5/3}`, so `σ(N) = L/(p q)`.  The width
`w = vkHadamardWidth` at `T + 1` is at least `1/(6·10⁸ p q)`, because `log(T+1) ≤ 2L^{3/5}` and
`log log(T+1) ≤ 2 log L`; hence the left edge `1 - u` of the rectangle satisfies

```text
u·log N ≥ L/(12·10⁸ p q) = κ σ(N) = 2s .
```

`(log log N)^{5/3} = o((log N)^{1/10})` gives `p q ≤ (κ/2)√L`, which makes `log T ≥ 2√L`, and every
polynomial in `L` that the contour produces is bounded by `L²`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The Vinogradov–Korobov scale `(log x)^{3/5}·(log log x)^{-5/3}`. -/
def vkScale (x : ℝ) : ℝ :=
  Real.log x ^ ((3 : ℝ) / 5) * Real.log (Real.log x) ^ (-((5 : ℝ) / 3))

/-- The constant relating the scale to the logarithm of the contour height. -/
def vkKappa : ℝ := 1 / (12 * 10 ^ 8)

/-- The contour height `exp(κ·σ(N))`. -/
def vkHeight (N : ℝ) : ℝ := Real.exp (vkKappa * vkScale N)

/-- The saving `κ·σ(N)/2`. -/
def vkSaving (N : ℝ) : ℝ := vkKappa * vkScale N / 2

/-- The smoothing width `N·exp(-s/6)`. -/
def vkWidth (N : ℝ) : ℝ := N * Real.exp (-(vkSaving N / 6))

theorem vkKappa_pos : 0 < vkKappa := by unfold vkKappa; norm_num

theorem log_vkHeight (N : ℝ) : Real.log (vkHeight N) = vkKappa * vkScale N := Real.log_exp _

theorem vkSaving_eq (N : ℝ) : vkSaving N = Real.log (vkHeight N) / 2 := by
  rw [log_vkHeight, vkSaving]

/-- `(log log x)^a = o((log x)^b)` in the form of an eventual inequality. -/
theorem eventually_logLog_rpow_le (a : ℝ) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) ^ a ≤ ε * Real.log x ^ b := by
  have h := Real.tendsto_log_atTop.eventually ((isLittleO_log_rpow_rpow_atTop a hb).bound hε)
  filter_upwards [h, Real.tendsto_log_atTop.eventually_ge_atTop 0] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
  exact le_trans (le_abs_self _) hx

/-- The scale as `L/(p q)`. -/
theorem vkScale_eq {x : ℝ} (hL : 0 < Real.log x) (hl : 0 < Real.log (Real.log x)) :
    vkScale x = Real.log x
      / (Real.log x ^ ((2 : ℝ) / 5) * Real.log (Real.log x) ^ ((5 : ℝ) / 3)) := by
  have h1 : Real.log x ^ ((3 : ℝ) / 5) * Real.log x ^ ((2 : ℝ) / 5) = Real.log x := by
    rw [← Real.rpow_add hL]; norm_num
  have hp : 0 < Real.log x ^ ((2 : ℝ) / 5) := Real.rpow_pos_of_pos hL _
  have hq : 0 < Real.log (Real.log x) ^ ((5 : ℝ) / 3) := Real.rpow_pos_of_pos hl _
  unfold vkScale
  rw [Real.rpow_neg hl.le, eq_div_iff (by positivity)]
  calc Real.log x ^ ((3 : ℝ) / 5) * (Real.log (Real.log x) ^ ((5 : ℝ) / 3))⁻¹
        * (Real.log x ^ ((2 : ℝ) / 5) * Real.log (Real.log x) ^ ((5 : ℝ) / 3))
      = Real.log x ^ ((3 : ℝ) / 5) * Real.log x ^ ((2 : ℝ) / 5) := by field_simp
    _ = Real.log x := h1

/-- `2^{7/3} ≤ 6`. -/
theorem two_rpow_seven_thirds_le : (2 : ℝ) ^ ((7 : ℝ) / 3) ≤ 6 := by
  by_contra h
  have h6 : (6 : ℝ) < 2 ^ ((7 : ℝ) / 3) := lt_of_not_ge h
  have hcube := pow_lt_pow_left₀ h6 (by norm_num) (n := 3) (by norm_num)
  have heq : ((2 : ℝ) ^ ((7 : ℝ) / 3)) ^ (3 : ℕ) = 128 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [heq] at hcube
  norm_num at hcube

/-- **The width at the contour height.**  If `log t ≤ 2L^{3/5}`, `log log t ≤ 2 log L` and
`1 ≤ log log t` with `0 < log t`, then `w(t) ≥ 1/(6·10⁸ L^{2/5} (log L)^{5/3})`. -/
theorem vkHadamardWidth_ge_of_log_le {t L : ℝ} (hL : 0 < L) (hl : 0 < Real.log L)
    (hlt0 : 0 < Real.log t) (ht1 : 1 ≤ Real.log (Real.log t))
    (ht : Real.log t ≤ 2 * L ^ ((3 : ℝ) / 5))
    (htt : Real.log (Real.log t) ≤ 2 * Real.log L) :
    1 / (6 * 10 ^ 8 * (L ^ ((2 : ℝ) / 5) * Real.log L ^ ((5 : ℝ) / 3)))
      ≤ RHTower.vkHadamardWidth t := by
  have hll0 : 0 < Real.log (Real.log t) := by linarith
  have hp : 0 < L ^ ((2 : ℝ) / 5) := Real.rpow_pos_of_pos hL _
  have hq : 0 < Real.log L ^ ((5 : ℝ) / 3) := Real.rpow_pos_of_pos hl _
  -- the first factor
  have hA : (2 * L ^ ((3 : ℝ) / 5)) ^ (-(2 : ℝ) / 3) ≤ Real.log t ^ (-(2 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hlt0 ht (by norm_num)
  have hAeq : (2 * L ^ ((3 : ℝ) / 5)) ^ (-(2 : ℝ) / 3)
      = (2 : ℝ) ^ (-(2 : ℝ) / 3) * (L ^ ((2 : ℝ) / 5))⁻¹ := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hL.le _), ← Real.rpow_mul hL.le,
      ← Real.rpow_neg hL.le]
    norm_num
  -- the second factor
  have hB : (2 * Real.log L) ^ (-(5 : ℝ) / 3) ≤ Real.log (Real.log t) ^ (-(5 : ℝ) / 3) :=
    Real.rpow_le_rpow_of_nonpos hll0 htt (by norm_num)
  have hBeq : (2 * Real.log L) ^ (-(5 : ℝ) / 3)
      = (2 : ℝ) ^ (-(5 : ℝ) / 3) * (Real.log L ^ ((5 : ℝ) / 3))⁻¹ := by
    rw [Real.mul_rpow (by norm_num) hl.le, show (-(5 : ℝ) / 3) = -((5 : ℝ) / 3) by ring,
      Real.rpow_neg hl.le]
  -- the power of two
  have h2 : (2 : ℝ) ^ (-(2 : ℝ) / 3) * (2 : ℝ) ^ (-(5 : ℝ) / 3) = ((2 : ℝ) ^ ((7 : ℝ) / 3))⁻¹ := by
    rw [← Real.rpow_add (by norm_num), ← Real.rpow_neg (by norm_num)]
    norm_num
  have h7 := two_rpow_seven_thirds_le
  have h7pos : 0 < (2 : ℝ) ^ ((7 : ℝ) / 3) := Real.rpow_pos_of_pos (by norm_num) _
  have h6 : (1 : ℝ) / 6 ≤ ((2 : ℝ) ^ ((7 : ℝ) / 3))⁻¹ := by
    rw [one_div]; exact inv_anti₀ h7pos h7
  have hA0 : 0 ≤ (2 * L ^ ((3 : ℝ) / 5)) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  have hB0 : 0 ≤ (2 * Real.log L) ^ (-(5 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  have hprod := mul_le_mul hA hB hB0 (Real.rpow_nonneg hlt0.le _)
  unfold RHTower.vkHadamardWidth
  rw [hAeq, hBeq] at hprod
  have hkey : (2 : ℝ) ^ (-(2 : ℝ) / 3) * (L ^ ((2 : ℝ) / 5))⁻¹
        * ((2 : ℝ) ^ (-(5 : ℝ) / 3) * (Real.log L ^ ((5 : ℝ) / 3))⁻¹)
      = ((2 : ℝ) ^ ((7 : ℝ) / 3))⁻¹ * (L ^ ((2 : ℝ) / 5) * Real.log L ^ ((5 : ℝ) / 3))⁻¹ := by
    rw [← h2, mul_inv]; ring
  rw [hkey] at hprod
  have hpq : 0 < L ^ ((2 : ℝ) / 5) * Real.log L ^ ((5 : ℝ) / 3) := mul_pos hp hq
  have hlow : 1 / 6 * (L ^ ((2 : ℝ) / 5) * Real.log L ^ ((5 : ℝ) / 3))⁻¹
      ≤ ((2 : ℝ) ^ ((7 : ℝ) / 3))⁻¹ * (L ^ ((2 : ℝ) / 5) * Real.log L ^ ((5 : ℝ) / 3))⁻¹ :=
    mul_le_mul_of_nonneg_right h6 (inv_nonneg.mpr hpq.le)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have hfin : 1 / 6 * (L ^ ((2 : ℝ) / 5) * Real.log L ^ ((5 : ℝ) / 3))⁻¹
      ≤ Real.log t ^ (-(2 : ℝ) / 3) * Real.log (Real.log t) ^ (-(5 : ℝ) / 3) := le_trans hlow hprod
  have hinv : (L ^ ((2 : ℝ) / 5) * Real.log L ^ ((5 : ℝ) / 3))⁻¹
      * (L ^ ((2 : ℝ) / 5) * Real.log L ^ ((5 : ℝ) / 3)) = 1 := inv_mul_cancel₀ hpq.ne'
  nlinarith [hfin, hinv, hpq]


theorem vkKappa_saving_eq (L b : ℝ) :
    2 * (vkKappa * (L / b) / 2) = 1 / (6 * 10 ^ 8 * b) / 2 * L := by
  unfold vkKappa
  rcases eq_or_ne b 0 with hb | hb
  · subst hb; simp
  · field_simp; ring

/-- **The thresholds of the Vinogradov–Korobov contour.**  For large `N`, with `T = vkHeight N`,
`L = log N`, `w = vkHadamardWidth` and `u = vkUniformRegWidth δ T`: `L₀ ≤ log T`, `8 ≤ log T`,
`2√L ≤ log T ≤ L`, `1/w(T+1) ≤ 6·10⁸ L`, `0 < u ≤ 1/8`, `1/u ≤ 12·10⁸ L` and `2s ≤ u L`. -/
theorem eventually_vk_conditions {δ : ℝ} (hδ : 0 < δ) (L₀ : ℝ) :
    ∀ᶠ N : ℝ in atTop,
      3 ≤ N ∧ 3 ≤ Real.log N ∧ L₀ ≤ Real.log (vkHeight N) ∧ 8 ≤ Real.log (vkHeight N)
      ∧ 2 * Real.sqrt (Real.log N) ≤ Real.log (vkHeight N)
      ∧ Real.log (vkHeight N) ≤ Real.log N
      ∧ 0 < RHTower.vkHadamardWidth (vkHeight N + 1)
      ∧ 1 / RHTower.vkHadamardWidth (vkHeight N + 1) ≤ 6 * 10 ^ 8 * Real.log N
      ∧ 0 < vkUniformRegWidth δ (vkHeight N) ∧ vkUniformRegWidth δ (vkHeight N) ≤ 1 / 8
      ∧ 1 / vkUniformRegWidth δ (vkHeight N) ≤ 12 * 10 ^ 8 * Real.log N
      ∧ 2 * vkSaving N ≤ vkUniformRegWidth δ (vkHeight N) * Real.log N := by
  have hκ := vkKappa_pos
  have hκ1 : vkKappa ≤ 1 := by unfold vkKappa; norm_num
  have hgrow : ∀ᶠ N : ℝ in atTop, 1 / (6 * 10 ^ 8 * δ) ≤ Real.log N ^ ((2 : ℝ) / 5) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 5)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (16 + L₀ ^ 2),
    eventually_logLog_rpow_le ((5 : ℝ) / 3) (by norm_num : (0 : ℝ) < 1 / 10) (half_pos hκ), hgrow]
    with N hN3 hLbig hA hG
  set L := Real.log N with hLdef
  have hL16 : 16 ≤ L := by nlinarith [sq_nonneg L₀]
  have hL0 : 0 < L := by linarith
  have hl1 : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]
    have := Real.exp_one_lt_d9; linarith
  have hl0 : 0 < Real.log L := by linarith
  set p := L ^ ((2 : ℝ) / 5) with hpdef
  set q := Real.log L ^ ((5 : ℝ) / 3) with hqdef
  set r := L ^ ((1 : ℝ) / 10) with hrdef
  have hp1 : 1 ≤ p := Real.one_le_rpow (by linarith) (by norm_num)
  have hq1 : 1 ≤ q := Real.one_le_rpow hl1 (by norm_num)
  have hpr : p * r = Real.sqrt L := by
    rw [hpdef, hrdef, ← Real.rpow_add hL0, Real.sqrt_eq_rpow]; norm_num
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hs4 : 4 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) hL0.le]; linarith
  have hsL0 : |L₀| ≤ Real.sqrt L := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hsLe : Real.sqrt L ≤ L := by nlinarith
  have hpq0 : 0 < p * q := by positivity
  have hpq : p * q ≤ vkKappa / 2 * Real.sqrt L := by
    have h1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℝ) ≤ p)
    calc p * q ≤ p * (vkKappa / 2 * r) := h1
      _ = vkKappa / 2 * (p * r) := by ring
      _ = vkKappa / 2 * Real.sqrt L := by rw [hpr]
  have hpqL : p * q ≤ L := by
    have : vkKappa / 2 * Real.sqrt L ≤ Real.sqrt L := by nlinarith
    linarith
  have hσ : vkScale N = L / (p * q) := vkScale_eq hL0 hl0
  have hLg : Real.log (vkHeight N) = vkKappa * (L / (p * q)) := by rw [log_vkHeight, hσ]
  have hLg2 : 2 * Real.sqrt L ≤ Real.log (vkHeight N) := by
    rw [hLg, mul_div_assoc', le_div_iff₀ hpq0]
    have h1 := mul_le_mul_of_nonneg_left hpq (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt L)
    calc 2 * Real.sqrt L * (p * q) ≤ 2 * Real.sqrt L * (vkKappa / 2 * Real.sqrt L) := h1
      _ = vkKappa * (Real.sqrt L * Real.sqrt L) := by ring
      _ = vkKappa * L := by rw [hsq]
  have hLpq1 : L / (p * q) ≤ L := div_le_self hL0.le (by nlinarith)
  have hLgL : Real.log (vkHeight N) ≤ L := by
    rw [hLg]
    calc vkKappa * (L / (p * q)) ≤ 1 * (L / (p * q)) :=
          mul_le_mul_of_nonneg_right hκ1 (by positivity)
      _ ≤ L := by rw [one_mul]; exact hLpq1
  have h35 : L ^ ((3 : ℝ) / 5) * p = L := by rw [hpdef, ← Real.rpow_add hL0]; norm_num
  have hLg35 : Real.log (vkHeight N) ≤ L ^ ((3 : ℝ) / 5) := by
    rw [hLg]
    have h1 : L / (p * q) ≤ L / p :=
      div_le_div_of_nonneg_left hL0.le (by positivity) (by nlinarith)
    have hLp : L / p = L ^ ((3 : ℝ) / 5) := by
      rw [div_eq_iff (by positivity)]; exact h35.symm
    calc vkKappa * (L / (p * q)) ≤ 1 * (L / (p * q)) :=
          mul_le_mul_of_nonneg_right hκ1 (by positivity)
      _ ≤ L / p := by rw [one_mul]; exact h1
      _ = L ^ ((3 : ℝ) / 5) := hLp
  have hT0 : 0 < vkHeight N := Real.exp_pos _
  set T := vkHeight N with hTdef
  clear_value T
  have hLg8 : 8 ≤ Real.log T := by linarith
  have hT1 : 1 ≤ T := by
    have := Real.add_one_le_exp (Real.log T)
    rw [Real.exp_log hT0] at this; linarith
  have hlogt : Real.log T ≤ Real.log (T + 1) := Real.log_le_log hT0 (by linarith)
  have hlogt2 : Real.log (T + 1) ≤ 2 * Real.log T := by
    have h2T : Real.log (T + 1) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne'] at h2T
    have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
    linarith
  have hll1 : 1 ≤ Real.log (Real.log (T + 1)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hll2 : Real.log (Real.log (T + 1)) ≤ 2 * Real.log L := by
    have hle : Real.log (T + 1) ≤ L ^ 2 := by nlinarith
    have h1 := Real.log_le_log (by linarith) hle
    rw [Real.log_pow] at h1; push_cast at h1; linarith
  have hlt35 : Real.log (T + 1) ≤ 2 * L ^ ((3 : ℝ) / 5) := by linarith
  have hw := vkHadamardWidth_ge_of_log_le hL0 hl0 (by linarith) hll1 hlt35 hll2
  have hm0 : 0 < 1 / (6 * 10 ^ 8 * (p * q)) := by positivity
  set m := 1 / (6 * 10 ^ 8 * (p * q)) with hmdef
  clear_value m
  have hw0 : 0 < RHTower.vkHadamardWidth (T + 1) := lt_of_lt_of_le hm0 hw
  have hLm : 6 * 10 ^ 8 * L * m = L / (p * q) := by rw [hmdef]; field_simp
  have hLpq : 1 ≤ L / (p * q) := by rw [le_div_iff₀ hpq0]; linarith
  have hwinv : 1 / RHTower.vkHadamardWidth (T + 1) ≤ 6 * 10 ^ 8 * L := by
    rw [div_le_iff₀ hw0]
    have h1 := mul_le_mul_of_nonneg_left hw (by positivity : (0 : ℝ) ≤ 6 * 10 ^ 8 * L)
    linarith
  have hδm : m ≤ δ := by
    rw [hmdef, div_le_iff₀ (by positivity)]
    have h1 := hG
    rw [div_le_iff₀ (by positivity)] at h1
    calc (1 : ℝ) ≤ p * (6 * 10 ^ 8 * δ) * 1 := by rw [mul_one]; exact h1
      _ ≤ p * (6 * 10 ^ 8 * δ) * q := mul_le_mul_of_nonneg_left hq1 (by positivity)
      _ = δ * (6 * 10 ^ 8 * (p * q)) := by ring
  have hmin : m ≤ min δ (RHTower.vkHadamardWidth (T + 1)) := le_min hδm hw
  have hu : vkUniformRegWidth δ T = min δ (RHTower.vkHadamardWidth (T + 1)) / 2 := rfl
  have hwle : RHTower.vkHadamardWidth (T + 1) ≤ 1 / 10 ^ 8 := by
    unfold RHTower.vkHadamardWidth
    have h1 : Real.log (T + 1) ^ (-(2 : ℝ) / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have h2 : Real.log (Real.log (T + 1)) ^ (-(5 : ℝ) / 3) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hll1 (by norm_num)
    have h3 := mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) zero_le_one
    exact div_le_div_of_nonneg_right (by linarith) (by norm_num)
  have hminle : min δ (RHTower.vkHadamardWidth (T + 1)) ≤ RHTower.vkHadamardWidth (T + 1) :=
    min_le_right _ _
  have hu0 : 0 < vkUniformRegWidth δ T := by rw [hu]; linarith only [hm0, hmin]
  refine ⟨hN3, by linarith only [hL16], ?_, hLg8, hLg2, hLgL, hw0, hwinv, hu0, ?_, ?_, ?_⟩
  · linarith only [le_abs_self L₀, hsL0, hLg2, hs4]
  · rw [hu]; linarith only [hminle, hwle]
  · rw [div_le_iff₀ hu0, hu]
    have h1 := mul_le_mul_of_nonneg_left hmin (by positivity : (0 : ℝ) ≤ 12 * 10 ^ 8 * L)
    linarith only [h1, hLm, hLpq]
  · rw [hu, vkSaving, hσ]
    rw [vkKappa_saving_eq L (p * q), ← hmdef]
    exact mul_le_mul_of_nonneg_right (by linarith only [hmin]) hL0.le

end

end RHTower.Sieve
