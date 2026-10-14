import GaloisForLFunctions.RHTower.InversionSymmetricFourierBlindRigidity

/-!
# Odd inversion-symmetric Fourier-blind functions: rigidity at an open cusp

Let `G : ℝ → ℝ` be continuous and odd, with `G(1/x) = x G(x)` for `x > 0`, vanishing on `[0, c)`,
and with Fourier transform vanishing at every integer `|n| ≥ 2`.

**Theorem** (`eq_zero_of_inversionSymmetric_odd_fourierBlind_of_golden`).  If `c² + c > 1`, then
`G = 0`.

**Proof.**  Put `β = 2 Im Ĝ(1)` and `H(v) = G(1 − 1/v)/v`.
* *Poisson periodization* (`tsum_add_eq_of_odd_fourierBlind`): `Ĝ` is odd, so `Ĝ(0) = 0` and
  `Σ_k G(x + k) = −β sin 2πx`.
* *Parabolic recursion* (`inversionSymmetric_odd_parabolic_recursion`): for `c > ½` and
  `v ≥ max(2, c/(2c − 1))` only the translates `1 − 1/v` and `−1 − 1/v` of `x = 1 − 1/v` meet
  the support, and inversion gives `H(v) = H(v + 1) + β sin(2π/v)/v`.  In
  `H(v) = χ H(v + 1) + …` the parabolic character is `χ = +1`, so the cusp is open; there is no
  pole term `a/v` because `Ĝ(0) = 0`.
* *Sign of the profile*: for `v > 2` every term `sin(2π/(v + k))/(v + k)` is positive.
  Telescoping from `v₀ ∈ (max(2, c/(2c − 1)), 1/(1 − c))`, where `H(v₀) = 0`, gives
  `|H(v₀ + N)| ≥ |β| sin(2π/v₀)/v₀` for `N ≥ 1`, while `H(v₀ + N) → 0`.  Hence `β = 0`; then `H`
  is `1`-periodic on `[v₀, ∞)` and tends to `0`, so it vanishes there.
* *Conclusion*: `H = 0` on `[2, ∞)`, so `G = 0` on `[0, 1)`, at `1` by continuity, on `(1, ∞)` by
  inversion and on `(−∞, 0)` by oddness.

For even `G` (`eq_zero_of_inversionSymmetric_fourierBlind_of_golden`) the parabolic character is
`χ = −1` (closed cusp), the profile is an alternating series with pole coefficient
`Re Ĝ(0) + 2 Re Ĝ(1)`, and the identity theorem is needed.  For odd `G` the cusp is open, the pole
coefficient vanishes, and the profile has a sign, so no analytic continuation is used.
-/

open MeasureTheory Set Real Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

/-- The Fourier transform of an odd function is odd. -/
theorem fourier_neg_of_odd {G : ℝ → ℝ} (hodd : ∀ x, G (-x) = -G x) (w : ℝ) :
    𝓕 (fun x => (G x : ℂ)) (-w) = -𝓕 (fun x => (G x : ℂ)) w := by
  have h1 := integral_neg_eq_self
    (fun v : ℝ => Complex.exp (↑(-2 * π * v * w) * Complex.I) • ((G v : ℝ) : ℂ)) volume
  rw [fourier_real_eq_integral_exp_smul, fourier_real_eq_integral_exp_smul, ← h1, ← integral_neg]
  congr 1
  funext v
  simp only [hodd, Complex.ofReal_neg, smul_neg, neg_neg]
  congr 3
  push_cast
  ring

/-- **Poisson periodization of an odd Fourier-blind function.**  For a continuous, compactly
supported, odd real `G` whose Fourier transform vanishes at every integer `|n| ≥ 2`,
`Σ_k G(x + k) = −2 Im Ĝ(1) sin 2πx`. -/
theorem tsum_add_eq_of_odd_fourierBlind {G : ℝ → ℝ} (hG : Continuous G)
    (hcpt : HasCompactSupport G) (hodd : ∀ x, G (-x) = -G x)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0) (x : ℝ) :
    ∑' k : ℤ, G (x + k) = -2 * (𝓕 (fun x => (G x : ℂ)) 1).im * Real.sin (2 * π * x) := by
  set ρ : C(ℝ, ℂ) := ⟨fun x => (G x : ℂ), Complex.continuous_ofReal.comp hG⟩ with hρ
  have hρc : (ρ : ℝ → ℂ) = fun x => (G x : ℂ) := rfl
  obtain ⟨B, hB⟩ : ∃ B, ∀ y, G y ≠ 0 → |y| ≤ B := by
    obtain ⟨B, hB⟩ := hcpt.isCompact.isBounded.subset_closedBall 0
    refine ⟨B, fun y hy => ?_⟩
    have := hB (subset_tsupport _ hy)
    rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  have hout : ∀ n : ℤ, n ∉ Finset.Icc (-1 : ℤ) 1 → 2 ≤ |n| := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [le_abs']
    omega
  have h_sum : Summable fun n : ℤ => 𝓕 (ρ : ℝ → ℂ) n := by
    refine summable_of_ne_finset_zero (s := Finset.Icc (-1 : ℤ) 1) fun n hn => ?_
    rw [hρc, hblind n (hout n hn)]
  have h_norm : ∀ K : TopologicalSpace.Compacts ℝ,
      Summable fun n : ℤ => ‖(ρ.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ := by
    intro K
    obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
    obtain ⟨N, hN⟩ := exists_int_gt (R + B)
    refine summable_of_ne_finset_zero (s := Finset.Icc (-N) N) fun n hn => ?_
    rw [norm_eq_zero]
    ext ⟨y, hy⟩
    have hyR : |y| ≤ R := by
      have := hR hy
      rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
    have hn' : (N : ℝ) < |(n : ℝ)| := by
      rw [Finset.mem_Icc] at hn
      have : N < |n| := by rw [lt_abs]; omega
      exact_mod_cast this
    have hbig : B < |y + n| := by
      have h3 := abs_add_le (y + n) (-y)
      have e1 : y + n + -y = (n : ℝ) := by ring
      rw [e1, abs_neg] at h3
      linarith
    simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_addRight, ContinuousMap.zero_apply, hρ, ContinuousMap.coe_mk]
    by_contra hne
    have hne' : G (y + n) ≠ 0 := fun h => hne (by rw [h, Complex.ofReal_zero])
    linarith [hB _ hne']
  have hP := Real.tsum_eq_tsum_fourier h_norm h_sum x
  have hL : (∑' k : ℤ, ρ (x + k)) = ((∑' k : ℤ, G (x + k) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]; rfl
  rw [hL] at hP
  conv_rhs at hP => rw [tsum_eq_sum (s := Finset.Icc (-1 : ℤ) 1) fun n hn => by
    rw [hρc, hblind n (hout n hn), zero_mul]]
  have hI : Finset.Icc (-1 : ℤ) 1 = {-1, 0, 1} := by decide
  rw [hI, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton] at hP
  have hneg : 𝓕 (fun x => (G x : ℂ)) ((-1 : ℤ) : ℝ) = -𝓕 (fun x => (G x : ℂ)) 1 := by
    rw [show ((-1 : ℤ) : ℝ) = -1 by norm_num]
    exact fourier_neg_of_odd hodd 1
  have hzero : 𝓕 (fun x => (G x : ℂ)) ((0 : ℤ) : ℝ) = 0 := by
    have h0 := fourier_neg_of_odd hodd 0
    rw [neg_zero] at h0
    rw [Int.cast_zero]
    linear_combination h0 / 2
  have hre := congrArg Complex.re hP
  rw [Complex.ofReal_re] at hre
  rw [hre]
  simp only [hρc, fourier_coe_apply]
  have hexp : ∀ n : ℤ, Complex.exp (2 * ↑π * Complex.I * (n : ℂ) * ↑x / ((1 : ℝ) : ℂ)) =
      ((Real.cos (n * (2 * π * x)) : ℝ) : ℂ) +
        ((Real.sin (n * (2 * π * x)) : ℝ) : ℂ) * Complex.I := by
    intro n
    rw [show 2 * ↑π * Complex.I * (n : ℂ) * ↑x / ((1 : ℝ) : ℂ) =
      ((n * (2 * π * x) : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [hexp]
  rw [hneg, hzero]
  simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, neg_mul, one_mul, zero_mul, zero_add,
    Real.cos_neg, Real.sin_neg, Complex.mul_re, Complex.add_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.mul_im,
    Complex.add_im]
  ring

/-- A continuous odd inversion-symmetric function vanishing on `[0, 1)` vanishes. -/
theorem eq_zero_of_inversionSymmetric_odd_of_zero_on_Ico {G : ℝ → ℝ} (hG : Continuous G)
    (hodd : ∀ x, G (-x) = -G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x)
    (h01 : ∀ x, 0 ≤ x → x < 1 → G x = 0) (y : ℝ) : G y = 0 := by
  have hcl : IsClosed {x | G x = 0} := isClosed_eq hG continuous_const
  have h1 : G 1 = 0 := by
    have hsub : Ico (0 : ℝ) 1 ⊆ {x | G x = 0} := fun x hx => h01 x hx.1 hx.2
    have := hcl.closure_subset_iff.mpr hsub
    rw [closure_Ico (by norm_num)] at this
    exact this ⟨by norm_num, le_rfl⟩
  have hpos : ∀ x, 0 ≤ x → G x = 0 := by
    intro x hx
    rcases lt_trichotomy x 1 with h | h | h
    · exact h01 x hx h
    · rw [h]; exact h1
    · have hx0 : 0 < x := by linarith
      have hi := hinv x hx0
      rw [h01 x⁻¹ (inv_nonneg.mpr hx) (inv_lt_one_of_one_lt₀ h)] at hi
      exact (mul_eq_zero.mp hi.symm).resolve_left hx0.ne'
  rcases le_or_gt 0 y with hy | hy
  · exact hpos y hy
  · have h := hodd (-y)
    rw [neg_neg, hpos (-y) (by linarith), neg_zero] at h
    exact h

section Odd

variable {G : ℝ → ℝ} (hG : Continuous G) (hodd : ∀ x, G (-x) = -G x)
  (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x) {c : ℝ} (hc : 1 / 2 < c)
  (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0)
  (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0)
include hG hodd hinv hc hsupp hblind

/-- **Four-term periodization.**  For `c > ½` and `v ≥ 2`,
`G(1 − 1/v) + G(2 − 1/v) − G(1 + 1/v) = 2 Im Ĝ(1) sin(2π/v)`. -/
theorem inversionSymmetric_odd_four_term_periodization {v : ℝ} (hv2 : 2 ≤ v) :
    G (1 - 1 / v) + G (2 - 1 / v) - G (1 + 1 / v) =
      2 * (𝓕 (fun x => (G x : ℂ)) 1).im * Real.sin (2 * π / v) := by
  have hc0 : 0 < c := by linarith
  have hbig := inversionSymmetric_eq_zero_of_inv_le hG hinv hc0 hsupp
  have hcpt : HasCompactSupport G := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -c⁻¹) (b := c⁻¹)) fun x hx => ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · have hz : G (-x) = 0 := hbig _ (by linarith)
      have h := hodd (-x)
      rw [neg_neg, hz, neg_zero] at h
      exact h
    · exact hbig _ hx.le
  have hci2 : c⁻¹ < 2 := by rw [inv_lt_comm₀ hc0 (by norm_num)]; linarith
  have hv0 : 0 < v := by linarith
  have hinvv : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv2
  have hinvv0 : 0 < 1 / v := by positivity
  have h := tsum_add_eq_of_odd_fourierBlind hG hcpt hodd hblind (1 - 1 / v)
  rw [tsum_eq_sum (s := {0, -2, 1}) fun k hk => ?_] at h
  · rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
      Finset.sum_singleton] at h
    have e0 : 1 - 1 / v + ((0 : ℤ) : ℝ) = 1 - 1 / v := by simp
    have e2 : G (1 - 1 / v + ((-2 : ℤ) : ℝ)) = -G (1 + 1 / v) := by
      rw [← hodd]; congr 1; push_cast; ring
    have e1 : 1 - 1 / v + ((1 : ℤ) : ℝ) = 2 - 1 / v := by push_cast; ring
    have hsin : Real.sin (2 * π * (1 - 1 / v)) = -Real.sin (2 * π / v) := by
      rw [show 2 * π * (1 - 1 / v) = 2 * π - 2 * π / v by ring, Real.sin_two_pi_sub]
    rw [e0, e2, e1, hsin] at h
    linarith
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    rcases le_or_gt 2 k with hk2 | hk2
    · have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      exact hbig _ (by linarith)
    rcases le_or_gt (-1) k with hkm | hkm
    · have : k = -1 := by omega
      subst this
      have h := hodd (1 / v)
      rw [hsupp _ hinvv0.le (by linarith), neg_zero] at h
      rw [show 1 - 1 / v + ((-1 : ℤ) : ℝ) = -(1 / v) by push_cast; ring, h]
    · have hk3 : k ≤ -3 := by omega
      have : (k : ℝ) ≤ -3 := by exact_mod_cast hk3
      have hz : G (-(1 - 1 / v + k)) = 0 := hbig _ (by linarith)
      have h := hodd (-(1 - 1 / v + k))
      rw [neg_neg, hz, neg_zero] at h
      exact h

/-- **The parabolic recursion at the open cusp.**  For `H(v) = G(1 − 1/v)/v`, `c > ½` and
`v ≥ max(2, c/(2c − 1))`, `H(v) − H(v + 1) = 2 Im Ĝ(1) sin(2π/v)/v`. -/
theorem inversionSymmetric_odd_parabolic_recursion {v : ℝ} (hv : max 2 (c / (2 * c - 1)) ≤ v) :
    G (1 - 1 / v) / v - G (1 - 1 / (v + 1)) / (v + 1) =
      2 * (𝓕 (fun x => (G x : ℂ)) 1).im * (Real.sin (2 * π / v) / v) := by
  have hc0 : 0 < c := by linarith
  have hbig := inversionSymmetric_eq_zero_of_inv_le hG hinv hc0 hsupp
  have h2c : 0 < 2 * c - 1 := by linarith
  have hv2 : 2 ≤ v := (le_max_left _ _).trans hv
  have hv0 : 0 < v := by linarith
  have hvw : c / (2 * c - 1) ≤ v := (le_max_right _ _).trans hv
  have hk1' : c⁻¹ ≤ 2 - 1 / v := by
    rw [div_le_iff₀ h2c] at hvw
    rw [inv_eq_one_div, div_le_iff₀ hc0]
    have : c / v ≤ 2 * c - 1 := by rw [div_le_iff₀ hv0]; linarith
    have e : (2 - 1 / v) * c = 2 * c - c / v := by ring
    linarith
  have h := inversionSymmetric_odd_four_term_periodization hG hodd hinv hc hsupp hblind hv2
  rw [hbig _ hk1', add_zero] at h
  have hvp : 0 < v + 1 := by linarith
  have hs1 : 1 - 1 / (v + 1) = v / (v + 1) := by field_simp; ring
  have hr : 0 < 1 - 1 / (v + 1) := by rw [hs1]; positivity
  have hi := hinv (1 - 1 / (v + 1)) hr
  have e1 : (1 - 1 / (v + 1))⁻¹ = 1 + 1 / v := by
    rw [hs1, inv_div]; field_simp
  rw [e1] at hi
  rw [hi] at h
  set X := G (1 - 1 / v)
  set Y := G (1 - 1 / (v + 1))
  rw [hs1] at h
  rw [mul_div_assoc', ← h]
  field_simp

end Odd

/-- **Odd inversion-symmetric Fourier-blind functions of support ratio below the golden ratio
vanish.** -/
theorem eq_zero_of_inversionSymmetric_odd_fourierBlind_of_golden {G : ℝ → ℝ} (hG : Continuous G)
    (hodd : ∀ x, G (-x) = -G x) (hinv : ∀ x, 0 < x → G x⁻¹ = x * G x) {c : ℝ} (hc0 : 0 < c)
    (hgold : 1 < c ^ 2 + c) (hsupp : ∀ x, 0 ≤ x → x < c → G x = 0)
    (hblind : ∀ n : ℤ, 2 ≤ |n| → 𝓕 (fun x => (G x : ℂ)) n = 0) (y : ℝ) : G y = 0 := by
  rcases le_or_gt 1 c with hc1 | hc1
  · exact eq_zero_of_inversionSymmetric_odd_of_zero_on_Ico hG hodd hinv
      (fun x hx hx1 => hsupp x hx (lt_of_lt_of_le hx1 hc1)) y
  have hhalf : 1 / 2 < c := by nlinarith
  set β := 2 * (𝓕 (fun x => (G x : ℂ)) 1).im with hβ
  have h2c : 0 < 2 * c - 1 := by linarith
  set vs := max 2 (c / (2 * c - 1)) with hvs
  set H : ℝ → ℝ := fun v => G (1 - 1 / v) / v with hH
  have hrec : ∀ v, vs ≤ v → H v - H (v + 1) = β * (Real.sin (2 * π / v) / v) := fun v hv =>
    inversionSymmetric_odd_parabolic_recursion hG hodd hinv hhalf hsupp hblind hv
  -- the zero range of `H`
  set w₂ := 1 / (1 - c) with hw₂
  have h1c : 0 < 1 - c := by linarith
  have hHzero : ∀ v, 2 ≤ v → v < w₂ → H v = 0 := by
    intro v hv2 hvw
    have hv0 : 0 < v := by linarith
    have hinvv : 1 / v ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hv2
    have hlt : 1 - 1 / v < c := by
      rw [hw₂, lt_div_iff₀ h1c] at hvw
      rw [show 1 - 1 / v = (v - 1) / v by field_simp, div_lt_iff₀ hv0]
      linarith
    simp only [hH]
    rw [hsupp _ (by linarith) hlt, zero_div]
  have hvsw : vs < w₂ := by
    rw [hvs, max_lt_iff]
    constructor
    · rw [hw₂, lt_div_iff₀ h1c]; linarith
    · rw [hw₂, div_lt_div_iff₀ h2c h1c]; nlinarith
  have hvs2 : 2 ≤ vs := le_max_left _ _
  -- the decay of `H`
  obtain ⟨CG, hCG⟩ : ∃ C, ∀ r, |G r| ≤ C := by
    have hcpt : HasCompactSupport G := by
      have hbig := inversionSymmetric_eq_zero_of_inv_le hG hinv hc0 hsupp
      refine HasCompactSupport.intro (isCompact_Icc (a := -c⁻¹) (b := c⁻¹)) fun x hx => ?_
      rw [mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with hx | hx
      · have hz : G (-x) = 0 := hbig _ (by linarith)
        have h := hodd (-x)
        rw [neg_neg, hz, neg_zero] at h
        exact h
      · exact hbig _ hx.le
    obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuous hG
    exact ⟨C, fun r => by rw [← Real.norm_eq_abs]; exact hC r⟩
  have hHle : ∀ v, 0 < v → |H v| ≤ CG / v := by
    intro v hv
    simp only [hH]
    rw [abs_div, abs_of_pos hv]
    exact div_le_div_of_nonneg_right (hCG _) hv.le
  have hlim : ∀ v, 0 < v → Tendsto (fun N : ℕ => CG / (v + N)) atTop (𝓝 0) := fun v _ =>
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  -- the profile has a sign, so `β = 0`
  set v₀ := (vs + w₂) / 2 with hv₀
  have hv₀s : vs < v₀ := by rw [hv₀]; linarith
  have hv₀2 : 2 < v₀ := by linarith
  set s : ℕ → ℝ := fun k => Real.sin (2 * π / (v₀ + k)) / (v₀ + k) with hs
  have hspos : ∀ k, 0 < s k := by
    intro k
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have hpos : 0 < v₀ + k := by linarith
    have hlt : 2 * π / (v₀ + k) < π := by
      rw [div_lt_iff₀ hpos]; nlinarith [Real.pi_pos]
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi (div_pos (by positivity) hpos) hlt) hpos
  have htel : ∀ N : ℕ, H v₀ - H (v₀ + N) = β * ∑ k ∈ Finset.range N, s k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have hN : (0 : ℝ) ≤ N := N.cast_nonneg
      have e : H (v₀ + N) - H (v₀ + N + 1) = β * s N := hrec (v₀ + N) (by linarith)
      rw [Finset.sum_range_succ, show v₀ + ((N + 1 : ℕ) : ℝ) = v₀ + N + 1 by push_cast; ring]
      linear_combination ih + e
  have hβ0 : β = 0 := by
    have hH0 : H v₀ = 0 := hHzero v₀ hv₀2.le (by rw [hv₀]; linarith)
    have hbd : ∀ N : ℕ, 1 ≤ N → |β| * s 0 ≤ CG / (v₀ + N) := by
      intro N hN
      have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
      have e := htel N
      rw [hH0, zero_sub] at e
      have hsum : s 0 ≤ ∑ k ∈ Finset.range N, s k :=
        Finset.single_le_sum (fun k _ => (hspos k).le) (Finset.mem_range.2 (by omega))
      calc |β| * s 0 ≤ |β| * ∑ k ∈ Finset.range N, s k :=
            mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
        _ = |H (v₀ + N)| := by
          rw [show H (v₀ + N) = -(β * ∑ k ∈ Finset.range N, s k) by linarith, abs_neg,
            abs_mul β, abs_of_pos (lt_of_lt_of_le (hspos 0) hsum)]
        _ ≤ CG / (v₀ + N) := hHle _ (by linarith)
    have hle : |β| * s 0 ≤ 0 :=
      ge_of_tendsto (hlim v₀ (by linarith)) (eventually_atTop.2 ⟨1, hbd⟩)
    have habs : |β| ≤ 0 := by nlinarith [abs_nonneg β, hspos 0]
    exact abs_nonpos_iff.mp habs
  -- with `β = 0`, `H` is `1`-periodic near the cusp and tends to `0`
  have hHcusp : ∀ v, vs ≤ v → H v = 0 := by
    intro v hv
    have hper : ∀ N : ℕ, H v = H (v + N) := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        have hN : (0 : ℝ) ≤ N := N.cast_nonneg
        have e := hrec (v + N) (by linarith)
        rw [hβ0, zero_mul, sub_eq_zero] at e
        rw [ih, e]
        congr 1
        push_cast
        ring
    have hv0 : 0 < v := by linarith
    have hbd : ∀ N : ℕ, |H v| ≤ CG / (v + N) := fun N => by
      rw [hper N]
      exact hHle _ (by have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith)
    exact abs_nonpos_iff.mp (ge_of_tendsto' (hlim v hv0) hbd)
  refine eq_zero_of_inversionSymmetric_odd_of_zero_on_Ico hG hodd hinv (fun x hx hx1 => ?_) y
  rcases lt_or_ge x (1 / 2) with hx2 | hx2
  · exact hsupp x hx (by linarith)
  · have hx1' : 0 < 1 - x := by linarith
    have hv2 : 2 ≤ 1 / (1 - x) := by rw [le_div_iff₀ hx1']; linarith
    have hx' : 1 - 1 / (1 / (1 - x)) = x := by rw [one_div_one_div]; ring
    have hHv : H (1 / (1 - x)) = 0 := by
      rcases lt_or_ge (1 / (1 - x)) w₂ with h | h
      · exact hHzero _ hv2 h
      · exact hHcusp _ (by linarith)
    simp only [hH] at hHv
    rw [hx'] at hHv
    exact (div_eq_zero_iff.mp hHv).resolve_right (one_div_pos.mpr hx1').ne'

end

end RHTower
