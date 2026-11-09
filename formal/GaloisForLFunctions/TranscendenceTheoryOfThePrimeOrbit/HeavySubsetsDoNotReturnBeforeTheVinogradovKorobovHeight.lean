import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.AZeroFreeRegionBoundsTheHeavyReturns

/-!
# Heavy subsets do not return before the Vinogradov–Korobov height

The unconditional heavy-return inequality (`heavy_return_bound_vinogradovKorobov`)
`√y ≤ K(y^{½ − w(2t)} log t + log(2 + t))`, `w(T) = (log T)^{−2/3}(log log T)^{−5/3}/10⁸`, read
at heights `log t ≤ Λ = (log y)^{3/2−ε}`: there `w(2t) log y ≥ c(log y)^{2ε/3}/(log log y)^{5/3}`
outgrows `log(KΛ)`, so the first term is `o(√y)`, and the second is `O(Λ) = o(√y)`.

* **The decay** (`eventually_vk_decay`). `K Λ exp(−w(2e^Λ)L) ≤ 1/3` for large `L`, `Λ = L^{3/2−ε}`.
* **No early heavy return** (`eventually_no_heavy_return_before_vk`). For every `0 < ε < 3/2`, for
  large `y` no `1/1000`-heavy subset of the primes `≤ y` has a return of precision `δ ≤ 1/20` at a
  height `t ≥ T₁` with `log t ≤ (log y)^{3/2−ε}`.

This is the Vinogradov–Korobov bracket `log R ≥ (log y)^{3/2−o(1)}` for heavy subsets at the top of
the column, where the weights `p^{−½}` sit; the spike argument at `ζ(1 + it)` reaches it only for
the full set of primes with weights `1/p`.
-/

open Real Filter Topology

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

/-- **The Vinogradov–Korobov decay.** For `0 < ε < 3/2` and `K > 0`, eventually in `L`,
`K Λ exp(−w(2e^Λ) L) ≤ 1/3` with `Λ = L^{3/2−ε}`. -/
theorem eventually_vk_decay {ε K : ℝ} (hε : 0 < ε) (hε1 : ε < 3 / 2) (hK : 0 < K) :
    ∀ᶠ L : ℝ in atTop, K * L ^ ((3 : ℝ) / 2 - ε) *
      Real.exp (-(RHTower.vkHadamardWidth (2 * Real.exp (L ^ ((3 : ℝ) / 2 - ε))) * L)) ≤ 1 / 3 := by
  set a : ℝ := 3 / 2 - ε with ha
  have ha0 : 0 < a := by linarith
  have ha2 : a ≤ 3 / 2 := by linarith
  set r : ℝ := 2 * ε / 3 with hr
  have hr0 : 0 < r := by positivity
  set c₀ : ℝ := (2 : ℝ) ^ (-(2 : ℝ) / 3) * (2 : ℝ) ^ (-(5 : ℝ) / 3) / 10 ^ 8 with hc₀def
  have hc₀ : 0 < c₀ := by positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (8 / 3 : ℝ) hr0).bound (show 0 < c₀ / 3 by positivity)
  filter_upwards [hlo, eventually_ge_atTop (max 4 (Real.exp (max 1 |Real.log (3 * K)|)))] with
    L hL hL4
  have hL4' : 4 ≤ L := le_trans (le_max_left _ _) hL4
  have hL0 : 0 < L := by linarith
  have hlogL : max 1 |Real.log (3 * K)| ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]; exact le_trans (le_max_right _ _) hL4
  have hlogL1 : 1 ≤ Real.log L := le_trans (le_max_left _ _) hlogL
  have hlogK : |Real.log (3 * K)| ≤ Real.log L := le_trans (le_max_right _ _) hlogL
  set Λ := L ^ a with hΛ
  have hΛ1 : 1 ≤ Λ := Real.one_le_rpow (by linarith) ha0.le
  set M := Real.log (2 * Real.exp Λ) with hMdef
  have hM : M = Real.log 2 + Λ := by
    rw [hMdef, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hM1 : 1 < M := by rw [hM]; linarith
  have hM2 : M ≤ 2 * Λ := by rw [hM]; linarith
  have hlogM0 : 0 < Real.log M := Real.log_pos hM1
  have hlogM : Real.log M ≤ Real.log (2 * Λ) := Real.log_le_log (by linarith) hM2
  have hlogΛ : Real.log Λ = a * Real.log L := by rw [hΛ, Real.log_rpow hL0]
  have hlog2Λ : Real.log (2 * Λ) ≤ 2 * Real.log L := by
    rw [Real.log_mul (by norm_num) (by linarith), hlogΛ]
    have h4 : Real.log 4 ≤ Real.log L := Real.log_le_log (by norm_num) hL4'
    have h4' : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    nlinarith
  -- the width times `L`
  have hpow1 : (2 * Λ) ^ (-(2 : ℝ) / 3) * L = (2 : ℝ) ^ (-(2 : ℝ) / 3) * L ^ r := by
    rw [Real.mul_rpow (by norm_num) (by linarith), hΛ, ← Real.rpow_mul hL0.le, mul_assoc]
    congr 1
    conv_lhs => rw [show L ^ (a * (-(2 : ℝ) / 3)) * L = L ^ (a * (-(2 : ℝ) / 3)) * L ^ (1 : ℝ) by
      rw [Real.rpow_one]]
    rw [← Real.rpow_add hL0]
    congr 1
    rw [ha, hr]; ring
  have hpow2 : (2 * Real.log L) ^ (-(5 : ℝ) / 3) =
      (2 : ℝ) ^ (-(5 : ℝ) / 3) * Real.log L ^ (-(5 : ℝ) / 3) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have hw : c₀ * L ^ r * Real.log L ^ (-(5 : ℝ) / 3) ≤
      RHTower.vkHadamardWidth (2 * Real.exp Λ) * L := by
    unfold RHTower.vkHadamardWidth
    rw [← hMdef]
    have h1 : (2 * Λ) ^ (-(2 : ℝ) / 3) ≤ M ^ (-(2 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hM2 (by norm_num)
    have h2 : (2 * Real.log L) ^ (-(5 : ℝ) / 3) ≤ Real.log M ^ (-(5 : ℝ) / 3) :=
      Real.rpow_le_rpow_of_nonpos hlogM0 (hlogM.trans hlog2Λ) (by norm_num)
    have hpos1 : 0 ≤ (2 * Λ) ^ (-(2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
    have hpos2 : 0 ≤ (2 * Real.log L) ^ (-(5 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
    calc c₀ * L ^ r * Real.log L ^ (-(5 : ℝ) / 3)
        = (2 * Λ) ^ (-(2 : ℝ) / 3) * L * (2 * Real.log L) ^ (-(5 : ℝ) / 3) / 10 ^ 8 := by
          rw [hpow1, hpow2, hc₀def]; ring
      _ ≤ M ^ (-(2 : ℝ) / 3) * L * Real.log M ^ (-(5 : ℝ) / 3) / 10 ^ 8 := by
          gcongr
      _ = M ^ (-(2 : ℝ) / 3) * Real.log M ^ (-(5 : ℝ) / 3) / 10 ^ 8 * L := by ring
  -- `log(3KΛ) ≤ wL`
  have hlL : 0 < Real.log L := by linarith
  have hgrow : 3 * Real.log L ≤ c₀ * L ^ r * Real.log L ^ (-(5 : ℝ) / 3) := by
    have hb : Real.log L ^ (8 / 3 : ℝ) ≤ c₀ / 3 * L ^ r := by
      have := hL
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlL.le _), Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg hL0.le _)] at this
      exact this
    have hsplit : Real.log L ^ (8 / 3 : ℝ) = Real.log L * Real.log L ^ ((5 : ℝ) / 3) := by
      conv_rhs => rw [show Real.log L * Real.log L ^ ((5 : ℝ) / 3) =
        Real.log L ^ (1 : ℝ) * Real.log L ^ ((5 : ℝ) / 3) by rw [Real.rpow_one]]
      rw [← Real.rpow_add hlL]; norm_num
    have hinv : Real.log L ^ (-(5 : ℝ) / 3) * Real.log L ^ ((5 : ℝ) / 3) = 1 := by
      rw [← Real.rpow_add hlL]; norm_num
    have hp : 0 < Real.log L ^ ((5 : ℝ) / 3) := Real.rpow_pos_of_pos hlL _
    have : 3 * Real.log L * Real.log L ^ ((5 : ℝ) / 3) ≤
        c₀ * L ^ r * Real.log L ^ (-(5 : ℝ) / 3) * Real.log L ^ ((5 : ℝ) / 3) := by
      rw [mul_assoc (c₀ * L ^ r), hinv, mul_one]
      nlinarith
    exact le_of_mul_le_mul_right this hp
  have hlog3KΛ : Real.log (3 * K * Λ) ≤ RHTower.vkHadamardWidth (2 * Real.exp Λ) * L := by
    rw [Real.log_mul (by positivity) (by linarith), hlogΛ]
    have : Real.log (3 * K) ≤ |Real.log (3 * K)| := le_abs_self _
    nlinarith
  -- conclude
  have hpos : 0 < 3 * K * Λ := by positivity
  have hexp : Real.exp (-(RHTower.vkHadamardWidth (2 * Real.exp Λ) * L)) ≤ (3 * K * Λ)⁻¹ := by
    rw [← Real.exp_log hpos, ← Real.exp_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  calc K * Λ * Real.exp (-(RHTower.vkHadamardWidth (2 * Real.exp Λ) * L))
      ≤ K * Λ * (3 * K * Λ)⁻¹ := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 1 / 3 := by field_simp

/-- `6K L^{3/2−ε} ≤ e^{L/2}` for large `L`. -/
theorem eventually_six_mul_rpow_le_exp {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K) :
    ∀ᶠ L : ℝ in atTop, 6 * K * L ^ ((3 : ℝ) / 2 - ε) ≤ Real.exp (L / 2) := by
  have hlo := (isLittleO_pow_exp_pos_mul_atTop 2 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show (0 : ℝ) < 1 / (6 * K) by positivity)
  filter_upwards [hlo, eventually_ge_atTop 1] with L hL hL1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_pos _).le] at hL
  have hle : L ^ ((3 : ℝ) / 2 - ε) ≤ L ^ 2 := by
    rw [show L ^ 2 = L ^ (2 : ℝ) by norm_cast]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have he : Real.exp (1 / 2 * L) = Real.exp (L / 2) := by ring_nf
  rw [he] at hL
  calc 6 * K * L ^ ((3 : ℝ) / 2 - ε) ≤ 6 * K * L ^ 2 := by gcongr
    _ ≤ 6 * K * (1 / (6 * K) * Real.exp (L / 2)) := by gcongr
    _ = Real.exp (L / 2) := by field_simp

/-- **Heavy subsets do not return before the Vinogradov–Korobov height.** For every
`0 < ε < 3/2`, for large `y`, no `1/1000`-heavy subset of the primes `≤ y` has a return of
precision `δ ≤ 1/20` at a height `t ≥ T₁` with `log t ≤ (log y)^{3/2−ε}`. -/
theorem eventually_no_heavy_return_before_vk {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 3 / 2) :
    ∃ T₁ : ℝ, ∀ᶠ y : ℕ in atTop, ∀ H : Finset ℕ, IsHeavy y (1 / 1000) H →
      ∀ δ t : ℝ, 0 ≤ δ → δ ≤ 1 / 20 → T₁ ≤ t → Real.log t ≤ Real.log y ^ ((3 : ℝ) / 2 - ε) →
        ¬ IsDeltaReturn H (fun p : ℕ => Real.log p) δ t := by
  obtain ⟨K, hK, T₁, hev⟩ := heavy_return_bound_vinogradovKorobov
  refine ⟨max T₁ (Real.exp (Real.exp 1)), ?_⟩
  have hlog : Tendsto (fun y : ℕ => Real.log y) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hev, hlog.eventually (eventually_vk_decay hε hε1 hK),
    hlog.eventually (eventually_six_mul_rpow_le_exp hε hK), eventually_ge_atTop 2] with
    y hy hdec hsq hy2 H hH δ t hδ0 hδ ht hlt hret
  have hb := hy H hH δ t hδ0 hδ ((le_max_left _ _).trans ht) hret
  have hy0' : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hsqrt : Real.sqrt y = Real.exp (Real.log y / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy0']; ring_nf
  set L := Real.log y
  set Λ := L ^ ((3 : ℝ) / 2 - ε)
  have hy0 : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (by omega : 1 ≤ y)
  have hee : Real.exp (Real.exp 1) ≤ t := (le_max_right _ _).trans ht
  have he2 : (2 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 := Real.add_one_le_exp (Real.exp 1)
    have h2 := Real.add_one_le_exp (1 : ℝ)
    linarith
  have ht2 : 2 ≤ t := he2.trans hee
  have ht0 : 0 < t := by linarith
  have hlt0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  -- `log(2 + t) ≤ 2Λ`
  have hl2t : Real.log (2 + t) ≤ 2 * Λ := by
    have h1 : Real.log (2 + t) ≤ Real.log (2 * t) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith)] at h1
    have : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht2
    linarith
  -- the width at `2t` is at least the width at `2e^Λ`
  have h2t : 2 * t ≤ 2 * Real.exp Λ := by
    have : t ≤ Real.exp Λ := by rw [← Real.exp_log ht0]; exact Real.exp_le_exp.mpr hlt
    linarith
  have hwle : RHTower.vkHadamardWidth (2 * Real.exp Λ) ≤ RHTower.vkHadamardWidth (2 * t) :=
    RHTower.vkHadamardWidth_antitoneOn (Set.mem_Ici.mpr (by linarith))
      (Set.mem_Ici.mpr (by linarith)) h2t
  have hsplit : (y : ℝ) ^ (1 / 2 - RHTower.vkHadamardWidth (2 * t)) =
      Real.sqrt y / (y : ℝ) ^ RHTower.vkHadamardWidth (2 * t) := by
    rw [Real.rpow_sub hy0, ← Real.sqrt_eq_rpow]
  have hypow : Real.exp (RHTower.vkHadamardWidth (2 * Real.exp Λ) * L) ≤
      (y : ℝ) ^ RHTower.vkHadamardWidth (2 * t) := by
    rw [Real.rpow_def_of_pos hy0]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ L := Real.log_nonneg hy1
    nlinarith
  have hfirst : K * ((y : ℝ) ^ (1 / 2 - RHTower.vkHadamardWidth (2 * t)) * Real.log t) ≤
      Real.sqrt y / 3 := by
    rw [hsplit]
    have hposE := Real.exp_pos (RHTower.vkHadamardWidth (2 * Real.exp Λ) * L)
    have h1 : Real.sqrt y / (y : ℝ) ^ RHTower.vkHadamardWidth (2 * t) ≤
        Real.sqrt y * Real.exp (-(RHTower.vkHadamardWidth (2 * Real.exp Λ) * L)) := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hposE hypow
    calc K * (Real.sqrt y / (y : ℝ) ^ RHTower.vkHadamardWidth (2 * t) * Real.log t)
        ≤ K * (Real.sqrt y * Real.exp (-(RHTower.vkHadamardWidth (2 * Real.exp Λ) * L)) * Λ) := by
          gcongr
      _ = Real.sqrt y * (K * Λ * Real.exp (-(RHTower.vkHadamardWidth (2 * Real.exp Λ) * L))) := by
          ring
      _ ≤ Real.sqrt y * (1 / 3) := mul_le_mul_of_nonneg_left hdec (Real.sqrt_nonneg _)
      _ = Real.sqrt y / 3 := by ring
  have hsecond : K * Real.log (2 + t) ≤ Real.sqrt y / 3 := by
    rw [hsqrt]
    have := mul_le_mul_of_nonneg_left hl2t hK.le
    linarith
  have hpos : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have h3 : K * ((y : ℝ) ^ (1 / 2 - RHTower.vkHadamardWidth (2 * t)) * Real.log t +
      Real.log (2 + t)) ≤ Real.sqrt y / 3 + Real.sqrt y / 3 := by
    rw [mul_add]; exact add_le_add hfirst hsecond
  linarith

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
