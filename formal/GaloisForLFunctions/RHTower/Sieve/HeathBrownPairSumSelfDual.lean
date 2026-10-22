import GaloisForLFunctions.RHTower.Sieve.GuthMaynardPropSixOneLifted

/-!
# Heath-Brown's pair sums: the loss localised at the self-dual length

`hbPairSum_Ioc_le_anyBlock` carries a fourth term `|W|^{3/2}M²`, harmless only when
`|W|^{1/4}M ≤ T^{1/2}`.  Above the self-dual length the reflection removes its `M`-dependence.
For `2T < N²` the reflection `hbAmp_half_le_reflection` expresses `𝒜((N,2N])` through the diagonal
`N|W|` and dual blocks of length `B ≤ 2T/N`; bounding each dual block by
`hbPairSum_Ioc_le_anyBlock` and using `𝒜((B,2B]) ≤ P((B,2B])/B` gives

`𝒜((N,2N]) ⪅ N|W| + |W|² + |W|^{5/4}T^{1/2} + |W|^{3/2}(T/N)`,

hence, after multiplying by `N`,

`Σ_{t₁,t₂∈W}|Σ_{N<n≤2N} a_n n^{i(t₁−t₂)}|² ⪅ |W|²N + |W|N² + |W|^{5/4}T^{1/2}N + |W|^{3/2}T`.

The last term no longer grows with `N`, and below `(2T)^{1/2}` the fourth term of
`hbPairSum_Ioc_le_anyBlock` satisfies `|W|^{3/2}M² ≤ 2|W|^{3/2}T` anyway, so the same four-term
bound holds for **every** `M ≥ 1` with the uniform last term `|W|^{3/2}T`
(`hbPairSum_Ioc_le_uniform`).

That term is absorbed into Heath-Brown's three terms when `M ≥ |W|^{1/4}T^{1/2}`, while
`hbPairSum_Ioc_le_middleBlock` absorbs its own when `M ≤ T^{1/2}/|W|^{1/4}`.  The exact
three-term Theorem 1.6 therefore holds for every block length outside the window
`T^{1/2}/|W|^{1/4} < M < T^{1/2}|W|^{1/4}` around the self-dual length `T^{1/2}`, where the
reflection `N ↦ T/N` is neutral and the squaring move pays `|W|^{1/2}`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The constant of the reflected bound. -/
def hbSelfDualConst (T δ : ℝ) : ℝ :=
  4 * hbReflFactor T + 3600000 * (1 + Real.logb 2 T) ^ 3 *
    (hbSmallConst T δ + hbBlockConst T δ (⌈2 * T⌉₊ ^ 2))

/-- **The weighted block sum from the unit-coefficient one.**  `n^{−1/2} ≤ B^{−1/2}` on `(B,2B]`. -/
theorem hbAmp_half_le_hbPairSum_div (W : Finset ℝ) {B : ℕ} (hB : 1 ≤ B) :
    hbAmp W (1 / 2) (Finset.Ioc B (2 * B)) ≤
      hbPairSum W (Finset.Ioc B (2 * B)) (fun _ => 1) / B := by
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hnorm : ∀ n ∈ Finset.Ioc B (2 * B),
      ‖((((n : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)‖ ≤ (B : ℝ) ^ (-(1 / 2 : ℝ)) := by
    intro n hn
    obtain ⟨hn1, -⟩ := Finset.mem_Ioc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn0.le _)]
    have hBn : (B : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1.le
    exact Real.rpow_le_rpow_of_nonpos hB0 hBn (by norm_num)
  have hmaj := hbPairSum_le_of_norm_le W (S := Finset.Ioc B (2 * B))
    (a := fun n => ((((n : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ))
    (b := fun _ => ((B : ℝ) ^ (-(1 / 2 : ℝ)))) hnorm
  have hconst := hbPairSum_const_mul W (Finset.Ioc B (2 * B)) (fun _ => (1 : ℂ))
    ((((B : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)
  simp only [mul_one] at hconst
  have hpow : ‖((((B : ℝ) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)‖ ^ 2 = (B : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      ← Real.rpow_natCast ((B : ℝ) ^ (-(1 / 2 : ℝ))) 2, ← Real.rpow_mul hB0.le,
      show (-(1 / 2 : ℝ) * (2 : ℕ)) = -1 by norm_num, Real.rpow_neg_one]
  rw [hbAmp]
  refine hmaj.trans (le_of_eq ?_)
  rw [hconst, hpow, div_eq_inv_mul]

/-- **Every dual block of the reflection is short.** -/
theorem hbDualBlock_le {N : ℕ} (hN : 1 ≤ N) {j i : ℕ} (hi : i < 3) {J : ℕ} (hj : j ≤ J) :
    ((2 ^ i * ubDualBase (2 * N) ((2 : ℝ) ^ j) : ℕ) : ℝ) ≤ (2 : ℝ) ^ J / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hcast : ((2 * N : ℕ) : ℝ) = 2 * N := by push_cast; ring
  have hfloor : ((ubDualBase (2 * N) ((2 : ℝ) ^ j) : ℕ) : ℝ) ≤
      (2 : ℝ) ^ j / (4 * Real.pi * (2 * (N : ℝ) + 1 / 4)) := by
    rw [ubDualBase, hcast]
    exact Nat.floor_le (by positivity)
  have h2i : (2 : ℝ) ^ i ≤ 4 := by
    calc (2 : ℝ) ^ i ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = 4 := by norm_num
  have hjJ : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ J := pow_le_pow_right₀ (by norm_num) hj
  have hj0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hprod : ((2 ^ i * ubDualBase (2 * N) ((2 : ℝ) ^ j) : ℕ) : ℝ) ≤
      4 * ((2 : ℝ) ^ j / (4 * Real.pi * (2 * (N : ℝ) + 1 / 4))) := by
    push_cast
    exact mul_le_mul h2i hfloor (Nat.cast_nonneg _) (by norm_num)
  refine hprod.trans ?_
  have hL : 4 * ((2 : ℝ) ^ j / (4 * Real.pi * (2 * (N : ℝ) + 1 / 4))) =
      (4 * (2 : ℝ) ^ j) / (4 * Real.pi * (2 * (N : ℝ) + 1 / 4)) := by ring
  rw [hL, div_le_div_iff₀ (by positivity) hN0]
  have hJ0 : (0 : ℝ) < (2 : ℝ) ^ J := by positivity
  have h1 : 4 * (2 : ℝ) ^ j * N ≤ 4 * (2 : ℝ) ^ J * N := by nlinarith
  have h2 : 4 * (N : ℝ) ≤ 4 * Real.pi * (2 * (N : ℝ) + 1 / 4) := by nlinarith
  calc 4 * (2 : ℝ) ^ j * N ≤ 4 * (2 : ℝ) ^ J * N := h1
    _ = (2 : ℝ) ^ J * (4 * N) := by ring
    _ ≤ (2 : ℝ) ^ J * (4 * Real.pi * (2 * (N : ℝ) + 1 / 4)) :=
        mul_le_mul_of_nonneg_left h2 hJ0.le

/-- Dividing the four-term bound by the block length. -/
private theorem block_div_le {C r s u b v : ℝ} (hC : 0 ≤ C) (hb : 0 < b) (hr : 0 ≤ r)
    (hu : 0 ≤ u) (hbv : b ≤ v) :
    C * (r ^ 2 * b + r * b ^ 2 + s * b + u * b ^ 2) / b ≤ C * (r ^ 2 + r * v + s + u * v) := by
  have hdiv : C * (r ^ 2 * b + r * b ^ 2 + s * b + u * b ^ 2) / b =
      C * (r ^ 2 + r * b + s + u * b) := by
    field_simp
  rw [hdiv]
  have h1 : r * b ≤ r * v := mul_le_mul_of_nonneg_left hbv hr
  have h2 : u * b ≤ u * v := mul_le_mul_of_nonneg_left hbv hu
  have h3 : r ^ 2 + r * b + s + u * b ≤ r ^ 2 + r * v + s + u * v := by linarith
  exact mul_le_mul_of_nonneg_left h3 hC

/-- Multiplying the dual bound by the block length, with `T ≤ N²`. -/
private theorem mul_dualBound_le {C r s u t n : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r) (hn : 0 < n)
    (ht : 0 ≤ t) (htn : t ≤ n ^ 2) (hs : 0 ≤ s) (hu : 0 ≤ u) :
    n * (C * (r ^ 2 + r * (2 * t / n) + s + u * (2 * t / n))) ≤
      2 * C * (r ^ 2 * n + r * n ^ 2 + s * n + u * t) := by
  have hexp : n * (C * (r ^ 2 + r * (2 * t / n) + s + u * (2 * t / n))) =
      C * (r ^ 2 * n + r * (2 * t) + s * n + u * (2 * t)) := by
    field_simp
  rw [hexp]
  have h1 : r * (2 * t) ≤ 2 * (r * n ^ 2) := by nlinarith
  have h2 : (0 : ℝ) ≤ r ^ 2 * n := by positivity
  have h3 : (0 : ℝ) ≤ s * n := by positivity
  have h4 : (0 : ℝ) ≤ u * t := mul_nonneg hu ht
  have h5 : r ^ 2 * n + r * (2 * t) + s * n + u * (2 * t) ≤
      2 * (r ^ 2 * n + r * n ^ 2 + s * n + u * t) := by linarith
  calc C * (r ^ 2 * n + r * (2 * t) + s * n + u * (2 * t))
      ≤ C * (2 * (r ^ 2 * n + r * n ^ 2 + s * n + u * t)) :=
        mul_le_mul_of_nonneg_left h5 hC
    _ = 2 * C * (r ^ 2 * n + r * n ^ 2 + s * n + u * t) := by ring

/-- **One dual block of the reflection.** -/
theorem hbDualTerm_le_bound {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {N : ℕ} (hN : 1 ≤ N)
    {δ : ℝ} (hδ : 0 < δ) {J j i : ℕ} (hj : j ≤ J) (hi : i < 3)
    (hJT : (2 : ℝ) ^ J ≤ 2 * T) :
    hbDualTerm W N j i ≤ (hbSmallConst T δ + hbBlockConst T δ (⌈2 * T⌉₊ ^ 2)) *
      ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 * T / N)
        + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2)
        + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (2 * T / N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : (0 : ℝ) < T := by linarith
  have hR0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hS0 : 0 ≤ hbSmallConst T δ := le_trans zero_le_one (one_le_hbSmallConst hT hδ)
  have hB0 : 0 ≤ hbBlockConst T δ (⌈2 * T⌉₊ ^ 2) := hbBlockConst_nonneg hT _
  have hC0 : (0 : ℝ) ≤ hbSmallConst T δ + hbBlockConst T δ (⌈2 * T⌉₊ ^ 2) := by linarith
  have hs0 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg hT0.le _)
  have hu0 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hR0 _
  have hRHS0 : (0 : ℝ) ≤ (hbSmallConst T δ + hbBlockConst T δ (⌈2 * T⌉₊ ^ 2)) *
      ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 * T / N)
        + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2)
        + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (2 * T / N)) := by
    have h1 : (0 : ℝ) ≤ (W.card : ℝ) * (2 * T / N) := by positivity
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) * (2 * T / N) :=
      mul_nonneg hu0 (by positivity)
    have h3 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 := by positivity
    exact mul_nonneg hC0 (by linarith)
  rw [hbDualTerm]
  split_ifs with hY
  swap
  · exact hRHS0
  -- the dual block
  obtain ⟨B, hBdef⟩ : ∃ B : ℕ, B = 2 ^ i * ubDualBase (2 * N) ((2 : ℝ) ^ j) := ⟨_, rfl⟩
  rw [← hBdef]
  have hj0 : (0 : ℝ) < (2 : ℝ) ^ j := by positivity
  have hMlo := ub_dualBase_ge hN (by omega : N < 2 * N) le_rfl hj0 (by linarith)
  have hM1 : 1 ≤ ubDualBase (2 * N) ((2 : ℝ) ^ j) := by
    have h11 : (1 : ℝ) < ((ubDualBase (2 * N) ((2 : ℝ) ^ j) : ℕ) : ℝ) := by linarith
    have h12 : 1 < ubDualBase (2 * N) ((2 : ℝ) ^ j) := by exact_mod_cast h11
    omega
  have hB1 : 1 ≤ B := by
    rw [hBdef]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
  have hB0' : (0 : ℝ) < B := by exact_mod_cast hB1
  have hBle : (B : ℝ) ≤ 2 * T / N := by
    rw [hBdef]
    refine (hbDualBlock_le hN hi hj).trans ?_
    gcongr
  -- the four-term bound on the dual block, divided by its length
  have hany := hbPairSum_Ioc_le_anyBlock hW hT hdiam (M := B) hB1 hδ
    (a := fun _ => (1 : ℂ)) (fun n _ => by norm_num)
  have hCB : hbSmallConst T δ + hbBlockConst T δ (B ^ 2) ≤
      hbSmallConst T δ + hbBlockConst T δ (⌈2 * T⌉₊ ^ 2) := by
    have hBT : B ^ 2 ≤ ⌈2 * T⌉₊ ^ 2 := by
      have h1 : (B : ℝ) ≤ (⌈2 * T⌉₊ : ℝ) := by
        refine hBle.trans ?_
        have h2 : 2 * T / N ≤ 2 * T := by
          rw [div_le_iff₀ hN0]
          nlinarith [hN0, Nat.one_le_cast (α := ℝ) |>.mpr hN]
        exact h2.trans (Nat.le_ceil _)
      have : B ≤ ⌈2 * T⌉₊ := by exact_mod_cast h1
      exact Nat.pow_le_pow_left this 2
    have := hbBlockConst_mono (T := T) (δ := δ) hδ hT hBT
    linarith
  have hsum0 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 * B + (W.card : ℝ) * (B : ℝ) ^ 2
      + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * B
      + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (B : ℝ) ^ 2 := by
    have h1 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * B :=
      mul_nonneg hs0 (Nat.cast_nonneg _)
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) * (B : ℝ) ^ 2 :=
      mul_nonneg hu0 (by positivity)
    have h3 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 * B := by positivity
    have h4 : (0 : ℝ) ≤ (W.card : ℝ) * (B : ℝ) ^ 2 := by positivity
    linarith
  refine (hbAmp_half_le_hbPairSum_div W hB1).trans ?_
  have hnum := hany.trans (mul_le_mul_of_nonneg_right hCB hsum0)
  have hdiv : hbPairSum W (Finset.Ioc B (2 * B)) (fun _ => 1) / (B : ℝ) ≤
      (hbSmallConst T δ + hbBlockConst T δ (⌈2 * T⌉₊ ^ 2)) *
        ((W.card : ℝ) ^ 2 * B + (W.card : ℝ) * (B : ℝ) ^ 2
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * B
          + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (B : ℝ) ^ 2) / (B : ℝ) := by
    gcongr
  exact hdiv.trans (block_div_le hC0 hB0' hR0 hu0 hBle)

/-- **The reflected bound.**  Above `(2T)^{1/2}` the fourth term is `|W|^{3/2}T`, independent of
the block length. -/
theorem hbPairSum_Ioc_le_reflected {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {N : ℕ} (hN : 1 ≤ N)
    (hN2 : 2 * T < (N : ℝ) ^ 2) {δ : ℝ} (hδ : 0 < δ)
    {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc N (2 * N)) a ≤ hbSelfDualConst T δ *
      ((W.card : ℝ) ^ 2 * N + (W.card : ℝ) * (N : ℝ) ^ 2
        + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * N
        + (W.card : ℝ) ^ ((3 : ℝ) / 2) * T) := by
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : (0 : ℝ) < T := by linarith
  have hR0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  obtain ⟨k, hk1, hk2⟩ := GaloisForLFunctions.Nevanlinna.exists_dyadic_band hT
  have hpow : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hJT : (2 : ℝ) ^ (k + 1) ≤ 2 * T := by rw [hpow]; linarith
  have hJN : (2 : ℝ) ^ (k + 1) < (N : ℝ) ^ 2 := lt_of_le_of_lt hJT hN2
  have hdiam' : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ (2 : ℝ) ^ (k + 1) := fun t ht t' ht' =>
    (hdiam t ht t' ht').trans hk2.le
  have hrefl := hbAmp_half_le_reflection hW (J := k + 1) (by omega) hN hdiam' hJN
  have hkL : ((k + 1 : ℕ) : ℝ) ≤ 1 + Real.logb 2 T := by
    have hlog : (k : ℝ) ≤ Real.logb 2 T := by
      have h := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hk1
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
    push_cast; linarith
  have hk0 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL0 : (0 : ℝ) ≤ 1 + Real.logb 2 T := hk0.trans hkL
  -- the dual bound
  obtain ⟨Cany, hCany⟩ : ∃ C : ℝ, C = hbSmallConst T δ + hbBlockConst T δ (⌈2 * T⌉₊ ^ 2) :=
    ⟨_, rfl⟩
  have hCany0 : 0 ≤ Cany := by
    rw [hCany]
    have h1 : 0 ≤ hbSmallConst T δ := le_trans zero_le_one (one_le_hbSmallConst hT hδ)
    have h2 : 0 ≤ hbBlockConst T δ (⌈2 * T⌉₊ ^ 2) := hbBlockConst_nonneg hT _
    linarith
  obtain ⟨Db, hDb⟩ : ∃ D : ℝ, D = Cany * ((W.card : ℝ) ^ 2 + (W.card : ℝ) * (2 * T / N)
      + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2)
      + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (2 * T / N)) := ⟨_, rfl⟩
  have hdual : ∀ j ∈ Finset.Icc 1 (k + 1), ∀ i ∈ Finset.range 3, hbDualTerm W N j i ≤ Db := by
    intro j hj i hi
    rw [hDb, hCany]
    exact hbDualTerm_le_bound hW hT hdiam hN hδ (Finset.mem_Icc.mp hj).2
      (Finset.mem_range.mp hi) hJT
  have hDb0 : 0 ≤ Db :=
    le_trans (hbDualTerm_nonneg W N 1 0) (hdual 1 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩) 0
      (Finset.mem_range.mpr (by omega)))
  -- sum over the dyadic family
  have hsum : ∑ j ∈ Finset.Icc 1 (k + 1), ∑ i ∈ Finset.range 3, hbDualTerm W N j i ≤
      3 * ((k + 1 : ℕ) : ℝ) * Db := by
    have hrow : ∀ j ∈ Finset.Icc 1 (k + 1),
        ∑ i ∈ Finset.range 3, hbDualTerm W N j i ≤ 3 * Db := by
      intro j hj
      calc ∑ i ∈ Finset.range 3, hbDualTerm W N j i ≤ ∑ _i ∈ Finset.range 3, Db :=
            Finset.sum_le_sum fun i hi => hdual j hj i hi
        _ = 3 * Db := by simp
    have hcard : (((Finset.Icc 1 (k + 1)).card : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by
      simp
    calc ∑ j ∈ Finset.Icc 1 (k + 1), ∑ i ∈ Finset.range 3, hbDualTerm W N j i
        ≤ ∑ _j ∈ Finset.Icc 1 (k + 1), 3 * Db := Finset.sum_le_sum hrow
      _ = (((Finset.Icc 1 (k + 1)).card : ℕ) : ℝ) * (3 * Db) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = 3 * ((k + 1 : ℕ) : ℝ) * Db := by rw [hcard]; ring
  -- the reflected amplitude
  have hamp : hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) ≤
      2 * N * W.card * hbReflFactor T + 900000 * (1 + Real.logb 2 T) ^ 3 * Db := by
    refine hrefl.trans ?_
    have h1 : 2 * (N : ℝ) * W.card * (1 + 12 * hbReflConst ^ 2 * ((k + 1 : ℕ) : ℝ) *
        ((1 + ((k + 1 : ℕ) : ℝ)) ^ 2 + 1)) ≤ 2 * N * W.card * hbReflFactor T := by
      rw [hbReflFactor]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsq : (1 + ((k + 1 : ℕ) : ℝ)) ^ 2 ≤ (1 + (1 + Real.logb 2 T)) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith) 2
      have hpos1 : (0 : ℝ) ≤ (1 + ((k + 1 : ℕ) : ℝ)) ^ 2 + 1 := by positivity
      have hmono : ((k + 1 : ℕ) : ℝ) * ((1 + ((k + 1 : ℕ) : ℝ)) ^ 2 + 1) ≤
          (1 + Real.logb 2 T) * ((1 + (1 + Real.logb 2 T)) ^ 2 + 1) := by
        calc ((k + 1 : ℕ) : ℝ) * ((1 + ((k + 1 : ℕ) : ℝ)) ^ 2 + 1)
            ≤ (1 + Real.logb 2 T) * ((1 + ((k + 1 : ℕ) : ℝ)) ^ 2 + 1) :=
              mul_le_mul_of_nonneg_right hkL hpos1
          _ ≤ (1 + Real.logb 2 T) * ((1 + (1 + Real.logb 2 T)) ^ 2 + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) hL0
      have hc2 : (0 : ℝ) ≤ 12 * hbReflConst ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hmono hc2]
    have h2 : 300000 * (((k + 1 : ℕ) : ℝ)) ^ 2 *
        ∑ j ∈ Finset.Icc 1 (k + 1), ∑ i ∈ Finset.range 3, hbDualTerm W N j i ≤
        900000 * (1 + Real.logb 2 T) ^ 3 * Db := by
      have hstep := mul_le_mul_of_nonneg_left hsum
        (by positivity : (0 : ℝ) ≤ 300000 * (((k + 1 : ℕ) : ℝ)) ^ 2)
      have hc1 : 300000 * (((k + 1 : ℕ) : ℝ)) ^ 2 * (3 * ((k + 1 : ℕ) : ℝ) * Db) =
          900000 * ((k + 1 : ℕ) : ℝ) ^ 3 * Db := by ring
      rw [hc1] at hstep
      refine hstep.trans ?_
      have hcube : ((k + 1 : ℕ) : ℝ) ^ 3 ≤ (1 + Real.logb 2 T) ^ 3 :=
        pow_le_pow_left₀ hk0 hkL 3
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube (by norm_num : (0 : ℝ) ≤ 900000)) hDb0
    linarith
  -- multiply by the block length
  have hNDb : (N : ℝ) * Db ≤ 2 * Cany * ((W.card : ℝ) ^ 2 * N + (W.card : ℝ) * (N : ℝ) ^ 2
      + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * N
      + (W.card : ℝ) ^ ((3 : ℝ) / 2) * T) := by
    rw [hDb]
    exact mul_dualBound_le hCany0 hR0 hN0 hT0.le (by nlinarith)
      (mul_nonneg (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg hT0.le _))
      (Real.rpow_nonneg hR0 _)
  have hfinal := hbPairSum_le_two_mul_hbAmp_half W ha
  have hstep2 : 2 * (N : ℝ) * hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) ≤
      4 * hbReflFactor T * ((W.card : ℝ) * (N : ℝ) ^ 2) +
        1800000 * (1 + Real.logb 2 T) ^ 3 * ((N : ℝ) * Db) := by
    have h := mul_le_mul_of_nonneg_left hamp (by positivity : (0 : ℝ) ≤ 2 * (N : ℝ))
    refine h.trans (le_of_eq ?_)
    ring
  -- assemble
  obtain ⟨Targ, hTarg⟩ : ∃ X : ℝ, X = (W.card : ℝ) ^ 2 * N + (W.card : ℝ) * (N : ℝ) ^ 2
      + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * N
      + (W.card : ℝ) ^ ((3 : ℝ) / 2) * T := ⟨_, rfl⟩
  rw [← hTarg] at hNDb ⊢
  have hTarg0 : 0 ≤ Targ := by
    rw [hTarg]
    have h1 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * N :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg hT0.le _))
        (Nat.cast_nonneg _)
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) * T :=
      mul_nonneg (Real.rpow_nonneg hR0 _) hT0.le
    have h3 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 * N := by positivity
    have h4 : (0 : ℝ) ≤ (W.card : ℝ) * (N : ℝ) ^ 2 := by positivity
    linarith
  have hc0 : 0 ≤ hbReflFactor T := le_trans zero_le_one (one_le_hbReflFactor hT)
  have hdiag : (W.card : ℝ) * (N : ℝ) ^ 2 ≤ Targ := by
    rw [hTarg]
    have h1 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * N :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg hT0.le _))
        (Nat.cast_nonneg _)
    have h2 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) * T :=
      mul_nonneg (Real.rpow_nonneg hR0 _) hT0.le
    have h3 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 * N := by positivity
    linarith
  have hlog0 : (0 : ℝ) ≤ 1800000 * (1 + Real.logb 2 T) ^ 3 := by positivity
  calc hbPairSum W (Finset.Ioc N (2 * N)) a
      ≤ 2 * (N : ℝ) * hbAmp W (1 / 2) (Finset.Ioc N (2 * N)) := hfinal
    _ ≤ 4 * hbReflFactor T * ((W.card : ℝ) * (N : ℝ) ^ 2) +
          1800000 * (1 + Real.logb 2 T) ^ 3 * ((N : ℝ) * Db) := hstep2
    _ ≤ 4 * hbReflFactor T * Targ +
          1800000 * (1 + Real.logb 2 T) ^ 3 * (2 * Cany * Targ) := by
        have ha1 : 4 * hbReflFactor T * ((W.card : ℝ) * (N : ℝ) ^ 2) ≤
            4 * hbReflFactor T * Targ :=
          mul_le_mul_of_nonneg_left hdiag (by linarith)
        have ha2 : 1800000 * (1 + Real.logb 2 T) ^ 3 * ((N : ℝ) * Db) ≤
            1800000 * (1 + Real.logb 2 T) ^ 3 * (2 * Cany * Targ) :=
          mul_le_mul_of_nonneg_left hNDb hlog0
        linarith
    _ = hbSelfDualConst T δ * Targ := by
        rw [hbSelfDualConst, ← hCany]
        ring

/-- Nonnegativity of the reflected constant. -/
theorem hbSelfDualConst_nonneg {T δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ) : 0 ≤ hbSelfDualConst T δ := by
  have hc : 0 ≤ hbReflFactor T := le_trans zero_le_one (one_le_hbReflFactor hT)
  have hS : 0 ≤ hbSmallConst T δ := le_trans zero_le_one (one_le_hbSmallConst hT hδ)
  have hB : 0 ≤ hbBlockConst T δ (⌈2 * T⌉₊ ^ 2) := hbBlockConst_nonneg hT _
  have hL : (0 : ℝ) ≤ 1 + Real.logb 2 T := by
    have := Real.logb_nonneg (b := 2) (by norm_num) hT; linarith
  rw [hbSelfDualConst]
  have h1 : (0 : ℝ) ≤ 3600000 * (1 + Real.logb 2 T) ^ 3 := by positivity
  nlinarith

/-- **Every block length, with the uniform fourth term `|W|^{3/2}T`.**  Below `(2T)^{1/2}` the
fourth term of `hbPairSum_Ioc_le_anyBlock` is at most `2|W|^{3/2}T`; above it the reflected bound
applies.  The term is absorbed into Heath-Brown's three terms when `|W|^{1/4}M ≥ T^{1/2}`, as
`hbPairSum_Ioc_le_middleBlock` absorbs its own when `|W|^{1/4}M ≤ T^{1/2}`. -/
theorem hbPairSum_Ioc_le_uniform {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {M : ℕ} (hM : 1 ≤ M)
    {δ : ℝ} (hδ : 0 < δ) {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc M (2 * M)) a ≤
      2 * (hbSelfDualConst T δ + hbSmallConst T δ + hbBlockConst T δ (M ^ 2)) *
        ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M
          + (W.card : ℝ) ^ ((3 : ℝ) / 2) * T) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hR0 : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hSD0 : 0 ≤ hbSelfDualConst T δ := hbSelfDualConst_nonneg hT hδ
  have hS0 : 0 ≤ hbSmallConst T δ := le_trans zero_le_one (one_le_hbSmallConst hT hδ)
  have hB0 : 0 ≤ hbBlockConst T δ (M ^ 2) := hbBlockConst_nonneg hT _
  have hm1 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 * M := by positivity
  have hm2 : (0 : ℝ) ≤ (W.card : ℝ) * (M : ℝ) ^ 2 := by positivity
  have hm3 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg hT0.le _))
      (Nat.cast_nonneg _)
  have hm4 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) * T :=
    mul_nonneg (Real.rpow_nonneg hR0 _) hT0.le
  rcases lt_or_ge (2 * T) ((M : ℝ) ^ 2) with hcase | hcase
  · -- above the self-dual length: the reflected bound
    refine (hbPairSum_Ioc_le_reflected hW hT hdiam hM hcase hδ ha).trans ?_
    have h1 : hbSelfDualConst T δ ≤
        2 * (hbSelfDualConst T δ + hbSmallConst T δ + hbBlockConst T δ (M ^ 2)) := by linarith
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  · -- below it: the fourth term of `anyBlock` is at most `2|W|^{3/2}T`
    refine (hbPairSum_Ioc_le_anyBlock hW hT hdiam hM hδ ha).trans ?_
    have hfour : (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2 ≤
        2 * ((W.card : ℝ) ^ ((3 : ℝ) / 2) * T) := by
      have h0 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hR0 _
      nlinarith
    have hsum : (W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
        + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M
        + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2 ≤
      2 * ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
        + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M
        + (W.card : ℝ) ^ ((3 : ℝ) / 2) * T) := by linarith
    have hconst : hbSmallConst T δ + hbBlockConst T δ (M ^ 2) ≤
        hbSelfDualConst T δ + hbSmallConst T δ + hbBlockConst T δ (M ^ 2) := by linarith
    calc (hbSmallConst T δ + hbBlockConst T δ (M ^ 2)) *
          ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
            + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M
            + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2)
        ≤ (hbSelfDualConst T δ + hbSmallConst T δ + hbBlockConst T δ (M ^ 2)) *
            (2 * ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
              + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M
              + (W.card : ℝ) ^ ((3 : ℝ) / 2) * T)) := by
          refine mul_le_mul hconst hsum ?_ (by linarith)
          have h2 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2 :=
            mul_nonneg (Real.rpow_nonneg hR0 _) (by positivity)
          linarith
      _ = 2 * (hbSelfDualConst T δ + hbSmallConst T δ + hbBlockConst T δ (M ^ 2)) *
            ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
              + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M
              + (W.card : ℝ) ^ ((3 : ℝ) / 2) * T) := by ring

end

end RHTower.Sieve
