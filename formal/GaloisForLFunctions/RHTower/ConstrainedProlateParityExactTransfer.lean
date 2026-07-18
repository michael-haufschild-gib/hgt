import GaloisForLFunctions.RHTower.ConstrainedProlateFuchsModelTransfer

/-!
# The exact constrained parity floors: `8/13`, `5/13`, and the `λ⁻⁴` separation

The negative compressed-Fourier prolate sector runs over the odd-pair indices `4j + 2`, so its
radial Fuchs family is

```text
d_λ(j) = fuchsRate (M j) (4j + 2) λ = M_j · λ^(8j+5) · e^(−4πλ²),
```

and its constraint coordinates converge to the Hermite values `|h_2(0)| = 2^{−1/4}` and
`|h_6(0)| = √5·2^{−7/4}`, whose squared weight is exactly `8/13`.  This module:

* evaluates that weight and its complement `5/13`;
* discharges the structural and tail-rate hypotheses of the infinite secular transfer for the
  offset radial family (ordering once `λ⁸` clears the adjacent constant ratios; the tail rate
  cancels the Gaussian clock at any base index and collapses like `λ⁻⁷`);
* concludes the negative-sector laws for the exact infinite-dimensional constrained root:
  `μ_-(λ)/d_6(λ) → 8/13`, the complementary gap `5/13`, and the quantified spectral gap; and
* combines the two sectors into the exact parity separation: the positive constrained floor is
  negligible against the negative one, `μ_+(λ)/μ_-(λ) → 0`, with the sharp rescaled limit
  `λ⁴·μ_+(λ)/μ_-(λ) → 13·A_4/(11·A_6)`.

Both parity floors are now the exact infinite-dimensional constrained optimizers of the
Fuchs-rate model, not two-mode truncations; only the constraint-coordinate inputs (Bessel bound
and prolate-to-Hermite limits) remain as hypotheses.
-/

open Filter

namespace RHTower

/-! ## The negative-sector Hermite weight -/

/-- The negative-sector squared Hermite weight: with `a_0 = 2^{−1/4}` (mode `2`) and
`a_1 = √5·2^{−7/4}` (mode `6`), the lower-mode weight is exactly `8/13`. -/
theorem ccm_negativeSector_hermite_weight_eq :
    ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 /
      (((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 + (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2)
      = 8 / 13 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 : ℝ) / 4)) 2, ← Real.rpow_mul h2]
    norm_num
  have ha1 : (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2 = 5 / (2 : ℝ) ^ ((7 : ℝ) / 2) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5),
      ← Real.rpow_natCast ((2 : ℝ) ^ ((7 : ℝ) / 4)) 2, ← Real.rpow_mul h2]
    norm_num
  have h24 : (2 : ℝ) ^ ((4 : ℝ)) = 16 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h72 : (2 : ℝ) ^ ((7 : ℝ) / 2) = 16 * (2 : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [show (7 : ℝ) / 2 = 4 + -(1 : ℝ) / 2 by norm_num, Real.rpow_add (by norm_num), h24]
  rw [ha0, ha1, h72]
  have hs : (0 : ℝ) < (2 : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hs2 : ((2 : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = 1 / 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul h2]
    norm_num [Real.rpow_neg_one]
  set s := (2 : ℝ) ^ (-(1 : ℝ) / 2) with hsdef
  have hne : s ≠ 0 := hs.ne'
  have hexp2 : s + 5 / (16 * s) = 13 / (16 * s) := by
    field_simp
    nlinarith [hs2]
  rw [hexp2, div_div_eq_mul_div, show s * (16 * s) = 16 * s ^ 2 by ring, hs2]
  norm_num

/-- The complementary negative-sector weight `5/13`. -/
theorem ccm_negativeSector_hermite_weight_complement_eq :
    (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2 /
      (((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 + (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2)
      = 5 / 13 := by
  have hS : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2
      + (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2 ≠ 0 := by positivity
  have h8 := ccm_negativeSector_hermite_weight_eq
  have hsum1 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 /
        (((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 + (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2)
      + (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2 /
        (((2 : ℝ) ^ (-(1 : ℝ) / 4)) ^ 2 + (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)) ^ 2)
      = 1 := by
    rw [← add_div]
    exact div_self hS
  linarith [h8, hsum1]

/-! ## Fuchs-family hypotheses at the offset radial indices -/

/-- The step-four Fuchs tail rate collapses at every base index: cancelling the common factor
`λ^(2n+1)·e^(−4πλ²)` leaves the rational function `A₁λ/(A₂λ⁸ − A₁) → 0`. -/
theorem fuchsRate_step4_tail_ratio_tendsto_zero {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (n : ℕ) :
    Tendsto (fun lam : ℝ =>
      lam * fuchsRate A₁ n lam / (fuchsRate A₂ (n + 4) lam - fuchsRate A₁ n lam))
      atTop (nhds 0) := by
  have hpow : ∀ᶠ lam : ℝ in atTop, 2 * A₁ / A₂ ≤ lam ^ 8 :=
    (tendsto_pow_atTop (α := ℝ) (n := 8) (by norm_num)).eventually_ge_atTop _
  have hmodel : Tendsto (fun lam : ℝ => A₁ * lam / (A₂ * lam ^ 8 - A₁)) atTop (nhds 0) := by
    have hbound : Tendsto (fun lam : ℝ => 2 * A₁ / A₂ * (lam ^ 7)⁻¹) atTop (nhds 0) := by
      have h7 := (tendsto_pow_atTop (α := ℝ) (n := 7)
        (by norm_num : (7 : ℕ) ≠ 0)).inv_tendsto_atTop
      simpa using h7.const_mul (2 * A₁ / A₂)
    refine squeeze_zero' ?_ ?_ hbound
    · filter_upwards [hpow, eventually_ge_atTop (1 : ℝ)] with lam hp hl1
      have hlam : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hl1
      have h2A : 2 * A₁ ≤ A₂ * lam ^ 8 := by
        have h := mul_le_mul_of_nonneg_left hp hA₂.le
        have heq : A₂ * (2 * A₁ / A₂) = 2 * A₁ := by field_simp
        rwa [heq] at h
      have hden : 0 < A₂ * lam ^ 8 - A₁ := by linarith
      exact div_nonneg (mul_nonneg hA₁.le hlam.le) hden.le
    · filter_upwards [hpow, eventually_ge_atTop (1 : ℝ)] with lam hp hl1
      have hlam : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hl1
      have h2A : 2 * A₁ ≤ A₂ * lam ^ 8 := by
        have h := mul_le_mul_of_nonneg_left hp hA₂.le
        have heq : A₂ * (2 * A₁ / A₂) = 2 * A₁ := by field_simp
        rwa [heq] at h
      have hhalf : 0 < A₂ / 2 * lam ^ 8 := mul_pos (half_pos hA₂) (pow_pos hlam 8)
      have hden_ge : A₂ / 2 * lam ^ 8 ≤ A₂ * lam ^ 8 - A₁ := by linarith
      have hstep : A₁ * lam / (A₂ * lam ^ 8 - A₁) ≤ A₁ * lam / (A₂ / 2 * lam ^ 8) :=
        div_le_div_of_nonneg_left (mul_nonneg hA₁.le hlam.le) hhalf hden_ge
      have heq : A₁ * lam / (A₂ / 2 * lam ^ 8) = 2 * A₁ / A₂ * (lam ^ 7)⁻¹ := by
        rw [show lam ^ 8 = lam * lam ^ 7 by ring]
        field_simp
      rw [heq] at hstep
      exact hstep
  refine hmodel.congr' ?_
  filter_upwards [hpow, eventually_ge_atTop (1 : ℝ)] with lam hp hl1
  have hlam : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hl1
  have hfac_ne : lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hlam.ne') (Real.exp_ne_zero _)
  have hnum : lam * fuchsRate A₁ n lam
      = lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2)) * (A₁ * lam) := by
    unfold fuchsRate
    ring
  have hfact : fuchsRate A₂ (n + 4) lam - fuchsRate A₁ n lam
      = lam ^ (2 * n + 1) * Real.exp (-(4 * Real.pi * lam ^ 2)) * (A₂ * lam ^ 8 - A₁) := by
    unfold fuchsRate
    rw [show 2 * (n + 4) + 1 = (2 * n + 1) + 8 by ring, pow_add]
    ring
  rw [hnum, hfact, mul_div_mul_left _ _ hfac_ne]

/-- The offset radial Fuchs family (indices `4j + 2`) satisfies the
ordered-triple-with-floor structural hypothesis for all sufficiently large apertures. -/
theorem fuchsRate_radial_offset2_struct {A : ℕ → ℝ} (hA : ∀ j, 0 < A j)
    {C : ℝ} (hC : 1 ≤ C) (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2)) :
    ∀ᶠ lam : ℝ in atTop,
      (0 ≤ fuchsRate (A 0) (4 * 0 + 2) lam ∧
        fuchsRate (A 0) (4 * 0 + 2) lam < fuchsRate (A 1) (4 * 1 + 2) lam ∧
        fuchsRate (A 1) (4 * 1 + 2) lam < fuchsRate (A 2) (4 * 2 + 2) lam) ∧
      ∀ j, fuchsRate (A 2) (4 * 2 + 2) lam ≤ fuchsRate (A (j + 2)) (4 * (j + 2) + 2) lam := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop C,
    (tendsto_pow_atTop (α := ℝ) (n := 8)
      (by norm_num : (8 : ℕ) ≠ 0)).eventually_gt_atTop (A 0 / A 1),
    (tendsto_pow_atTop (α := ℝ) (n := 8)
      (by norm_num : (8 : ℕ) ≠ 0)).eventually_gt_atTop (A 1 / A 2)]
    with lam hl1 hlC hpow01 hpow12
  have hlam : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hl1
  have hE : (0 : ℝ) < Real.exp (-(4 * Real.pi * lam ^ 2)) := Real.exp_pos _
  refine ⟨⟨(fuchsRate_pos (hA 0) _ hlam).le, ?_, ?_⟩, ?_⟩
  · have hA0lt : A 0 < lam ^ 8 * A 1 := (div_lt_iff₀ (hA 1)).mp hpow01
    have hmul := mul_lt_mul_of_pos_right hA0lt (pow_pos hlam 5)
    have hkey : A 0 * lam ^ (2 * (4 * 0 + 2) + 1) < A 1 * lam ^ (2 * (4 * 1 + 2) + 1) := by
      calc A 0 * lam ^ (2 * (4 * 0 + 2) + 1) = A 0 * lam ^ 5 := by norm_num
        _ < lam ^ 8 * A 1 * lam ^ 5 := hmul
        _ = A 1 * lam ^ (2 * (4 * 1 + 2) + 1) := by norm_num; ring
    exact mul_lt_mul_of_pos_right hkey hE
  · have hA1lt : A 1 < lam ^ 8 * A 2 := (div_lt_iff₀ (hA 2)).mp hpow12
    have hmul := mul_lt_mul_of_pos_right hA1lt (pow_pos hlam 13)
    have hkey : A 1 * lam ^ (2 * (4 * 1 + 2) + 1) < A 2 * lam ^ (2 * (4 * 2 + 2) + 1) := by
      calc A 1 * lam ^ (2 * (4 * 1 + 2) + 1) = A 1 * lam ^ 13 := by norm_num
        _ < lam ^ 8 * A 2 * lam ^ 13 := hmul
        _ = A 2 * lam ^ (2 * (4 * 2 + 2) + 1) := by norm_num; ring
    exact mul_lt_mul_of_pos_right hkey hE
  · intro j
    have hCj : C ^ j ≤ lam ^ (8 * j) := by
      calc C ^ j ≤ lam ^ j := pow_le_pow_left₀ (le_trans zero_le_one hC) hlC j
        _ ≤ lam ^ (8 * j) := pow_le_pow_right₀ hl1 (by omega)
    have hA2le : A 2 ≤ A (j + 2) * lam ^ (8 * j) := by
      calc A 2 ≤ C ^ j * A (j + 2) := hgrow j
        _ ≤ lam ^ (8 * j) * A (j + 2) := mul_le_mul_of_nonneg_right hCj (hA _).le
        _ = A (j + 2) * lam ^ (8 * j) := mul_comm _ _
    have hexp : 2 * (4 * (j + 2) + 2) + 1 = 8 * j + 21 := by ring
    unfold fuchsRate
    rw [hexp, pow_add lam (8 * j) 21]
    have hstep : A 2 * lam ^ 21 ≤ A (j + 2) * lam ^ (8 * j) * lam ^ 21 :=
      mul_le_mul_of_nonneg_right hA2le (pow_nonneg hlam.le 21)
    calc A 2 * lam ^ (2 * (4 * 2 + 2) + 1) * Real.exp (-(4 * Real.pi * lam ^ 2))
        = A 2 * lam ^ 21 * Real.exp (-(4 * Real.pi * lam ^ 2)) := by norm_num
      _ ≤ A (j + 2) * lam ^ (8 * j) * lam ^ 21 * Real.exp (-(4 * Real.pi * lam ^ 2)) :=
          mul_le_mul_of_nonneg_right hstep hE.le
      _ = A (j + 2) * (lam ^ (8 * j) * lam ^ 21) * Real.exp (-(4 * Real.pi * lam ^ 2)) := by
          ring

/-! ## The exact negative-sector laws -/

/-- **The `8/13` law for the exact negative-sector constrained root.**  For the offset radial
Fuchs family and the `h_2`/`h_6` Hermite coordinate limits, the exact infinite-dimensional
constrained ground root satisfies `μ_-(λ)/d_6(λ) → 8/13`. -/
theorem ccm_fuchsModel_negativeSector_root_ratio_tendsto
    {M : ℕ → ℝ} (hM : ∀ j, 0 < M j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    Tendsto (fun lam =>
      infiniteSecularRoot (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓ lam) /
        fuchsRate (M 1) (4 * 1 + 2) lam) atTop (nhds (8 / 13)) := by
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  have h := infiniteSecularRoot_ratio_tendsto
    (d := fun lam j => fuchsRate (M j) (4 * j + 2) lam)
    ha0 ha1 (fuchsRate_radial_offset2_struct hM hC hgrow) hsum hbessel
    (fuchsRate_div_tendsto_zero (hM 1) (hM 0) 2 (k := 4) (by norm_num))
    (fuchsRate_step4_tail_ratio_tendsto_zero (hM 1) (hM 2) 6)
    hl0 hl1
  rwa [ccm_negativeSector_hermite_weight_eq] at h

/-- **The `5/13` gap law for the exact negative-sector constrained root.** -/
theorem ccm_fuchsModel_negativeSector_gap_ratio_tendsto
    {M : ℕ → ℝ} (hM : ∀ j, 0 < M j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    Tendsto (fun lam =>
      (fuchsRate (M 1) (4 * 1 + 2) lam -
        infiniteSecularRoot (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓ lam)) /
        fuchsRate (M 1) (4 * 1 + 2) lam) atTop (nhds (5 / 13)) := by
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  have h := infiniteSecularRoot_gap_ratio_tendsto
    (d := fun lam j => fuchsRate (M j) (4 * j + 2) lam)
    ha0 ha1 (fuchsRate_radial_offset2_struct hM hC hgrow) hsum hbessel
    (fuchsRate_div_tendsto_zero (hM 1) (hM 0) 2 (k := 4) (by norm_num))
    (fuchsRate_step4_tail_ratio_tendsto_zero (hM 1) (hM 2) 6)
    hl0 hl1
  rwa [ccm_negativeSector_hermite_weight_complement_eq] at h

/-- **The quantified negative-sector spectral gap.**  Every `c < 5/13` eventually separates all
competing secular zeros of the negative sector from its exact ground root by `c·d_6`. -/
theorem ccm_fuchsModel_negativeSector_spectralGap_eventually
    {M : ℕ → ℝ} (hM : ∀ j, 0 < M j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, M 2 ≤ C ^ j * M (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4))))
    {c : ℝ} (hc : c < 5 / 13) :
    ∀ᶠ lam in atTop, ∀ μ' : ℝ,
      infiniteSecular (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓ lam) μ' = 0 →
      μ' ≠ infiniteSecularRoot (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓ lam) →
      c * fuchsRate (M 1) (4 * 1 + 2) lam ≤
        μ' - infiniteSecularRoot (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓ lam) := by
  have ha0 : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1 : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  refine infiniteSecularRoot_spectralGap_eventually
    (d := fun lam j => fuchsRate (M j) (4 * j + 2) lam)
    ha0 ha1 (fuchsRate_radial_offset2_struct hM hC hgrow) hsum hbessel
    (fuchsRate_div_tendsto_zero (hM 1) (hM 0) 2 (k := 4) (by norm_num))
    (fuchsRate_step4_tail_ratio_tendsto_zero (hM 1) (hM 2) 6)
    hl0 hl1 ?_
  rwa [ccm_negativeSector_hermite_weight_complement_eq]

/-! ## The exact parity floor separation -/

/-- **The exact parity floor collapse.**  The exact positive-sector constrained ground root is
negligible against the exact negative-sector one: `μ_+(λ)/μ_-(λ) → 0`. -/
theorem ccm_fuchsModel_parity_floor_ratio_tendsto_zero
    {P M : ℕ → ℝ} (hP : ∀ j, 0 < P j) (hM : ∀ j, 0 < M j)
    {Cp Cm : ℝ} (hCp : 1 ≤ Cp) (hCm : 1 ≤ Cm)
    (hgrowp : ∀ j, P 2 ≤ Cp ^ j * P (j + 2)) (hgrowm : ∀ j, M 2 ≤ Cm ^ j * M (j + 2))
    {ℓp ℓm : ℝ → ℕ → ℝ}
    (hsump : ∀ᶠ lam in atTop, Summable fun j => ℓp lam j ^ 2)
    (hbesselp : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓp lam j ^ 2) ≤ 2 * lam)
    (hlp0 : Tendsto (fun lam => ℓp lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hlp1 : Tendsto (fun lam => ℓp lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))))
    (hsumm : ∀ᶠ lam in atTop, Summable fun j => ℓm lam j ^ 2)
    (hbesselm : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓm lam j ^ 2) ≤ 2 * lam)
    (hlm0 : Tendsto (fun lam => ℓm lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hlm1 : Tendsto (fun lam => ℓm lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    Tendsto (fun lam =>
      infiniteSecularRoot (fun j => fuchsRate (P j) (4 * j) lam) (ℓp lam) /
        infiniteSecularRoot (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓm lam))
      atTop (nhds 0) := by
  have hplus := ccm_fuchsModel_infiniteSecularRoot_ratio_tendsto hP hCp hgrowp
    hsump hbesselp hlp0 hlp1
  have hminus := ccm_fuchsModel_negativeSector_root_ratio_tendsto hM hCm hgrowm
    hsumm hbesselm hlm0 hlm1
  have hscale : Tendsto (fun lam : ℝ =>
      fuchsRate (P 1) (4 * 1) lam / fuchsRate (M 1) (4 * 1 + 2) lam) atTop (nhds 0) :=
    fuchsRate_div_tendsto_zero (hM 1) (hP 1) 4 (k := 2) (by norm_num)
  have h1 := hplus.mul hscale
  have h2 := h1.div hminus (by norm_num : (8 : ℝ) / 13 ≠ 0)
  have h3 : Tendsto (fun lam =>
      infiniteSecularRoot (fun j => fuchsRate (P j) (4 * j) lam) (ℓp lam) /
          fuchsRate (P 1) (4 * 1) lam *
        (fuchsRate (P 1) (4 * 1) lam / fuchsRate (M 1) (4 * 1 + 2) lam) /
        (infiniteSecularRoot (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓm lam) /
          fuchsRate (M 1) (4 * 1 + 2) lam)) atTop (nhds 0) := by
    simpa using h2
  have ha0m : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1m : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  refine h3.congr' ?_
  filter_upwards [fuchsRate_radial_struct hP hCp hgrowp,
    fuchsRate_radial_offset2_struct hM hCm hgrowm, hsumm,
    hlm0.eventually_ne ha0m, hlm1.eventually_ne ha1m,
    eventually_gt_atTop (0 : ℝ)] with lam hstp hstm hsm hm0 hm1 hlam
  obtain ⟨⟨hpd0, hp01, hp12⟩, _⟩ := hstp
  obtain ⟨⟨hmd0, hm01, hm12⟩, hmd2⟩ := hstm
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec
    (d := fun j => fuchsRate (M j) (4 * j + 2) lam) hm01 hm12 hmd2 hsm hm0 hm1
  have hdp1 : fuchsRate (P 1) (4 * 1) lam ≠ 0 := (lt_of_le_of_lt hpd0 hp01).ne'
  have hdm1 : fuchsRate (M 1) (4 * 1 + 2) lam ≠ 0 := (lt_of_le_of_lt hmd0 hm01).ne'
  have hμm : infiniteSecularRoot (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓm lam) ≠ 0 :=
    (lt_of_le_of_lt hmd0 hrmem.1).ne'
  field_simp

/-- **The sharp exact parity scale.**  Multiplying the exact positive/negative constrained floor
ratio by `λ⁴` exposes the coefficient `13·A_4/(11·A_6)` — the two-mode parity constant survives
to the exact infinite-dimensional optimizers. -/
theorem ccm_fuchsModel_parity_floor_scaled_ratio_tendsto
    {P M : ℕ → ℝ} (hP : ∀ j, 0 < P j) (hM : ∀ j, 0 < M j)
    {Cp Cm : ℝ} (hCp : 1 ≤ Cp) (hCm : 1 ≤ Cm)
    (hgrowp : ∀ j, P 2 ≤ Cp ^ j * P (j + 2)) (hgrowm : ∀ j, M 2 ≤ Cm ^ j * M (j + 2))
    {ℓp ℓm : ℝ → ℕ → ℝ}
    (hsump : ∀ᶠ lam in atTop, Summable fun j => ℓp lam j ^ 2)
    (hbesselp : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓp lam j ^ 2) ≤ 2 * lam)
    (hlp0 : Tendsto (fun lam => ℓp lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hlp1 : Tendsto (fun lam => ℓp lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))))
    (hsumm : ∀ᶠ lam in atTop, Summable fun j => ℓm lam j ^ 2)
    (hbesselm : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓm lam j ^ 2) ≤ 2 * lam)
    (hlm0 : Tendsto (fun lam => ℓm lam 0) atTop (nhds ((2 : ℝ) ^ (-(1 : ℝ) / 4))))
    (hlm1 : Tendsto (fun lam => ℓm lam 1) atTop
      (nhds (Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4)))) :
    Tendsto (fun lam => lam ^ 4 *
      infiniteSecularRoot (fun j => fuchsRate (P j) (4 * j) lam) (ℓp lam) /
        infiniteSecularRoot (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓm lam))
      atTop (nhds (13 * P 1 / (11 * M 1))) := by
  have hplus := ccm_fuchsModel_infiniteSecularRoot_ratio_tendsto hP hCp hgrowp
    hsump hbesselp hlp0 hlp1
  have hminus := ccm_fuchsModel_negativeSector_root_ratio_tendsto hM hCm hgrowm
    hsumm hbesselm hlm0 hlm1
  have hscale4 : Tendsto (fun lam : ℝ =>
      lam ^ 4 * fuchsRate (P 1) (4 * 1) lam / fuchsRate (M 1) (4 * 1 + 2) lam)
      atTop (nhds (P 1 / M 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    unfold fuchsRate
    have hE : Real.exp (-(4 * Real.pi * lam ^ 2)) ≠ 0 := Real.exp_ne_zero _
    field_simp [(hM 1).ne', hlam.ne']
    ring
  have hminv := hminus.inv₀ (by norm_num : (8 : ℝ) / 13 ≠ 0)
  have h1 := (hplus.mul hscale4).mul hminv
  have hval : 8 / 11 * (P 1 / M 1) * ((8 : ℝ) / 13)⁻¹ = 13 * P 1 / (11 * M 1) := by
    field_simp [(hM 1).ne']
  rw [hval] at h1
  have ha0m : ((2 : ℝ) ^ (-(1 : ℝ) / 4)) ≠ 0 := ne_of_gt (by positivity)
  have ha1m : Real.sqrt 5 / (2 : ℝ) ^ ((7 : ℝ) / 4) ≠ 0 := ne_of_gt (by positivity)
  refine h1.congr' ?_
  filter_upwards [fuchsRate_radial_struct hP hCp hgrowp,
    fuchsRate_radial_offset2_struct hM hCm hgrowm, hsumm,
    hlm0.eventually_ne ha0m, hlm1.eventually_ne ha1m,
    eventually_gt_atTop (0 : ℝ)] with lam hstp hstm hsm hm0 hm1 hlam
  obtain ⟨⟨hpd0, hp01, hp12⟩, _⟩ := hstp
  obtain ⟨⟨hmd0, hm01, hm12⟩, hmd2⟩ := hstm
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec
    (d := fun j => fuchsRate (M j) (4 * j + 2) lam) hm01 hm12 hmd2 hsm hm0 hm1
  have hdp1 : fuchsRate (P 1) (4 * 1) lam ≠ 0 := (lt_of_le_of_lt hpd0 hp01).ne'
  have hdm1 : fuchsRate (M 1) (4 * 1 + 2) lam ≠ 0 := (lt_of_le_of_lt hmd0 hm01).ne'
  have hμm : infiniteSecularRoot (fun j => fuchsRate (M j) (4 * j + 2) lam) (ℓm lam) ≠ 0 :=
    (lt_of_le_of_lt hmd0 hrmem.1).ne'
  field_simp

end RHTower
