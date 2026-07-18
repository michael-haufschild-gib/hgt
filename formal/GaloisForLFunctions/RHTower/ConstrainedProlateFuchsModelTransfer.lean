import GaloisForLFunctions.RHTower.ConstrainedProlateInfiniteSecular

/-!
# Fuchs-model discharge of the infinite secular transfer hypotheses

The exact infinite-dimensional constrained ground theorems take an abstract leakage family
`d : ℝ → ℕ → ℝ` subject to three structural hypotheses: an ordered positive triple with a
uniform floor above the third scale, the collapse `d_0/d_1 → 0`, and the tail-domination rate
`λ·d_1/(d_2 − d_1) → 0`.  This module discharges all three for the radial Fuchs family

```text
d_λ(j) = fuchsRate (A j) (4j) λ = A_j · λ^(8j+1) · e^(−4πλ²),
```

assuming only positivity of the Fuchs constants and the tempered growth
`A_2 ≤ C^j · A_{j+2}` for some `C ≥ 1` (adjacent Fuchs constants do not decay faster than a
fixed geometric rate).  The ordering holds once `λ⁸` clears the two adjacent constant ratios and
`λ ≥ max(1, C)`; the tail rate reduces, after cancelling the common Gaussian clock, to the
rational limit `A₁λ/(A₂λ⁸ − A₁) → 0`.

Consequently the Connes–Consani–Moscovici `8/11` ground ratio, the `3/11` complementary gap,
and the quantified constrained spectral gap hold for the exact infinite-dimensional constrained
root of the Fuchs-rate model, with only the constraint-coordinate hypotheses (Bessel bound and
prolate-to-Hermite limits) remaining as inputs.
-/

open Filter

namespace RHTower

/-- After cancelling the common Gaussian clock, the radial Fuchs tail rate is the rational
function `A₁λ/(A₂λ⁸ − A₁)`, which collapses at speed `λ⁻⁷`. -/
theorem fuchsRate_radial_tail_ratio_tendsto_zero {A₁ A₂ : ℝ} (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) :
    Tendsto (fun lam : ℝ =>
      lam * fuchsRate A₁ 4 lam / (fuchsRate A₂ 8 lam - fuchsRate A₁ 4 lam))
      atTop (nhds 0) := by
  have hpow : ∀ᶠ lam : ℝ in atTop, 2 * A₁ / A₂ ≤ lam ^ 8 :=
    (tendsto_pow_atTop (α := ℝ) (n := 8) (by norm_num)).eventually_ge_atTop _
  have hmodel : Tendsto (fun lam : ℝ => A₁ * lam / (A₂ * lam ^ 8 - A₁)) atTop (nhds 0) := by
    have hbound : Tendsto (fun lam : ℝ => 2 * A₁ / A₂ * (lam ^ 7)⁻¹) atTop (nhds 0) := by
      have h7 := (tendsto_pow_atTop (α := ℝ) (n := 7) (by norm_num : (7 : ℕ) ≠ 0)).inv_tendsto_atTop
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
      have hhalf : 0 < A₂ / 2 * lam ^ 8 :=
        mul_pos (half_pos hA₂) (pow_pos hlam 8)
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
  have hfac_ne : lam ^ 9 * Real.exp (-(4 * Real.pi * lam ^ 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hlam.ne') (Real.exp_ne_zero _)
  have hnum : lam * fuchsRate A₁ 4 lam
      = lam ^ 9 * Real.exp (-(4 * Real.pi * lam ^ 2)) * (A₁ * lam) := by
    unfold fuchsRate
    ring
  have hfact : fuchsRate A₂ 8 lam - fuchsRate A₁ 4 lam
      = lam ^ 9 * Real.exp (-(4 * Real.pi * lam ^ 2)) * (A₂ * lam ^ 8 - A₁) := by
    unfold fuchsRate
    ring
  rw [hnum, hfact, mul_div_mul_left _ _ hfac_ne]

/-- The radial Fuchs family satisfies the ordered-triple-with-floor structural hypothesis for
all sufficiently large apertures. -/
theorem fuchsRate_radial_struct {A : ℕ → ℝ} (hA : ∀ j, 0 < A j)
    {C : ℝ} (hC : 1 ≤ C) (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2)) :
    ∀ᶠ lam : ℝ in atTop,
      (0 ≤ fuchsRate (A 0) (4 * 0) lam ∧
        fuchsRate (A 0) (4 * 0) lam < fuchsRate (A 1) (4 * 1) lam ∧
        fuchsRate (A 1) (4 * 1) lam < fuchsRate (A 2) (4 * 2) lam) ∧
      ∀ j, fuchsRate (A 2) (4 * 2) lam ≤ fuchsRate (A (j + 2)) (4 * (j + 2)) lam := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop C,
    (tendsto_pow_atTop (α := ℝ) (n := 8) (by norm_num : (8 : ℕ) ≠ 0)).eventually_gt_atTop (A 0 / A 1),
    (tendsto_pow_atTop (α := ℝ) (n := 8) (by norm_num : (8 : ℕ) ≠ 0)).eventually_gt_atTop (A 1 / A 2)]
    with lam hl1 hlC hpow01 hpow12
  have hlam : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hl1
  have hE : (0 : ℝ) < Real.exp (-(4 * Real.pi * lam ^ 2)) := Real.exp_pos _
  refine ⟨⟨(fuchsRate_pos (hA 0) _ hlam).le, ?_, ?_⟩, ?_⟩
  · -- d₀ < d₁ once λ⁸ > A₀/A₁
    have hA0lt : A 0 < lam ^ 8 * A 1 := (div_lt_iff₀ (hA 1)).mp hpow01
    have hmul := mul_lt_mul_of_pos_right hA0lt hlam
    have hkey : A 0 * lam ^ (2 * (4 * 0) + 1) < A 1 * lam ^ (2 * (4 * 1) + 1) := by
      calc A 0 * lam ^ (2 * (4 * 0) + 1) = A 0 * lam := by norm_num
        _ < lam ^ 8 * A 1 * lam := hmul
        _ = A 1 * lam ^ (2 * (4 * 1) + 1) := by norm_num; ring
    exact mul_lt_mul_of_pos_right hkey hE
  · -- d₁ < d₂ once λ⁸ > A₁/A₂
    have hA1lt : A 1 < lam ^ 8 * A 2 := (div_lt_iff₀ (hA 2)).mp hpow12
    have hmul := mul_lt_mul_of_pos_right hA1lt (pow_pos hlam 9)
    have hkey : A 1 * lam ^ (2 * (4 * 1) + 1) < A 2 * lam ^ (2 * (4 * 2) + 1) := by
      calc A 1 * lam ^ (2 * (4 * 1) + 1) = A 1 * lam ^ 9 := by norm_num
        _ < lam ^ 8 * A 2 * lam ^ 9 := hmul
        _ = A 2 * lam ^ (2 * (4 * 2) + 1) := by norm_num; ring
    exact mul_lt_mul_of_pos_right hkey hE
  · -- the uniform floor above the third scale
    intro j
    have hCj : C ^ j ≤ lam ^ (8 * j) := by
      calc C ^ j ≤ lam ^ j := pow_le_pow_left₀ (le_trans zero_le_one hC) hlC j
        _ ≤ lam ^ (8 * j) := pow_le_pow_right₀ hl1 (by omega)
    have hA2le : A 2 ≤ A (j + 2) * lam ^ (8 * j) := by
      calc A 2 ≤ C ^ j * A (j + 2) := hgrow j
        _ ≤ lam ^ (8 * j) * A (j + 2) :=
          mul_le_mul_of_nonneg_right hCj (hA _).le
        _ = A (j + 2) * lam ^ (8 * j) := mul_comm _ _
    have hexp : 2 * (4 * (j + 2)) + 1 = 8 * j + 17 := by ring
    unfold fuchsRate
    rw [hexp, pow_add lam (8 * j) 17]
    have hstep : A 2 * lam ^ 17 ≤ A (j + 2) * lam ^ (8 * j) * lam ^ 17 :=
      mul_le_mul_of_nonneg_right hA2le (pow_nonneg hlam.le 17)
    calc A 2 * lam ^ (2 * (4 * 2) + 1) * Real.exp (-(4 * Real.pi * lam ^ 2))
        = A 2 * lam ^ 17 * Real.exp (-(4 * Real.pi * lam ^ 2)) := by norm_num
      _ ≤ A (j + 2) * lam ^ (8 * j) * lam ^ 17 * Real.exp (-(4 * Real.pi * lam ^ 2)) :=
          mul_le_mul_of_nonneg_right hstep hE.le
      _ = A (j + 2) * (lam ^ (8 * j) * lam ^ 17) * Real.exp (-(4 * Real.pi * lam ^ 2)) := by
          ring

/-- **The CCM `8/11` law for the exact Fuchs-model constrained root.**  Only the
constraint-coordinate inputs — square-summability, the Bessel bound `Σℓ² ≤ 2λ`, and the
prolate-to-Hermite limits of the first two coordinates — remain as hypotheses; the whole
leakage side is the concrete radial Fuchs family. -/
theorem ccm_fuchsModel_infiniteSecularRoot_ratio_tendsto
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam =>
      infiniteSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) /
        fuchsRate (A 1) (4 * 1) lam) atTop (nhds (8 / 11)) :=
  ccm_infiniteSecularRoot_ratio_tendsto (d := fun lam j => fuchsRate (A j) (4 * j) lam)
    (fuchsRate_radial_struct hA hC hgrow) hsum hbessel
    (fuchsRate_div_tendsto_zero (hA 1) (hA 0) 0 (k := 4) (by norm_num))
    (fuchsRate_radial_tail_ratio_tendsto_zero (hA 1) (hA 2))
    hl0 hl1

/-- **The CCM `3/11` gap law for the exact Fuchs-model constrained root.** -/
theorem ccm_fuchsModel_infiniteSecularRoot_gap_ratio_tendsto
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)))) :
    Tendsto (fun lam =>
      (fuchsRate (A 1) (4 * 1) lam -
        infiniteSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam)) /
        fuchsRate (A 1) (4 * 1) lam) atTop (nhds (3 / 11)) :=
  ccm_infiniteSecularRoot_gap_ratio_tendsto (d := fun lam j => fuchsRate (A j) (4 * j) lam)
    (fuchsRate_radial_struct hA hC hgrow) hsum hbessel
    (fuchsRate_div_tendsto_zero (hA 1) (hA 0) 0 (k := 4) (by norm_num))
    (fuchsRate_radial_tail_ratio_tendsto_zero (hA 1) (hA 2))
    hl0 hl1

/-- **The quantified CCM constrained spectral gap for the exact Fuchs-model root.**  Every
`c < 3/11` eventually separates all competing secular zeros from the ground root by `c·d_1`. -/
theorem ccm_fuchsModel_infiniteSecularRoot_spectralGap_eventually
    {A : ℕ → ℝ} (hA : ∀ j, 0 < A j) {C : ℝ} (hC : 1 ≤ C)
    (hgrow : ∀ j, A 2 ≤ C ^ j * A (j + 2))
    {ℓ : ℝ → ℕ → ℝ}
    (hsum : ∀ᶠ lam in atTop, Summable fun j => ℓ lam j ^ 2)
    (hbessel : ∀ᶠ lam in atTop, (∑' j : ℕ, ℓ lam j ^ 2) ≤ 2 * lam)
    (hl0 : Tendsto (fun lam => ℓ lam 0) atTop (nhds ((2 : ℝ) ^ ((1 : ℝ) / 4))))
    (hl1 : Tendsto (fun lam => ℓ lam 1) atTop
      (nhds (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4))))
    {c : ℝ} (hc : c < 3 / 11) :
    ∀ᶠ lam in atTop, ∀ μ' : ℝ,
      infiniteSecular (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) μ' = 0 →
      μ' ≠ infiniteSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) →
      c * fuchsRate (A 1) (4 * 1) lam ≤
        μ' - infiniteSecularRoot (fun j => fuchsRate (A j) (4 * j) lam) (ℓ lam) :=
  ccm_infiniteSecularRoot_spectralGap_eventually (d := fun lam j => fuchsRate (A j) (4 * j) lam)
    (fuchsRate_radial_struct hA hC hgrow) hsum hbessel
    (fuchsRate_div_tendsto_zero (hA 1) (hA 0) 0 (k := 4) (by norm_num))
    (fuchsRate_radial_tail_ratio_tendsto_zero (hA 1) (hA 2))
    hl0 hl1 hc

end RHTower
