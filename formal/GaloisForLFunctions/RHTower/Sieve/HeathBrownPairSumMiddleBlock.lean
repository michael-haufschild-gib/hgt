import GaloisForLFunctions.RHTower.Sieve.HeathBrownPairSumSmallBlock

/-!
# Heath-Brown's pair sums: every block length

`HeathBrownPairSumSmallBlock` reflects a block of length `M` onto the *fixed* auxiliary length
`⌈(2T)^{2/3}⌉`, which forces `M² ≤ (2T)^{2/3}`.  Taking instead the *variable* target `N = M²`
removes that restriction: `hbAmp_sq_le_rpow` applies for every `M` (its only hypothesis is
`M² ≤ N`), and the long-block bound applies at `N = M²` as soon as `2T < M⁴` and `4T² ≤ 9M⁶`,
both of which follow from `(2T)^{1/3} ≤ M`.  There is no upper constraint anywhere: the
hypotheses of `hbAmp_half_Ioc_eight_le_of_diam` are lower bounds on the length.

The resulting bound is

`Σ_{t₁,t₂∈W} |Σ_{M<n≤2M} a_n n^{i(t₁−t₂)}|² ≤ C(T,δ,M) (|W|² M + |W|^{3/2} M²)`,

because the long-block bound at `N = M²` contributes `112 M² |W| c(T)`, and the square root of
Corollary 2.1 turns `|W|²·M²|W|c` into `|W|^{3/2}M`.  Together with the short-block theorem at
`M ≤ (2T)^{1/3}` — the two ranges meet exactly at `(2T)^{1/3}` — this gives a bound valid for
*every* block length (`hbPairSum_Ioc_le_anyBlock`).

The middle term is `|W|^{3/2}M²` rather than Heath-Brown's `|W|M² + |W|^{5/4}T^{1/2}M`: the
Cauchy–Schwarz of Corollary 2.1 pays a factor `|W|^{1/2}` that the two Heath-Brown terms do not.
It is absorbed when `|W|^{1/4}M ≤ T^{1/2}` and when `M ≥ (2T)^{2/3}` (where
`hbPairSum_Ioc_le_of_twoThirds` is sharper), so the loss is confined to
`T^{1/2}/|W|^{1/4} < M < (2T)^{2/3}`.
-/

set_option autoImplicit false

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The explicit constant attached to an auxiliary block length `L`; `hbSmallConst T δ` is the
case `L = hbLongBlock T`. -/
def hbBlockConst (T δ : ℝ) (L : ℕ) : ℝ :=
  3584 * ((divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
    (hbReflFactor T + hbDualFactor T + 1)

theorem hbSmallConst_eq_hbBlockConst (T δ : ℝ) :
    hbSmallConst T δ = hbBlockConst T δ (hbLongBlock T) := rfl

theorem hbBlockConst_nonneg {T δ : ℝ} (hT : 1 ≤ T) (L : ℕ) : 0 ≤ hbBlockConst T δ L := by
  have hc := one_le_hbReflFactor (T := T) hT
  have hK := hbDualFactor_nonneg T
  have hA : (0 : ℝ) ≤ (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 := by positivity
  rw [hbBlockConst]
  nlinarith

theorem one_le_hbBlockConst_div_two {T δ : ℝ} (hT : 1 ≤ T) (L : ℕ) :
    1 ≤ hbBlockConst T δ L / 2 := by
  have hc := one_le_hbReflFactor (T := T) hT
  have hK := hbDualFactor_nonneg T
  have hA : (0 : ℝ) ≤ (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 := by positivity
  have h2 : (2 : ℝ) ≤ ((divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
      (hbReflFactor T + hbDualFactor T + 1) := by nlinarith
  rw [hbBlockConst]
  linarith

theorem hbBlockConst_refl_le {T δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ) (L : ℕ) :
    896 * (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 5 * hbReflFactor T ≤
      hbBlockConst T δ L / 2 := by
  have hC0 : (0 : ℝ) ≤ divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ :=
    mul_nonneg (divisorBoundConst_pos hδ).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h5 : (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 5 ≤
      (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 + 1 := by
    rcases le_total (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) 1 with h | h
    · have h1 : (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 5 ≤ 1 := pow_le_one₀ hC0 h
      have h2 : (0 : ℝ) ≤ (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 := by positivity
      linarith
    · have h1 : (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 5 ≤
          (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 :=
        pow_le_pow_right₀ h (by norm_num)
      linarith
  have hc := one_le_hbReflFactor (T := T) hT
  have hK := hbDualFactor_nonneg T
  have hA : (0 : ℝ) ≤ (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 := by positivity
  have hprod : (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 5 * hbReflFactor T ≤
      ((divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
        (hbReflFactor T + hbDualFactor T + 1) :=
    mul_le_mul h5 (by linarith) (by linarith) (by linarith)
  have hpos : (0 : ℝ) ≤ ((divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
      (hbReflFactor T + hbDualFactor T + 1) := by nlinarith
  rw [hbBlockConst]
  linarith

theorem hbBlockConst_dual_le {T δ : ℝ} (hT : 1 ≤ T) (L : ℕ) :
    4 * (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 * hbDualFactor T ≤
      hbBlockConst T δ L / 2 := by
  have hc := one_le_hbReflFactor (T := T) hT
  have hK := hbDualFactor_nonneg T
  have hA : (0 : ℝ) ≤ (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 := by positivity
  have hprod : (divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 * hbDualFactor T ≤
      ((divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
        (hbReflFactor T + hbDualFactor T + 1) :=
    mul_le_mul (by linarith) (by linarith) hK (by linarith)
  have hpos : (0 : ℝ) ≤ ((divisorBoundConst δ * ((8 * L : ℕ) : ℝ) ^ δ) ^ 10 + 1) *
      (hbReflFactor T + hbDualFactor T + 1) := by nlinarith
  rw [hbBlockConst]
  linarith

/-- The scalar inequality for the variable target `N = M²`. -/
private theorem middleBlock_arith {w m c K C X : ℝ} (hw : 1 ≤ w) (hm : 0 ≤ m) (hC : 0 ≤ C)
    (_hc : 1 ≤ c) (hX1 : 1 ≤ X) (hXa : 896 * C ^ 5 * c ≤ X) (hXb : 4 * C ^ 10 * K ≤ X) :
    2 * C ^ 5 * w ^ 2 * (112 * m ^ 2 * w * c + K * (2 * C ^ 5 * w ^ 2)) ≤
      (X * (w ^ ((3 : ℝ) / 2) * m + w ^ 2)) ^ 2 := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hC5 : (0 : ℝ) ≤ C ^ 5 := by positivity
  have hC10 : (0 : ℝ) ≤ C ^ 10 := by positivity
  have hw3 : (w ^ ((3 : ℝ) / 2)) ^ 2 = w ^ 3 := by
    rw [← Real.rpow_natCast (w ^ ((3 : ℝ) / 2)) 2, ← Real.rpow_mul hw0.le,
      show ((3 : ℝ) / 2 * (2 : ℕ)) = 3 by norm_num,
      show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hwm : (0 : ℝ) ≤ w ^ ((3 : ℝ) / 2) * m := mul_nonneg (Real.rpow_nonneg hw0.le _) hm
  have hw2 : (0 : ℝ) ≤ w ^ 2 := by positivity
  have hw4 : (0 : ℝ) ≤ w ^ 4 := by positivity
  have hm3 : (0 : ℝ) ≤ w ^ 3 * m ^ 2 := by positivity
  -- the expanded square dominates the two monomials
  have hexp : (X * (w ^ ((3 : ℝ) / 2) * m + w ^ 2)) ^ 2 =
      X ^ 2 * (w ^ 3 * m ^ 2) + 2 * (X ^ 2 * (w ^ ((3 : ℝ) / 2) * m * w ^ 2)) + X ^ 2 * w ^ 4 := by
    have h : (w ^ ((3 : ℝ) / 2) * m + w ^ 2) ^ 2 =
        (w ^ ((3 : ℝ) / 2)) ^ 2 * m ^ 2 + 2 * (w ^ ((3 : ℝ) / 2) * m * w ^ 2) + (w ^ 2) ^ 2 := by
      ring
    rw [mul_pow, h, hw3]
    ring
  have hX2 : X ≤ X ^ 2 := by nlinarith
  have hXa2 : 896 * C ^ 5 * c ≤ X ^ 2 := hXa.trans hX2
  have hXb2 : 4 * C ^ 10 * K ≤ X ^ 2 := hXb.trans hX2
  have k1 : 224 * C ^ 5 * c * (w ^ 3 * m ^ 2) ≤ X ^ 2 * (w ^ 3 * m ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hXa2 hm3
    nlinarith
  have k2 : 4 * C ^ 10 * K * w ^ 4 ≤ X ^ 2 * w ^ 4 := mul_le_mul_of_nonneg_right hXb2 hw4
  have k3 : (0 : ℝ) ≤ X ^ 2 * (w ^ ((3 : ℝ) / 2) * m * w ^ 2) :=
    mul_nonneg (sq_nonneg X) (mul_nonneg hwm hw2)
  have hlhs : 2 * C ^ 5 * w ^ 2 * (112 * m ^ 2 * w * c + K * (2 * C ^ 5 * w ^ 2)) =
      224 * C ^ 5 * c * (w ^ 3 * m ^ 2) + 4 * C ^ 10 * K * w ^ 4 := by ring
  rw [hexp, hlhs]
  linarith

/-- **Heath-Brown's pair sum for `M ≥ (2T)^{1/3}`.**  Corollary 2.1 at the variable target
`N = M²`, where the long-block theorem applies. -/
theorem hbPairSum_Ioc_le_middleBlock {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {M : ℕ}
    (hMT : (2 * T) ^ ((1 : ℝ) / 3) ≤ (M : ℝ)) {δ : ℝ} (hδ : 0 < δ)
    {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc M (2 * M)) a ≤ hbBlockConst T δ (M ^ 2) *
      ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2) := by
  classical
  have hT0 : (0 : ℝ) ≤ 2 * T := by linarith
  have hC0 : 0 ≤ hbBlockConst T δ (M ^ 2) := hbBlockConst_nonneg hT _
  -- `M³ ≥ 2T`, hence `M ≥ 2`
  have hM3 : 2 * T ≤ (M : ℝ) ^ 3 := by
    have hcube : ((2 * T) ^ ((1 : ℝ) / 3)) ^ 3 = 2 * T := by
      rw [← Real.rpow_natCast ((2 * T) ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul hT0,
        show ((1 : ℝ) / 3 * (3 : ℕ)) = 1 by norm_num, Real.rpow_one]
    calc 2 * T = ((2 * T) ^ ((1 : ℝ) / 3)) ^ 3 := hcube.symm
      _ ≤ (M : ℝ) ^ 3 := pow_le_pow_left₀ (Real.rpow_nonneg hT0 _) hMT 3
  have hMcube : (2 : ℝ) ≤ (M : ℝ) ^ 3 := by linarith
  have hM2 : 2 ≤ M := by
    rcases Nat.lt_or_ge M 2 with hcon | hcon
    · interval_cases M
      · norm_num at hMcube
      · norm_num at hMcube
    · exact hcon
  have hMge : (1 : ℝ) < (M : ℝ) := by exact_mod_cast hM2
  rcases Nat.eq_zero_or_pos W.card with hw0 | hwpos
  · have hWe : W = ∅ := Finset.card_eq_zero.mp hw0
    have hzero : hbPairSum W (Finset.Ioc M (2 * M)) a = 0 := by
      rw [hbPairSum, hWe]; simp
    rw [hzero]
    exact mul_nonneg hC0 (by positivity)
  · have hw1 : (1 : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hwpos
    -- the long block is `N = M²`
    have hN1 : 1 ≤ M ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hN2 : 2 * T < ((M ^ 2 : ℕ) : ℝ) ^ 2 := by
      have h4 : ((M ^ 2 : ℕ) : ℝ) ^ 2 = (M : ℝ) ^ 3 * (M : ℝ) := by push_cast; ring
      rw [h4]
      nlinarith [pow_pos (lt_trans zero_lt_one hMge) 3]
    have hN3 : 4 * T ^ 2 ≤ 9 * ((M ^ 2 : ℕ) : ℝ) ^ 3 := by
      have h6 : ((M ^ 2 : ℕ) : ℝ) ^ 3 = ((M : ℝ) ^ 3) ^ 2 := by push_cast; ring
      rw [h6]
      nlinarith [sq_nonneg ((M : ℝ) ^ 3 - 2 * T)]
    have hstep1 := hbAmp_sq_le_rpow W hδ (by omega : 0 < M) (le_refl (M ^ 2))
      (subset_rfl (a := Finset.Ioc M (2 * M)))
    have hstep2 := hbAmp_half_Ioc_eight_le_of_diam hW hT hdiam hN1 hN2 hN3 hδ
    have hC₁0 : 0 ≤ divisorBoundConst δ * ((8 * M ^ 2 : ℕ) : ℝ) ^ δ :=
      mul_nonneg (divisorBoundConst_pos hδ).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hP0 : (0 : ℝ) ≤ 2 * (divisorBoundConst δ * ((8 * M ^ 2 : ℕ) : ℝ) ^ δ) ^ 5 *
        (W.card : ℝ) ^ 2 := by positivity
    have hsq := hstep1.trans (mul_le_mul_of_nonneg_left hstep2 hP0)
    have hG : hbAmp W (1 / 2) (Finset.Ioc M (2 * M)) ≤
        (hbBlockConst T δ (M ^ 2) / 2) *
          ((W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) + (W.card : ℝ) ^ 2) := by
      have hA0 : 0 ≤ hbAmp W (1 / 2) (Finset.Ioc M (2 * M)) := hbAmp_nonneg W _ _
      have hX1 : (1 : ℝ) ≤ hbBlockConst T δ (M ^ 2) / 2 := one_le_hbBlockConst_div_two hT _
      have hwm : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) :=
        mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
      have hG0 : (0 : ℝ) ≤ (hbBlockConst T δ (M ^ 2) / 2) *
          ((W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) + (W.card : ℝ) ^ 2) := by
        have h2 : (0 : ℝ) ≤ hbBlockConst T δ (M ^ 2) / 2 := by linarith
        have h3 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 := by positivity
        exact mul_nonneg h2 (by linarith)
      refine (pow_le_pow_iff_left₀ hA0 hG0 (two_ne_zero)).mp (hsq.trans ?_)
      have hc1 := one_le_hbReflFactor (T := T) hT
      have hNcast : (((M ^ 2 : ℕ)) : ℝ) = (M : ℝ) ^ 2 := by push_cast; ring
      have hmain := middleBlock_arith (w := (W.card : ℝ)) (m := (M : ℝ))
        (c := hbReflFactor T) (K := hbDualFactor T)
        (C := divisorBoundConst δ * ((8 * M ^ 2 : ℕ) : ℝ) ^ δ)
        (X := hbBlockConst T δ (M ^ 2) / 2) hw1 (Nat.cast_nonneg _) hC₁0 hc1 hX1
        (hbBlockConst_refl_le hT hδ _) (hbBlockConst_dual_le hT _)
      rw [hNcast]
      exact hmain
    calc hbPairSum W (Finset.Ioc M (2 * M)) a
        ≤ 2 * M * hbAmp W (1 / 2) (Finset.Ioc M (2 * M)) :=
          hbPairSum_le_two_mul_hbAmp_half W ha
      _ ≤ 2 * M * ((hbBlockConst T δ (M ^ 2) / 2) *
            ((W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) + (W.card : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hG (by positivity)
      _ = hbBlockConst T δ (M ^ 2) *
            ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2) := by ring

/-- **Every block length.**  Below `(2T)^{1/3}` the short-block bound applies, above it the
middle-block bound; the two ranges meet exactly at `(2T)^{1/3}`. -/
theorem hbPairSum_Ioc_le_anyBlock {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {M : ℕ} (hM : 1 ≤ M)
    {δ : ℝ} (hδ : 0 < δ) {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) :
    hbPairSum W (Finset.Ioc M (2 * M)) a ≤
      (hbSmallConst T δ + hbBlockConst T δ (M ^ 2)) *
        ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M
          + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2) := by
  have hT0 : (0 : ℝ) ≤ 2 * T := by linarith
  have hS0 : 0 ≤ hbSmallConst T δ := le_trans zero_le_one (one_le_hbSmallConst hT hδ)
  have hB0 : 0 ≤ hbBlockConst T δ (M ^ 2) := hbBlockConst_nonneg hT _
  have hm1 : (0 : ℝ) ≤ (W.card : ℝ) ^ 2 * M := by positivity
  have hm2 : (0 : ℝ) ≤ (W.card : ℝ) * (M : ℝ) ^ 2 := by positivity
  have hm3 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (by linarith) _)) (Nat.cast_nonneg _)
  have hm4 : (0 : ℝ) ≤ (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  rcases le_total ((M : ℝ)) ((2 * T) ^ ((1 : ℝ) / 3)) with h | h
  · -- the short range
    have hMT : (M : ℝ) ^ 2 ≤ (2 * T) ^ ((2 : ℝ) / 3) := by
      have h2 : ((2 * T) ^ ((1 : ℝ) / 3)) ^ 2 = (2 * T) ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast ((2 * T) ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul hT0]
        norm_num
      calc (M : ℝ) ^ 2 ≤ ((2 * T) ^ ((1 : ℝ) / 3)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
        _ = _ := h2
    refine (hbPairSum_Ioc_le_smallBlock hW hT hdiam hM hMT hδ ha).trans ?_
    have h1 : hbSmallConst T δ ≤ hbSmallConst T δ + hbBlockConst T δ (M ^ 2) := by linarith
    have h2 : (W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2 +
        (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M ≤
      (W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2 +
        (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M +
        (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2 := by linarith
    exact mul_le_mul h1 h2 (by linarith) (by linarith)
  · -- the middle and long range
    refine (hbPairSum_Ioc_le_middleBlock hW hT hdiam h hδ ha).trans ?_
    have h1 : hbBlockConst T δ (M ^ 2) ≤ hbSmallConst T δ + hbBlockConst T δ (M ^ 2) := by linarith
    have h2 : (W.card : ℝ) ^ 2 * M + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2 ≤
      (W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2 +
        (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M +
        (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2 := by linarith
    exact mul_le_mul h1 h2 (by linarith) (by linarith)

/-- **Every block length, in the Section 11 phase convention.** -/
theorem sum_sum_norm_sq_exp_le_anyBlock {W : Finset ℝ} (hW : GuthMaynard.IsSeparated 1 W)
    {T : ℝ} (hT : 1 ≤ T) (hdiam : ∀ t ∈ W, ∀ t' ∈ W, |t - t'| ≤ T) {M : ℕ} (hM : 1 ≤ M)
    {δ : ℝ} (hδ : 0 < δ) {a : ℕ → ℂ} (ha : ∀ n ∈ Finset.Ioc M (2 * M), ‖a n‖ ≤ 1) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ‖∑ n ∈ Finset.Ioc M (2 * M),
        a n * Complex.exp (Complex.I * ((t₁ : ℂ) - (t₂ : ℂ)) * (Real.log n : ℂ))‖ ^ 2 ≤
      (hbSmallConst T δ + hbBlockConst T δ (M ^ 2)) *
        ((W.card : ℝ) ^ 2 * M + (W.card : ℝ) * (M : ℝ) ^ 2
          + (W.card : ℝ) ^ ((5 : ℝ) / 4) * T ^ ((1 : ℝ) / 2) * M
          + (W.card : ℝ) ^ ((3 : ℝ) / 2) * (M : ℝ) ^ 2) := by
  rw [← hbPairSum_eq_sum_exp]
  exact hbPairSum_Ioc_le_anyBlock hW hT hdiam hM hδ ha

end

end RHTower.Sieve
