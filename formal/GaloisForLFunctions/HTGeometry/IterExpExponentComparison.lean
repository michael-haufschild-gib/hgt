import GaloisForLFunctions.HTGeometry.AffineExponentialCascadeGrowth

/-!
# Lowering the exponent absorbs a constant factor inside a tower

At the iterated-exponential scale a fixed positive factor and a halving of the radius are both
harmless: for every tower height `m`, every `δ > 0` and every `A > 0` there is a `δ' > 0` with

```text
iterExp m (r ^ δ') ≤ A · iterExp m ((r/2) ^ δ)   eventually.
```

This is the comparison the composition-depth lower bound runs on: Pólya's inequality produces a
modulus of the shape `exp((c · iterExp k ((r/2)^δ))^ε)`, and this lemma converts it into the shape
`iterExp (k+1) (r ^ δ')` required by `GrowthHeightAtLeast`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- **Lowering the exponent absorbs a constant factor.** -/
theorem exists_exponent_iterExp_le_const_mul (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ A : ℝ, 0 < A → ∃ δ' : ℝ, 0 < δ' ∧
      ∀ᶠ r : ℝ in atTop, iterExp m (r ^ δ') ≤ A * iterExp m ((r / 2) ^ δ) := by
  induction m with
  | zero =>
      intro A hA
      refine ⟨δ / 2, by linarith, ?_⟩
      have hK : 0 < A * (1 / 2 : ℝ) ^ δ := by positivity
      have hev : ∀ᶠ r : ℝ in atTop, (A * (1 / 2 : ℝ) ^ δ)⁻¹ ≤ r ^ (δ / 2) :=
        (tendsto_rpow_atTop (by linarith : (0:ℝ) < δ / 2)).eventually_ge_atTop _
      filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with r hr hr1
      have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
      have hsplit : (r / 2 : ℝ) ^ δ = r ^ δ * (1 / 2 : ℝ) ^ δ := by
        rw [show (r / 2 : ℝ) = r * (1 / 2) by ring, Real.mul_rpow hr0.le (by norm_num)]
      have hpow : r ^ (δ / 2) * r ^ (δ / 2) = r ^ δ := by
        rw [← Real.rpow_add hr0]
        congr 1
        ring
      simp only [iterExp_zero]
      rw [hsplit]
      have hstep : r ^ (δ / 2) ≤ (A * (1 / 2 : ℝ) ^ δ) * (r ^ (δ / 2) * r ^ (δ / 2)) := by
        have hrp : (0 : ℝ) < r ^ (δ / 2) := Real.rpow_pos_of_pos hr0 _
        rw [← mul_assoc]
        have h1 : 1 ≤ (A * (1 / 2 : ℝ) ^ δ) * r ^ (δ / 2) := by
          have hmul := mul_le_mul_of_nonneg_left hr hK.le
          rw [mul_inv_cancel₀ (ne_of_gt hK)] at hmul
          exact hmul
        nlinarith [h1, hrp]
      rw [hpow] at hstep
      calc r ^ (δ / 2) ≤ (A * (1 / 2 : ℝ) ^ δ) * r ^ δ := hstep
        _ = A * (r ^ δ * (1 / 2 : ℝ) ^ δ) := by ring
  | succ m ih =>
      intro A hA
      obtain ⟨δ', hδ'0, hδ'ev⟩ := ih (1 / 2) (by norm_num)
      refine ⟨δ', hδ'0, ?_⟩
      have hYtop : Tendsto (fun r : ℝ => iterExp m ((r / 2) ^ δ)) atTop atTop := by
        have h1 : Tendsto (fun r : ℝ => r / 2) atTop atTop :=
          Filter.tendsto_atTop_atTop.mpr fun b => ⟨2 * b, fun a ha => by linarith⟩
        exact (tendsto_iterExp_rpow m hδ).comp h1
      filter_upwards [hδ'ev, hYtop.eventually_ge_atTop (-(2 * Real.log A))] with r hr hY
      rw [iterExp_succ, iterExp_succ]
      have hexp : A * Real.exp (iterExp m ((r / 2) ^ δ))
          = Real.exp (Real.log A + iterExp m ((r / 2) ^ δ)) := by
        rw [Real.exp_add, Real.exp_log hA]
      rw [hexp]
      refine Real.exp_le_exp.mpr ?_
      linarith [hr, hY]



/-- **Lowering the exponent absorbs a fractional power.**  For every tower height `k`, every `δ > 0`
and every `ε > 0` there is a `δ' > 0` with `iterExp k (r^δ') ≤ (iterExp k ((r/2)^δ))^ε`
eventually. -/
theorem exists_exponent_iterExp_le_rpow (k : ℕ) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ δ' : ℝ, 0 < δ' ∧
      ∀ᶠ r : ℝ in atTop, iterExp k (r ^ δ') ≤ (iterExp k ((r / 2) ^ δ)) ^ ε := by
  cases k with
  | zero =>
      refine ⟨δ * ε / 2, by positivity, ?_⟩
      have hev : ∀ᶠ r : ℝ in atTop, (2 : ℝ) ^ (δ * ε) ≤ r ^ (δ * ε / 2) :=
        (tendsto_rpow_atTop (by positivity : (0:ℝ) < δ * ε / 2)).eventually_ge_atTop _
      filter_upwards [hev, eventually_gt_atTop (0 : ℝ)] with r hr hr0
      simp only [iterExp_zero]
      have hrhs : ((r / 2 : ℝ) ^ δ) ^ ε = (r / 2 : ℝ) ^ (δ * ε) :=
        (Real.rpow_mul (by positivity) δ ε).symm
      rw [hrhs]
      have hsplit : (r / 2 : ℝ) ^ (δ * ε) = r ^ (δ * ε) * (1 / 2 : ℝ) ^ (δ * ε) := by
        rw [show (r / 2 : ℝ) = r * (1 / 2) by ring, Real.mul_rpow hr0.le (by norm_num)]
      rw [hsplit]
      have hpow : r ^ (δ * ε) = r ^ (δ * ε / 2) * r ^ (δ * ε / 2) := by
        rw [← Real.rpow_add hr0]
        congr 1
        ring
      rw [hpow]
      have hhalfpos : (0 : ℝ) < (1 / 2 : ℝ) ^ (δ * ε) := Real.rpow_pos_of_pos (by norm_num) _
      have h2 : (2 : ℝ) ^ (δ * ε) * (1 / 2 : ℝ) ^ (δ * ε) = 1 := by
        rw [← Real.mul_rpow (by norm_num) (by norm_num)]
        norm_num
      have hrp : (0 : ℝ) < r ^ (δ * ε / 2) := Real.rpow_pos_of_pos hr0 _
      have hstep : 1 ≤ r ^ (δ * ε / 2) * (1 / 2 : ℝ) ^ (δ * ε) := by
        nlinarith [hr, hhalfpos, h2]
      nlinarith [hstep, hrp]
  | succ k =>
      obtain ⟨δ', hδ'0, hδ'ev⟩ := exists_exponent_iterExp_le_const_mul k hδ ε hε
      refine ⟨δ', hδ'0, ?_⟩
      filter_upwards [hδ'ev] with r hr
      rw [iterExp_succ, iterExp_succ]
      have hrhs : (Real.exp (iterExp k ((r / 2) ^ δ))) ^ ε
          = Real.exp (iterExp k ((r / 2) ^ δ) * ε) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [hrhs]
      refine Real.exp_le_exp.mpr ?_
      calc iterExp k (r ^ δ') ≤ ε * iterExp k ((r / 2) ^ δ) := hr
        _ = iterExp k ((r / 2) ^ δ) * ε := by ring

end GaloisForLFunctions.HTGeometry
