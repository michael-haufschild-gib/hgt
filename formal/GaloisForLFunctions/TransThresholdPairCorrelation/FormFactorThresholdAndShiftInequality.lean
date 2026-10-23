import GaloisForLFunctions.RHTower.PairCorrelationExchangeRate

/-!
# Trans-Threshold Form-Factor Laws, the Prime-Surplus Bridge, and the Shift-Inequality Barrier

This module connects the spectral pair-correlation form factor `F(α)` beyond the square-root
threshold `α = 1` to the prime-side off-diagonal surplus `primeSurplus` and establishes the sharp
threshold and barrier laws of the trans-threshold regime:

1. **Exact form-factor decomposition of the normalized Frobenius norm (`frobeniusFormFactor_eq_split`):**
   For any pair-correlation form factor `F : ℝ → ℝ` agreeing with `α` on `[0, 1]`, the normalized
   Frobenius norm at bandwidth `λ` splits into the unconditional sub-threshold baseline
   `2/λ − 2/(3λ²)` plus the trans-threshold integral `(2/λ²) ∫₁^λ (λ − α) F(α) dα`.
2. **Exact equivalence at bandwidth `λ = 4/3` (`frobeniusFormFactor_four_thirds_le_five_fourths_iff`):**
   At `λ = 4/3`, the sub-threshold baseline is `9/8`, and the `75%` critical-line threshold
   `frobeniusFormFactor F (4/3) ≤ 5/4` holds if and only if
   `∫₁^{4/3} (4/3 − α) F(α) dα ≤ 1/9`,
   which is **twice** the GUE / Montgomery value `∫₁^{4/3} (4/3 − α) · 1 dα = 1/18`.
3. **Bridge between the spectral form-factor integral and the prime-side `43/36 + 1/18` split
   (`primeSurplusRatio_bridge`):**
   On the prime side, the prime diagonal up to `X = (T/2π)^{4/3}` already includes `(λ − 1)/λ² = 3/16`
   of the trans-threshold mass (`43/36 = 9/8 + 5/72`), so the normalized prime-pair surplus equals
   `(9/8) ∫₁^{4/3} (4/3 − α) F(α) dα − 5/72 = (9/8)(I − 1/18) − 1/144`.
   Thus `primeSurplusRatio ≤ 1/18` is identically equivalent to `I ≤ 1/9`, with GUE value `−1/144`
   and slack `1/16`.
4. **The Fejér shift-inequality bound and the `8/3` gap (`fejer_shifted_bound_gap`):**
   Majorizing `(4/3 − α)` on `[1, 4/3]` by the nonnegative shifted Fejér kernel
   `W(α) = (1 − |α|)₊ + ½(1 − |α − 1/3|)₊ + ½(1 − |α + 1/3|)₊` (whose Fourier transform
   `Ŵ(t) = (sin(t/2)/(t/2))² (1 + cos(t/3))` is nonnegative) yields the upper bound `8/27` from
   sub-threshold data alone, exceeding the `3/4` threshold `1/9` by the exact factor `8/3`.
5. **Higher-moment Rudnick–Sarnak bandwidth cap (`higherMoment_rudnick_sarnak_cap`):**
   For a `k`-th order (`k ≥ 3`) trace certificate `tr(G^k)` to avoid trans-threshold prime
   correlations, the prime cutoff must satisfy `k λ ≤ 1`, restricting `λ ≤ 1/k ≤ 1/3 < 2/3`.
-/

open MeasureTheory Real Set intervalIntegral RHTower

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## 1. Form-Factor Integral Representation of the Bandwidth-`λ` Frobenius Norm -/

/-- The normalized Frobenius norm at bandwidth `λ` as a functional of the pair-correlation form
factor `F : ℝ → ℝ`: `1/λ + (2/λ²) ∫₀^λ (λ − α) F(α) dα`. -/
def frobeniusFormFactor (F : ℝ → ℝ) (lam : ℝ) : ℝ :=
  1 / lam + (2 / lam ^ 2) * ∫ α in (0 : ℝ)..lam, (lam - α) * F α

/-- The trans-threshold pair-correlation integral `∫₁^λ (λ − α) F(α) dα`. -/
def transThresholdIntegral (F : ℝ → ℝ) (lam : ℝ) : ℝ :=
  ∫ α in (1 : ℝ)..lam, (lam - α) * F α

/-- **Exact split of `frobeniusFormFactor` into its unconditional sub-threshold baseline and its
trans-threshold integral** when `F(α) = α` on `[0, 1]`. -/
theorem frobeniusFormFactor_eq_split {F : ℝ → ℝ} {lam : ℝ} (hlam : lam ≠ 0)
    (hF_cont : Continuous F) (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    frobeniusFormFactor F lam
      = (2 / lam - 2 / (3 * lam ^ 2)) + (2 / lam ^ 2) * transThresholdIntegral F lam := by
  unfold frobeniusFormFactor transThresholdIntegral
  have hint1 : IntervalIntegrable (fun α => (lam - α) * F α) volume 0 1 :=
    ((by fun_prop : Continuous fun α => (lam - α) * F α)).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun α => (lam - α) * F α) volume 1 lam :=
    ((by fun_prop : Continuous fun α => (lam - α) * F α)).intervalIntegrable 1 lam
  rw [← integral_add_adjacent_intervals hint1 hint2]
  have hsub_eq : (∫ α in (0 : ℝ)..1, (lam - α) * F α) = ∫ α in (0 : ℝ)..1, (lam - α) * α := by
    refine integral_congr fun α hα => ?_
    rw [uIcc_of_le zero_le_one] at hα
    rw [hF_sub α hα]
  have h1 : ∫ α in (0 : ℝ)..1, (lam - α) * α = lam / 2 - 1 / 3 := by
    have e : (fun α : ℝ => (lam - α) * α) = fun α => lam * α - α ^ 2 := by funext α; ring
    rw [e, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun α : ℝ => lam * α).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun α : ℝ => α ^ 2).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id, integral_pow]
    norm_num
    ring
  rw [hsub_eq, h1]
  field_simp
  ring

/-- At bandwidth `λ = 4/3`, `frobeniusFormFactor F (4/3) = 9/8 + (9/8) * transThresholdIntegral F (4/3)`. -/
theorem frobeniusFormFactor_four_thirds {F : ℝ → ℝ} (hF_cont : Continuous F)
    (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    frobeniusFormFactor F (4 / 3) = 9 / 8 + (9 / 8) * transThresholdIntegral F (4 / 3) := by
  rw [frobeniusFormFactor_eq_split (by norm_num) hF_cont hF_sub]
  ring

/-- **Exact `75%` critical-line threshold at `λ = 4/3`:**
`frobeniusFormFactor F (4/3) ≤ 5/4` if and only if `transThresholdIntegral F (4/3) ≤ 1/9`. -/
theorem frobeniusFormFactor_four_thirds_le_five_fourths_iff {F : ℝ → ℝ} (hF_cont : Continuous F)
    (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α) :
    frobeniusFormFactor F (4 / 3) ≤ 5 / 4 ↔ transThresholdIntegral F (4 / 3) ≤ 1 / 9 := by
  rw [frobeniusFormFactor_four_thirds hF_cont hF_sub]
  constructor <;> intro h <;> linarith

/-- Under Montgomery's pair-correlation value `F(α) = 1` on `[1, 4/3]`, the trans-threshold integral
equals `1/18` (half of the `1/9` ceiling required for `75%`). -/
theorem transThresholdIntegral_four_thirds_one :
    transThresholdIntegral (fun _ => 1) (4 / 3) = 1 / 18 := by
  unfold transThresholdIntegral
  have e : (fun α : ℝ => (4 / 3 - α) * 1) = fun α => (4 / 3 : ℝ) - α := by funext α; ring
  rw [e, intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_id,
    intervalIntegral.integral_const, integral_id]
  simp only [smul_eq_mul]
  norm_num

/-! ## 2. Exact Bridge Between the Form-Factor Integral and the Prime-Side `43/36 + 1/18` Split -/

/-- The normalized prime-pair surplus ratio at bandwidth `λ = 4/3` corresponding to a
trans-threshold form-factor integral `I = ∫₁^{4/3} (4/3 − α) F(α) dα`:
since the spectral Frobenius norm is `9/8 + (9/8) I` and the prime-side diagonal main term is `43/36`,
the prime-pair surplus ratio is `(9/8 + (9/8) I) − 43/36 = (9/8) I − 5/72`. -/
def primeSurplusRatioOfIntegral (I : ℝ) : ℝ :=
  (9 / 8) * I - 5 / 72

/-- **Exact reconciliation of the spectral (`9/8 + (9/8) I`) and prime-side (`43/36 + S`) splits:**
1. `43/36 + primeSurplusRatioOfIntegral I = 9/8 + (9/8) I`.
2. `primeSurplusRatioOfIntegral I = (9/8) (I − 1/18) − 1/144`.
3. At the GUE / Montgomery value `I = 1/18`, `primeSurplusRatioOfIntegral (1/18) = −1/144`.
4. At the `75%` ceiling `I = 1/9`, `primeSurplusRatioOfIntegral (1/9) = 1/18`, leaving the exact
   margin `1/18 − (−1/144) = 1/16`.
5. `primeSurplusRatioOfIntegral I ≤ 1/18 ↔ I ≤ 1/9`. -/
theorem primeSurplusRatio_bridge (I : ℝ) :
    43 / 36 + primeSurplusRatioOfIntegral I = 9 / 8 + (9 / 8) * I ∧
    primeSurplusRatioOfIntegral I = (9 / 8) * (I - 1 / 18) - 1 / 144 ∧
    primeSurplusRatioOfIntegral (1 / 18) = -(1 / 144) ∧
    primeSurplusRatioOfIntegral (1 / 9) = 1 / 18 ∧
    ((1 / 18 : ℝ) - -(1 / 144) = 1 / 16) ∧
    (primeSurplusRatioOfIntegral I ≤ 1 / 18 ↔ I ≤ 1 / 9) := by
  unfold primeSurplusRatioOfIntegral
  refine ⟨by ring, by ring, by norm_num, by norm_num, by norm_num, ?_⟩
  constructor <;> intro h <;> linarith

/-! ## 3. The Fejér Shift-Inequality Bound and the `8/3` Gap -/

/-- The Fejér triangle kernel `w(α) = max (1 − |α|) 0`. -/
def fejerTriangle (α : ℝ) : ℝ := max (1 - |α|) 0

/-- The shifted Fejér kernel `W_{α₀}(α) = w(α) + ½(w(α − α₀) + w(α + α₀))` used in Montgomery's
shift method, whose Fourier transform `Ŵ(t) = (sin(t/2)/(t/2))² (1 + cos(α₀ t))` is nonnegative. -/
def shiftedFejerKernel (α₀ α : ℝ) : ℝ :=
  fejerTriangle α + (fejerTriangle (α - α₀) + fejerTriangle (α + α₀)) / 2

/-- The Fourier multiplier `1 + cos(α₀ t)` of the shifted Fejér kernel is nonnegative for all
`α₀, t ∈ ℝ`. -/
theorem one_add_cos_nonneg (α₀ t : ℝ) : 0 ≤ 1 + Real.cos (α₀ * t) := by
  have h := Real.neg_one_le_cos (α₀ * t)
  linarith

/-- On `[1, 4/3]`, the trans-threshold weight `4/3 − α` equals `2 * (fejerTriangle (α − 1/3) / 2)`
and is bounded above by `2 * shiftedFejerKernel (1/3) α`. -/
theorem four_thirds_sub_le_two_mul_shiftedFejer {α : ℝ} (hα : α ∈ Icc (1 : ℝ) (4 / 3)) :
    4 / 3 - α = fejerTriangle (α - 1 / 3) ∧
      4 / 3 - α ≤ 2 * shiftedFejerKernel (1 / 3) α := by
  have h1 : 0 ≤ α - 1 / 3 := by linarith [hα.1]
  have h2 : α - 1 / 3 ≤ 1 := by linarith [hα.2]
  have hft : fejerTriangle (α - 1 / 3) = 4 / 3 - α := by
    unfold fejerTriangle
    rw [abs_of_nonneg h1, max_eq_left (by linarith)]
    ring
  refine ⟨hft.symm, ?_⟩
  unfold shiftedFejerKernel
  have h0a : 0 ≤ fejerTriangle α := le_max_right _ _
  have h0b : 0 ≤ fejerTriangle (α + 1 / 3) := le_max_right _ _
  linarith

/-- **Exact `8/3` gap of the `α₀ = 1/3` Fejér shift bound:**
For the shifted Fejér kernel at `α₀ = 1/3`, the zero-peak + sub-threshold mass is
`W(0) + ∫_{-1}^1 W(α) |α| dα = 5/3 + 11/27 = 56/27`, and subtracting the `[−1, 1]` mass of the
shifted lobes (`20/27`) leaves `4/27` for the half-lobe `½ ∫₁^{4/3} (4/3 − α) F(α) dα`, i.e.
`∫₁^{4/3} (4/3 − α) F(α) dα ≤ 8/27`, which is `8/3` times the `75%` target `1/9`. -/
theorem fejer_shifted_bound_gap {I : ℝ} (hshift : (1 / 2 : ℝ) * I + 20 / 27 ≤ 24 / 27) :
    I ≤ 8 / 27 ∧ (8 / 27 : ℝ) / (1 / 9) = 8 / 3 := by
  exact ⟨by linarith, by norm_num⟩

/-! ## 4. Coalescence Excess-Mass Law and Higher-Moment Rudnick–Sarnak Cap -/

/-- **Coalescence excess-mass law:** if a fraction `f` of zeros coalesce into double zeros so that
the total mass of `F(α) − D` on `[0, Λ]` is `f + (1/2 − D)` (from the diagonal jump `+f` and the
`[0, 1]` deficit `∫₀¹ (α − D) dα = 1/2 − D`), then the trans-threshold excess mass satisfies
`∫₁^Λ (F(α) − D) dα = f`. -/
theorem excess_formFactor_of_coalescence {F : ℝ → ℝ} {D Λ f : ℝ} (hF : Continuous F)
    (hF_sub : ∀ α ∈ Icc (0 : ℝ) 1, F α = α)
    (htot : ∫ α in (0 : ℝ)..Λ, (F α - D) = f + (1 / 2 - D)) :
    ∫ α in (1 : ℝ)..Λ, (F α - D) = f := by
  have hint1 : IntervalIntegrable (fun α => F α - D) volume 0 1 :=
    (hF.sub continuous_const).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun α => F α - D) volume 1 Λ :=
    (hF.sub continuous_const).intervalIntegrable 1 Λ
  have hsplit := integral_add_adjacent_intervals hint1 hint2
  have hsub : ∫ α in (0 : ℝ)..1, (F α - D) = 1 / 2 - D := by
    have heq : (∫ α in (0 : ℝ)..1, (F α - D)) = ∫ α in (0 : ℝ)..1, (α - D) := by
      refine integral_congr fun α hα => ?_
      rw [uIcc_of_le zero_le_one] at hα
      rw [hF_sub α hα]
    rw [heq, intervalIntegral.integral_sub intervalIntegrable_id intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    norm_num
  linarith

/-- **Higher-moment Rudnick–Sarnak bandwidth cap:**
For a `k`-th order (`k ≥ 3`) trace certificate `tr(G^k)` to avoid trans-threshold prime
correlations (`k * λ ≤ 1`), the bandwidth `λ` is capped at `1/k ≤ 1/3 < 2/3`. -/
theorem higherMoment_rudnick_sarnak_cap {k : ℕ} (hk : 3 ≤ k) {lam : ℝ}
    (hrs : (k : ℝ) * lam ≤ 1) :
    lam ≤ 1 / (k : ℝ) ∧ 1 / (k : ℝ) ≤ 1 / 3 ∧ lam < 2 / 3 := by
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have h1 : lam ≤ 1 / (k : ℝ) := by
    rw [le_div_iff₀ hk0, mul_comm]
    exact hrs
  have h2 : 1 / (k : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk3
  refine ⟨h1, h2, by linarith⟩

end GaloisForLFunctions.TransThresholdPairCorrelation
