import GaloisForLFunctions.RHTower.DeepOffLineZerosAreCountedByTheHeatFlow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Heat-count growth and the density of deep zeros

The persistence time `δ²/(C log⁴ X)` transfers an exponential heat-count
envelope to a stretched exponential in `log X`. Exponents below `1/4`
therefore give `X^{o(1)}` deep-zero counts, uniformly over finite sets of
multiplicity copies. These are implications between growth laws; no
small-time bound on the heat count is asserted here.
-/

open Filter Topology

namespace RHTower.DeBruijn

noncomputable section

/-- At heat time proportional to `log⁻⁴ X`, persistence bounds every finite deep-zero window.
The selected time eventually lies below any prescribed positive time. -/
theorem exists_deep_window_bound_at_logarithmic_heat {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ t₀ : ℝ, 0 < t₀ → ∀ᶠ X : ℝ in atTop,
      1 ≤ Real.log X ∧
      0 < δ ^ 2 / (C * Real.log X ^ 4) ∧
      δ ^ 2 / (C * Real.log X ^ 4) ≤ t₀ ∧
      ∀ F : Finset XiZeroCopy,
        (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
          δ ≤ |(q.1 : ℂ).re - 1 / 2|) →
        (F.card : ℝ) ≤ C * Real.log X *
          nonrealZeroCount (δ ^ 2 / (C * Real.log X ^ 4)) := by
  obtain ⟨C, hC, X₀, hbound⟩ := exists_card_deep_le_mul_nonrealZeroCount hδ hδ2
  refine ⟨C, hC, ?_⟩
  intro t₀ ht₀
  let B : ℝ := max 1 (δ ^ 2 / (C * t₀))
  filter_upwards [eventually_ge_atTop X₀, eventually_ge_atTop (Real.exp B)] with X hX hXB
  have hBL : B ≤ Real.log X := by
    rw [← Real.log_exp B]
    exact Real.log_le_log (Real.exp_pos B) hXB
  have hL1 : 1 ≤ Real.log X := (le_max_left _ _).trans hBL
  have hL0 : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL1
  have ht : 0 < δ ^ 2 / (C * Real.log X ^ 4) := by positivity
  have hL4 : Real.log X ≤ Real.log X ^ 4 := by
    have h3 : 1 ≤ Real.log X ^ 3 := one_le_pow₀ hL1
    nlinarith only [mul_nonneg hL0.le (sub_nonneg.mpr h3)]
  have hsmall : δ ^ 2 / (C * Real.log X ^ 4) ≤ t₀ := by
    have hq : δ ^ 2 / (C * t₀) ≤ Real.log X ^ 4 :=
      ((le_max_right _ _).trans hBL).trans hL4
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hq
    nlinarith only [hq]
  exact ⟨hL1, ht, hsmall, hbound X hX _ ht le_rfl⟩

private theorem logarithmic_heat_rpow_neg {δ C X : ℝ}
    (hδ : 0 < δ) (hC : 0 < C) (hX : 0 < Real.log X) (a : ℝ) :
    (δ ^ 2 / (C * Real.log X ^ 4)) ^ (-a) =
      (C / δ ^ 2) ^ a * Real.log X ^ (4 * a) := by
  rw [Real.rpow_neg (by positivity), Real.div_rpow (by positivity) (by positivity),
    inv_div, Real.mul_rpow (by positivity) (by positivity),
    Real.div_rpow (by positivity) (by positivity)]
  have h4 : (Real.log X ^ 4 : ℝ) ^ a = Real.log X ^ (4 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
    norm_num
  rw [h4]
  field_simp

/-- An exponential heat-count envelope transfers to a stretched exponential in `log X`,
with exponent multiplied by four and only the persistence factor `log X` lost. -/
theorem stretchedExponential_deep_density_of_nonrealZeroCount
    {A a t₀ : ℝ} (hA : 0 ≤ A) (ht₀ : 0 < t₀)
    (hN : ∀ t : ℝ, 0 < t → t ≤ t₀ →
      (nonrealZeroCount t : ℝ) ≤ Real.exp (A * t ^ (-a)))
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∃ C K : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ F : Finset XiZeroCopy,
        (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
          δ ≤ |(q.1 : ℂ).re - 1 / 2|) →
        (F.card : ℝ) ≤ C * Real.log X * Real.exp (K * Real.log X ^ (4 * a)) := by
  obtain ⟨C, hC, htime⟩ := exists_deep_window_bound_at_logarithmic_heat hδ hδ2
  refine ⟨C, A * (C / δ ^ 2) ^ a, hC, by positivity, ?_⟩
  filter_upwards [htime t₀ ht₀] with X hX F hF
  obtain ⟨hL1, ht, htt₀, hcount⟩ := hX
  have hL0 : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL1
  calc
    (F.card : ℝ) ≤ C * Real.log X * nonrealZeroCount (δ ^ 2 / (C * Real.log X ^ 4)) :=
      hcount F hF
    _ ≤ C * Real.log X * Real.exp (A * (δ ^ 2 / (C * Real.log X ^ 4)) ^ (-a)) :=
      mul_le_mul_of_nonneg_left (hN _ ht htt₀) (mul_nonneg hC.le hL0.le)
    _ = _ := by rw [logarithmic_heat_rpow_neg hδ hC hL0, ← mul_assoc]

/-- A stretched exponential with exponent below one in `log X` is below every positive power. -/
private theorem eventually_log_mul_exp_rpow_le_rpow {C K b ε : ℝ}
    (hC : 0 ≤ C) (hb : b < 1) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      C * Real.log X * Real.exp (K * Real.log X ^ b) ≤ X ^ ε := by
  have hhalf : 0 < ε / 2 := half_pos hε
  have hratio : Tendsto (fun y : ℝ => K * y ^ (b - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 - b by linarith only [hb])).const_mul K
    simpa only [neg_sub, mul_zero] using h
  have hexponent : ∀ᶠ X : ℝ in atTop,
      K * Real.log X ^ b ≤ (ε / 2) * Real.log X := by
    have hsmall := Real.tendsto_log_atTop.eventually
      (hratio.eventually (gt_mem_nhds hhalf))
    filter_upwards [hsmall, Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
      with X hX hL
    have hmul := mul_le_mul_of_nonneg_right hX.le hL.le
    rw [Real.rpow_sub hL, Real.rpow_one] at hmul
    rwa [mul_assoc, div_mul_cancel₀ _ hL.ne'] at hmul
  have hprefactor : ∀ᶠ X : ℝ in atTop, C * Real.log X ≤ X ^ (ε / 2) := by
    have hsmall := ((isLittleO_log_rpow_atTop hhalf).const_mul_left C).bound (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with X hX hX1
    have hX0 : 0 ≤ X := zero_le_one.trans hX1
    have hL : 0 ≤ Real.log X := Real.log_nonneg hX1
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hL),
      abs_of_nonneg (Real.rpow_nonneg hX0 _), one_mul] using hX
  filter_upwards [hexponent, hprefactor, eventually_gt_atTop (1 : ℝ)] with X hE hP hX
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hL : 0 ≤ Real.log X := Real.log_nonneg hX.le
  have he : Real.exp (K * Real.log X ^ b) ≤ X ^ (ε / 2) := by
    rw [Real.rpow_def_of_pos hX0]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hE)
  calc
    C * Real.log X * Real.exp (K * Real.log X ^ b) ≤
        X ^ (ε / 2) * X ^ (ε / 2) :=
      mul_le_mul hP he (Real.exp_pos _).le (Real.rpow_nonneg hX0.le _)
    _ = X ^ ε := by rw [← Real.rpow_add hX0]; congr 1; ring

/-- Heat-count growth `exp(A t⁻ᵃ)` with `a<1/4` forces `X^{o(1)}` deep-zero density.
For every positive `ε`, the bound `#F≤X^ε` holds eventually, uniformly over finite windows. -/
theorem subpower_deep_density_of_subcritical_nonrealZeroCount
    {A a t₀ : ℝ} (hA : 0 ≤ A) (ha : a < 1 / 4) (ht₀ : 0 < t₀)
    (hN : ∀ t : ℝ, 0 < t → t ≤ t₀ →
      (nonrealZeroCount t : ℝ) ≤ Real.exp (A * t ^ (-a)))
    {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℝ in atTop,
      ∀ F : Finset XiZeroCopy,
        (∀ q ∈ F, X ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * X ∧
          δ ≤ |(q.1 : ℂ).re - 1 / 2|) →
        (F.card : ℝ) ≤ X ^ ε := by
  obtain ⟨C, K, hC, _, hbound⟩ :=
    stretchedExponential_deep_density_of_nonrealZeroCount hA ht₀ hN hδ hδ2
  intro ε hε
  have hsub := eventually_log_mul_exp_rpow_le_rpow (C := C) (K := K) hC.le
    (show 4 * a < 1 by linarith only [ha]) hε
  filter_upwards [hbound, hsub] with X hX hXsub F hF
  exact (hX F hF).trans hXsub

end
end RHTower.DeBruijn

#print axioms RHTower.DeBruijn.exists_deep_window_bound_at_logarithmic_heat
#print axioms RHTower.DeBruijn.stretchedExponential_deep_density_of_nonrealZeroCount
#print axioms RHTower.DeBruijn.subpower_deep_density_of_subcritical_nonrealZeroCount
#print axioms RHTower.DeBruijn.polylog_deep_density_of_polynomial_nonrealZeroCount
