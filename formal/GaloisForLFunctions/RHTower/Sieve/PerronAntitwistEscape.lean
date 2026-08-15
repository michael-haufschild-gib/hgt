import GaloisForLFunctions.RHTower.Sieve.PerronVerticalTripleBound
import GaloisForLFunctions.HTGeometry.PuncturedMajorantIntegral

/-!
# The antitwist cell of a twisted Perron integral

Twisting a multiplicative function by `n^{-iτ}` moves its trivial frequency from `0` to `-τ`.  All but a
bounded window of the Perron range therefore stays at the twisted distance, and only the unit window
around the antitwist centre `c` has to be charged the trivial Euler size.  Since the Perron kernel there
is `x^σ/‖σ+ic‖ ≤ x^σ/(|c|−1)` and the window has length two, the excess costs exactly

```text
2·V_A·V_B·V_triv·x^σ/(|c|−1),
```

so the whole triple integral is the ordinary damped bound plus an escape term of order `1/|c|`.  This is
the exact mechanism by which the frequency of the twist, and not the distance of the untwisted function,
governs the antitwist cell.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The symmetric triple Perron integral with a constant third-factor size.**  The third factor enters
only through the constant `V`; the two outer factors through their affine mean squares. -/
theorem integral_symm_norm_prod_const_kernel_affine_le {A B : ℕ → ℂ} {sA sB : Finset ℕ}
    (hA0 : 0 ∉ sA) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hB0 : 0 ∉ sB) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    {σ x t₀ V QA κA QB κB : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hQA : 0 ≤ QA) (hκA : 0 ≤ κA) (hQB : 0 ≤ QB) (hκB : 0 ≤ κB)
    (hmsA : ∀ U : ℝ, 1 ≤ U →
      (∫ y in Set.Icc (-U) U, ‖LSeries A ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2) ≤ QA + κA * U)
    (hmsB : ∀ U : ℝ, 1 ≤ U →
      (∫ y in Set.Icc (-U) U, ‖LSeries B ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2) ≤ QB + κB * U)
    (M : ℕ) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        (‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ * ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖)
          * (V * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)))
      ≤ 2 * perronVerticalAffineProductBound σ x t₀ V QA κA QB κB M
          + (V * x ^ σ / σ) * (Real.sqrt (QA + κA * t₀) * Real.sqrt (QB + κB * t₀)) := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hAc : Continuous fun t : ℝ => LSeries A ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hA0 hAsupp σ
  have hBc : Continuous fun t : ℝ => LSeries B ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hB0 hBsupp σ
  set FA : ℝ → ℂ := fun t => LSeries A ((σ : ℂ) + (t : ℝ) * I) with hFA
  set FB : ℝ → ℂ := fun t => LSeries B ((σ : ℂ) + (t : ℝ) * I) with hFB
  set G : ℝ → ℝ := fun t => V * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖) with hG
  have hGc : Continuous G := continuous_const.mul (continuous_perron_kernel_norm hσ)
  have hFprod : Continuous fun t : ℝ => ‖FA t‖ * ‖FB t‖ := hAc.norm.mul hBc.norm
  have hGle : ∀ t : ℝ, 0 < t → G t ≤ V * x ^ σ / t := by
    intro t ht
    calc G t ≤ V * (x ^ σ / t) :=
          mul_le_mul_of_nonneg_left (perron_kernel_norm_le hx ht) hV
      _ = V * x ^ σ / t := by ring
  have hGleneg : ∀ t : ℝ, 0 < t → G (-t) ≤ V * x ^ σ / t := by
    intro t ht
    have hker : x ^ σ / ‖(σ : ℂ) + ((-t : ℝ) : ℂ) * I‖ ≤ x ^ σ / t := by
      rw [perron_kernel_norm_neg x σ t]
      exact perron_kernel_norm_le hx ht
    calc G (-t) ≤ V * (x ^ σ / t) := mul_le_mul_of_nonneg_left hker hV
      _ = V * x ^ σ / t := by ring
  have hpos : (∫ t in t₀..(t₀ * 2 ^ M), (‖FA t‖ * ‖FB t‖) * G t)
      ≤ perronVerticalAffineProductBound σ x t₀ V QA κA QB κB M := by
    rw [perronVerticalAffineProductBound]
    exact GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_mul_kernel_le hAc hBc hGc
      hQA hκA hQB hκB (by positivity) ht₀0
      (fun U hU => hmsA U (by linarith)) (fun U hU => hmsB U (by linarith)) M
      (fun t ht _ => hGle t (by linarith))
  have hneg : (∫ t in t₀..(t₀ * 2 ^ M), (‖FA (-t)‖ * ‖FB (-t)‖) * G (-t))
      ≤ perronVerticalAffineProductBound σ x t₀ V QA κA QB κB M := by
    rw [perronVerticalAffineProductBound]
    refine GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_mul_kernel_le
      (A := fun t => FA (-t)) (B := fun t => FB (-t)) (G := fun t => G (-t))
      (hAc.comp continuous_neg) (hBc.comp continuous_neg) (hGc.comp continuous_neg)
      hQA hκA hQB hκB (by positivity) ht₀0 (fun U hU => ?_) (fun U hU => ?_) M
      (fun t ht _ => hGleneg t (by linarith))
    · rw [GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg FA (by linarith)]
      exact hmsA U (by linarith)
    · rw [GaloisForLFunctions.HTGeometry.integral_Icc_normSq_comp_neg FB (by linarith)]
      exact hmsB U (by linarith)
  have hlow : (∫ t in (-t₀)..t₀, (‖FA t‖ * ‖FB t‖) * G t)
      ≤ (V * x ^ σ / σ) * (Real.sqrt (QA + κA * t₀) * Real.sqrt (QB + κB * t₀)) := by
    refine GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_low_le hAc hBc hGc
      (by positivity) ht₀0 (fun t _ => ?_) (hmsA t₀ ht₀) (hmsB t₀ ht₀)
    calc G t ≤ V * (x ^ σ / σ) :=
          mul_le_mul_of_nonneg_left (perron_kernel_norm_le_const hx hσ t) hV
      _ = V * x ^ σ / σ := by ring
  exact GaloisForLFunctions.HTGeometry.integral_symm_le_of_flanks hFprod hGc hpos hneg hlow

/-- The Perron kernel is small on the unit window around a distant centre. -/
theorem perron_kernel_norm_le_of_near_center {x σ c t : ℝ} (hx : 0 < x) (hc : 1 < |c|)
    (ht : |t - c| ≤ 1) : x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ≤ x ^ σ / (|c| - 1) := by
  have hcpos : (0 : ℝ) < |c| - 1 := by linarith
  refine div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le σ) hcpos ?_
  have habs : |c| - 1 ≤ |t| := by
    have h1 : |c| ≤ |t| + |c - t| := by
      have := abs_sub_abs_le_abs_sub c t
      linarith [abs_nonneg (c - t)]
    have h2 : |c - t| = |t - c| := abs_sub_comm c t
    linarith [ht, h1, h2.le, h2.ge]
  have him : ((σ : ℂ) + (t : ℝ) * I).im = t := by simp
  calc |c| - 1 ≤ |t| := habs
    _ = |((σ : ℂ) + (t : ℝ) * I).im| := by rw [him]
    _ ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ := Complex.abs_im_le_norm _

/-- **The triple Perron integral with one antitwist cell.**  The third factor is charged its damped size
`V` outside the unit window around `c` and only its trivial size `V_triv` inside; the two outer factors
are charged their pointwise sizes on that window.  The excess is the escape term `2V_AV_Bx^σ/(|c|−1)`. -/
theorem integral_symm_norm_perron_triple_punctured_affine_le {A B f : ℕ → ℂ} {sA sB : Finset ℕ}
    (hA0 : 0 ∉ sA) (hAsupp : ∀ n : ℕ, A n ≠ 0 → n ∈ sA)
    (hB0 : 0 ∉ sB) (hBsupp : ∀ n : ℕ, B n ≠ 0 → n ∈ sB)
    {σ x t₀ V Vtr VA VB QA κA QB κB c : ℝ} (hσ : 0 < σ) (hx : 0 < x) (ht₀ : 1 ≤ t₀) (hV : 0 ≤ V)
    (hVtr : 0 ≤ Vtr) (hVA : 0 ≤ VA) (hVB : 0 ≤ VB)
    (hQA : 0 ≤ QA) (hκA : 0 ≤ κA) (hQB : 0 ≤ QB) (hκB : 0 ≤ κB)
    (hFc : Continuous fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℝ) * I))
    (hmsA : ∀ U : ℝ, 1 ≤ U →
      (∫ y in Set.Icc (-U) U, ‖LSeries A ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2) ≤ QA + κA * U)
    (hmsB : ∀ U : ℝ, 1 ≤ U →
      (∫ y in Set.Icc (-U) U, ‖LSeries B ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2) ≤ QB + κB * U)
    (M : ℕ) (hc : 1 < |c|)
    (hFbound : ∀ t : ℝ, |t| ≤ t₀ * 2 ^ M → 1 ≤ |t - c| →
      ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V)
    (hFtriv : ∀ t : ℝ, ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ Vtr)
    (hAb : ∀ t : ℝ, ‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VA)
    (hBb : ∀ t : ℝ, ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VB) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M),
        ‖LSeries A ((σ : ℂ) + (t : ℝ) * I) * LSeries B ((σ : ℂ) + (t : ℝ) * I)
            * LSeries f ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I))‖)
      ≤ (2 * perronVerticalAffineProductBound σ x t₀ V QA κA QB κB M
            + (V * x ^ σ / σ) * (Real.sqrt (QA + κA * t₀) * Real.sqrt (QB + κB * t₀)))
          + 2 * (VA * VB * (Vtr * (x ^ σ / (|c| - 1)))) := by
  have ht₀0 : (0 : ℝ) < t₀ := by linarith
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hcpos : (0 : ℝ) < |c| - 1 := by linarith
  have hAc : Continuous fun t : ℝ => LSeries A ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hA0 hAsupp σ
  have hBc : Continuous fun t : ℝ => LSeries B ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hB0 hBsupp σ
  have hker : Continuous fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ :=
    continuous_perron_kernel_norm hσ
  have hT : (0 : ℝ) ≤ t₀ * 2 ^ M := by positivity
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      (‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ * ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖)
        * (‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)))
    (fun t _ => norm_perron_triple_integrand hx _ _ _ σ t)]
  have hmajor := GaloisForLFunctions.HTGeometry.intervalIntegral_le_of_punctured_majorant
    (Φ := fun t : ℝ =>
      (‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ * ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖)
        * (‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)))
    (Φ₁ := fun t : ℝ =>
      (‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ * ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖)
        * (V * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)))
    (T := t₀ * 2 ^ M) (c := c) (K := VA * VB * (Vtr * (x ^ σ / (|c| - 1))))
    ((hAc.norm.mul hBc.norm).mul (hFc.norm.mul hker))
    ((hAc.norm.mul hBc.norm).mul (continuous_const.mul hker)) hT
    (fun t => by positivity) (by positivity) (fun t ht hout => ?_) (fun t ht hin => ?_)
  · refine le_trans hmajor ?_
    have hconst := integral_symm_norm_prod_const_kernel_affine_le hA0 hAsupp hB0 hBsupp hσ hx ht₀
      hV hQA hκA hQB hκB hmsA hmsB M
    linarith [hconst]
  · exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hFbound t ht hout) (by positivity)) (by positivity)
  · have hA' : ‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VA := hAb t
    have hB' : ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖ ≤ VB := hBb t
    have hf' : ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ ≤ Vtr := hFtriv t
    have hk' : x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ≤ x ^ σ / (|c| - 1) :=
      perron_kernel_norm_le_of_near_center hx hc hin
    have h1 : ‖LSeries A ((σ : ℂ) + (t : ℝ) * I)‖ * ‖LSeries B ((σ : ℂ) + (t : ℝ) * I)‖
        ≤ VA * VB := mul_le_mul hA' hB' (norm_nonneg _) hVA
    have h2 : ‖LSeries f ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖)
        ≤ Vtr * (x ^ σ / (|c| - 1)) := mul_le_mul hf' hk' (by positivity) hVtr
    exact mul_le_mul h1 h2 (by positivity) (by positivity)

end RHTower.Sieve
end
