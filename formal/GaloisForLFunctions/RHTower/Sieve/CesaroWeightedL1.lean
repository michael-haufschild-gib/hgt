import GaloisForLFunctions.RHTower.Sieve.CesaroLogWeightL1

/-!
# The Cesàro kernel as its own Cauchy–Schwarz weight

Pairing `‖L‖` with the kernel `x^σ/‖s‖²` and applying Cauchy–Schwarz *against the kernel* rather than
against `1` replaces the range length `2T` by the kernel mass `x^σπ/σ`:

`∫_{|t| ≤ T} ‖L(g,σ+it)·x^s/s²‖ dt ≤ x^σ·√(πQ/σ³)`   whenever `∫_{|t| ≤ T}‖L(g,σ+it)‖² ≤ Q`.

Against the unweighted form `(x^σ/σ²)√(2TQ)` this is better for every `T > π/2`, and it does not grow
with the height at all beyond the growth of `Q` itself.  With the affine mean square
`Q = Q₁ + Q₀T` and `|f| ≤ 1` truncated at `N`, the analytic term of the Cesàro chain is
`≍ x^σ√(log N + T)`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The Cesàro vertical integral from a mean square.**  Cauchy–Schwarz against the kernel. -/
theorem integral_symm_norm_cesaro_le_of_meanSquare {g : ℕ → ℂ} {sg : Finset ℕ} (hg0 : 0 ∉ sg)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ sg) {σ x Q T : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hT : 0 ≤ T)
    (hQ : (∫ t in Set.Icc (-T) T, ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ^ 2) ≤ Q) :
    (∫ t in (-T)..T,
        ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖)
      ≤ x ^ σ * Real.sqrt (Real.pi * Q / σ ^ 3) := by
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  have hTle : -T ≤ T := by linarith
  set G : ℝ → ℝ := fun t => ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ with hG
  set w : ℝ → ℝ := fun t => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 with hw
  have hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hg0 hgsupp σ
  have hGc : Continuous G := hgc.norm
  have hwc : Continuous w := by
    have hKeq : w = fun t : ℝ => x ^ σ * (1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) := by
      funext t
      rw [hw, mul_one_div]
    rw [hKeq]
    exact continuous_const.mul (continuous_inv_normSq_line hσ)
  have hwnn : ∀ t : ℝ, 0 ≤ w t := fun t => by
    rw [hw]
    exact div_nonneg hxσ.le (by positivity)
  -- the kernel mass
  have hmassIcc : (∫ t in Set.Icc (-T) T, w t) ≤ x ^ σ * (Real.pi / σ) := by
    have hbridge : (∫ t in Set.Icc (-T) T, w t) = ∫ t in (-T)..T, w t := by
      rw [intervalIntegral.integral_of_le hTle, MeasureTheory.integral_Icc_eq_integral_Ioc]
    have hconst : (∫ t in (-T)..T, w t)
        = x ^ σ * ∫ t in (-T)..T, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hw, mul_one_div]
    rw [hbridge, hconst]
    exact mul_le_mul_of_nonneg_left (integral_symm_inv_normSq_le hσ T) hxσ.le
  -- the weighted mean square
  have hσle : ∀ t : ℝ, σ ≤ ‖(σ : ℂ) + (t : ℝ) * I‖ := by
    intro t
    have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
    have h := Complex.abs_re_le_norm ((σ : ℂ) + (t : ℝ) * I)
    rw [hre, abs_of_pos hσ] at h
    exact h
  have hwle : ∀ t : ℝ, w t ≤ x ^ σ / σ ^ 2 := by
    intro t
    rw [hw]
    refine div_le_div_of_nonneg_left hxσ.le (by positivity) ?_
    exact pow_le_pow_left₀ hσ.le (hσle t) 2
  have hwms : (∫ t in Set.Icc (-T) T, w t * G t ^ 2) ≤ (x ^ σ / σ ^ 2) * Q := by
    have hpt : ∀ t ∈ Set.Icc (-T) T, w t * G t ^ 2 ≤ (x ^ σ / σ ^ 2) * G t ^ 2 := fun t _ =>
      mul_le_mul_of_nonneg_right (hwle t) (sq_nonneg _)
    have hstep := setIntegral_mono_on
      ((hwc.mul (hGc.pow 2)).integrableOn_Icc (μ := volume) (a := -T) (b := T))
      ((continuous_const.mul (hGc.pow 2)).integrableOn_Icc (μ := volume) (a := -T) (b := T))
      measurableSet_Icc hpt
    simp only [Pi.mul_apply, Pi.pow_apply] at hstep
    rw [MeasureTheory.integral_const_mul] at hstep
    have hmul := mul_le_mul_of_nonneg_left hQ (by positivity : (0 : ℝ) ≤ x ^ σ / σ ^ 2)
    linarith [hstep, hmul]
  -- Cauchy-Schwarz against the kernel
  have hCS := GaloisForLFunctions.HTGeometry.sq_integral_weighted_le
    (μ := volume.restrict (Set.Icc (-T) T)) (w := w) (g := G) hwnn
    hwc.aestronglyMeasurable hGc.aestronglyMeasurable (hwc.integrableOn_Icc)
    ((hwc.mul (hGc.pow 2)).integrableOn_Icc)
  have hprod : (∫ t in Set.Icc (-T) T, w t * G t) ^ 2
      ≤ (x ^ σ * (Real.pi / σ)) * ((x ^ σ / σ ^ 2) * Q) := by
    refine le_trans hCS ?_
    have hQ0 : (0 : ℝ) ≤ (∫ t in Set.Icc (-T) T, w t * G t ^ 2) :=
      setIntegral_nonneg measurableSet_Icc fun t _ => mul_nonneg (hwnn t) (sq_nonneg _)
    have hm0 : (0 : ℝ) ≤ ∫ t in Set.Icc (-T) T, w t :=
      setIntegral_nonneg measurableSet_Icc fun t _ => hwnn t
    have h1 : (∫ t in Set.Icc (-T) T, w t) * (∫ t in Set.Icc (-T) T, w t * G t ^ 2)
        ≤ (x ^ σ * (Real.pi / σ)) * (∫ t in Set.Icc (-T) T, w t * G t ^ 2) :=
      mul_le_mul_of_nonneg_right hmassIcc hQ0
    have h2 : (x ^ σ * (Real.pi / σ)) * (∫ t in Set.Icc (-T) T, w t * G t ^ 2)
        ≤ (x ^ σ * (Real.pi / σ)) * ((x ^ σ / σ ^ 2) * Q) :=
      mul_le_mul_of_nonneg_left hwms (by positivity)
    linarith
  have hval : (x ^ σ * (Real.pi / σ)) * ((x ^ σ / σ ^ 2) * Q)
      = (x ^ σ * Real.sqrt (Real.pi * Q / σ ^ 3)) ^ 2 := by
    have hQnn : (0 : ℝ) ≤ Real.pi * Q / σ ^ 3 := by
      have hQ0 : (0 : ℝ) ≤ Q := by
        refine le_trans (setIntegral_nonneg measurableSet_Icc fun t _ => sq_nonneg _) hQ
      positivity
    rw [mul_pow, Real.sq_sqrt hQnn]
    field_simp
  have hint0 : (0 : ℝ) ≤ ∫ t in Set.Icc (-T) T, w t * G t :=
    setIntegral_nonneg measurableSet_Icc fun t _ => mul_nonneg (hwnn t) (norm_nonneg _)
  have hfinal : (∫ t in Set.Icc (-T) T, w t * G t) ≤ x ^ σ * Real.sqrt (Real.pi * Q / σ ^ 3) := by
    rw [hval] at hprod
    have hrhs : (0 : ℝ) ≤ x ^ σ * Real.sqrt (Real.pi * Q / σ ^ 3) := by positivity
    nlinarith [hprod, hint0, hrhs]
  have hgoal : (∫ t in (-T)..T,
        ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖)
      = ∫ t in Set.Icc (-T) T, w t * G t := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ => G t * w t)
      (fun t _ => norm_cesaro_integrand hx _ σ t)]
    rw [intervalIntegral.integral_of_le hTle, MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    exact mul_comm (G t) (w t)
  rw [hgoal]
  exact hfinal

/-- **The mean square of a bounded truncated Dirichlet series, explicitly.** -/
theorem integral_Icc_normSq_LSeries_truncSeq_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (N : ℕ) {σ : ℝ}
    (hσ : 1 ≤ σ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ y in Set.Icc (-T) T, ‖LSeries (truncSeq f N) ((σ : ℂ) + (y : ℝ) * I)‖ ^ 2)
      ≤ 5 * Real.pi * Real.exp 1 * (1 + Real.log N) + 5 * Real.pi * T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, truncSeq f N n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => truncSeq_support h
  have hms := integral_Icc_normSq_LSeries_le_general_affine hs0 hsupp σ hT
  have hC := generalMeanSquareConst_truncSeq_le hf N hσ
  have hR := generalMeanSquareRate_truncSeq_le hf N hσ
  have hRT : generalMeanSquareRate (truncSeq f N) (Finset.Icc 1 N) σ * T ≤ 5 * Real.pi * T :=
    mul_le_mul_of_nonneg_right hR hT0.le
  linarith

/-- **The Cesàro chain with the kernel-weighted first moment.**  The kernel mass `π/σ` replaces the
range length `2T`, so the analytic term is `≍ x^σ√(log N + T)` with no factor `√T` in front. -/
theorem norm_sum_Icc_mul_log_div_le_cesaro_meanSquare {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) {σ T x : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hxN : (N : ℝ) ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 N, truncSeq f N n * ((Real.log (x / n) : ℝ) : ℂ)‖
      ≤ (∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
        + (1 / (2 * Real.pi))
          * (x ^ σ * Real.sqrt (Real.pi
              * (5 * Real.pi * Real.exp 1 * (1 + Real.log N) + 5 * Real.pi * T) / σ ^ 3)) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < x := by linarith
  have hTle : -T ≤ T := by linarith
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 N := by simp
  have hsupp : ∀ n : ℕ, truncSeq f N n ≠ 0 → n ∈ Finset.Icc 1 N := fun _ h => truncSeq_support h
  have hQ := integral_Icc_normSq_LSeries_truncSeq_le hbdd N hσ1 hT
  have hker := integral_symm_norm_cesaro_le_of_meanSquare hs0 hsupp hσ0 hx hT0.le hQ
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t : ℝ => LSeries (truncSeq f N) ((σ : ℂ) + (t : ℝ) * I)
      * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)) hTle
  exact norm_sum_Icc_mul_log_div_le_cesaro_of_integral hbdd hN hσ1 hσ2 hT hxN
    (le_trans hnorm hker)

end RHTower.Sieve
end
