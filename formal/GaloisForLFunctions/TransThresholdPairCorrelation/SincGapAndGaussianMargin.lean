import GaloisForLFunctions.TransThresholdPairCorrelation.PeriodicSincMajorant
import GaloisForLFunctions.HTGeometry.FejerLatticeVanishing

/-!
# Quadratic sinc gaps and Gaussian regularization

The squared sinc leaves a uniform quadratic gap. Adding a narrow positive
Gaussian to such a background absorbs every uniformly bounded perturbation
of order `R⁻²` once the Gaussian concentration parameter `R` is large.
-/

open Real Set
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- The squared sinc has a quadratic gap at the origin and a fixed gap away from it. -/
theorem min_sq_one_le_sinc_gap (t : ℝ) :
    min (t ^ 2) 1 / 12 ≤ 1 - sinc t ^ 2 := by
  wlog ht : 0 ≤ t generalizing t
  · simpa only [neg_sq, sinc_neg] using this (-t) (by linarith)
  rcases le_or_gt t (π / 2) with hsmall | hlarge
  · have hs := Real.mul_le_sin ht hsmall
    have hπ : π < 4 := lt_trans Real.pi_lt_d2 (by norm_num)
    have hconst : (1 : ℝ) / 2 ≤ 2 / π := by
      apply (le_div_iff₀ pi_pos).mpr
      linarith only [hπ]
    have hsin : t / 2 ≤ sin t := by
      have hh := mul_le_mul_of_nonneg_right hconst ht
      linarith only [hh, hs]
    have hsin0 : 0 ≤ sin t := (by positivity : (0 : ℝ) ≤ t / 2).trans hsin
    have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ t / 2) hsin
    have henv := sinc_sq_le_scaled_cos_envelope (b := 1) le_rfl t
    simp only [one_pow, one_mul] at henv
    have hgap : sin t ^ 2 / 3 ≤ 1 - sinc t ^ 2 := by
      nlinarith only [henv, sin_sq_add_cos_sq t, sq_abs (cos t),
        sq_nonneg (|cos t| - 1)]
    nlinarith only [hsq, hgap, min_le_left (t ^ 2) (1 : ℝ)]
  · have htpos : 0 < t := (half_pos pi_pos).trans hlarge
    have htne : t ≠ 0 := htpos.ne'
    have hsin := abs_sin_le_one t
    have hsinc : sinc t ^ 2 * t ^ 2 ≤ 1 := by
      rw [sinc_of_ne_zero htne, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ htne)]
      exact (sq_le_one_iff_abs_le_one _).mpr hsin
    have htlarge : (3 : ℝ) / 2 < t := by linarith only [hlarge, pi_gt_three]
    have ht2 : 9 / 4 ≤ t ^ 2 := by nlinarith only [htlarge]
    have hprod := mul_le_mul_of_nonneg_left ht2 (sq_nonneg (sinc t))
    nlinarith only [hsinc, hprod, min_le_right (t ^ 2) (1 : ℝ)]

/-- Dilation retains an explicit positive quadratic gap. -/
theorem scaled_sinc_gap (a x : ℝ) :
    min (a ^ 2) 1 / 12 * min (x ^ 2) 1 ≤ 1 - sinc (a * x) ^ 2 := by
  have hnonnega : 0 ≤ min (a ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
  have hnonnegx : 0 ≤ min (x ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
  have hsq : min (a ^ 2) 1 * min (x ^ 2) 1 ≤ (a * x) ^ 2 := by
    have h := mul_le_mul (min_le_left (a ^ 2) (1 : ℝ))
      (min_le_left (x ^ 2) (1 : ℝ)) hnonnegx (sq_nonneg a)
    nlinarith only [h]
  have hone : min (a ^ 2) 1 * min (x ^ 2) 1 ≤ 1 := by
    have h := mul_le_mul (min_le_right (a ^ 2) (1 : ℝ))
      (min_le_right (x ^ 2) (1 : ℝ)) hnonnegx zero_le_one
    simpa only [one_mul] using h
  have hmin := le_min hsq hone
  have hgap := min_sq_one_le_sinc_gap (a * x)
  nlinarith only [hmin, hgap]

/-- A narrow positive Gaussian fills the quadratic zero of a nonnegative background.
Any uniform perturbation of order `R⁻²` is absorbed for sufficiently large `R`. -/
theorem eventually_gaussian_fills_quadratic_gap {c a b C : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hb : 0 ≤ b) (hC : 0 ≤ C) :
    ∀ᶠ R : ℝ in Filter.atTop, 0 < R ∧ ∀ x : ℝ,
      C / R ^ 2 ≤ c * min (x ^ 2) 1 + a * R * exp (-b * (R * x) ^ 2) := by
  let D : ℝ := C / c + 1
  have hD1 : 1 ≤ D := by
    dsimp only [D]
    linarith only [div_nonneg hC hc.le]
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hCD : C ≤ c * D ^ 2 := by
    have hDc : c * D = C + c := by dsimp only [D]; field_simp
    have hDsq : D ≤ D ^ 2 := by nlinarith only [hD1]
    have hmul := mul_le_mul_of_nonneg_left hDsq hc.le
    linarith only [hDc, hmul, hc]
  let K : ℝ := a * exp (-b * D ^ 2)
  have hK : 0 < K := mul_pos ha (exp_pos _)
  filter_upwards [Filter.eventually_ge_atTop (max D (C / K))] with R hR
  have hRD : D ≤ R := (le_max_left _ _).trans hR
  have hRC : C / K ≤ R := (le_max_right _ _).trans hR
  have hR1 : 1 ≤ R := hD1.trans hRD
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR0
  refine ⟨hR0, fun x => ?_⟩
  have hbg : 0 ≤ c * min (x ^ 2) 1 := mul_nonneg hc.le (le_min (sq_nonneg _) zero_le_one)
  have hgauss : 0 ≤ a * R * exp (-b * (R * x) ^ 2) := by positivity
  rcases le_or_gt |R * x| D with hnear | hfar
  · have hsq : (R * x) ^ 2 ≤ D ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg _) hnear
      simpa only [sq_abs, ← pow_two] using h
    have hexp : exp (-b * D ^ 2) ≤ exp (-b * (R * x) ^ 2) := by
      apply exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hsq hb]
    have hCR : C ≤ K * R := by
      have h := (div_le_iff₀ hK).mp hRC
      simpa only [mul_comm] using h
    have hprod := mul_le_mul_of_nonneg_left hexp (mul_nonneg ha.le hR0.le)
    have hCbound : C / R ^ 2 ≤ C := by
      apply (div_le_iff₀ hR2).mpr
      have hsq1 : 1 ≤ R ^ 2 := by nlinarith only [hR1]
      nlinarith only [mul_le_mul_of_nonneg_left hsq1 hC]
    dsimp only [K] at hCR
    nlinarith only [hCR, hprod, hbg, hCbound]
  · have hDx : D ^ 2 ≤ R ^ 2 * x ^ 2 := by
      have h := mul_self_le_mul_self hD0.le hfar.le
      simpa only [sq_abs, ← pow_two, mul_pow] using h
    have hDR : D ^ 2 ≤ R ^ 2 := by
      nlinarith only [mul_self_le_mul_self hD0.le hRD]
    have hmin : D ^ 2 / R ^ 2 ≤ min (x ^ 2) 1 := by
      apply le_min
      · exact (div_le_iff₀ hR2).mpr (by simpa only [mul_comm] using hDx)
      · exact (div_le_one hR2).mpr hDR
    have hmul := mul_le_mul_of_nonneg_left hmin hc.le
    have hdiv := div_le_div_of_nonneg_right hCD hR2.le
    calc
      C / R ^ 2 ≤ c * D ^ 2 / R ^ 2 := hdiv
      _ = c * (D ^ 2 / R ^ 2) := by ring
      _ ≤ c * min (x ^ 2) 1 := hmul
      _ ≤ _ := le_add_of_nonneg_right hgauss

end GaloisForLFunctions.TransThresholdPairCorrelation
