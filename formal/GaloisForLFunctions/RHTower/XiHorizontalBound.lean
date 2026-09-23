import GaloisForLFunctions.RHTower.ZetaRealTraceSignChanges
import GaloisForLFunctions.RHTower.XiLogDerivFactorization

/-!
# The horizontal side of the rectangle is `O(log T)`

On the segment `[1/2, 2]` at height `T` the four-factor splitting of `ξ'/ξ` has three elementary
imaginary parts — two Cauchy kernels bounded by `1/T` and a digamma whose imaginary part the
vertical sandwich pins between `0` and `π + 2/T` — and one arithmetic part, the argument increment
of `ζ`, which Backlund bounds by `O(log T)`.  Hence the whole horizontal contribution is `O(log T)`.
-/

open Complex Set MeasureTheory intervalIntegral
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The digamma bound -/

theorem im_digamma_vertical_nonneg_le {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t) :
    0 ≤ (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im ∧
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im ≤ Real.pi + 1 / t := by
  obtain ⟨hlow, hhigh⟩ := im_digamma_vertical_sandwich hσ ht
  have h1 := Real.arctan_lt_pi_div_two (σ / t)
  have h2 := Real.neg_pi_div_two_lt_arctan (σ / t)
  constructor <;> linarith

/-! ## The pointwise splitting on the horizontal segment -/

theorem im_logDeriv_xi_horizontal {x T : ℝ} (hT : 0 < T)
    (hζ : riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im
      = -T / (x ^ (2 : ℕ) + T ^ (2 : ℕ)) + -T / ((x - 1) ^ (2 : ℕ) + T ^ (2 : ℕ))
        + (Complex.digamma (((x / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im / 2
        + (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im := by
  set s : ℂ := (x : ℂ) + (T : ℂ) * I with hs
  have him : s.im = T := by simp [hs]
  have hre : s.re = x := by simp [hs]
  have hsim : s.im ≠ 0 := by rw [him]; linarith
  have hhalf : s / 2 = ((x / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I := by
    rw [hs]
    push_cast
    ring
  have hdiv2 : ∀ z : ℂ, (z / 2).im = z.im / 2 := by
    intro z
    simp
  have hinv1 : ((1 : ℂ) / s).im = -T / (x ^ (2 : ℕ) + T ^ (2 : ℕ)) := by
    rw [one_div, Complex.inv_im, Complex.normSq_apply, hre, him]
    ring
  have hinv2 : ((1 : ℂ) / (s - 1)).im = -T / ((x - 1) ^ (2 : ℕ) + T ^ (2 : ℕ)) := by
    have hsub : (s - 1).re = x - 1 := by rw [Complex.sub_re, hre]; norm_num
    have hsubim : (s - 1).im = T := by rw [Complex.sub_im, him]; norm_num
    rw [one_div, Complex.inv_im, Complex.normSq_apply, hsub, hsubim]
    ring
  rw [logDeriv_xi_fourFactor_offReal hsim hζ, hhalf]
  simp only [Complex.add_im, Complex.sub_im, hdiv2, Complex.ofReal_im]
  rw [hinv1, hinv2]
  ring

/-! ## The bound -/

theorem abs_im_logDeriv_xi_horizontal_le {x T : ℝ} (hT : 4 ≤ T) (hx : x ∈ Icc (1 / 2 : ℝ) 2)
    (hζ : riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0) :
    |(logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im
        - (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im|
      ≤ 1 + Real.pi / 2 := by
  have hT0 : (0 : ℝ) < T := by linarith
  rw [im_logDeriv_xi_horizontal hT0 hζ]
  have hx0 : (0 : ℝ) ≤ x := by linarith [hx.1]
  have hdig := im_digamma_vertical_nonneg_le (σ := x / 2) (t := T / 2) (by linarith) (by linarith)
  have hden1 : (0 : ℝ) < x ^ (2 : ℕ) + T ^ (2 : ℕ) := by positivity
  have hden2 : (0 : ℝ) < (x - 1) ^ (2 : ℕ) + T ^ (2 : ℕ) := by positivity
  have hb1 : |(-T) / (x ^ (2 : ℕ) + T ^ (2 : ℕ))| ≤ 1 / 4 := by
    rw [abs_div, abs_neg, abs_of_pos hT0, abs_of_pos hden1, div_le_div_iff₀ hden1 (by norm_num)]
    nlinarith [sq_nonneg x, hT0]
  have hb2 : |(-T) / ((x - 1) ^ (2 : ℕ) + T ^ (2 : ℕ))| ≤ 1 / 4 := by
    rw [abs_div, abs_neg, abs_of_pos hT0, abs_of_pos hden2, div_le_div_iff₀ hden2 (by norm_num)]
    nlinarith [sq_nonneg (x - 1), hT0]
  have hb3 : |(Complex.digamma (((x / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im / 2|
      ≤ Real.pi / 2 + 1 / 4 := by
    rw [abs_div, abs_of_nonneg hdig.1]
    have h2 : (Complex.digamma (((x / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im
        ≤ Real.pi + 1 / (T / 2) := hdig.2
    have hTinv : 1 / (T / 2) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hsimp : -T / (x ^ (2 : ℕ) + T ^ (2 : ℕ)) + -T / ((x - 1) ^ (2 : ℕ) + T ^ (2 : ℕ))
      + (Complex.digamma (((x / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im / 2
      + (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im
      - (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im
      = -T / (x ^ (2 : ℕ) + T ^ (2 : ℕ)) + -T / ((x - 1) ^ (2 : ℕ) + T ^ (2 : ℕ))
        + (Complex.digamma (((x / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im / 2 := by
    ring
  rw [hsimp]
  calc |(-T) / (x ^ (2 : ℕ) + T ^ (2 : ℕ)) + (-T) / ((x - 1) ^ (2 : ℕ) + T ^ (2 : ℕ))
        + (Complex.digamma (((x / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im / 2|
      ≤ |(-T) / (x ^ (2 : ℕ) + T ^ (2 : ℕ)) + (-T) / ((x - 1) ^ (2 : ℕ) + T ^ (2 : ℕ))|
        + |(Complex.digamma (((x / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im / 2| :=
        abs_add_le _ _
    _ ≤ (|(-T) / (x ^ (2 : ℕ) + T ^ (2 : ℕ))| + |(-T) / ((x - 1) ^ (2 : ℕ) + T ^ (2 : ℕ))|)
        + |(Complex.digamma (((x / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I)).im / 2| := by
        gcongr
        exact abs_add_le _ _
    _ ≤ (1 / 4 + 1 / 4) + (Real.pi / 2 + 1 / 4) := by
        exact add_le_add (add_le_add hb1 hb2) hb3
    _ ≤ 1 + Real.pi / 2 := by linarith

/-! ## The integrated horizontal bound -/

/-- **The horizontal side of the rectangle is `O(log T)`.** -/
theorem exists_horizontal_xi_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℝ, 4 ≤ T →
      (∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0) →
      |∫ x in (1 / 2 : ℝ)..2, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im| ≤ c * Real.log T := by
  obtain ⟨c₀, hc₀, hζbound⟩ := exists_horizontal_zeta_bound
  refine ⟨c₀ + 3 * (1 + Real.pi / 2), by positivity, fun T hT hne => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hTne : T ≠ 0 := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  have hζne : ∀ x : ℝ, riemannZeta ((x : ℂ) + (T : ℂ) * I) ≠ 0 :=
    zeta_horizontal_ne_zero hTne hne
  have hcxi : Continuous fun x : ℝ => (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im :=
    Complex.continuous_im.comp (continuous_logDeriv_xi_horizontal hne)
  have hcζ : Continuous fun x : ℝ => (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im :=
    Complex.continuous_im.comp (continuous_logDeriv_zeta_horizontal hTne hζne)
  have hsplit : (∫ x in (1 / 2 : ℝ)..2, (logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im)
      = (∫ x in (1 / 2 : ℝ)..2, ((logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im
          - (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im))
        + ∫ x in (1 / 2 : ℝ)..2, (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im := by
    rw [intervalIntegral.integral_sub (hcxi.intervalIntegrable _ _)
      (hcζ.intervalIntegrable _ _)]
    ring
  have hhead : |∫ x in (1 / 2 : ℝ)..2, ((logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im
      - (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im)| ≤ 3 * (1 + Real.pi / 2) := by
    have hbnd : ∀ x ∈ Set.uIoc (1 / 2 : ℝ) 2,
        ‖(logDeriv xi ((x : ℂ) + (T : ℂ) * I)).im
          - (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * I)).im‖ ≤ 1 + Real.pi / 2 := by
      intro x hx
      rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hx
      rw [Real.norm_eq_abs]
      exact abs_im_logDeriv_xi_horizontal_le hT ⟨hx.1.le, hx.2⟩ (hζne x)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rw [Real.norm_eq_abs] at h
    have harith : (1 + Real.pi / 2) * |2 - 1 / 2| ≤ 3 * (1 + Real.pi / 2) := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2 - 1 / 2)]
      nlinarith [Real.pi_pos]
    linarith [h, harith]
  have htail := hζbound T hT hne
  rw [hsplit]
  refine le_trans (abs_add_le _ _) ?_
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  nlinarith [hhead, htail, hlog1, hπ, hc₀]

end RHTower
