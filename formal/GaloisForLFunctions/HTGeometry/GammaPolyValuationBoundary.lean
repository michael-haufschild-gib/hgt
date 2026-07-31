import GaloisForLFunctions.HTGeometry.GammaSuperPolynomialDecay
import GaloisForLFunctions.HTGeometry.GammaRationalProjectiveBoundary

/-!
# The bigraded valuation ordering on `s`-weighted Gamma-rational coefficients

Equation (26) of the projective-boundary law orders a finite coefficient tuple lexicographically:
smaller Gamma exponent dominates; at equal Gamma exponent, larger power of `s` dominates.  This file
proves that ordering unconditionally for the coefficients `s^a · P(Γ)/Q(Γ)`, the `s`-monomial
weighted part of `ℂ(s)(Γ)`.

The Gamma direction beats the polynomial direction outright: super-polynomial decay gives
`s^n Γ(s)^k → 0` on every vertical line for every `n` and every `k ≥ 1`, so a strictly larger Gamma
valuation forces the normalized ratio to `0` whatever powers of `s` accompany it.  At equal Gamma
valuation the Gamma factors cancel and the comparison is the plain monomial one: the ratio tends to
`0` when the numerator carries the smaller power of `s`, and to the residue quotient when the powers
agree.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

/-! ### Vertical-line norms -/

theorem le_norm_vertical (σ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
  have habs := Complex.abs_im_le_norm ((σ : ℂ) + (t : ℂ) * Complex.I)
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rwa [him, abs_of_nonneg ht] at habs

theorem norm_vertical_le {σ t : ℝ} (hσ : 0 ≤ σ) (ht : 0 ≤ t) :
    ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ σ + t := by
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, Complex.norm_I, mul_one]

/-! ### The Gamma direction dominates every power of `s` -/

/-- **Super-polynomial dominance.**  On a vertical line of positive abscissa, any positive power of
`Γ` annihilates any power of `s`. -/
theorem tendsto_pow_mul_Gamma_pow {σ : ℝ} (hσ : 0 < σ) (n k : ℕ) (hk : 0 < k) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ n *
        (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ k) atTop (nhds 0) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hG0 : 0 ≤ Real.Gamma σ := le_of_lt (Real.Gamma_pos_of_pos hσ)
  have hG1 : 0 ≤ Real.Gamma (σ + (n + 1 : ℕ)) :=
    le_of_lt (Real.Gamma_pos_of_pos (by positivity))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun t : ℝ =>
      ((σ + 1) ^ n * (Real.Gamma σ ^ j * Real.Gamma (σ + (n + 1 : ℕ)))) / t)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have hs : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ≤ (σ + 1) * t := by
      refine (norm_vertical_le hσ.le ht0.le).trans ?_
      nlinarith
    have hEuler : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Real.Gamma σ := by
      have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
      have h := norm_Gamma_le_real_Gamma_re (s := (σ : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; exact hσ)
      rwa [hre] at h
    have hdecay := norm_Gamma_vertical_le_pow hσ (n + 1) ht0
    rw [norm_mul, norm_pow, norm_pow, pow_succ]
    have hA : ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ n ≤ ((σ + 1) * t) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) hs n
    have hB : ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ j ≤ Real.Gamma σ ^ j :=
      pow_le_pow_left₀ (norm_nonneg _) hEuler j
    calc ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ n *
          (‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ j *
            ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖)
        ≤ ((σ + 1) * t) ^ n *
            (Real.Gamma σ ^ j * (Real.Gamma (σ + (n + 1 : ℕ)) / t ^ (n + 1))) := by
          refine mul_le_mul hA (mul_le_mul hB hdecay (norm_nonneg _) (by positivity))
            (by positivity) (by positivity)
      _ = ((σ + 1) ^ n * (Real.Gamma σ ^ j * Real.Gamma (σ + (n + 1 : ℕ)))) / t := by
          rw [mul_pow, pow_succ]
          field_simp
  · exact tendsto_const_nhds.div_atTop tendsto_id

/-- The reciprocal of a positive power of `s` vanishes on a vertical line. -/
theorem tendsto_inv_pow_vertical (σ : ℝ) {d : ℕ} (hd : 0 < d) :
    Tendsto (fun t : ℝ => (((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)⁻¹) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun t : ℝ => t⁻¹)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have hkey : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d := by
      calc t ≤ t ^ d := le_self_pow₀ ht hd.ne'
        _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ d :=
            pow_le_pow_left₀ ht0.le (le_norm_vertical σ ht0.le) d
    rw [norm_inv, norm_pow, inv_le_inv₀ (lt_of_lt_of_le ht0 hkey) ht0]
    exact hkey
  · simpa using tendsto_inv_atTop_zero

/-! ### The ratio of two Gamma-rational data on a vertical line -/

/-- Vertical-line form of the Gamma-rational projective boundary. -/
theorem gammaRationalDatum_ratio_vertical_tendsto (D₁ D₂ : GammaRationalDatum) (n : ℕ)
    (hn : D₁.numOrder + D₂.denOrder = n + (D₂.numOrder + D₁.denOrder))
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
        D₁.fn ((σ : ℂ) + (t : ℂ) * Complex.I) / D₂.fn ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds ((0 : ℂ) ^ n * (D₁.residue / D₂.residue))) := by
  have hlimit :=
    (gammaRational_ratio_tendsto D₁.numUnit D₁.denUnit D₂.numUnit D₂.denUnit
      D₁.numOrder D₁.denOrder D₂.numOrder D₂.denOrder n hn
      D₁.denUnit_ne D₂.numUnit_ne D₂.denUnit_ne).comp
      (Gamma_vertical_tendsto_nhdsWithin_zero hσ)
  have hres : (D₁.numUnit.eval 0 * D₂.denUnit.eval 0) /
      (D₁.denUnit.eval 0 * D₂.numUnit.eval 0) = D₁.residue / D₂.residue := by
    simp only [GammaRationalDatum.residue]
    field_simp
  rw [← hres]
  exact hlimit

/-- A Gamma-rational coefficient weighted by the monomial `s^a`. -/
def GammaRationalDatum.polyFn (D : GammaRationalDatum) (a : ℕ) (s : ℂ) : ℂ :=
  s ^ a * D.fn s

theorem polyFn_ratio_eq (D₁ D₂ : GammaRationalDatum) (a₁ a₂ : ℕ) (s : ℂ) :
    D₁.polyFn a₁ s / D₂.polyFn a₂ s
      = (s ^ a₁ / s ^ a₂) * (D₁.fn s / D₂.fn s) := by
  simp only [GammaRationalDatum.polyFn]
  rw [div_mul_div_comm]

/-- **The Gamma exponent dominates the `s` exponent (eq. 26, first clause).**  A strictly larger
Gamma valuation in the numerator drives the normalized ratio to zero regardless of the accompanying
powers of `s`. -/
theorem gammaRationalDatum_polyRatio_tendsto_zero_of_gap
    (D₁ D₂ : GammaRationalDatum) (a₁ a₂ n : ℕ)
    (hn : D₁.numOrder + D₂.denOrder = n + (D₂.numOrder + D₁.denOrder)) (hnpos : 0 < n)
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
        D₁.polyFn a₁ ((σ : ℂ) + (t : ℂ) * Complex.I) /
          D₂.polyFn a₂ ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  -- the numerator factor `s^{a₁} Γ^n` already vanishes
  have hnum := tendsto_pow_mul_Gamma_pow hσ a₁ n hnpos
  -- the unit factor converges
  have hunit : Tendsto (fun t : ℝ =>
      (D₁.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
        D₂.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))) /
      (D₁.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
        D₂.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))))
      atTop (nhds ((D₁.numUnit.eval 0 * D₂.denUnit.eval 0) /
        (D₁.denUnit.eval 0 * D₂.numUnit.eval 0))) := by
    have hg : Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
        atTop (nhds 0) := Gamma_vertical_tendsto_zero hσ
    exact ((((Polynomial.continuous D₁.numUnit).tendsto 0).mul
      ((Polynomial.continuous D₂.denUnit).tendsto 0)).div
      (((Polynomial.continuous D₁.denUnit).tendsto 0).mul
        ((Polynomial.continuous D₂.numUnit).tendsto 0))
      (mul_ne_zero D₁.denUnit_ne D₂.numUnit_ne)).comp hg
  have hmodel : Tendsto (fun t : ℝ =>
      (((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₁ *
        (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ n) *
        ((D₁.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
            D₂.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))) /
          (D₁.denUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) *
            D₂.numUnit.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)))) *
        (((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₂)⁻¹) atTop (nhds 0) := by
    have hprod := hnum.mul hunit
    rw [zero_mul] at hprod
    rw [tendsto_zero_iff_norm_tendsto_zero] at hprod ⊢
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hprod
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
    have hs1 : (1 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ :=
      le_trans ht (le_norm_vertical σ ht0.le)
    have hinv : ‖(((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₂)⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_pow]
      rw [inv_le_one₀ (by positivity)]
      exact one_le_pow₀ hs1
    rw [norm_mul]
    calc ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₁ *
            (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ n *
            ((D₁.numUnit.eval _ * D₂.denUnit.eval _) /
              (D₁.denUnit.eval _ * D₂.numUnit.eval _))‖ *
          ‖(((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₂)⁻¹‖
        ≤ ‖((σ : ℂ) + (t : ℂ) * Complex.I) ^ a₁ *
            (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ n *
            ((D₁.numUnit.eval _ * D₂.denUnit.eval _) /
              (D₁.denUnit.eval _ * D₂.numUnit.eval _))‖ * 1 :=
          mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = _ := by rw [mul_one]
  refine hmodel.congr' ?_
  have hgne : ∀ᶠ t : ℝ in atTop, Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    have hg := Gamma_vertical_tendsto_nhdsWithin_zero hσ
    exact hg.eventually self_mem_nhdsWithin
  have hunits : ∀ (R : Polynomial ℂ), R.eval 0 ≠ 0 →
      ∀ᶠ t : ℝ in atTop, R.eval (Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
    intro R hR
    have hg : Tendsto (fun t : ℝ => Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
        atTop (nhds 0) := Gamma_vertical_tendsto_zero hσ
    exact (((Polynomial.continuous R).tendsto 0).comp hg).eventually
      (isOpen_ne.mem_nhds hR)
  filter_upwards [hgne, hunits D₁.denUnit D₁.denUnit_ne, hunits D₂.numUnit D₂.numUnit_ne,
    hunits D₂.denUnit D₂.denUnit_ne] with t hg h1 h2 h3
  have hfac := gammaRational_ratio_eq (g := Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I))
    hg D₁.numUnit D₁.denUnit D₂.numUnit D₂.denUnit
    D₁.numOrder D₁.denOrder D₂.numOrder D₂.denOrder n hn h1 h2 h3
  rw [polyFn_ratio_eq]
  simp only [GammaRationalDatum.fn, GammaRationalDatum.num, GammaRationalDatum.den]
  rw [hfac]
  field_simp

/-- **At equal Gamma valuation the `s` exponents decide (eq. 26, second clause).**  With the same
Gamma valuation, a strictly smaller power of `s` in the numerator sends the normalized ratio to
zero. -/
theorem gammaRationalDatum_polyRatio_tendsto_zero_of_sPow
    (D₁ D₂ : GammaRationalDatum) (a₁ a₂ : ℕ)
    (hn : D₁.numOrder + D₂.denOrder = D₂.numOrder + D₁.denOrder) (ha : a₁ < a₂)
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
        D₁.polyFn a₁ ((σ : ℂ) + (t : ℂ) * Complex.I) /
          D₂.polyFn a₂ ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds 0) := by
  have hratio := gammaRationalDatum_ratio_vertical_tendsto D₁ D₂ 0 (by omega) hσ
  rw [pow_zero, one_mul] at hratio
  obtain ⟨d, hd⟩ : ∃ d, a₂ = a₁ + d ∧ 0 < d := ⟨a₂ - a₁, by omega, by omega⟩
  have hinv := tendsto_inv_pow_vertical σ hd.2
  have hmodel : Tendsto (fun t : ℝ =>
      (D₁.fn ((σ : ℂ) + (t : ℂ) * Complex.I) / D₂.fn ((σ : ℂ) + (t : ℂ) * Complex.I)) *
        ((((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)⁻¹)) atTop (nhds 0) := by
    simpa using hratio.mul hinv
  refine hmodel.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h] at him
    simp only [Complex.zero_im] at him
    linarith
  rw [polyFn_ratio_eq, hd.1, pow_add]
  field_simp

/-- **Equal Gamma valuation and equal `s` power give the residue quotient.** -/
theorem gammaRationalDatum_polyRatio_tendsto_residue
    (D₁ D₂ : GammaRationalDatum) (a : ℕ)
    (hn : D₁.numOrder + D₂.denOrder = D₂.numOrder + D₁.denOrder)
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun t : ℝ =>
        D₁.polyFn a ((σ : ℂ) + (t : ℂ) * Complex.I) /
          D₂.polyFn a ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds (D₁.residue / D₂.residue)) := by
  have hratio := gammaRationalDatum_ratio_vertical_tendsto D₁ D₂ 0 (by omega) hσ
  rw [pow_zero, one_mul] at hratio
  refine hratio.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hsne : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [h] at him
    simp only [Complex.zero_im] at him
    linarith
  rw [polyFn_ratio_eq, div_self (pow_ne_zero a hsne), one_mul]

end

end GaloisForLFunctions
