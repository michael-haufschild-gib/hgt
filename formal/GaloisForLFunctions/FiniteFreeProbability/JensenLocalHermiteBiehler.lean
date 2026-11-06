import GaloisForLFunctions.FiniteFreeProbability.JensenUpperTransform

/-!
# Local Hermite–Biehler estimates for the upper transform

Fix a saddle `τ₁`, `(a₀ - iz) τ₁ = d`, with `a₀ = G'/G(τ₁)`, `r = Re τ₁`.

* **Near the real axis.** On the disc `|w - x| < K/r` the mean `𝓜(c)`, `c = -i(w - x)τ₁`, stays within
  `1/2` of `1`, because `|c| ≪ √d`. So `log 𝓜` is a bounded holomorphic function, Schwarz's lemma
  bounds its variation by `O(r/K)` per unit length, and the main factor `e^{c}` grows at rate `r`. Hence
  `|E(x + it)| > |E(x - it)|` for `0 < t < K/r`.
* **Away from the real axis.** Moving from `z` to `conj z` multiplies the integrand by
  `e^{-2t Re τ}`. Since `Re τ ≥ r/2` on the essential part of the circle, `|E(conj z)|` is smaller than
  `|E(z)|` once `t r ≥ 3`.

In either case `R_d = E + conj E(conj ·)` does not vanish.
-/

open Polynomial Filter Topology Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace FiniteFreeProbability

noncomputable section

/-! ## The constants at a complex saddle -/

theorem re_mul_norm_sq {d : ℕ} {w τ : ℂ} (hs : w * τ = d) : w.re * ‖τ‖ ^ 2 = d * τ.re := by
  have h1 : w * (τ * (starRingEnd ℂ) τ) = d * (starRingEnd ℂ) τ := by
    rw [← mul_assoc, hs]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
  have h2 := congrArg Complex.re h1
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, natCast_re, natCast_im, conj_re,
    conj_im, zero_mul] at h2
  simpa using h2

/-- The three smallness bounds behind the saddle defect, in real variables. -/
theorem saddle_real_bounds {A B ρ r D : ℝ} (hA : 8000 ≤ A) (hBA : A ≤ B) (hr : 400 ≤ r) (hρr : r ≤ ρ)
    (hid : B * ρ ^ 2 = D * r) (hρA : ρ * A ≤ D) (hlogρ : Real.log ρ ≤ 2 * A + 14) :
    6 * ρ * π ^ 2 ≤ D ∧
      24 * π ^ 2 * ρ / D + 1 / 1000 + 6 * ρ ^ 2 * Real.exp (-(D * r ^ 2 / (8 * π ^ 2 * ρ ^ 2))) ≤ 1 / 25 ∧
      Real.exp 1 * Real.sqrt D * Real.exp (-(D * (r / ρ) ^ 2 / 2)) ≤ 1 / 1000 := by
  have hπ := Real.pi_pos
  have hπ2 : π ^ 2 ≤ 10 := by
    have := Real.pi_lt_d2
    nlinarith only [this, hπ]
  have hπ2' : 9 ≤ π ^ 2 := by
    have := Real.pi_gt_three
    nlinarith only [this]
  have hρpos : 0 < ρ := by linarith only [hρr, hr]
  have hA0 : 0 < A := by linarith only [hA]
  have hB0 : 0 < B := by linarith only [hA, hBA]
  have hD0 : 0 < D := lt_of_lt_of_le (mul_pos hρpos hA0) hρA
  have hρd : ρ / D ≤ 1 / A := by
    rw [div_le_div_iff₀ hD0 hA0]
    linarith only [hρA]
  have hρα : 6 * ρ * π ^ 2 ≤ D := by nlinarith only [hρA, hA, hρpos, hπ2]
  have hρe : ρ ≤ Real.exp (2 * A + 14) := by
    rw [← Real.log_le_iff_le_exp hρpos]
    exact hlogρ
  have hsq1 : D * r ^ 2 = (B * ρ ^ 2) * r := by rw [hid]; ring
  have hexpo1 : D * r ^ 2 / (8 * π ^ 2 * ρ ^ 2) = B * r / (8 * π ^ 2) := by
    rw [hsq1]
    field_simp
  have hexpo2 : D * (r / ρ) ^ 2 / 2 = B * r / 2 := by
    rw [div_pow, ← mul_div_assoc, hsq1]
    field_simp
  rw [hexpo1, hexpo2]
  have hBr : 400 * B ≤ B * r := by nlinarith only [hr, hB0]
  have hAr1 : 5 * A ≤ B * r / (8 * π ^ 2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [hBr, hBA, hπ2, hA0]
  have hterm1 : 24 * π ^ 2 * ρ / D ≤ 3 / 100 := by
    calc 24 * π ^ 2 * ρ / D = 24 * π ^ 2 * (ρ / D) := by ring
      _ ≤ 24 * 10 * (1 / 8000) :=
          mul_le_mul (by linarith only [hπ2]) (hρd.trans (one_div_le_one_div_of_le (by norm_num) hA))
            (by positivity) (by norm_num)
      _ = 3 / 100 := by norm_num
  have hbig : Real.exp (-(A - 28)) ≤ 1 / 1000 := by
    have h := Real.add_one_le_exp (A - 28)
    rw [Real.exp_neg]
    have hp : 0 < A - 28 + 1 := by linarith only [hA]
    calc (Real.exp (A - 28))⁻¹ ≤ (A - 28 + 1)⁻¹ := inv_anti₀ hp h
      _ ≤ 1 / 1000 := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le (by norm_num) (by linarith only [hA])
  have hterm2 : 6 * ρ ^ 2 * Real.exp (-(B * r / (8 * π ^ 2))) ≤ 6 / 1000 := by
    have h1 : ρ ^ 2 ≤ Real.exp (4 * A + 28) := by
      calc ρ ^ 2 ≤ Real.exp (2 * A + 14) ^ 2 := pow_le_pow_left₀ hρpos.le hρe 2
        _ = _ := by
            rw [← Real.exp_nat_mul]
            congr 1
            push_cast
            ring
    have h2 : Real.exp (-(B * r / (8 * π ^ 2))) ≤ Real.exp (-(5 * A)) :=
      Real.exp_le_exp.2 (by linarith only [hAr1])
    have h3 : 6 * ρ ^ 2 * Real.exp (-(B * r / (8 * π ^ 2))) ≤
        6 * Real.exp (4 * A + 28) * Real.exp (-(5 * A)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2 (Real.exp_pos _).le (by positivity)
    have h4 : 6 * Real.exp (4 * A + 28) * Real.exp (-(5 * A)) = 6 * Real.exp (-(A - 28)) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    linarith only [h3, h4, hbig]
  have hterm3 : Real.exp 1 * Real.sqrt D * Real.exp (-(B * r / 2)) ≤ 1 / 1000 := by
    have hdle : D ≤ B * ρ ^ 2 := by
      rw [hid]
      nlinarith only [hr, hD0]
    have hsq : Real.sqrt D ≤ Real.exp B * Real.exp (2 * A + 14) := by
      rw [Real.sqrt_le_left (by positivity)]
      have hB2 : B ≤ Real.exp B ^ 2 := by
        have hB1 := Real.add_one_le_exp B
        have h1 : 1 ≤ Real.exp B := Real.one_le_exp hB0.le
        nlinarith only [hB1, h1]
      have hρ2 : ρ ^ 2 ≤ Real.exp (2 * A + 14) ^ 2 := pow_le_pow_left₀ hρpos.le hρe 2
      calc D ≤ B * ρ ^ 2 := hdle
        _ ≤ Real.exp B ^ 2 * Real.exp (2 * A + 14) ^ 2 :=
          mul_le_mul hB2 hρ2 (sq_nonneg _) (sq_nonneg _)
        _ = _ := by ring
    have h4 : Real.exp 1 * (Real.exp B * Real.exp (2 * A + 14)) * Real.exp (-(200 * B)) ≤
        Real.exp (-(A - 28)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith only [hA, hBA]
    have h5 : Real.exp (-(B * r / 2)) ≤ Real.exp (-(200 * B)) :=
      Real.exp_le_exp.2 (by linarith only [hBr])
    have h6 : Real.exp 1 * Real.sqrt D * Real.exp (-(B * r / 2)) ≤
        Real.exp 1 * (Real.exp B * Real.exp (2 * A + 14)) * Real.exp (-(200 * B)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le) h5 (Real.exp_pos _).le
        (by positivity)
    linarith only [h6, h4, hbig]
  exact ⟨hρα, by linarith only [hterm1, hterm2], hterm3⟩

/-- The three smallness bounds behind the saddle defect, at a complex point of the upper half-plane. -/
theorem saddle_constants {d : ℕ} (hd : 0 < d) {z τ₁ : ℂ} (hz : 0 ≤ z.im)
    (hs : (gammaSlope τ₁ - I * z) * τ₁ = d) (hA : 8000 ≤ (gammaSlope τ₁).re) (hr : 400 ≤ τ₁.re) :
    6 * ‖τ₁‖ * π ^ 2 ≤ d ∧
      24 * π ^ 2 * ‖τ₁‖ / d + 1 / 1000 +
        6 * ‖τ₁‖ ^ 2 * Real.exp (-(d * τ₁.re ^ 2 / (8 * π ^ 2 * ‖τ₁‖ ^ 2))) ≤ 1 / 25 ∧
      Real.exp 1 * Real.sqrt d * Real.exp (-(d * (τ₁.re / ‖τ₁‖) ^ 2 / 2)) ≤ 1 / 1000 := by
  have hwre : (gammaSlope τ₁ - I * z).re = (gammaSlope τ₁).re + z.im := by simp
  have hnid : ‖gammaSlope τ₁ - I * z‖ * ‖τ₁‖ = d := by
    rw [← norm_mul, hs, Complex.norm_natCast]
  have hBle := Complex.re_le_norm (gammaSlope τ₁ - I * z)
  have hρ0 : 0 ≤ ‖τ₁‖ := norm_nonneg _
  have hρA : ‖τ₁‖ * (gammaSlope τ₁).re ≤ d := by
    rw [← hnid, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hρ0
    linarith only [hBle, hwre, hz]
  have hst := abs_le.1 (abs_re_gammaSlope_sub_le (τ := τ₁) (by linarith only [hr]))
  exact saddle_real_bounds hA (by linarith only [hwre, hz]) hr (Complex.re_le_norm τ₁)
    (re_mul_norm_sq hs) hρA (by linarith only [hst.1])

/-- The saddle defect is at most `1/5` at a complex point of the upper half-plane. -/
theorem norm_saddleError_le_fifth {d : ℕ} (hd : 0 < d) {z τ₁ : ℂ} (hz : 0 ≤ z.im)
    (hs : (gammaSlope τ₁ - I * z) * τ₁ = d) (hA : 8000 ≤ (gammaSlope τ₁).re) (hr : 400 ≤ τ₁.re) :
    ‖saddleError d (gammaSlope τ₁) τ₁‖ ≤ 1 / 5 := by
  obtain ⟨hρα, h1, h2⟩ := saddle_constants hd hz hs hA hr
  have h := norm_saddleError_le hd hr hρα
  linarith

/-! ## Pointwise and integrated bounds -/

/-- The weighted ratio on the right half-circle has a Gaussian majorant. -/
theorem norm_weight_mul_ratio_le {d : ℕ} {τ₁ : ℂ} (hr : 400 ≤ τ₁.re)
    (hρα : 6 * ‖τ₁‖ * π ^ 2 ≤ d) {C : ℝ}
    (hC : 24 * π ^ 2 * ‖τ₁‖ / d + 1 / 1000 +
      6 * ‖τ₁‖ ^ 2 * Real.exp (-(d * τ₁.re ^ 2 / (8 * π ^ 2 * ‖τ₁‖ ^ 2))) ≤ C) {φ : ℝ}
    (hφ : φ ∈ Icc (-(π / 2) - Complex.arg τ₁) (π / 2 - Complex.arg τ₁)) :
    ‖saddleWeight d φ * saddleRatio (gammaSlope τ₁) τ₁ φ‖ ≤
      Real.exp d * ((1 + C) * Real.exp (-(d / π ^ 2 / 2 * φ ^ 2))) := by
  have hπ := Real.pi_pos
  have hθ' := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith : 0 < τ₁.re)))
  have habs : |φ| ≤ π := by
    rw [abs_le]
    constructor <;> linarith [hφ.1, hφ.2, hθ'.1, hθ'.2]
  have hbase := exp_mul_norm_saddleRatio_sub_one_le hr hρα hφ
  set g := Real.exp (-(d / π ^ 2 / 2 * φ ^ 2)) with hg
  set Y := Real.exp (d * (Real.cos φ - 1)) with hY
  have hg0 : 0 ≤ g := (Real.exp_pos _).le
  have hY0 : 0 ≤ Y := (Real.exp_pos _).le
  have hYg : Y ≤ g := by
    apply Real.exp_le_exp.2
    have h := one_sub_cos_ge habs
    have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have hmul := mul_le_mul_of_nonneg_left h hdn
    have e : (d : ℝ) * (2 / π ^ 2 * φ ^ 2) = 4 * (d / π ^ 2 / 2 * φ ^ 2) := by
      field_simp
      ring
    have hp : 0 ≤ (d : ℝ) / π ^ 2 / 2 * φ ^ 2 := by positivity
    nlinarith
  have hW : ‖saddleWeight d φ‖ = Real.exp d * Y := by
    rw [norm_saddleWeight, hY, ← Real.exp_add]
    congr 1
    ring
  have hQ : ‖saddleRatio (gammaSlope τ₁) τ₁ φ‖ ≤ 1 + ‖saddleRatio (gammaSlope τ₁) τ₁ φ - 1‖ := by
    have := norm_le_norm_add_norm_sub' (saddleRatio (gammaSlope τ₁) τ₁ φ) (1 : ℂ)
    simpa using this
  rw [norm_mul, hW, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  calc
    Y * ‖saddleRatio (gammaSlope τ₁) τ₁ φ‖ ≤ Y * (1 + ‖saddleRatio (gammaSlope τ₁) τ₁ φ - 1‖) :=
      mul_le_mul_of_nonneg_left hQ hY0
    _ = Y + Y * ‖saddleRatio (gammaSlope τ₁) τ₁ φ - 1‖ := by ring
    _ ≤ g + C * g := add_le_add hYg (hbase.trans (mul_le_mul_of_nonneg_right hC hg0))
    _ = (1 + C) * g := by ring

theorem norm_saddleF_mul_exp_le {d : ℕ} (hd : 0 < d) :
    ‖saddleF d‖ * Real.exp d ≤ Real.exp 1 * Real.sqrt d / (2 * π) := by
  have hπ := Real.pi_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdpow : (0 : ℝ) < (d : ℝ) ^ d := by positivity
  have hnorm : ‖saddleF d‖ = (d.factorial : ℝ) / (2 * π * (d : ℝ) ^ d) := by
    rw [saddleF, norm_div, Complex.norm_natCast, norm_mul, norm_mul, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Complex.norm_two, Real.norm_of_nonneg hπ.le]
  have hfac := factorial_le_stirling hd
  have he : ((d : ℝ) / Real.exp 1) ^ d * Real.exp d = (d : ℝ) ^ d := by
    rw [div_pow, ← Real.exp_nat_mul, mul_one]
    field_simp
  rw [hnorm]
  calc _ = (d.factorial : ℝ) * Real.exp d / (2 * π * (d : ℝ) ^ d) := by ring
    _ ≤ (Real.exp 1 * Real.sqrt d * ((d : ℝ) / Real.exp 1) ^ d) * Real.exp d /
        (2 * π * (d : ℝ) ^ d) := by
        gcongr
    _ = Real.exp 1 * Real.sqrt d * (((d : ℝ) / Real.exp 1) ^ d * Real.exp d) /
        (2 * π * (d : ℝ) ^ d) := by ring
    _ = _ := by
        rw [he]
        field_simp

theorem norm_exp_sub_one_le_mul_exp (u : ℂ) : ‖Complex.exp u - 1‖ ≤ ‖u‖ * Real.exp ‖u‖ := by
  have hf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivWithinAt (fun t : ℝ => Complex.exp ((t : ℂ) * u))
      (Complex.exp ((t : ℂ) * u) * u) (Icc 0 1) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * u) u t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const u
    exact h1.cexp.hasDerivWithinAt
  have hb : ∀ t ∈ Ico (0 : ℝ) 1, ‖Complex.exp ((t : ℂ) * u) * u‖ ≤ ‖u‖ * Real.exp ‖u‖ := by
    intro t ht
    rw [norm_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg u)
    refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
    nlinarith [norm_nonneg u, ht.2.le]
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hf hb
  simpa using h

/-- The mean moves by at most `O(|c|/√d)`. -/
theorem norm_saddleMean_sub_le {d : ℕ} (hd : 0 < d) {τ₁ : ℂ} (hr : 400 ≤ τ₁.re)
    (hρα : 6 * ‖τ₁‖ * π ^ 2 ≤ d) {C : ℝ}
    (hC : 24 * π ^ 2 * ‖τ₁‖ / d + 1 / 1000 +
      6 * ‖τ₁‖ ^ 2 * Real.exp (-(d * τ₁.re ^ 2 / (8 * π ^ 2 * ‖τ₁‖ ^ 2))) ≤ C) (hC0 : 0 ≤ C)
    {c : ℂ} {s : ℝ} (hs0 : 0 ≤ s) (hc : ‖c‖ ≤ s * Real.sqrt (d / π ^ 2)) :
    ‖saddleMean d (gammaSlope τ₁) τ₁ c - saddleMean d (gammaSlope τ₁) τ₁ 0‖ ≤
      14 * (1 + C) * s * Real.exp (s ^ 2) := by
  have hπ := Real.pi_pos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set α : ℝ := d / π ^ 2 with hα
  have hαpos : 0 < α := by positivity
  set sa := Real.sqrt α with hsa
  have hsa2 : sa ^ 2 = α := Real.sq_sqrt hαpos.le
  have hsa0 : 0 ≤ sa := Real.sqrt_nonneg _
  set a := Complex.arg τ₁ with ha
  have hθ' := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith : 0 < τ₁.re)))
  have hle : -(π / 2) - a ≤ π / 2 - a := by linarith
  have hW := continuous_saddleWeight d
  have hQ := continuous_saddleRatio (gammaSlope τ₁) τ₁
  have hΘ : Continuous fun φ : ℝ => Complex.exp (φ * I) - 1 := by fun_prop
  have hgint : Integrable fun φ : ℝ => Real.exp (-(α / 8 * φ ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := α / 8) (by positivity)
  have hgval : ∫ φ : ℝ, Real.exp (-(α / 8 * φ ^ 2)) = Real.sqrt (π / (α / 8)) := by
    simpa using integral_gaussian (α / 8)
  set D := Real.exp d * ((1 + C) * (2 * s * Real.exp (s ^ 2))) with hD
  have hbound : ∀ φ ∈ Icc (-(π / 2) - a) (π / 2 - a),
      ‖saddleWeight d φ * saddleRatio (gammaSlope τ₁) τ₁ φ *
        (Complex.exp (c * (Complex.exp (φ * I) - 1)) - 1)‖ ≤ D * Real.exp (-(α / 8 * φ ^ 2)) := by
    intro φ hφ
    have h0 := norm_weight_mul_ratio_le hr hρα hC hφ
    set v := sa * |φ| with hv
    have hv0 : 0 ≤ v := by positivity
    have hv2 : v ^ 2 = α * φ ^ 2 := by
      rw [hv, mul_pow, hsa2, sq_abs]
    have hΘφ : ‖Complex.exp (φ * I) - 1‖ ≤ |φ| := by
      have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := φ)
      rw [mul_comm] at h
      simpa using h
    have hy : ‖c * (Complex.exp (φ * I) - 1)‖ ≤ s * v := by
      rw [norm_mul, hv, ← mul_assoc]
      exact mul_le_mul hc hΘφ (norm_nonneg _) (by positivity)
    have hexp1 := norm_exp_sub_one_le_mul_exp (c * (Complex.exp (φ * I) - 1))
    have hexp2 : ‖Complex.exp (c * (Complex.exp (φ * I) - 1)) - 1‖ ≤
        (s * v) * Real.exp (s * v) :=
      hexp1.trans (mul_le_mul hy (Real.exp_le_exp.2 hy) (Real.exp_pos _).le (by positivity))
    have hv1 : v ≤ 2 * Real.exp (v ^ 2 / 8) := by
      have h := Real.add_one_le_exp (v ^ 2 / 8)
      nlinarith [sq_nonneg (v - 2)]
    have hsv : Real.exp (s * v) ≤ Real.exp (s ^ 2) * Real.exp (v ^ 2 / 4) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg (s - v / 2)]
    have hexp3 : (s * v) * Real.exp (s * v) ≤
        (2 * s * Real.exp (s ^ 2)) * (Real.exp (v ^ 2 / 8) * Real.exp (v ^ 2 / 4)) := by
      calc
        (s * v) * Real.exp (s * v) ≤ (s * (2 * Real.exp (v ^ 2 / 8))) *
            (Real.exp (s ^ 2) * Real.exp (v ^ 2 / 4)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hv1 hs0) hsv (Real.exp_pos _).le (by positivity)
        _ = _ := by ring
    rw [norm_mul]
    calc
      _ ≤ (Real.exp d * ((1 + C) * Real.exp (-(d / π ^ 2 / 2 * φ ^ 2)))) *
          ((2 * s * Real.exp (s ^ 2)) * (Real.exp (v ^ 2 / 8) * Real.exp (v ^ 2 / 4))) :=
        mul_le_mul h0 (hexp2.trans hexp3) (norm_nonneg _) (by positivity)
      _ = D * (Real.exp (-(α / 2 * φ ^ 2)) * (Real.exp (v ^ 2 / 8) * Real.exp (v ^ 2 / 4))) := by
        rw [hD, hα]
        ring
      _ = D * Real.exp (-(α / 8 * φ ^ 2)) := by
        rw [← Real.exp_add, ← Real.exp_add, hv2]
        congr 2
        ring
  have hsplit : saddleMean d (gammaSlope τ₁) τ₁ c - saddleMean d (gammaSlope τ₁) τ₁ 0 =
      saddleF d * ∫ φ in (-(π / 2) - a)..(π / 2 - a),
        saddleWeight d φ * saddleRatio (gammaSlope τ₁) τ₁ φ *
          (Complex.exp (c * (Complex.exp (φ * I) - 1)) - 1) := by
    have hint (c' : ℂ) : IntervalIntegrable (fun φ : ℝ =>
        saddleWeight d φ * saddleRatio (gammaSlope τ₁) τ₁ φ *
          Complex.exp (c' * (Complex.exp (φ * I) - 1))) volume (-(π / 2) - a) (π / 2 - a) :=
      ((hW.mul hQ).mul (Complex.continuous_exp.comp (continuous_const.mul hΘ))).intervalIntegrable _ _
    rw [saddleMean, saddleMean, ← ha, ← mul_sub, ← intervalIntegral.integral_sub (hint c) (hint 0)]
    congr 1
    refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [zero_mul, Complex.exp_zero, mul_one]
    ring
  have hI : ‖∫ φ in (-(π / 2) - a)..(π / 2 - a),
      saddleWeight d φ * saddleRatio (gammaSlope τ₁) τ₁ φ *
        (Complex.exp (c * (Complex.exp (φ * I) - 1)) - 1)‖ ≤ D * Real.sqrt (π / (α / 8)) := by
    have h1 := intervalIntegral.norm_integral_le_of_norm_le hle
      (Eventually.of_forall fun φ hφ => hbound φ ⟨hφ.1.le, hφ.2⟩)
      ((hgint.const_mul D).intervalIntegrable)
    refine h1.trans ?_
    rw [intervalIntegral.integral_of_le hle, integral_const_mul]
    have hD0 : 0 ≤ D := by positivity
    apply mul_le_mul_of_nonneg_left _ hD0
    rw [← hgval]
    exact setIntegral_le_integral hgint (Eventually.of_forall fun φ => (Real.exp_pos _).le)
  have hF := norm_saddleF_mul_exp_le hd
  have hsqrt : Real.sqrt d * Real.sqrt (π / (α / 8)) = π * Real.sqrt (8 * π) := by
    rw [← Real.sqrt_mul hdR.le, show (d : ℝ) * (π / (α / 8)) = π ^ 2 * (8 * π) by
      rw [hα]
      field_simp, Real.sqrt_mul (by positivity), Real.sqrt_sq hπ.le]
  have hconst : Real.exp 1 * Real.sqrt (8 * π) ≤ 14 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.sqrt (8 * π) ≤ 5.02 := by
      rw [Real.sqrt_le_left (by norm_num)]
      have := Real.pi_lt_d2
      norm_num
      linarith
    have h3 : 0 ≤ Real.sqrt (8 * π) := Real.sqrt_nonneg _
    nlinarith
  have hE0 : 0 < Real.exp (s ^ 2) := Real.exp_pos _
  have hprod : 0 ≤ (1 + C) * s * Real.exp (s ^ 2) := by positivity
  rw [hsplit, norm_mul]
  calc
    ‖saddleF d‖ * ‖_‖ ≤ ‖saddleF d‖ * (D * Real.sqrt (π / (α / 8))) :=
      mul_le_mul_of_nonneg_left hI (norm_nonneg _)
    _ = (‖saddleF d‖ * Real.exp d) * ((1 + C) * (2 * s * Real.exp (s ^ 2))) *
        Real.sqrt (π / (α / 8)) := by
      rw [hD]
      ring
    _ ≤ (Real.exp 1 * Real.sqrt d / (2 * π)) * ((1 + C) * (2 * s * Real.exp (s ^ 2))) *
        Real.sqrt (π / (α / 8)) := by
      gcongr
    _ = (Real.exp 1 * Real.sqrt (8 * π)) * ((1 + C) * s * Real.exp (s ^ 2)) := by
      have e : Real.exp 1 * Real.sqrt d / (2 * π) * ((1 + C) * (2 * s * Real.exp (s ^ 2))) *
          Real.sqrt (π / (α / 8)) =
          Real.exp 1 * (1 + C) * s * Real.exp (s ^ 2) / π *
            (Real.sqrt d * Real.sqrt (π / (α / 8))) := by
        ring
      rw [e, hsqrt]
      field_simp
    _ ≤ 14 * ((1 + C) * s * Real.exp (s ^ 2)) := mul_le_mul_of_nonneg_right hconst hprod
    _ = _ := by ring

/-- On the essential part of the circle the real part of `τ` stays above `r/2`. -/
theorem half_le_re_mul_exp {τ₁ : ℂ} {φ φ₁ : ℝ} (hr : 0 ≤ τ₁.re) (hφ : |φ| ≤ φ₁) (hφ₁ : φ₁ ≤ 1 / 2)
    (hfar : φ₁ * ‖τ₁‖ ≤ 3 / 8 * τ₁.re) : τ₁.re / 2 ≤ (τ₁ * Complex.exp (φ * I)).re := by
  have hre : (τ₁ * Complex.exp (φ * I)).re = τ₁.re * Real.cos φ - τ₁.im * Real.sin φ := by
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hcos := Real.one_sub_sq_div_two_le_cos (x := φ)
  have hφ2 : φ ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]
    have h0 := abs_nonneg φ
    nlinarith
  have hc : τ₁.re * (1 - 1 / 8) ≤ τ₁.re * Real.cos φ :=
    mul_le_mul_of_nonneg_left (by linarith) hr
  have hs : |τ₁.im * Real.sin φ| ≤ ‖τ₁‖ * |φ| := by
    rw [abs_mul]
    exact mul_le_mul (Complex.abs_im_le_norm τ₁) Real.abs_sin_le_abs (abs_nonneg _) (norm_nonneg _)
  have hs2 : ‖τ₁‖ * |φ| ≤ φ₁ * ‖τ₁‖ := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hφ (norm_nonneg _)
  have hle := le_abs_self (τ₁.im * Real.sin φ)
  rw [hre]
  linarith

/-- Gaussian majorant for the integrand at the conjugate point. -/
theorem far_majorant {N D α φ sa t r R : ℝ} (hN : N ≤ D * Real.exp (-(α / 2 * φ ^ 2))) (hD0 : 0 ≤ D)
    (hN0 : 0 ≤ N) (ht : 0 ≤ t) (hR0 : 0 ≤ R) (hnear : |φ| ≤ 4 / sa → r / 2 ≤ R) (hsa2 : sa ^ 2 = α)
    (hsa : 0 < sa) :
    N * Real.exp (-(2 * t * R)) ≤
      D * (Real.exp (-(t * r)) * Real.exp (-(α / 2 * φ ^ 2)) +
        Real.exp (-4 : ℝ) * Real.exp (-(α / 4 * φ ^ 2))) := by
  have hα : 0 < α := by rw [← hsa2]; positivity
  have hE1 := Real.exp_pos (-(t * r))
  have hE4 := Real.exp_pos (-4 : ℝ)
  have hg2 := Real.exp_pos (-(α / 2 * φ ^ 2))
  have hg4 := Real.exp_pos (-(α / 4 * φ ^ 2))
  by_cases hc : |φ| ≤ 4 / sa
  · have hexp : Real.exp (-(2 * t * R)) ≤ Real.exp (-(t * r)) := by
      apply Real.exp_le_exp.2
      rw [neg_le_neg_iff]
      nlinarith only [hnear hc, ht]
    have h1 : N * Real.exp (-(2 * t * R)) ≤ (D * Real.exp (-(α / 2 * φ ^ 2))) * Real.exp (-(t * r)) :=
      mul_le_mul hN hexp (Real.exp_pos _).le (by positivity)
    have h2 : 0 ≤ D * (Real.exp (-4 : ℝ) * Real.exp (-(α / 4 * φ ^ 2))) := by positivity
    rw [mul_add]
    linarith only [h1, h2]
  · push Not at hc
    have hexp : Real.exp (-(2 * t * R)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht) hR0
      linarith only [this]
    have hαφ : 16 ≤ α * φ ^ 2 := by
      have h1 : (4 / sa) ^ 2 ≤ |φ| ^ 2 := pow_le_pow_left₀ (by positivity) hc.le 2
      rw [sq_abs, div_pow, hsa2, div_le_iff₀ hα] at h1
      linarith only [h1]
    have hsplit : Real.exp (-(α / 2 * φ ^ 2)) ≤
        Real.exp (-4 : ℝ) * Real.exp (-(α / 4 * φ ^ 2)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      linarith only [hαφ]
    have h1 : N * Real.exp (-(2 * t * R)) ≤ N := by
      calc _ ≤ N * 1 := mul_le_mul_of_nonneg_left hexp hN0
        _ = N := mul_one N
    have h2 : D * Real.exp (-(α / 2 * φ ^ 2)) ≤
        D * (Real.exp (-4 : ℝ) * Real.exp (-(α / 4 * φ ^ 2))) :=
      mul_le_mul_of_nonneg_left hsplit hD0
    have h3 : 0 ≤ D * (Real.exp (-(t * r)) * Real.exp (-(α / 2 * φ ^ 2))) := by positivity
    rw [mul_add]
    linarith only [h1, h2, h3, hN]

theorem interval_gaussian_le {u v β : ℝ} (huv : u ≤ v) (hβ : 0 < β) :
    ∫ φ in u..v, Real.exp (-(β * φ ^ 2)) ≤ Real.sqrt (π / β) := by
  have hg : Integrable fun φ : ℝ => Real.exp (-(β * φ ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := β) hβ
  have hval : ∫ φ : ℝ, Real.exp (-(β * φ ^ 2)) = Real.sqrt (π / β) := by
    simpa using integral_gaussian β
  rw [intervalIntegral.integral_of_le huv, ← hval]
  exact setIntegral_le_integral hg (Eventually.of_forall fun φ => (Real.exp_pos _).le)

/-- Value of the majorant integral. -/
theorem far_constant {F e dd D C α E₁ E₄ s₂ s₄ : ℝ} (hd : 0 < dd) (hπα : α = dd / π ^ 2)
    (hF : F * Real.exp dd ≤ e * Real.sqrt dd / (2 * π)) (hD : D = Real.exp dd * (1 + C))
    (hC : 0 ≤ C) (hF0 : 0 ≤ F) (hE₁ : 0 ≤ E₁) (hE₄ : 0 ≤ E₄)
    (hs₂ : s₂ = Real.sqrt (π / (α / 2))) (hs₄ : s₄ = Real.sqrt (π / (α / 4))) :
    F * (D * (E₁ * s₂ + E₄ * s₄)) ≤
      e / 2 * (1 + C) * (Real.sqrt (2 * π) * E₁ + Real.sqrt (4 * π) * E₄) := by
  have hπ := Real.pi_pos
  have hs2 : Real.sqrt dd * s₂ = π * Real.sqrt (2 * π) := by
    rw [hs₂, ← Real.sqrt_mul hd.le, show dd * (π / (α / 2)) = π ^ 2 * (2 * π) by
      rw [hπα]
      field_simp, Real.sqrt_mul (by positivity), Real.sqrt_sq hπ.le]
  have hs4 : Real.sqrt dd * s₄ = π * Real.sqrt (4 * π) := by
    rw [hs₄, ← Real.sqrt_mul hd.le, show dd * (π / (α / 4)) = π ^ 2 * (4 * π) by
      rw [hπα]
      field_simp, Real.sqrt_mul (by positivity), Real.sqrt_sq hπ.le]
  have hs₂0 : 0 ≤ s₂ := by rw [hs₂]; positivity
  have hs₄0 : 0 ≤ s₄ := by rw [hs₄]; positivity
  have hbr : 0 ≤ (1 + C) * (E₁ * s₂ + E₄ * s₄) := by positivity
  calc
    F * (D * (E₁ * s₂ + E₄ * s₄)) = (F * Real.exp dd) * ((1 + C) * (E₁ * s₂ + E₄ * s₄)) := by
      rw [hD]
      ring
    _ ≤ (e * Real.sqrt dd / (2 * π)) * ((1 + C) * (E₁ * s₂ + E₄ * s₄)) :=
      mul_le_mul_of_nonneg_right hF hbr
    _ = e / (2 * π) * (1 + C) * (E₁ * (Real.sqrt dd * s₂) + E₄ * (Real.sqrt dd * s₄)) := by ring
    _ = _ := by
      rw [hs2, hs4]
      field_simp

/-- **The conjugate point sees only a small part of the weight.** -/
theorem saddle_far_integral_le {d : ℕ} (hd : 0 < d) {τ₁ : ℂ} (hr : 400 ≤ τ₁.re)
    (hρα : 6 * ‖τ₁‖ * π ^ 2 ≤ d) {C : ℝ}
    (hC : 24 * π ^ 2 * ‖τ₁‖ / d + 1 / 1000 +
      6 * ‖τ₁‖ ^ 2 * Real.exp (-(d * τ₁.re ^ 2 / (8 * π ^ 2 * ‖τ₁‖ ^ 2))) ≤ C) (hC0 : 0 ≤ C)
    {t : ℝ} (ht : 0 ≤ t) (hfar : 4 / Real.sqrt (d / π ^ 2) * ‖τ₁‖ ≤ 3 / 8 * τ₁.re)
    (hsmall : 4 / Real.sqrt (d / π ^ 2) ≤ 1 / 2) :
    ‖saddleF d‖ * ∫ φ in (-(π / 2) - Complex.arg τ₁)..(π / 2 - Complex.arg τ₁),
        ‖saddleWeight d φ * saddleRatio (gammaSlope τ₁) τ₁ φ‖ *
          Real.exp (-(2 * t * (τ₁ * Complex.exp (φ * I)).re)) ≤
      Real.exp 1 / 2 * (1 + C) *
        (Real.sqrt (2 * π) * Real.exp (-(t * τ₁.re)) + Real.sqrt (4 * π) * Real.exp (-4)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hαpos : 0 < (d : ℝ) / π ^ 2 := by positivity
  have hsa2 := Real.sq_sqrt hαpos.le
  have hsapos := Real.sqrt_pos.2 hαpos
  have hρpos : 0 < ‖τ₁‖ := lt_of_lt_of_le (by linarith only [hr]) (Complex.re_le_norm τ₁)
  have hθ' := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith only [hr] : 0 < τ₁.re)))
  have hle : -(π / 2) - Complex.arg τ₁ ≤ π / 2 - Complex.arg τ₁ := by linarith only [hθ'.1, hθ'.2]
  have hW := continuous_saddleWeight d
  have hQ := continuous_saddleRatio (gammaSlope τ₁) τ₁
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (d : ℝ) / π ^ 2 := ⟨_, rfl⟩
  rw [← hα] at hαpos hsa2 hsapos hfar hsmall
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = Real.exp d * (1 + C) := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hpoint : ∀ φ ∈ Icc (-(π / 2) - Complex.arg τ₁) (π / 2 - Complex.arg τ₁),
      ‖saddleWeight d φ * saddleRatio (gammaSlope τ₁) τ₁ φ‖ *
        Real.exp (-(2 * t * (τ₁ * Complex.exp (φ * I)).re)) ≤
      D * (Real.exp (-(t * τ₁.re)) * Real.exp (-(α / 2 * φ ^ 2)) +
        Real.exp (-4 : ℝ) * Real.exp (-(α / 4 * φ ^ 2))) := by
    intro φ hφ
    have h0 := norm_weight_mul_ratio_le hr hρα hC hφ
    have h0' : ‖saddleWeight d φ * saddleRatio (gammaSlope τ₁) τ₁ φ‖ ≤
        D * Real.exp (-(α / 2 * φ ^ 2)) := by
      rw [hD, hα, mul_assoc]
      exact h0
    have hRe0 : 0 ≤ (τ₁ * Complex.exp (φ * I)).re := by
      rw [re_mul_exp]
      refine mul_nonneg hρpos.le (Real.cos_nonneg_of_mem_Icc ?_)
      constructor <;> linarith only [hφ.1, hφ.2]
    exact far_majorant h0' hD0 (norm_nonneg _) ht hRe0
      (fun hn => half_le_re_mul_exp (by linarith only [hr]) hn hsmall hfar) hsa2 hsapos
  have hg (β : ℝ) (hβ : 0 < β) : IntervalIntegrable (fun φ : ℝ => Real.exp (-(β * φ ^ 2))) volume
      (-(π / 2) - Complex.arg τ₁) (π / 2 - Complex.arg τ₁) :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hg2 := hg (α / 2) (by positivity)
  have hg4 := hg (α / 4) (by positivity)
  have hLint : IntervalIntegrable (fun φ : ℝ =>
      ‖saddleWeight d φ * saddleRatio (gammaSlope τ₁) τ₁ φ‖ *
        Real.exp (-(2 * t * (τ₁ * Complex.exp (φ * I)).re))) volume
      (-(π / 2) - Complex.arg τ₁) (π / 2 - Complex.arg τ₁) := by
    have hc : Continuous fun φ : ℝ => (τ₁ * Complex.exp (φ * I)).re :=
      Complex.continuous_re.comp (by fun_prop)
    exact ((hW.mul hQ).norm.mul (Real.continuous_exp.comp
      ((continuous_const.mul hc).neg))).intervalIntegrable _ _
  have hGint : IntervalIntegrable (fun φ : ℝ =>
      D * (Real.exp (-(t * τ₁.re)) * Real.exp (-(α / 2 * φ ^ 2)) +
        Real.exp (-4 : ℝ) * Real.exp (-(α / 4 * φ ^ 2)))) volume
      (-(π / 2) - Complex.arg τ₁) (π / 2 - Complex.arg τ₁) :=
    ((hg2.const_mul _).add (hg4.const_mul _)).const_mul _
  have hmono := intervalIntegral.integral_mono_on hle hLint hGint hpoint
  have hval : ∫ φ in (-(π / 2) - Complex.arg τ₁)..(π / 2 - Complex.arg τ₁),
      D * (Real.exp (-(t * τ₁.re)) * Real.exp (-(α / 2 * φ ^ 2)) +
        Real.exp (-4 : ℝ) * Real.exp (-(α / 4 * φ ^ 2))) ≤
      D * (Real.exp (-(t * τ₁.re)) * Real.sqrt (π / (α / 2)) +
        Real.exp (-4 : ℝ) * Real.sqrt (π / (α / 4))) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hg2.const_mul _) (hg4.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ hD0
    exact add_le_add
      (mul_le_mul_of_nonneg_left (interval_gaussian_le hle (by positivity)) (Real.exp_pos _).le)
      (mul_le_mul_of_nonneg_left (interval_gaussian_le hle (by positivity)) (Real.exp_pos _).le)
  have hF := norm_saddleF_mul_exp_le hd
  have hfinal := far_constant hdR hα hF hD hC0 (norm_nonneg _) (Real.exp_pos (-(t * τ₁.re))).le
    (Real.exp_pos (-4 : ℝ)).le rfl rfl
  calc
    _ ≤ ‖saddleF d‖ * (D * (Real.exp (-(t * τ₁.re)) * Real.sqrt (π / (α / 2)) +
        Real.exp (-4 : ℝ) * Real.sqrt (π / (α / 4)))) :=
      mul_le_mul_of_nonneg_left (hmono.trans hval) (norm_nonneg _)
    _ ≤ _ := hfinal

/-! ## Non-vanishing -/

theorem re_ne_half_of_ge {τ₁ : ℂ} (hr : 400 ≤ τ₁.re) : τ₁ ≠ 1 / 2 := re_ne_half (by linarith)

/-- The numerical margin of the far region. -/
theorem far_numeric {y : ℝ} (hy : 3 ≤ y) :
    Real.exp 1 / 2 * (1 + 1 / 25) *
      (Real.sqrt (2 * π) * Real.exp (-y) + Real.sqrt (4 * π) * Real.exp (-4)) ≤ 3 / 10 := by
  have he1 := Real.exp_one_lt_d9
  have he2 := Real.exp_one_gt_d9
  have hs2 : Real.sqrt (2 * π) ≤ 2.51 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have := Real.pi_lt_d2
    norm_num
    linarith only [this]
  have hs4 : Real.sqrt (4 * π) ≤ 3.55 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have := Real.pi_lt_d2
    norm_num
    linarith only [this]
  have hexp3 : (19.6 : ℝ) ≤ Real.exp 3 := by
    have h : Real.exp 3 = Real.exp 1 ^ 3 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h]
    have : (2.7 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith only [he2]) 3
    norm_num at this ⊢
    linarith only [this]
  have hexp4 : (53 : ℝ) ≤ Real.exp 4 := by
    have h : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [h]
    have : (2.7 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith only [he2]) 4
    norm_num at this ⊢
    linarith only [this]
  have hE3 : Real.exp (-y) ≤ 1 / 19.6 := by
    calc Real.exp (-y) ≤ Real.exp (-3) := Real.exp_le_exp.2 (by linarith only [hy])
      _ = (Real.exp 3)⁻¹ := Real.exp_neg 3
      _ ≤ 1 / 19.6 := by
        rw [inv_eq_one_div]
        exact one_div_le_one_div_of_le (by norm_num) hexp3
  have hE4 : Real.exp (-4 : ℝ) ≤ 1 / 53 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexp4
  have hbr : Real.sqrt (2 * π) * Real.exp (-y) + Real.sqrt (4 * π) * Real.exp (-4) ≤
      2.51 * (1 / 19.6) + 3.55 * (1 / 53) := by
    have h1 := mul_le_mul hs2 hE3 (Real.exp_pos _).le (by norm_num)
    have h2 := mul_le_mul hs4 hE4 (Real.exp_pos _).le (by norm_num)
    linarith only [h1, h2]
  have hbr0 : 0 ≤ Real.sqrt (2 * π) * Real.exp (-y) + Real.sqrt (4 * π) * Real.exp (-4) := by
    positivity
  have hcoef : Real.exp 1 / 2 * (1 + 1 / 25) ≤ 1.42 := by
    norm_num
    linarith only [he1]
  calc
    _ ≤ 1.42 * (2.51 * (1 / 19.6) + 3.55 * (1 / 53)) :=
      mul_le_mul hcoef hbr hbr0 (by norm_num)
    _ ≤ 3 / 10 := by norm_num

/-- **No root once `t r ≥ 3`.** -/
theorem eval_ne_zero_of_far {d : ℕ} (hd : 0 < d) {z τ₁ : ℂ} (ht : 0 < z.im)
    (hs : (gammaSlope τ₁ - I * z) * τ₁ = d) (hA : 8000 ≤ (gammaSlope τ₁).re) (hr : 400 ≤ τ₁.re)
    (h3 : 3 ≤ z.im * τ₁.re) (hfar : 4 / Real.sqrt (d / π ^ 2) * ‖τ₁‖ ≤ 3 / 8 * τ₁.re)
    (hsmall : 4 / Real.sqrt (d / π ^ 2) ≤ 1 / 2) :
    (jensenRev d xiSeries).eval z ≠ 0 := by
  have hπ := Real.pi_pos
  obtain ⟨hρα, hC, -⟩ := saddle_constants hd ht.le hs hA hr
  have hτ₁ : τ₁ ≠ 0 := fun h => by
    rw [h] at hr
    norm_num at hr
  have hρ : 0 < ‖τ₁‖ := norm_pos_iff.2 hτ₁
  have hne := re_ne_half_of_ge hr
  have hG : gammaFactor τ₁ ≠ 0 := gammaFactor_ne_zero (by linarith) hne
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  set a := gammaSlope τ₁ with ha
  have hw : a - I * z ≠ 0 := fun h => by
    rw [h, zero_mul] at hs
    exact hdC hs.symm
  have hzw : z + I * a ≠ 0 := fun h => by
    apply hw
    have : a - I * z = -I * (z + I * a) := by
      ring_nf
      rw [I_sq]
      ring
    rw [this, h, mul_zero]
  obtain ⟨M, hM⟩ : ∃ M, M = (z + I * a) ^ d * gammaFactor τ₁ * Complex.exp (-(a * τ₁)) := ⟨_, rfl⟩
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hzw) hG) (Complex.exp_ne_zero _)
  have hMn : 0 < ‖M‖ := norm_pos_iff.2 hM0
  -- The value at `z` is the main term up to a factor `1 + ε`.
  have hEz : jensenUpper d ‖τ₁‖ z = M * (1 + saddleError d a τ₁) := by
    rw [jensenUpper_eq_mean hd hτ₁ hG hs (w := z), ← hM, sub_self]
    simp [saddleMean_zero hd]
  have hε := norm_saddleError_le_fifth hd ht.le hs hA hr
  have hEzn : 4 / 5 * ‖M‖ ≤ ‖jensenUpper d ‖τ₁‖ z‖ := by
    rw [hEz, norm_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ hMn.le
    have := norm_sub_norm_le (1 : ℂ) (-saddleError d a τ₁)
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  -- The value at the conjugate point is much smaller.
  set zc := (starRingEnd ℂ) z with hzc
  have hdiff : -(I * (zc - z)) = -(2 * (z.im : ℂ)) := by
    have : zc - z = -(2 * (z.im : ℂ) * I) := by
      apply Complex.ext <;> simp [hzc]
      ring
    rw [this]
    ring_nf
    rw [I_sq]
    ring
  have hEc := jensenUpper_eq_integral hd hτ₁ hG hs (w := zc)
  rw [← hM] at hEc
  have hint : ‖∫ φ in (-(π / 2) - Complex.arg τ₁)..(π / 2 - Complex.arg τ₁),
        saddleWeight d φ * saddleRatio a τ₁ φ *
          Complex.exp (-(I * (zc - z) * (τ₁ * Complex.exp (φ * I))))‖ ≤
      ∫ φ in (-(π / 2) - Complex.arg τ₁)..(π / 2 - Complex.arg τ₁),
        ‖saddleWeight d φ * saddleRatio a τ₁ φ‖ *
          Real.exp (-(2 * z.im * (τ₁ * Complex.exp (φ * I)).re)) := by
    have hθ' := abs_lt.1 (Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl (by linarith : 0 < τ₁.re)))
    have hle : -(π / 2) - Complex.arg τ₁ ≤ π / 2 - Complex.arg τ₁ := by linarith
    refine (intervalIntegral.norm_integral_le_integral_norm hle).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun φ _ => ?_
    rw [norm_mul, Complex.norm_exp]
    congr 2
    have e : -(I * (zc - z) * (τ₁ * Complex.exp (φ * I))) =
        -(2 * (z.im : ℂ)) * (τ₁ * Complex.exp (φ * I)) := by
      rw [← hdiff]
      ring
    rw [e, Complex.mul_re]
    simp
  have hfarint := saddle_far_integral_le hd hr hρα hC (by norm_num) ht.le hfar hsmall
  have hnum := far_numeric h3
  have hEcn : ‖jensenUpper d ‖τ₁‖ zc‖ ≤ 3 / 10 * ‖M‖ := by
    rw [hEc, norm_mul, norm_mul, mul_comm]
    apply mul_le_mul_of_nonneg_right _ hMn.le
    exact (mul_le_mul_of_nonneg_left hint (norm_nonneg _)).trans (hfarint.trans hnum)
  intro h0
  rw [eval_eq_jensenUpper_add_conj d z hρ, ← hzc, add_eq_zero_iff_eq_neg] at h0
  have hnorm : ‖jensenUpper d ‖τ₁‖ z‖ = ‖jensenUpper d ‖τ₁‖ zc‖ := by
    rw [h0, norm_neg, Complex.norm_conj]
  rw [hnorm] at hEzn
  nlinarith

/-- **No non-real root near a real saddle.** Inside the disc `t r < K`, the modulus of the upper
transform strictly increases across the real axis. -/
theorem eval_ne_zero_of_near {d : ℕ} (hd : 0 < d) {x : ℝ} {τ₁ : ℂ}
    (hs : (gammaSlope τ₁ - I * x) * τ₁ = d) (hA : 8000 ≤ (gammaSlope τ₁).re) (hr : 400 ≤ τ₁.re)
    {K : ℝ} (hK : 3 ≤ K) (hKρ : K * ‖τ₁‖ / τ₁.re ≤ Real.sqrt (d / π ^ 2) / 200)
    {t : ℝ} (ht0 : 0 < t) (htK : t * τ₁.re < K) :
    (jensenRev d xiSeries).eval ((x : ℂ) + t * I) ≠ 0 := by
  have hπ := Real.pi_pos
  have him0 : (0 : ℝ) ≤ (x : ℂ).im := by simp
  obtain ⟨hρα, hC, -⟩ := saddle_constants hd him0 hs hA hr
  have hr0 : 0 < τ₁.re := by linarith
  have hτ₁ : τ₁ ≠ 0 := fun h => by
    rw [h] at hr
    norm_num at hr
  have hρ : 0 < ‖τ₁‖ := norm_pos_iff.2 hτ₁
  have hne := re_ne_half_of_ge hr
  have hG : gammaFactor τ₁ ≠ 0 := gammaFactor_ne_zero (by linarith) hne
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  set a := gammaSlope τ₁ with ha
  have hw : a - I * x ≠ 0 := fun h => by
    rw [h, zero_mul] at hs
    exact hdC hs.symm
  have hzw : (x : ℂ) + I * a ≠ 0 := fun h => by
    apply hw
    have : a - I * x = -I * ((x : ℂ) + I * a) := by
      ring_nf
      rw [I_sq]
      ring
    rw [this, h, mul_zero]
  obtain ⟨M, hM⟩ : ∃ M, M = ((x : ℂ) + I * a) ^ d * gammaFactor τ₁ * Complex.exp (-(a * τ₁)) :=
    ⟨_, rfl⟩
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hzw) hG) (Complex.exp_ne_zero _)
  have hKpos : 0 < K := by linarith
  set Rc := K / τ₁.re with hRc
  have hRcpos : 0 < Rc := div_pos hKpos hr0
  let cf : ℂ → ℂ := fun w => -(I * (w - x) * τ₁)
  have hmean (w : ℂ) (hw : w ∈ Metric.ball (x : ℂ) Rc) :
      ‖saddleMean d a τ₁ (cf w) - 1‖ ≤ 1 / 2 := by
    have hdist : ‖w - x‖ < Rc := by simpa [dist_eq_norm] using hw
    have hc : ‖cf w‖ ≤ 1 / 200 * Real.sqrt (d / π ^ 2) := by
      have e : ‖cf w‖ = ‖w - x‖ * ‖τ₁‖ := by
        simp only [cf, norm_neg, norm_mul, Complex.norm_I, one_mul]
      rw [e]
      calc
        ‖w - x‖ * ‖τ₁‖ ≤ Rc * ‖τ₁‖ := mul_le_mul_of_nonneg_right hdist.le hρ.le
        _ = K * ‖τ₁‖ / τ₁.re := by rw [hRc]; ring
        _ ≤ Real.sqrt (d / π ^ 2) / 200 := hKρ
        _ = _ := by ring
    have hdiff := norm_saddleMean_sub_le hd hr hρα hC (by norm_num) (by norm_num) hc
    rw [saddleMean_zero hd] at hdiff
    have hε := norm_saddleError_le_fifth hd him0 hs hA hr
    have hexp : Real.exp ((1 / 200 : ℝ) ^ 2) ≤ 3 := by
      have h1 : Real.exp ((1 / 200 : ℝ) ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.2 (by norm_num)
      have h2 := Real.exp_one_lt_d9
      linarith
    have h1 : 14 * (1 + 1 / 25) * (1 / 200) * Real.exp ((1 / 200 : ℝ) ^ 2) ≤ 1 / 4 := by
      nlinarith
    have htri : ‖saddleMean d a τ₁ (cf w) - 1‖ ≤
        ‖saddleMean d a τ₁ (cf w) - (1 + saddleError d a τ₁)‖ + ‖saddleError d a τ₁‖ := by
      have e : saddleMean d a τ₁ (cf w) - 1 =
          (saddleMean d a τ₁ (cf w) - (1 + saddleError d a τ₁)) + saddleError d a τ₁ := by ring
      rw [e]
      exact norm_add_le _ _
    linarith
  -- The mean is a bounded holomorphic function of `w`.
  let f : ℂ → ℂ := fun w => jensenUpper d ‖τ₁‖ w / (M * Complex.exp (cf w))
  have hfeq (w : ℂ) : f w = saddleMean d a τ₁ (cf w) := by
    have h := jensenUpper_eq_mean hd hτ₁ hG hs (w := w)
    rw [← hM] at h
    simp only [f, cf]
    rw [h]
    field_simp
  have hfdiff : Differentiable ℂ f := by
    have hcf : Differentiable ℂ cf := by
      simp only [cf]
      fun_prop
    exact (differentiable_jensenUpper d hρ).div (differentiable_const M |>.mul hcf.cexp)
      fun w => mul_ne_zero hM0 (Complex.exp_ne_zero _)
  have hfclose (w : ℂ) (hw : w ∈ Metric.ball (x : ℂ) Rc) : ‖f w - 1‖ ≤ 1 / 2 := by
    rw [hfeq]
    exact hmean w hw
  have hslit (w : ℂ) (hw : w ∈ Metric.ball (x : ℂ) Rc) : f w ∈ Complex.slitPlane := by
    left
    have h1 := hfclose w hw
    have h2 := Complex.abs_re_le_norm (f w - 1)
    have h3 := (abs_le.1 (h2.trans h1)).1
    simp only [sub_re, one_re] at h3
    linarith
  let h : ℂ → ℂ := fun w => Complex.log (f w)
  have hhdiff : DifferentiableOn ℂ h (Metric.ball (x : ℂ) Rc) := fun w hw =>
    ((hfdiff w).clog (hslit w hw)).differentiableWithinAt
  have hhb (w : ℂ) (hw : w ∈ Metric.ball (x : ℂ) Rc) : ‖h w‖ ≤ 3 / 4 := by
    have hz := hfclose w hw
    have hbound := Complex.norm_log_one_add_half_le_self hz
    have e : (1 : ℂ) + (f w - 1) = f w := by ring
    rw [e] at hbound
    simp only [h]
    linarith
  have hcenter : (x : ℂ) ∈ Metric.ball (x : ℂ) Rc := Metric.mem_ball_self hRcpos
  have hmaps : MapsTo h (Metric.ball (x : ℂ) Rc) (Metric.closedBall (h (x : ℂ)) 2) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 := hhb w hw
    have h2 := hhb (x : ℂ) hcenter
    have h3 := norm_sub_le (h w) (h (x : ℂ))
    linarith
  have hschwarz (w : ℂ) (hw : w ∈ Metric.ball (x : ℂ) Rc) :
      ‖h w - h (x : ℂ)‖ ≤ 2 / Rc * ‖w - x‖ := by
    have := Complex.dist_le_div_mul_dist_of_mapsTo_ball hhdiff hmaps hw
    simpa only [dist_eq_norm] using this
  -- Compare `x + it` and `x - it`.
  set wp : ℂ := (x : ℂ) + t * I with hwp
  set wm : ℂ := (x : ℂ) - t * I with hwm
  have hconj : (starRingEnd ℂ) wp = wm := by
    simp only [hwp, hwm, map_add, map_mul, conj_ofReal, conj_I]
    ring
  have htRc : t < Rc := by
    rw [hRc, lt_div_iff₀ hr0]
    exact htK
  have hnp : ‖wp - x‖ = t := by
    rw [hwp, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg ht0.le]
  have hnm : ‖wm - x‖ = t := by
    rw [hwm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg ht0.le]
  have hwpb : wp ∈ Metric.ball (x : ℂ) Rc := by
    rw [Metric.mem_ball, dist_eq_norm, hnp]
    exact htRc
  have hwmb : wm ∈ Metric.ball (x : ℂ) Rc := by
    rw [Metric.mem_ball, dist_eq_norm, hnm]
    exact htRc
  have hcp : (cf wp).re = t * τ₁.re := by
    have e : cf wp = (t : ℂ) * τ₁ := by
      simp only [cf, hwp, add_sub_cancel_left]
      ring_nf
      rw [I_sq]
      ring
    rw [e, Complex.re_ofReal_mul]
  have hcm : (cf wm).re = -(t * τ₁.re) := by
    have e : cf wm = -((t : ℂ) * τ₁) := by
      simp only [cf, hwm, sub_sub_cancel_left]
      ring_nf
      rw [I_sq]
      ring
    rw [e, neg_re, Complex.re_ofReal_mul]
  have hfne (w : ℂ) (hw : w ∈ Metric.ball (x : ℂ) Rc) : f w ≠ 0 :=
    Complex.slitPlane_ne_zero (hslit w hw)
  have hE (w : ℂ) (hw : w ∈ Metric.ball (x : ℂ) Rc) :
      ‖jensenUpper d ‖τ₁‖ w‖ = ‖M‖ * Real.exp ((cf w).re + (h w).re) := by
    have he : jensenUpper d ‖τ₁‖ w = M * Complex.exp (cf w) * f w := by
      simp only [f]
      field_simp
    have hf : ‖f w‖ = Real.exp (h w).re := by
      have := Complex.norm_exp (h w)
      simp only [h] at this ⊢
      rw [Complex.exp_log (hfne w hw)] at this
      exact this
    rw [he, norm_mul, norm_mul, Complex.norm_exp, hf, Real.exp_add]
    ring
  intro h0
  rw [eval_eq_jensenUpper_add_conj d _ hρ, hconj, add_eq_zero_iff_eq_neg] at h0
  have hnorm : ‖jensenUpper d ‖τ₁‖ wp‖ = ‖jensenUpper d ‖τ₁‖ wm‖ := by
    rw [h0, norm_neg, Complex.norm_conj]
  rw [hE wp hwpb, hE wm hwmb, hcp, hcm] at hnorm
  have hMn : ‖M‖ ≠ 0 := norm_ne_zero_iff.2 hM0
  have hexp := Real.exp_injective (mul_left_cancel₀ hMn hnorm)
  have hvar : ‖h wp - h wm‖ ≤ 4 * t / Rc := by
    have h1 := hschwarz wp hwpb
    have h2 := hschwarz wm hwmb
    rw [hnp] at h1
    rw [hnm] at h2
    have h3 : ‖h wp - h wm‖ ≤ ‖h wp - h (x : ℂ)‖ + ‖h wm - h (x : ℂ)‖ := by
      have e : h wp - h wm = (h wp - h (x : ℂ)) - (h wm - h (x : ℂ)) := by ring
      rw [e]
      exact norm_sub_le _ _
    calc
      _ ≤ 2 / Rc * t + 2 / Rc * t := h3.trans (add_le_add h1 h2)
      _ = _ := by ring
  have hre : (h wm).re - (h wp).re ≤ ‖h wp - h wm‖ := by
    have := Complex.abs_re_le_norm (h wp - h wm)
    rw [sub_re] at this
    have h1 := neg_abs_le ((h wp).re - (h wm).re)
    linarith
  have hgap : 2 * (t * τ₁.re) ≤ 4 * t / Rc := by linarith
  have hval : 4 * t / Rc = 4 * (t * τ₁.re) / K := by
    rw [hRc]
    field_simp
  rw [hval, le_div_iff₀ hKpos] at hgap
  have htr : 0 < t * τ₁.re := mul_pos ht0 hr0
  nlinarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.saddle_constants
#print axioms FiniteFreeProbability.norm_saddleMean_sub_le
#print axioms FiniteFreeProbability.saddle_far_integral_le
#print axioms FiniteFreeProbability.eval_ne_zero_of_far
#print axioms FiniteFreeProbability.eval_ne_zero_of_near
