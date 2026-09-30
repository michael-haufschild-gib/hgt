import GaloisForLFunctions.RHTower.ZetaNotchAnalyticPairing

/-!
# The mixed `|ζ|²` notch pairing at the critical abscissa

The mixed test `G = Ω_L Q W` has double poles at `z = ±i/2`, from the factor `(2/(¼+z²))²` of `W`.
On the line `|Im z| = ½ − η` the factor is `≤ 16/(Re z² + η²)`
(`norm_two_div_quarter_add_sq_sq_le`), whose line mass is `16π/η`. Shifting the transform integral
to that line with `η = 1/(4 + |w|)` gives linear-exponential decay
(`exists_norm_integral_mixTest_mul_cexp_le`):

`‖∫ G(x) e^{−iwx} dx‖ ≤ B (1 + |w|) e^{−|w|/2}`.

Hence the pairing inequality `Σ_n v(n) Re M_Ω(log n) ≤ 0` holds as soon as
`Σ_n |v(n)| (1 + log n) n^{−1/2} < ∞` (`sum_mul_re_mixMoment_nonpos_crit`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry
open FourierTransform
open scoped ComplexConjugate

namespace RHTower.ZetaNotch

/-- `‖Γℝ(½ + iz)^{−1}‖ ≤ C e^{π|Re z|/2}` on the closed strip `|Im z| ≤ 1/2`. -/
theorem exists_norm_inv_Gammaℝ_half_add_le_closed :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖(Complex.Gammaℝ (1 / 2 + z * I))⁻¹‖ ≤ C * Real.exp (Real.pi * |z.re| / 2) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_bound_norm_inv_Gammaℝ 0 1 (by norm_num)
  have hG : Differentiable ℂ fun s : ℂ => (Complex.Gammaℝ s)⁻¹ := Complex.differentiable_Gammaℝ_inv
  obtain ⟨M, hM0, hM⟩ := exists_bound_on_box (f := fun z : ℂ => (Complex.Gammaℝ (1 / 2 + z * I))⁻¹)
    (a := 2) (c := 1 / 2) fun z _ _ => (hG.differentiableAt.comp z (by fun_prop)).continuousAt
  refine ⟨max C₁ M, le_max_of_le_left hC₁0, fun z hz => ?_⟩
  have hre : (1 / 2 + z * I).re = 1 / 2 - z.im := by simp; ring
  have him : (1 / 2 + z * I).im = z.re := by simp
  have he : 1 ≤ Real.exp (Real.pi * |z.re| / 2) := Real.one_le_exp (by positivity)
  rcases le_or_gt 2 |z.re| with h2 | h2
  · have h := hC₁ (1 / 2 + z * I) (by rw [hre]; linarith [(abs_le.mp hz).2])
      (by rw [hre]; linarith [(abs_le.mp hz).1]) (by rw [him]; exact h2)
    rw [him] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · calc ‖(Complex.Gammaℝ (1 / 2 + z * I))⁻¹‖ ≤ M := hM z h2.le hz
      _ ≤ max C₁ M * 1 := by rw [mul_one]; exact le_max_right _ _
      _ ≤ max C₁ M * Real.exp (Real.pi * |z.re| / 2) :=
          mul_le_mul_of_nonneg_left he (le_max_of_le_left hC₁0)

/-- Near the double pole: on `|Im z| = 1/2 − η` with `0 < η ≤ 1/4`,
`‖(2/(¼+z²))²‖ ≤ 16/(Re z² + η²)`. -/
theorem norm_two_div_quarter_add_sq_sq_le {z : ℂ} {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 4)
    (hz : |z.im| = 1 / 2 - η) :
    ‖(2 / (1 / 4 + z ^ 2)) ^ 2‖ ≤ 16 / (z.re ^ 2 + η ^ 2) := by
  set x := z.re with hx
  set y := z.im with hy
  have hy2 : y ^ 2 = (1 / 2 - η) ^ 2 := by rw [← sq_abs, hz]
  have hre : (1 / 4 + z ^ 2).re = 1 / 4 + x ^ 2 - y ^ 2 := re_quarter_add_sq z
  have him : (1 / 4 + z ^ 2).im = 2 * x * y := by simp [sq]; ring
  have hA : 3 * η / 4 ≤ 1 / 4 + x ^ 2 - y ^ 2 := by nlinarith [sq_nonneg x]
  have hA2 : (3 * η / 4) ^ 2 ≤ (1 / 4 + x ^ 2 - y ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hA 2
  have hy16 : 1 / 16 ≤ y ^ 2 := by rw [hy2]; nlinarith
  have hB : x ^ 2 / 4 ≤ (2 * x * y) ^ 2 := by nlinarith [sq_nonneg x]
  have hN : (x ^ 2 + η ^ 2) / 4 ≤ ‖(1 / 4 : ℂ) + z ^ 2‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    nlinarith
  have hpos : 0 < x ^ 2 + η ^ 2 := by positivity
  have hN0 : 0 < ‖(1 / 4 : ℂ) + z ^ 2‖ ^ 2 := by linarith
  rw [norm_pow, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num, div_pow,
    div_le_div_iff₀ hN0 hpos]
  nlinarith

/-- **The mixed test near its double poles**: on `|Im z| = 1/2 − η`,
`‖G(z)‖ ≤ B e^{−|Re z|}/(Re z² + η²)`. -/
theorem exists_norm_mixTest_le_near_pole (L : ℝ) {Q : ℂ → ℂ} {CQ : ℝ}
    (hQb : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Q z‖ ≤ CQ) :
    ∃ B, 0 ≤ B ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 4 → ∀ z : ℂ, |z.im| = 1 / 2 - η →
      ‖mixTest L Q z‖ ≤ B * (Real.exp (-|z.re|) / (z.re ^ 2 + η ^ 2)) := by
  obtain ⟨CΓ, hCΓ0, hCΓ⟩ := exists_norm_inv_Gammaℝ_half_add_le_closed
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hQb 0 (by norm_num))
  refine ⟨Real.exp 1 * (4 * Real.exp (L ^ 2)) * CQ * (16 * (CΓ * CΓ)) * Real.exp 56,
    by positivity, fun η hη0 hη z hz => ?_⟩
  have hzi : |z.im| ≤ 1 / 2 := by rw [hz]; linarith
  have h1 := norm_mixWindow_le_gauss L hzi
  have h2 := hQb z hzi
  have h3 := hCΓ z hzi
  have h4 := hCΓ (-z) (by rw [Complex.neg_im, abs_neg]; exact hzi)
  rw [Complex.neg_re, abs_neg, show (1 / 2 : ℂ) + -z * I = 1 / 2 - z * I by ring] at h4
  have h5 := norm_two_div_quarter_add_sq_sq_le hη0 hη hz
  have h6 := gauss_mul_exp_pi_le z.re
  have hpos : 0 < z.re ^ 2 + η ^ 2 := by positivity
  have hexp : Real.exp (Real.pi * |z.re| / 2) * Real.exp (Real.pi * |z.re| / 2) =
      Real.exp (Real.pi * |z.re|) := by rw [← Real.exp_add]; ring_nf
  have hW : ‖gammaWeightC z‖ ≤ 16 / (z.re ^ 2 + η ^ 2) * ((CΓ * CΓ) * Real.exp (Real.pi * |z.re|)) := by
    unfold gammaWeightC
    rw [norm_mul, norm_mul, ← hexp]
    calc ‖(2 / (1 / 4 + z ^ 2)) ^ 2‖ * (‖(Complex.Gammaℝ (1 / 2 + z * I))⁻¹‖ *
          ‖(Complex.Gammaℝ (1 / 2 - z * I))⁻¹‖)
        ≤ 16 / (z.re ^ 2 + η ^ 2) * ((CΓ * Real.exp (Real.pi * |z.re| / 2)) *
            (CΓ * Real.exp (Real.pi * |z.re| / 2))) :=
          mul_le_mul h5 (mul_le_mul h3 h4 (norm_nonneg _) (by positivity)) (by positivity)
            (by positivity)
      _ = _ := by ring
  unfold mixTest
  rw [norm_mul, norm_mul]
  calc ‖mixWindow L z‖ * ‖Q z‖ * ‖gammaWeightC z‖
      ≤ (Real.exp 1 * (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * z.re ^ 2)))) * CQ *
          (16 / (z.re ^ 2 + η ^ 2) * ((CΓ * CΓ) * Real.exp (Real.pi * |z.re|))) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) hW (norm_nonneg _)
          (by positivity)
    _ = Real.exp 1 * (4 * Real.exp (L ^ 2)) * CQ * (16 * (CΓ * CΓ)) *
          ((Real.exp (-(2 / 25) * z.re ^ 2) * Real.exp (Real.pi * |z.re|)) /
            (z.re ^ 2 + η ^ 2)) := by ring
    _ ≤ Real.exp 1 * (4 * Real.exp (L ^ 2)) * CQ * (16 * (CΓ * CΓ)) *
          ((Real.exp 56 * Real.exp (-|z.re|)) / (z.re ^ 2 + η ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- `∫ (x² + η²)^{−1} dx = π/η`, in the scaled form `η^{−2} (1 + (x/η)²)^{−1}`. -/
theorem integral_inv_sq_add_sq {η : ℝ} (hη : 0 < η) :
    Integrable (fun x : ℝ => (η ^ 2)⁻¹ * (1 + (x / η) ^ 2)⁻¹) ∧
      ∫ x : ℝ, (η ^ 2)⁻¹ * (1 + (x / η) ^ 2)⁻¹ = Real.pi / η := by
  refine ⟨(integrable_inv_one_add_sq.comp_div hη.ne').const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_div (fun x : ℝ => (1 + x ^ 2)⁻¹) η,
    integral_univ_inv_one_add_sq, abs_of_pos hη, smul_eq_mul]
  field_simp

theorem inv_sq_add_sq_eq {η : ℝ} (hη : 0 < η) (x : ℝ) :
    (x ^ 2 + η ^ 2)⁻¹ = (η ^ 2)⁻¹ * (1 + (x / η) ^ 2)⁻¹ := by
  field_simp
  ring

/-- The transform of the mixed test is conjugation-symmetric: `G` is real on the real line. -/
theorem norm_integral_mixTest_mul_cexp_neg (L : ℝ) {Q : ℂ → ℂ} {q : ℝ → ℝ}
    (hQq : ∀ t : ℝ, Q t = q t) (w : ℝ) :
    ‖∫ x : ℝ, mixTest L Q x * Complex.exp (-((-w : ℝ) * x) * I)‖ =
      ‖∫ x : ℝ, mixTest L Q x * Complex.exp (-(w * x) * I)‖ := by
  have e : (∫ x : ℝ, mixTest L Q x * Complex.exp (-((-w : ℝ) * x) * I)) =
      conj (∫ x : ℝ, mixTest L Q x * Complex.exp (-(w * x) * I)) := by
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [map_mul, mixTest_ofReal L hQq, Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
  rw [e, Complex.norm_conj]

/-- **Linear-exponential decay of the transform of the mixed test**:
`‖∫ G(x) e^{−iwx} dx‖ ≤ B (1 + |w|) e^{−|w|/2}`. -/
theorem exists_norm_integral_mixTest_mul_cexp_le (L : ℝ) {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q)
    {CQ : ℝ} (hQb : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Q z‖ ≤ CQ) {q : ℝ → ℝ}
    (hQq : ∀ t : ℝ, Q t = q t) :
    ∃ B, 0 ≤ B ∧ ∀ w : ℝ, ‖∫ x : ℝ, mixTest L Q x * Complex.exp (-(w * x) * I)‖ ≤
      B * ((1 + |w|) * Real.exp (-(1 / 2 * |w|))) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_mixTest_le_near_pole L hQb
  refine ⟨4 * Real.pi * Real.exp 1 * B, by positivity, ?_⟩
  -- the case `w ≥ 0`
  have hpos : ∀ w : ℝ, 0 ≤ w → ‖∫ x : ℝ, mixTest L Q x * Complex.exp (-(w * x) * I)‖ ≤
      4 * Real.pi * Real.exp 1 * B * ((1 + w) * Real.exp (-(1 / 2 * w))) := by
    intro w hw
    set η : ℝ := (4 + w)⁻¹ with hη
    have hη0 : 0 < η := inv_pos.mpr (by linarith)
    have hη4 : η ≤ 1 / 4 := by rw [hη, inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    set c : ℝ := 1 / 2 - η with hc
    have hc0 : 0 ≤ c := by rw [hc]; linarith
    have hc2 : c < 1 / 2 := by rw [hc]; linarith
    obtain ⟨CG, -, hGb⟩ := exists_norm_mixTest_le L hc0 hc2 (fun z hz => hQb z (by linarith))
    have hGd : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ (mixTest L Q) z := fun z hz =>
      differentiableAt_mixTest L hQd (by linarith)
    set m : ℝ → ℝ := fun x => B * ((η ^ 2)⁻¹ * (1 + (x / η) ^ 2)⁻¹) with hm
    obtain ⟨hmi, hmint⟩ := integral_inv_sq_add_sq hη0
    have hGm : ∀ x : ℝ, ‖mixTest L Q ((x : ℂ) - (c : ℂ) * I)‖ ≤ m x := by
      intro x
      have hz : |((x : ℂ) - (c : ℂ) * I).im| = 1 / 2 - η := by
        simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_sub, abs_neg]
        rw [abs_of_nonneg hc0]
      have h := hB η hη0 hη4 _ hz
      have hre : ((x : ℂ) - (c : ℂ) * I).re = x := by simp
      rw [hre] at h
      refine h.trans (mul_le_mul_of_nonneg_left ?_ hB0)
      rw [← inv_sq_add_sq_eq hη0, div_eq_mul_inv]
      have : 0 < x ^ 2 + η ^ 2 := by positivity
      exact mul_le_of_le_one_left (by positivity) (Real.exp_le_one_iff.mpr (by
        linarith [abs_nonneg x]))
    have h := norm_integral_mul_cexp_le_lower hc0 hGd hGb w (hmi.const_mul B) hGm
    rw [show (∫ x, m x) = B * (Real.pi / η) by rw [hm, integral_const_mul, hmint]] at h
    refine h.trans ?_
    have hηw : η * w ≤ 1 := by
      rw [hη, inv_mul_le_iff₀ (by linarith)]; linarith
    have hexp : Real.exp (-(c * w)) ≤ Real.exp 1 * Real.exp (-(1 / 2 * w)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by rw [hc]; nlinarith)
    have hinv : Real.pi / η ≤ 4 * Real.pi * (1 + w) := by
      rw [hη, div_inv_eq_mul]; nlinarith [Real.pi_pos]
    calc Real.exp (-(c * w)) * (B * (Real.pi / η))
        ≤ (Real.exp 1 * Real.exp (-(1 / 2 * w))) * (B * (4 * Real.pi * (1 + w))) :=
          mul_le_mul hexp (mul_le_mul_of_nonneg_left hinv hB0) (by positivity) (by positivity)
      _ = 4 * Real.pi * Real.exp 1 * B * ((1 + w) * Real.exp (-(1 / 2 * w))) := by ring
  intro w
  rcases le_or_gt 0 w with hw | hw
  · rw [abs_of_nonneg hw]; exact hpos w hw
  · have h := hpos (-w) (by linarith)
    rw [norm_integral_mixTest_mul_cexp_neg L hQq w] at h
    rw [abs_of_neg hw]
    exact h

/-- **The pairing inequality for the mixed notch at the critical abscissa.** If `−ψ_v` is positive
definite and `Σ_n |v(n)| (1 + log n) n^{−1/2} < ∞`, then `Σ_n v(n) Re M_Ω(log n) ≤ 0`. -/
theorem sum_mul_re_mixMoment_nonpos_crit {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) * (n : ℝ) ^ (-(1 / 2 : ℝ))))
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (L : ℝ) {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) {CQ : ℝ}
    (hQb : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Q z‖ ≤ CQ) {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t)
    (hq0 : ∀ t, 0 ≤ q t) :
    ∑' n : ℕ, v n * (mixMoment L q (Real.log n)).re ≤ 0 := by
  have hcont := RHTower.WeilRegular.continuous_nullPotential_of_log hv0 hA ha
  obtain ⟨σ, hσf, hσ⟩ := exists_charFun_eq_of_positiveDefinite hPD
    (Complex.continuous_ofReal.comp hcont.neg)
  set G : ℂ → ℂ := mixTest L Q with hG
  set g : ℝ → ℂ := fun ξ => G ((2 * Real.pi * ξ : ℝ) : ℂ) with hg
  obtain ⟨CG, hCG0, hGb⟩ := exists_norm_mixTest_le L le_rfl (by norm_num : (0 : ℝ) < 1 / 2)
    (fun z hz => hQb z (by linarith))
  have hGc : Continuous fun t : ℝ => G t := continuous_mixTest_ofReal L hQd
  have hgc : Continuous g := hGc.comp (by fun_prop)
  have hgb : ∀ ξ : ℝ, ‖g ξ‖ ≤ CG * Real.exp (-(1 * |ξ|)) := by
    intro ξ
    have h := hGb ((2 * Real.pi * ξ : ℝ) : ℂ) (by simp)
    rw [Complex.ofReal_re] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCG0)
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), one_mul]
    have := Real.pi_gt_three
    nlinarith [abs_nonneg ξ]
  have hgi : Integrable g :=
    ((integrable_exp_neg_mul_abs' one_pos).const_mul CG).mono' hgc.aestronglyMeasurable
      (Eventually.of_forall hgb)
  obtain ⟨B, hB0, hBt⟩ := exists_norm_integral_mixTest_mul_cexp_le L hQd hQb hQq
  have hdec : ∀ w, ‖𝓕 g w‖ ≤ ((2 * Real.pi)⁻¹ * B) * ((1 + |w|) * Real.exp (-(1 / 2 * |w|))) := by
    intro w
    rw [RHTower.WeilExcess.fourier_eq_integral]
    set h : ℝ → ℂ := fun t => G t * Complex.exp (-(w * t) * I) with hh
    have e : (fun ξ : ℝ => Complex.exp (-(2 * Real.pi * ξ * w : ℝ) * I) * g ξ) =
        fun ξ : ℝ => h (2 * Real.pi * ξ) := by
      funext ξ
      rw [hh, hg]
      simp only
      rw [show -((2 * Real.pi * ξ * w : ℝ) : ℂ) * I = -((w : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ)) * I by
        push_cast; ring]
      ring
    rw [e, Measure.integral_comp_mul_left h (2 * Real.pi), norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < |(2 * Real.pi)⁻¹|),
      abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)]
    calc (2 * Real.pi)⁻¹ * ‖∫ t, h t‖
        ≤ (2 * Real.pi)⁻¹ * (B * ((1 + |w|) * Real.exp (-(1 / 2 * |w|)))) :=
          mul_le_mul_of_nonneg_left (hBt w) (by positivity)
      _ = _ := by ring
  have hGb1 : ∀ t : ℝ, ‖G t‖ ≤ CG := fun t => by
    have h := hGb t (by simp)
    exact h.trans (mul_le_of_le_one_right hCG0 (Real.exp_le_one_iff.mpr (by
      simp only [Complex.ofReal_re]; linarith [abs_nonneg t])))
  exact sum_mul_re_mixMoment_nonpos_of_pairing L hQq hq0 σ hGc hGb1
    (RHTower.WeilRegular.nullPotential_pairing_linexp hv0 (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num) hs σ hσ hgc hgi hdec)

end RHTower.ZetaNotch
