import GaloisForLFunctions.RHTower.ProlateDefectTransfer
import GaloisForLFunctions.RHTower.HermiteWeightedDerivativeIntegrable

/-!
# Discharging the pairing hypotheses from boundedness alone

Every weight appearing in the ladder pin and in the defect transfer is a polynomial multiple of a
Hermite function plus a polynomial multiple of its derivative, hence a polynomial times `e^{-ξ²/2}`.
Such a weight is integrable and vanishes at both ends of the line.  Consequently a profile whose
value and first two derivatives are merely *bounded* satisfies every integrability and boundary
hypothesis of `hermitePairing_pin` and `integral_prolateDefect_transfer_explicit`.
-/

noncomputable section

open MeasureTheory Filter Polynomial

open scoped Topology

namespace RHTower

/-! ## Hermite combinations are polynomial Gaussians -/

/-- A polynomial multiple of a Hermite function plus a polynomial multiple of its derivative is a
polynomial times a Gaussian. -/
theorem exists_poly_hermiteCombination (n : ℕ) (p q : Polynomial ℝ) :
    ∃ r : Polynomial ℝ, ∀ x : ℝ,
      p.eval x * hermiteFun n x + q.eval x * deriv (hermiteFun n) x
        = r.eval x * Real.exp (-(1 / 2 * x ^ (2 : ℕ))) := by
  obtain ⟨P, hP⟩ := exists_poly_hermiteFun n
  obtain ⟨Q, hQ⟩ := deriv_hermiteFun_poly n
  refine ⟨p * P + q * Q, fun x => ?_⟩
  rw [hP x, hQ x, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul]
  ring

theorem integrable_hermiteCombination (n : ℕ) (p q : Polynomial ℝ) :
    Integrable fun x : ℝ =>
      p.eval x * hermiteFun n x + q.eval x * deriv (hermiteFun n) x := by
  obtain ⟨r, hr⟩ := exists_poly_hermiteCombination n p q
  refine (integrable_polyEval_mul_gauss r (b := 1 / 2) (by norm_num)).congr ?_
  exact Filter.Eventually.of_forall fun x => (hr x).symm

theorem tendsto_hermiteCombination_atTop (n : ℕ) (p q : Polynomial ℝ) :
    Tendsto (fun x : ℝ =>
      p.eval x * hermiteFun n x + q.eval x * deriv (hermiteFun n) x) atTop (𝓝 0) := by
  obtain ⟨r, hr⟩ := exists_poly_hermiteCombination n p q
  refine (tendsto_polyEval_mul_gauss_atTop r (b := 1 / 2) (by norm_num)).congr ?_
  exact fun x => (hr x).symm

theorem tendsto_hermiteCombination_atBot (n : ℕ) (p q : Polynomial ℝ) :
    Tendsto (fun x : ℝ =>
      p.eval x * hermiteFun n x + q.eval x * deriv (hermiteFun n) x) atBot (𝓝 0) := by
  obtain ⟨r, hr⟩ := exists_poly_hermiteCombination n p q
  refine (tendsto_polyEval_mul_gauss_atBot r (b := 1 / 2) (by norm_num)).congr ?_
  exact fun x => (hr x).symm

/-! ## Bounded factors -/

/-- A bounded continuous factor preserves integrability. -/
theorem integrable_bounded_mul {B : ℝ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hB : ∀ x, |f x| ≤ B) (hg : Integrable g) : Integrable fun x => f x * g x := by
  refine Integrable.bdd_mul (c := B) hg hf.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [Real.norm_eq_abs]
  exact hB x

/-- A bounded factor preserves vanishing along any filter. -/
theorem tendsto_bounded_mul_zero {B : ℝ} {f g : ℝ → ℝ} {l : Filter ℝ}
    (hB : ∀ x, |f x| ≤ B) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg (f 0)) (hB 0)
  have hmaj : Tendsto (fun x => B * |g x|) l (𝓝 0) := by
    have h := (hg.abs).const_mul B
    simpa using h
  refine squeeze_zero_norm (fun x => ?_) hmaj
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)


/-! ## The individual weights -/

/-- Integrability and vanishing of a weight presented as a Hermite combination. -/
theorem hermiteWeight_package {g : ℝ → ℝ} (n : ℕ) (p q : Polynomial ℝ)
    (h : ∀ x, g x = p.eval x * hermiteFun n x + q.eval x * deriv (hermiteFun n) x) :
    Integrable g ∧ Tendsto g atTop (𝓝 0) ∧ Tendsto g atBot (𝓝 0) := by
  have hfun : g = fun x => p.eval x * hermiteFun n x + q.eval x * deriv (hermiteFun n) x :=
    funext h
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]; exact integrable_hermiteCombination n p q
  · rw [hfun]; exact tendsto_hermiteCombination_atTop n p q
  · rw [hfun]; exact tendsto_hermiteCombination_atBot n p q

theorem hermiteFun_package (n : ℕ) :
    Integrable (hermiteFun n) ∧ Tendsto (hermiteFun n) atTop (𝓝 0)
      ∧ Tendsto (hermiteFun n) atBot (𝓝 0) := by
  refine hermiteWeight_package n 1 0 fun x => ?_
  simp

theorem deriv_hermiteFun_package (n : ℕ) :
    Integrable (deriv (hermiteFun n)) ∧ Tendsto (deriv (hermiteFun n)) atTop (𝓝 0)
      ∧ Tendsto (deriv (hermiteFun n)) atBot (𝓝 0) := by
  refine hermiteWeight_package n 0 1 fun x => ?_
  simp

theorem deriv2_hermiteFun_package (n : ℕ) :
    Integrable (deriv (deriv (hermiteFun n)))
      ∧ Tendsto (deriv (deriv (hermiteFun n))) atTop (𝓝 0)
      ∧ Tendsto (deriv (deriv (hermiteFun n))) atBot (𝓝 0) := by
  refine hermiteWeight_package n (X ^ (2 : ℕ) - C (2 * (n : ℝ) + 1)) 0 fun x => ?_
  rw [deriv2_hermiteFun]
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_zero, zero_mul, add_zero]
  ring

theorem hermiteSqWeight_package (n : ℕ) :
    Integrable (hermiteSqWeight n) ∧ Tendsto (hermiteSqWeight n) atTop (𝓝 0)
      ∧ Tendsto (hermiteSqWeight n) atBot (𝓝 0) := by
  refine hermiteWeight_package n (X ^ (2 : ℕ)) 0 fun x => ?_
  rw [hermiteSqWeight]
  simp

theorem hermiteSqWeightDeriv_package (n : ℕ) :
    Integrable (hermiteSqWeightDeriv n) ∧ Tendsto (hermiteSqWeightDeriv n) atTop (𝓝 0)
      ∧ Tendsto (hermiteSqWeightDeriv n) atBot (𝓝 0) := by
  refine hermiteWeight_package n (C 2 * X) (X ^ (2 : ℕ)) fun x => ?_
  rw [hermiteSqWeightDeriv]
  simp

theorem hermiteSqWeightSecondDeriv_package (n : ℕ) :
    Integrable (hermiteSqWeightSecondDeriv n)
      ∧ Tendsto (hermiteSqWeightSecondDeriv n) atTop (𝓝 0)
      ∧ Tendsto (hermiteSqWeightSecondDeriv n) atBot (𝓝 0) := by
  refine hermiteWeight_package n (C 2 + X ^ (2 : ℕ) * (X ^ (2 : ℕ) - C (2 * (n : ℝ) + 1))) (C 4 * X)
    fun x => ?_
  rw [hermiteSqWeightSecondDeriv, deriv2_hermiteFun]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  ring

theorem hermiteLinWeight_package (n : ℕ) :
    Integrable (hermiteLinWeight n) ∧ Tendsto (hermiteLinWeight n) atTop (𝓝 0)
      ∧ Tendsto (hermiteLinWeight n) atBot (𝓝 0) := by
  refine hermiteWeight_package n (C 2 * X) 0 fun x => ?_
  rw [hermiteLinWeight]
  simp

theorem hermiteLinWeightDeriv_package (n : ℕ) :
    Integrable (hermiteLinWeightDeriv n) ∧ Tendsto (hermiteLinWeightDeriv n) atTop (𝓝 0)
      ∧ Tendsto (hermiteLinWeightDeriv n) atBot (𝓝 0) := by
  refine hermiteWeight_package n (C 2) (C 2 * X) fun x => ?_
  rw [hermiteLinWeightDeriv]
  simp

/-- The explicit weight of the transferred defect pairing. -/
def prolateDefectWeight (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 : ℕ) * (x ^ (2 : ℕ) - 2 * n - 1) * hermiteFun n x + 2 * x * deriv (hermiteFun n) x

theorem prolateDefectWeight_package (n : ℕ) :
    Integrable (prolateDefectWeight n) ∧ Tendsto (prolateDefectWeight n) atTop (𝓝 0)
      ∧ Tendsto (prolateDefectWeight n) atBot (𝓝 0) := by
  refine hermiteWeight_package n (X ^ (2 : ℕ) * (X ^ (2 : ℕ) - C (2 * (n : ℝ) + 1))) (C 2 * X) fun x => ?_
  rw [prolateDefectWeight]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C]
  ring


/-! ## The pin with hypotheses discharged -/

/-- **The ladder pin from boundedness alone.**  A profile whose value and first two derivatives are
bounded, and which satisfies the exact prolate-to-oscillator identity, sits at distance
`|⟨u, W_n⟩| / (|c| · |⟨u, φ_n⟩|)` from the `n`-th rung. -/
theorem abs_sub_ladder_mul_eq_of_bounded {u u' u'' : ℝ → ℝ} {c μ B B₂ : ℝ} (n : ℕ) (hc : c ≠ 0)
    (hcu : Continuous u) (hcu' : Continuous u') (hcu'' : Continuous u'')
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hB : ∀ x, |u x| ≤ B) (hB' : ∀ x, |u' x| ≤ B₂) (hB'' : ∀ x, |u'' x| ≤ B₂)
    (heq : ∀ x, hermiteSLAction u x + μ * u x = (x ^ (2 : ℕ) * u'' x + 2 * x * u' x) / c) :
    |μ - (2 * n + 1)| * |∫ x, u x * hermiteFun n x|
      = |∫ x, u x * prolateDefectWeight n x| / |c| := by
  obtain ⟨hHint, hHtop, hHbot⟩ := hermiteFun_package n
  obtain ⟨hDint, hDtop, hDbot⟩ := deriv_hermiteFun_package n
  obtain ⟨hD2int, hD2top, hD2bot⟩ := deriv2_hermiteFun_package n
  obtain ⟨hSint, hStop, hSbot⟩ := hermiteSqWeight_package n
  obtain ⟨hSDint, hSDtop, hSDbot⟩ := hermiteSqWeightDeriv_package n
  obtain ⟨hS2int, hS2top, hS2bot⟩ := hermiteSqWeightSecondDeriv_package n
  obtain ⟨hLint, hLtop, hLbot⟩ := hermiteLinWeight_package n
  obtain ⟨hLDint, hLDtop, hLDbot⟩ := hermiteLinWeightDeriv_package n
  have hintL : Integrable fun x => u'' x * hermiteFun n x :=
    integrable_bounded_mul hcu'' hB'' hHint
  have hintR : Integrable fun x => u x * deriv (deriv (hermiteFun n)) x :=
    integrable_bounded_mul hcu hB hD2int
  have hintU : Integrable fun x => u x * hermiteFun n x :=
    integrable_bounded_mul hcu hB hHint
  have hintSq : Integrable fun x => x ^ (2 : ℕ) * (u x * hermiteFun n x) := by
    refine (integrable_bounded_mul hcu hB hSint).congr ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [hermiteSqWeight]
    ring
  have hiA : Integrable fun x => u'' x * hermiteSqWeight n x :=
    integrable_bounded_mul hcu'' hB'' hSint
  have hiB : Integrable fun x => u x * hermiteSqWeightSecondDeriv n x :=
    integrable_bounded_mul hcu hB hS2int
  have hiC : Integrable fun x => u' x * hermiteLinWeight n x :=
    integrable_bounded_mul hcu' hB' hLint
  have hiD : Integrable fun x => u x * hermiteLinWeightDeriv n x :=
    integrable_bounded_mul hcu hB hLDint
  have hplus : Tendsto (fun x => u' x * hermiteFun n x - u x * deriv (hermiteFun n) x)
      atTop (𝓝 0) := by
    have h := (tendsto_bounded_mul_zero hB' hHtop).sub (tendsto_bounded_mul_zero hB hDtop)
    simpa using h
  have hminus : Tendsto (fun x => u' x * hermiteFun n x - u x * deriv (hermiteFun n) x)
      atBot (𝓝 0) := by
    have h := (tendsto_bounded_mul_zero hB' hHbot).sub (tendsto_bounded_mul_zero hB hDbot)
    simpa using h
  have hWplus : Tendsto (fun x => u' x * hermiteSqWeight n x - u x * hermiteSqWeightDeriv n x)
      atTop (𝓝 0) := by
    have h := (tendsto_bounded_mul_zero hB' hStop).sub (tendsto_bounded_mul_zero hB hSDtop)
    simpa using h
  have hWminus : Tendsto (fun x => u' x * hermiteSqWeight n x - u x * hermiteSqWeightDeriv n x)
      atBot (𝓝 0) := by
    have h := (tendsto_bounded_mul_zero hB' hSbot).sub (tendsto_bounded_mul_zero hB hSDbot)
    simpa using h
  have hPplus : Tendsto (fun x => u x * hermiteLinWeight n x) atTop (𝓝 0) :=
    tendsto_bounded_mul_zero hB hLtop
  have hPminus : Tendsto (fun x => u x * hermiteLinWeight n x) atBot (𝓝 0) :=
    tendsto_bounded_mul_zero hB hLbot
  have hpin := hermitePairing_pin (u := u) (u' := u') (u'' := u'')
    (D := fun x => (x ^ (2 : ℕ) * u'' x + 2 * x * u' x) / c) (μ := μ) n hu hu' heq
    hintL hintR hintSq hintU hplus hminus
  have htransfer := integral_prolateDefect_transfer_explicit n hu hu' hiA hiB hiC hiD
    hWplus hWminus hPplus hPminus
  have hside := prolateLadder_pin_hermiteSide (u := u) (u' := u') (u'' := u'')
    (D := fun x => (x ^ (2 : ℕ) * u'' x + 2 * x * u' x) / c) (c := c) (μ := μ) n hc hpin
    (fun x => rfl) htransfer hiA hiC
  have hweight : (∫ x, u x * (x ^ (2 : ℕ) * (x ^ (2 : ℕ) - 2 * n - 1) * hermiteFun n x
        + 2 * x * deriv (hermiteFun n) x))
      = ∫ x, u x * prolateDefectWeight n x := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [prolateDefectWeight]
  rw [hweight] at hside
  have habs := congrArg abs hside
  rw [abs_mul, abs_div] at habs
  exact habs


/-- A bounded factor pulls out of an absolute pairing. -/
theorem abs_integral_bounded_mul_le {B : ℝ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hB : ∀ x, |f x| ≤ B) (hg : Integrable g) :
    |∫ x, f x * g x| ≤ B * ∫ x, |g x| := by
  have h1 : |∫ x, f x * g x| ≤ ∫ x, |f x * g x| := by
    have h := MeasureTheory.norm_integral_le_integral_norm (μ := volume)
      (f := fun x => f x * g x)
    simpa [Real.norm_eq_abs] using h
  have h2 : (∫ x, |f x * g x|) ≤ ∫ x, B * |g x| := by
    refine MeasureTheory.integral_mono (integrable_bounded_mul hf hB hg).abs
      (hg.abs.const_mul B) fun x => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
  rw [MeasureTheory.integral_const_mul] at h2
  linarith

/-- **The ladder pin as an inequality.**  The distance to the `n`-th rung is at most the profile
bound times the fixed weight mass, divided by the bandwidth and the pairing. -/
theorem abs_sub_ladder_le_of_bounded {u u' u'' : ℝ → ℝ} {c μ B B₂ : ℝ} (n : ℕ) (hc : c ≠ 0)
    (hcu : Continuous u) (hcu' : Continuous u') (hcu'' : Continuous u'')
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (u'' x) x)
    (hB : ∀ x, |u x| ≤ B) (hB' : ∀ x, |u' x| ≤ B₂) (hB'' : ∀ x, |u'' x| ≤ B₂)
    (heq : ∀ x, hermiteSLAction u x + μ * u x = (x ^ (2 : ℕ) * u'' x + 2 * x * u' x) / c)
    (hne : (∫ x, u x * hermiteFun n x) ≠ 0) :
    |μ - (2 * n + 1)|
      ≤ B * (∫ x, |prolateDefectWeight n x|)
          / (|c| * |∫ x, u x * hermiteFun n x|) := by
  have hA : (0 : ℝ) < |∫ x, u x * hermiteFun n x| := abs_pos.2 hne
  have hcpos : (0 : ℝ) < |c| := abs_pos.2 hc
  have hkey := abs_sub_ladder_mul_eq_of_bounded (B := B) (B₂ := B₂) n hc hcu hcu' hcu'' hu hu'
    hB hB' hB'' heq
  have hbnd : |∫ x, u x * prolateDefectWeight n x| ≤ B * ∫ x, |prolateDefectWeight n x| :=
    abs_integral_bounded_mul_le hcu hB (prolateDefectWeight_package n).1
  rw [le_div_iff₀ (by positivity)]
  have hmul : |μ - (2 * n + 1)| * |∫ x, u x * hermiteFun n x| * |c|
      = |∫ x, u x * prolateDefectWeight n x| := by
    rw [hkey]
    field_simp
  nlinarith [hmul, hbnd, hcpos, hA]

end RHTower

end
