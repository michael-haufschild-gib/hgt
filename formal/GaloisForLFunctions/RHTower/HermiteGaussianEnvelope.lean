import GaloisForLFunctions.RHTower.HermiteFunctionOrthogonality

/-!
# Gaussian envelope of the Hermite functions

Every Hermite function and every derivative of one is a polynomial times `e^{−ξ²/2}`.  Writing that
explicitly turns all the integrals of the trial-space computation into integrals of a polynomial
against a Gaussian: such a function is bounded, absolutely integrable, and therefore its truncated
integrals are bounded uniformly in the truncation.

The boundedness step is the only analytic input, and it is elementary: a continuous function that
tends to zero at both ends of the line is bounded.
-/

open Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

/-- A polynomial times a Gaussian is bounded on the line. -/
theorem exists_bound_polyEval_mul_gauss (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |p.eval x * Real.exp (-(b * x ^ 2))| ≤ C := by
  have hcont : Continuous fun x : ℝ => p.eval x * Real.exp (-(b * x ^ 2)) := by
    fun_prop
  have htop := tendsto_polyEval_mul_gauss_atTop p hb
  have hbot := tendsto_polyEval_mul_gauss_atBot p hb
  obtain ⟨R₁, hR₁⟩ :=
    (NormedAddGroup.tendsto_nhds_zero.1 htop 1 one_pos).exists_forall_of_atTop
  obtain ⟨R₂, hR₂⟩ :=
    (NormedAddGroup.tendsto_nhds_zero.1 hbot 1 one_pos).exists_forall_of_atBot
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := R₂) (b := R₁)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C₀ 1, le_trans zero_le_one (le_max_right _ _), fun x => ?_⟩
  rcases le_or_gt x R₂ with hx | hx
  · exact le_trans (le_of_lt (by simpa [Real.norm_eq_abs] using hR₂ x hx)) (le_max_right _ _)
  · rcases le_or_gt R₁ x with hx1 | hx1
    · exact le_trans (le_of_lt (by simpa [Real.norm_eq_abs] using hR₁ x hx1)) (le_max_right _ _)
    · have hmem : x ∈ Icc R₂ R₁ := ⟨hx.le, hx1.le⟩
      exact le_trans (by simpa [Real.norm_eq_abs] using hC₀ x hmem) (le_max_left _ _)

/-- A polynomial times a Gaussian is absolutely integrable. -/
theorem integrable_polyEval_mul_gauss (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => p.eval x * Real.exp (-(b * x ^ 2))) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_polyEval_mul_gauss p (b := b / 2) (by linarith)
  have hgint : Integrable (fun x : ℝ => C * Real.exp (-(b / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by linarith : (0 : ℝ) < b / 2)).const_mul C
  have hmeas : AEStronglyMeasurable (fun x : ℝ => p.eval x * Real.exp (-(b * x ^ 2)))
      volume := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  refine hgint.mono' hmeas (Filter.Eventually.of_forall fun x => ?_)
  have hsplit : p.eval x * Real.exp (-(b * x ^ 2))
      = (p.eval x * Real.exp (-(b / 2 * x ^ 2))) * Real.exp (-(b / 2) * x ^ 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [Real.norm_eq_abs, hsplit, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le

/-- The Gaussian envelope of a Hermite function. -/
theorem exists_poly_hermiteFun (n : ℕ) :
    ∃ p : Polynomial ℝ, ∀ x : ℝ, hermiteFun n x = p.eval x * Real.exp (-(1 / 2 * x ^ 2)) := by
  refine ⟨((Polynomial.hermite n).map (algebraMap ℤ ℝ)).comp
    (Polynomial.C (Real.sqrt 2) * Polynomial.X), fun x => ?_⟩
  rw [Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have haeval : Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite n)
      = ((Polynomial.hermite n).map (algebraMap ℤ ℝ)).eval (Real.sqrt 2 * x) := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hsq : (Real.sqrt 2 * x) ^ 2 = 2 * x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  show probHermiteFun n (Real.sqrt 2 * x) = _
  rw [probHermiteFun, haeval, hsq]
  congr 2
  ring

/-- The Gaussian envelope of the derivative of a Hermite function. -/
theorem exists_poly_deriv_hermiteFun (n : ℕ) :
    ∃ p : Polynomial ℝ,
      ∀ x : ℝ, deriv (hermiteFun n) x = p.eval x * Real.exp (-(1 / 2 * x ^ 2)) := by
  set q : Polynomial ℝ := (Polynomial.hermite n).map (algebraMap ℤ ℝ) with hq
  refine ⟨Polynomial.C (Real.sqrt 2) *
    ((Polynomial.derivative q - Polynomial.C (1 / 2 : ℝ) * Polynomial.X * q).comp
      (Polynomial.C (Real.sqrt 2) * Polynomial.X)), fun x => ?_⟩
  rw [deriv_hermiteFun_eq, deriv_probHermiteFun]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X,
    Polynomial.eval_sub]
  have hmap : ∀ y : ℝ, Polynomial.aeval y (Polynomial.hermite n) = q.eval y := by
    intro y
    rw [hq, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hmapd : ∀ y : ℝ, Polynomial.aeval y (Polynomial.derivative (Polynomial.hermite n))
      = (Polynomial.derivative q).eval y := by
    intro y
    rw [hq, Polynomial.derivative_map, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  have hsq : (Real.sqrt 2 * x) ^ 2 = 2 * x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [probHermiteFun, hmap, hmapd, hsq]
  have hexp : Real.exp (-(2 * x ^ 2 / 4)) = Real.exp (-(1 / 2 * x ^ 2)) := by
    congr 1
    ring
  rw [hexp]
  ring

/-- The absolute value of an interval integral never exceeds the total absolute mass. -/
theorem abs_intervalIntegral_le_integral_abs {f : ℝ → ℝ} (hf : Integrable f) (a b : ℝ) :
    |∫ x in a..b, f x| ≤ ∫ x : ℝ, |f x| := by
  have key : ∀ u v : ℝ, u ≤ v → |∫ x in u..v, f x| ≤ ∫ x : ℝ, |f x| := by
    intro u v huv
    rw [intervalIntegral.integral_of_le huv]
    have h1 : |∫ x in Ioc u v, f x| ≤ ∫ x in Ioc u v, |f x| := by
      simpa [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (μ := volume.restrict (Ioc u v)) f
    exact h1.trans
      (setIntegral_le_integral hf.abs (Filter.Eventually.of_forall fun x => abs_nonneg _))
  rcases le_total a b with hab | hab
  · exact key a b hab
  · rw [intervalIntegral.integral_symm b a, abs_neg]
    exact key b a hab

/-- **Uniform truncation bound.**  A function with a Gaussian envelope has all its truncated
integrals bounded by one constant, independent of the truncation. -/
theorem exists_uniform_bound_of_gaussEnvelope {f : ℝ → ℝ} (p : Polynomial ℝ) {b : ℝ} (hb : 0 < b)
    (hf : ∀ x : ℝ, f x = p.eval x * Real.exp (-(b * x ^ 2))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, |∫ x in u..v, f x| ≤ C := by
  have hint : Integrable f := by
    have h := integrable_polyEval_mul_gauss p hb
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    rw [hf x]
  exact ⟨∫ x : ℝ, |f x|, integral_nonneg fun x => abs_nonneg _,
    fun u v => abs_intervalIntegral_le_integral_abs hint u v⟩

/-- A product of two Hermite objects, against a polynomial weight, again has a Gaussian
envelope — now with exponent one. -/
theorem exists_poly_weighted_product {f g : ℝ → ℝ} (w : Polynomial ℝ)
    (hf : ∃ p : Polynomial ℝ, ∀ x : ℝ, f x = p.eval x * Real.exp (-(1 / 2 * x ^ 2)))
    (hg : ∃ q : Polynomial ℝ, ∀ x : ℝ, g x = q.eval x * Real.exp (-(1 / 2 * x ^ 2))) :
    ∃ r : Polynomial ℝ, ∀ x : ℝ,
      w.eval x * (f x * g x) = r.eval x * Real.exp (-(1 * x ^ 2)) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨w * p * q, fun x => ?_⟩
  rw [hp x, hq x]
  simp only [Polynomial.eval_mul]
  rw [show Real.exp (-(1 * x ^ 2))
      = Real.exp (-(1 / 2 * x ^ 2)) * Real.exp (-(1 / 2 * x ^ 2)) by
    rw [← Real.exp_add]; congr 1; ring]
  ring

/-- **Uniform truncation bound for the Hermite correction integrals.**  Any polynomial-weighted
product of Hermite functions and their derivatives has all its truncated integrals bounded by one
constant. -/
theorem exists_uniform_bound_hermite_weighted {f g : ℝ → ℝ} (w : Polynomial ℝ)
    (hf : ∃ p : Polynomial ℝ, ∀ x : ℝ, f x = p.eval x * Real.exp (-(1 / 2 * x ^ 2)))
    (hg : ∃ q : Polynomial ℝ, ∀ x : ℝ, g x = q.eval x * Real.exp (-(1 / 2 * x ^ 2))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, |∫ x in u..v, w.eval x * (f x * g x)| ≤ C := by
  obtain ⟨r, hr⟩ := exists_poly_weighted_product w hf hg
  exact exists_uniform_bound_of_gaussEnvelope r (by norm_num : (0 : ℝ) < 1) hr

end RHTower
