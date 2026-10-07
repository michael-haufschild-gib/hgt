import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorPolynomialBoundary
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorAxisPolynomial

/-!
# Polynomial Poisson boundary limits along arbitrary moving paths

Positive dilation reduces the moving point to 1. A finite binomial expansion
retains every logarithmic order, without any relation between approach rates.
-/

noncomputable section

open MeasureTheory Set Complex Filter Topology Polynomial

namespace RHTower.WeilHigherDenominator

private lemma tendsto_translated_polynomial_integral {α : Type*} {l : Filter α}
    {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (P : ℂ[X])
    {y : α → ℝ} (hy : Tendsto y l (𝓝[>] 0)) {u : α → ℂ} {u₀ : ℂ}
    (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun a =>
      (∫ t : ℝ, P.eval (u a + (Real.log |t| : ℂ)) *
        polarKernel ρ (1 + (y a : ℂ) * I) t) / (Real.log (y a) : ℂ))
      l (𝓝 (-2 * P.eval u₀)) := by
  have hypos : ∀ᶠ a in l, 0 < y a := hy.eventually self_mem_nhdsWithin
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    have he : -2 * P.eval u₀ + -2 * Q.eval u₀ = -2 * (P + Q).eval u₀ := by
      rw [eval_add]
      ring
    have hlim := hP.add hQ
    rw [he] at hlim
    apply hlim.congr'
    filter_upwards [hypos] with a ha
    have hInt (R : ℂ[X]) : Integrable (fun t : ℝ =>
        R.eval (u a + (Real.log |t| : ℂ)) * polarKernel ρ (1 + (y a : ℂ) * I) t) := by
      simpa only [eval_comp, eval_add, eval_C, eval_X] using
        (integrable_polynomial_polarKernel (z := 1 + (y a : ℂ) * I) hρ₀ hρ₁ (by simpa using ha)
          (R.comp (Polynomial.C (u a) + X)))
    simp only [eval_add, add_mul, integral_add (hInt P) (hInt Q), add_div]
  | monomial n c =>
    let A (a : α) (j : ℕ) : ℂ := c * u a ^ (n - j) * (n.choose j : ℂ)
    let B (j : ℕ) : ℂ := c * u₀ ^ (n - j) * (n.choose j : ℂ)
    have hm (j : ℕ) : Tendsto (fun a =>
        (∫ t : ℝ, (Real.log |t| : ℂ) ^ j * polarKernel ρ (1 + (y a : ℂ) * I) t) /
          (Real.log (y a) : ℂ)) l (𝓝 (-2 * (0 : ℂ) ^ j)) := by
      simpa only [eval_monomial, one_mul, Function.comp_def] using
        (polynomial_polarKernel_boundary_one hρ₀ hρ₁ (monomial j 1)).comp hy
    have hA (j : ℕ) : Tendsto (fun a => A a j) l (𝓝 (B j)) :=
      ((hu.pow (n - j)).const_mul c).mul_const (n.choose j : ℂ)
    have hlim := tendsto_finsetSum (Finset.range (n + 1)) fun j _ => (hA j).mul (hm j)
    have he : (∑ j ∈ Finset.range (n + 1), B j * (-2 * (0 : ℂ) ^ j)) =
        -2 * (monomial n c).eval u₀ := by
      rw [Finset.sum_eq_single 0]
      · simp only [B, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
          pow_zero, eval_monomial]
        ring
      · intro j _ hj
        simp [zero_pow hj]
      · intro h
        exact (h (by simp)).elim
    rw [he] at hlim
    apply hlim.congr'
    filter_upwards [hypos] with a ha
    have hz : 0 < (1 + (y a : ℂ) * I).im := by simpa using ha
    have hInt (j : ℕ) : Integrable (fun t : ℝ => A a j *
        ((Real.log |t| : ℂ) ^ j * polarKernel ρ (1 + (y a : ℂ) * I) t)) :=
      (integrable_logPolarKernel hρ₀ hρ₁ hz j).const_mul (A a j)
    have heval (t : ℝ) : (monomial n c).eval (u a + (Real.log |t| : ℂ)) *
        polarKernel ρ (1 + (y a : ℂ) * I) t =
        ∑ j ∈ Finset.range (n + 1), A a j *
          ((Real.log |t| : ℂ) ^ j * polarKernel ρ (1 + (y a : ℂ) * I) t) := by
      rw [eval_monomial, add_comm (u a), add_pow, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [A]
      ring
    calc
      _ = (∑ j ∈ Finset.range (n + 1), ∫ t : ℝ, A a j *
          ((Real.log |t| : ℂ) ^ j * polarKernel ρ (1 + (y a : ℂ) * I) t)) /
            (Real.log (y a) : ℂ) := by
        simp only [integral_const_mul, Finset.sum_div, mul_div_assoc]
      _ = (∫ t : ℝ, ∑ j ∈ Finset.range (n + 1), A a j *
          ((Real.log |t| : ℂ) ^ j * polarKernel ρ (1 + (y a : ℂ) * I) t)) /
            (Real.log (y a) : ℂ) := by
        rw [integral_finsetSum (Finset.range (n + 1)) (fun j _ => hInt j)]
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun t => (heval t).symm

/-- A positive scale converging to a positive number does not change the leading logarithm. -/
theorem tendsto_log_div_height {α : Type*} {l : Filter α} {x y : α → ℝ} {x₀ : ℝ}
    (hx₀ : 0 < x₀) (hx : Tendsto x l (𝓝 x₀)) (hy : Tendsto y l (𝓝[>] 0)) :
    Tendsto (fun a => Real.log (y a / x a) / Real.log (y a)) l (𝓝 1) := by
  have hxpos : ∀ᶠ a in l, 0 < x a := hx.eventually (eventually_gt_nhds hx₀)
  have hypos : ∀ᶠ a in l, 0 < y a := hy.eventually self_mem_nhdsWithin
  have hyone : ∀ᶠ a in l, y a < 1 := hy.eventually
    ((eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)
  have hlog := (Real.continuousAt_log hx₀.ne').tendsto.comp hx
  have hinv := (tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero).comp hy
  have hlim : Tendsto (fun a => 1 - Real.log (x a) * (Real.log (y a))⁻¹) l (𝓝 1) := by
    simpa only [mul_zero, sub_zero, Function.comp_def] using tendsto_const_nhds.sub (hlog.mul hinv)
  apply hlim.congr'
  filter_upwards [hxpos, hypos, hyone] with a hxa hya hya1
  rw [Real.log_div hya.ne' hxa.ne']
  have hne := (Real.log_neg hya hya1).ne
  field_simp

/-- Exact polynomial boundary coefficient along every path to a positive real point. -/
theorem polynomial_polarKernel_boundary_moving {α : Type*} {l : Filter α}
    {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (P : ℂ[X])
    {x y : α → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hx : Tendsto x l (𝓝 x₀)) (hy : Tendsto y l (𝓝[>] 0)) :
    Tendsto (fun a =>
      (∫ t : ℝ, P.eval (Real.log |t| : ℂ) * polarKernel ρ ((x a : ℂ) + (y a : ℂ) * I) t) /
        (Real.log (y a) : ℂ)) l (𝓝 (-2 * (x₀ : ℂ) ^ (-ρ) * P.eval (Real.log x₀ : ℂ))) := by
  have hxpos : ∀ᶠ a in l, 0 < x a := hx.eventually (eventually_gt_nhds hx₀)
  have hypos : ∀ᶠ a in l, 0 < y a := hy.eventually self_mem_nhdsWithin
  have hyone : ∀ᶠ a in l, y a < 1 := hy.eventually
    ((eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)
  have hquot : Tendsto (fun a => y a / x a) l (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [zero_div, Pi.div_apply] using
        (tendsto_nhds_of_tendsto_nhdsWithin hy).div hx hx₀.ne'
    · filter_upwards [hypos, hxpos] with a hya hxa
      exact div_pos hya hxa
  have hqone : ∀ᶠ a in l, y a / x a < 1 := hquot.eventually
    ((eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds)
  have hlog : Tendsto (fun a => (Real.log (x a) : ℂ)) l (𝓝 (Real.log x₀ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuousAt_log hx₀.ne').tendsto.comp hx)
  have hpow := (continuousAt_ofReal_cpow_const x₀ (-ρ) (Or.inr hx₀.ne')).tendsto.comp hx
  have hp := tendsto_translated_polynomial_integral hρ₀ hρ₁ P hquot hlog
  have hr : Tendsto (fun a => ((Real.log (y a / x a) / Real.log (y a) : ℝ) : ℂ))
      l (𝓝 (1 : ℂ)) := by
    simpa only [ofReal_one, Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_log_div_height hx₀ hx hy)
  have hlim := (hpow.mul hp).mul hr
  have he : (x₀ : ℂ) ^ (-ρ) * (-2 * P.eval (Real.log x₀ : ℂ)) * 1 =
      -2 * (x₀ : ℂ) ^ (-ρ) * P.eval (Real.log x₀ : ℂ) := by ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [hxpos, hypos, hyone, hqone] with a hxa hya hya1 hqa1
  have hxc : (x a : ℂ) ≠ 0 := ofReal_ne_zero.mpr hxa.ne'
  have hly : (Real.log (y a) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.log_neg hya hya1).ne
  have hlq : (Real.log (y a / x a) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.log_neg (div_pos hya hxa) hqa1).ne
  have hz : (x a : ℂ) + (y a : ℂ) * I =
      (x a : ℂ) * (1 + ((y a / x a : ℝ) : ℂ) * I) := by
    push_cast
    field_simp
  rw [hz, integral_polynomial_polarKernel_dilate ρ _ P hxa]
  simp only [Function.comp_def, ofReal_div]
  field_simp <;> ring

/-- No approach-rate assumption is needed for the actual polynomial Poisson mode. -/
theorem polynomialPolarMode_boundary_moving {α : Type*} {l : Filter α}
    {ρ : ℂ} (hρ₀ : 0 < ρ.re) (hρ₁ : ρ.re < 1) (P : ℂ[X])
    {x y : α → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hx : Tendsto x l (𝓝 x₀)) (hy : Tendsto y l (𝓝[>] 0)) :
    Tendsto (fun a => polynomialPolarMode ρ P ((x a : ℂ) + (y a : ℂ) * I) /
      ((Real.sqrt (y a) : ℂ) * (Real.log (y a) : ℂ)))
      l (𝓝 (-2 * (x₀ : ℂ) ^ (-ρ) * P.eval (Real.log x₀ : ℂ))) := by
  apply (polynomial_polarKernel_boundary_moving hρ₀ hρ₁ P hx₀ hx hy).congr'
  filter_upwards [hy.eventually self_mem_nhdsWithin] with a (ha : 0 < y a)
  have hs : (Real.sqrt (y a) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ha).ne'
  simp only [polynomialPolarMode, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one,
    I_re, mul_zero, add_zero, zero_add]
  field_simp

end RHTower.WeilHigherDenominator
