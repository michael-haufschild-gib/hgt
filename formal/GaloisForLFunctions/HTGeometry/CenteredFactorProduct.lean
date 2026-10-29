import GaloisForLFunctions.HTGeometry.FiniteRegularizedDeterminant
import GaloisForLFunctions.HTGeometry.WeierstrassFactor
import GaloisForLFunctions.HTGeometry.LogDerivativeSaddle

/-!
# Quadratic errors of centered finite products

Removing each linear logarithmic slope turns a finite zero product into
genus-one factors. Their errors have a quadratic exponential bound on
the whole plane, including segments that cross zeros. Multiplicity
enters through the total degree.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The centered linear factor has quadratic exponential error globally. -/
theorem norm_centered_linear_factor_sub_one_le (w : ℂ) :
    ‖(1 + w) * Complex.exp (-w) - 1‖ ≤ Real.exp (2 * ‖w‖ ^ 2) - 1 := by
  by_cases hw : ‖w‖ ≤ 1
  · have h := RHTower.weierstrassE1_sub_one_norm_le (z := -w) (by simpa using hw)
    simp only [RHTower.weierstrassE1, sub_neg_eq_add, norm_neg] at h
    have he := Real.add_one_le_exp (2 * ‖w‖ ^ 2)
    nlinarith only [h, he, sq_nonneg ‖w‖]
  · have hv : 1 ≤ ‖w‖ ^ 2 := by
      have hw1 : 1 < ‖w‖ := lt_of_not_ge hw
      nlinarith only [hw1]
    have he : 2 ≤ Real.exp (‖w‖ ^ 2) := by
      linarith only [Real.add_one_le_exp (‖w‖ ^ 2), hv]
    have hehalf : Real.exp (‖w‖ ^ 2 / 2) ≤ Real.exp (‖w‖ ^ 2) :=
      Real.exp_le_exp.mpr (by nlinarith only [hv])
    have hedouble : Real.exp (2 * ‖w‖ ^ 2) = Real.exp (‖w‖ ^ 2) ^ 2 := by
      rw [show 2 * ‖w‖ ^ 2 = ‖w‖ ^ 2 + ‖w‖ ^ 2 by ring, Real.exp_add]
      ring
    have htri := norm_sub_le ((1 + w) * Complex.exp (-w)) (1 : ℂ)
    rw [norm_one] at htri
    have hscalar := norm_one_add_mul_exp_neg_le w
    rw [hedouble]
    nlinarith only [htri, hscalar, he, hehalf]

/-- Exponential error bounds multiply by adding their exponents. -/
theorem norm_mul_sub_one_le_exp_add {a b : ℂ} {x y : ℝ}
    (ha : ‖a - 1‖ ≤ Real.exp x - 1)
    (hb : ‖b - 1‖ ≤ Real.exp y - 1) :
    ‖a * b - 1‖ ≤ Real.exp (x + y) - 1 := by
  have hx : 0 ≤ Real.exp x - 1 := (norm_nonneg _).trans ha
  have hbnorm : ‖b‖ ≤ Real.exp y := by
    have h := norm_le_norm_sub_add b (1 : ℂ)
    rw [norm_one] at h
    linarith only [h, hb]
  calc
    _ = ‖(a - 1) * b + (b - 1)‖ := by congr 1; ring
    _ ≤ ‖a - 1‖ * ‖b‖ + ‖b - 1‖ := by
      simpa only [norm_mul] using norm_add_le ((a - 1) * b) (b - 1)
    _ ≤ (Real.exp x - 1) * Real.exp y + (Real.exp y - 1) :=
      add_le_add (mul_le_mul ha hbnorm (norm_nonneg _) hx) hb
    _ = _ := by rw [Real.exp_add]; ring

/-- Raising a factor to a natural multiplicity multiplies its error exponent. -/
theorem norm_pow_sub_one_le_exp_mul {a : ℂ} {K : ℝ}
    (ha : ‖a - 1‖ ≤ Real.exp K - 1) (m : ℕ) :
    ‖a ^ m - 1‖ ≤ Real.exp ((m : ℝ) * K) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    have h := norm_mul_sub_one_le_exp_add ih ha
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using h

/-- A common factor error is charged exactly once per multiplicity. -/
theorem norm_prod_powers_sub_one_le_exp {ι : Type*} {T : Finset ι}
    {m : ι → ℕ} {f : ι → ℂ} {K : ℝ}
    (hf : ∀ a ∈ T, ‖f a - 1‖ ≤ Real.exp K - 1) :
    ‖(∏ a ∈ T, f a ^ m a) - 1‖ ≤
      Real.exp (((∑ a ∈ T, m a : ℕ) : ℝ) * K) - 1 := by
  classical
  revert hf
  induction T using Finset.induction_on with
  | empty => intro _; simp
  | @insert a T ha ih =>
    intro hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hfirst := norm_pow_sub_one_le_exp_mul (hf a (Finset.mem_insert_self a T)) (m a)
    have hrest := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    have h := norm_mul_sub_one_le_exp_add hfirst hrest
    simpa only [Nat.cast_add, add_mul] using h

/-- Normalizing a zero product and cancelling its slope gives genus-one factors. -/
theorem centered_root_product_eq {T : Finset ℂ} {m : ℂ → ℕ} {s u : ℂ}
    (hne : ∀ a ∈ T, s ≠ a) :
    Complex.exp (-(u * ∑ a ∈ T, (m a : ℂ) / (s - a))) *
        (∏ a ∈ T, (s + u - a) ^ m a) / (∏ a ∈ T, (s - a) ^ m a) =
      ∏ a ∈ T, ((1 + u / (s - a)) * Complex.exp (-(u / (s - a)))) ^ m a := by
  classical
  have hphase : Complex.exp (-(u * ∑ a ∈ T, (m a : ℂ) / (s - a))) =
      ∏ a ∈ T, Complex.exp (-(u / (s - a))) ^ m a := by
    have he : -(u * ∑ a ∈ T, (m a : ℂ) / (s - a)) =
        ∑ a ∈ T, (m a : ℂ) * (-(u / (s - a))) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [he, Complex.exp_sum]
    exact Finset.prod_congr rfl (fun a _ => Complex.exp_nat_mul _ _)
  have hratio : (∏ a ∈ T, (s + u - a) ^ m a) / (∏ a ∈ T, (s - a) ^ m a) =
      ∏ a ∈ T, (1 + u / (s - a)) ^ m a := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [← div_pow]
    congr 1
    field_simp [sub_ne_zero.mpr (hne a ha)]
    ring
  rw [hphase, mul_div_assoc, hratio, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← mul_pow, mul_comm (Complex.exp _)]

/-- A separated finite zero product has a quadratic centered error on every segment. -/
theorem norm_centered_root_product_sub_one_le {T : Finset ℂ} {m : ℂ → ℕ}
    {s u : ℂ} {d : ℝ} (hd : 0 < d) (hfar : ∀ a ∈ T, d ≤ ‖s - a‖) :
    ‖Complex.exp (-(u * ∑ a ∈ T, (m a : ℂ) / (s - a))) *
        (∏ a ∈ T, (s + u - a) ^ m a) / (∏ a ∈ T, (s - a) ^ m a) - 1‖ ≤
      Real.exp ((2 * ((∑ a ∈ T, m a : ℕ) : ℝ) / d ^ 2) * ‖u‖ ^ 2) - 1 := by
  have hne : ∀ a ∈ T, s ≠ a := by
    intro a ha h
    have hsep := hfar a ha
    rw [h, sub_self, norm_zero] at hsep
    linarith only [hd, hsep]
  rw [centered_root_product_eq hne]
  have hfactor : ∀ a ∈ T,
      ‖(1 + u / (s - a)) * Complex.exp (-(u / (s - a))) - 1‖ ≤
        Real.exp (2 * ‖u‖ ^ 2 / d ^ 2) - 1 := by
    intro a ha
    refine (norm_centered_linear_factor_sub_one_le _).trans (sub_le_sub_right ?_ 1)
    apply Real.exp_le_exp.mpr
    rw [norm_div, div_pow]
    have hsq : d ^ 2 ≤ ‖s - a‖ ^ 2 :=
      pow_le_pow_left₀ hd.le (hfar a ha) 2
    have hdiv := div_le_div_of_nonneg_left (sq_nonneg ‖u‖) (sq_pos_of_pos hd) hsq
    calc
      _ ≤ 2 * (‖u‖ ^ 2 / d ^ 2) := mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = _ := by ring
  have h := norm_prod_powers_sub_one_le_exp (m := m) hfactor
  convert h using 1
  congr 2
  ring

/-- A separated zero product and a smooth zero-free cofactor have a centered
quadratic error on a fixed segment, even if that segment crosses polynomial zeros. -/
theorem norm_centered_factorization_sub_one_le
    {T : Finset ℂ} {m : ℂ → ℕ} {f g : ℂ → ℂ} {s a : ℂ} {d R K : ℝ}
    (hd : 0 < d) (hR : 0 < R) (hK : 0 < K)
    (hg : Differentiable ℂ g)
    (hgne : ∀ w : ℂ, ‖w - s‖ ≤ 4 * R → g w ≠ 0)
    (hgq : ∀ w : ℂ, ‖w - s‖ ≤ 4 * R →
      ‖deriv (fun v => deriv g v / g v) w‖ ≤ K)
    (hfac : ∀ w : ℂ, f w = (∏ b ∈ T, (w - b) ^ m b) * g w)
    (hfar : ∀ b ∈ T, d ≤ ‖s - b‖)
    (ha : a = (∑ b ∈ T, (m b : ℂ) / (s - b)) + deriv g s / g s)
    {u : ℝ} (hu : |u| ≤ R) :
    ‖Complex.exp (-(u : ℂ) * a) * f (s + u) / f s - 1‖ ≤
      Real.exp ((2 * ((∑ b ∈ T, m b : ℕ) : ℝ) / d ^ 2 + K) * u ^ 2) - 1 := by
  have hne : ∀ b ∈ T, s - b ≠ 0 := by
    intro b hb h
    have hsep := hfar b hb
    rw [h, norm_zero] at hsep
    linarith only [hd, hsep]
  have hP : (∏ b ∈ T, (s - b) ^ m b) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun b hb => pow_ne_zero _ (hne b hb))
  have hgs : g s ≠ 0 := hgne s (by simpa only [sub_self, norm_zero] using (by positivity : 0 ≤ 4 * R))
  let p := ∑ b ∈ T, (m b : ℂ) / (s - b)
  let q := deriv g s / g s
  have hsplit : Complex.exp (-(u : ℂ) * a) * f (s + u) / f s =
      (Complex.exp (-((u : ℂ) * p)) *
        (∏ b ∈ T, (s + u - b) ^ m b) / (∏ b ∈ T, (s - b) ^ m b)) *
      (Complex.exp (-(u : ℂ) * q) * g (s + u) / g s) := by
    rw [ha, hfac (s + u), hfac s]
    change Complex.exp (-(u : ℂ) * (p + q)) * _ / _ = _
    rw [mul_add, Complex.exp_add]
    have he : -(u : ℂ) * p = -((u : ℂ) * p) := by ring
    rw [he]
    field_simp [hP, hgs]
  have hpoly := norm_centered_root_product_sub_one_le (m := m) (u := (u : ℂ)) hd hfar
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hpoly
  have hcofactor := norm_exp_logDeriv_normalized_sub_one_le (z := s) (s := s)
    hR hK hg hgne hgq (by simp; positivity) hu
  rw [hsplit]
  have h := norm_mul_sub_one_le_exp_add hpoly hcofactor
  convert h using 1
  congr 2
  ring

end

end GaloisForLFunctions.HTGeometry
