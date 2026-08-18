/-
# Critical-packet gauges: positivity, order, and the exponential cost

Three properties of the polynomial gauge that turns a finite packet of regular points into
critical points.

* The gauge can be taken *positive on the real axis*: interpolating an even Schwarz-real `Q` with
  `Q(a) = 1` and `Q'(a) = -F'(a)/F(a)` and setting `P = 1 + Q²` gives a real-even multiplier that is
  at least one on all of `ℝ`, hence has no real zeros, and still kills `(PF)'` on the packet
  (because `P(a) = 2` and `P'(a) = 2Q'(a)`).
* The gauge costs no growth: a polynomial factor keeps the order-one envelope
  `exp(C(1+r)log(2+r))`, only enlarging `C`.
* The zero-divisor-preserving alternative `H = e^Q F` shifts the logarithmic derivative by `Q'` and
  keeps the divisor, but it *does* cost growth: if both `F` and `e^Q F` keep subquadratic proximity,
  the fixed-divisor rigidity forces `e^Q` itself to be the exponential of an affine function.
-/
import GaloisForLFunctions.RHTower.CriticalPointInterpolation
import GaloisForLFunctions.RHTower.CoshPolynomialExactOrderOne
import GaloisForLFunctions.RHTower.OrderOneFixedDivisorRigidity

noncomputable section

open Polynomial Complex Filter Topology ValueDistribution Asymptotics

namespace RHTower.SpeiserGauge

open RHTower.OrderOneRigidity

/-! ## The positive real-axis multiplier -/

theorem eval_real_of_conjEquivariant {Q : Polynomial ℂ}
    (hQconj : ∀ z, Q.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Q.eval z)) (x : ℝ) :
    ∃ t : ℝ, Q.eval (x : ℂ) = (t : ℂ) := by
  refine ⟨(Q.eval (x : ℂ)).re, ?_⟩
  have h := hQconj (x : ℂ)
  rw [Complex.conj_ofReal] at h
  have him : (Q.eval (x : ℂ)).im = 0 := by
    have h2 := congrArg Complex.im h
    rw [Complex.conj_im] at h2
    linarith
  exact Complex.ext rfl (by rw [him, Complex.ofReal_im])

/-- **A positive real-even critical-packet multiplier.**  On a sign- and conjugation-invariant
packet with compatible value and derivative data, the interpolating gauge can be taken of the form
`1 + Q²` with `Q` even and Schwarz-real.  The multiplier is then real and at least one on the whole
real axis — in particular it has no real zeros — while still forcing the product-rule derivative to
vanish at every packet point. -/
theorem exists_positive_real_even_polynomial_critical_packet
    {ι : Type*} [Finite ι]
    (negIdx conjIdx : ι ≃ ι)
    (w : ι → ℂ) (hw : Function.Injective w)
    (f df : ι → ℂ) (hf : ∀ i, f i ≠ 0)
    (hwneg : ∀ i, w (negIdx i) = -w i)
    (hwconj : ∀ i, w (conjIdx i) = (starRingEnd ℂ) (w i))
    (hfneg : ∀ i, f (negIdx i) = f i)
    (hdfneg : ∀ i, df (negIdx i) = -df i)
    (hfconj : ∀ i, f (conjIdx i) = (starRingEnd ℂ) (f i))
    (hdfconj : ∀ i, df (conjIdx i) = (starRingEnd ℂ) (df i)) :
    ∃ P : Polynomial ℂ,
      (∀ z, P.eval (-z) = P.eval z) ∧
      (∀ z, P.eval ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.eval z)) ∧
      (∀ x : ℝ, ∃ t : ℝ, P.eval (x : ℂ) = (t : ℂ) ∧ 1 ≤ t) ∧
      (∀ x : ℝ, P.eval (x : ℂ) ≠ 0) ∧
      ∀ i, P.eval (w i) = 2 ∧
        (derivative P).eval (w i) * f i + P.eval (w i) * df i = 0 := by
  obtain ⟨Q, hQneg, hQconj, hQ⟩ :=
    exists_real_even_polynomial_critical_packet negIdx conjIdx w hw f df hf
      hwneg hwconj hfneg hdfneg hfconj hdfconj
  have hreal := eval_real_of_conjEquivariant hQconj
  have hvalx : ∀ x : ℝ, ∃ t : ℝ, (1 + Q * Q).eval (x : ℂ) = ((1 + t ^ 2 : ℝ) : ℂ) := by
    intro x
    obtain ⟨t, ht⟩ := hreal x
    refine ⟨t, ?_⟩
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, ht]
    push_cast
    ring
  refine ⟨1 + Q * Q, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, hQneg]
  · intro z
    simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, hQconj, map_add,
      map_one, map_mul]
  · intro x
    obtain ⟨t, ht⟩ := hvalx x
    exact ⟨1 + t ^ 2, ht, by nlinarith [sq_nonneg t]⟩
  · intro x
    obtain ⟨t, ht⟩ := hvalx x
    rw [ht]
    have hpos : (0 : ℝ) < 1 + t ^ 2 := by nlinarith [sq_nonneg t]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  · intro i
    obtain ⟨hQ1, hQ2⟩ := hQ i
    have hval : (1 + Q * Q).eval (w i) = 2 := by
      simp only [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, hQ1]
      norm_num
    refine ⟨hval, ?_⟩
    have hderiv : (derivative (1 + Q * Q)).eval (w i) = 2 * (derivative Q).eval (w i) := by
      rw [derivative_add, derivative_one, derivative_mul]
      simp only [Polynomial.eval_add, Polynomial.eval_zero, Polynomial.eval_mul, hQ1]
      ring
    rw [hval, hderiv]
    rw [hQ1] at hQ2
    linear_combination 2 * hQ2

/-- **Analytic realization of the positive gauge.**  Every packet point becomes a genuine critical
point of `P·F` for a real-even multiplier with no real zeros. -/
theorem exists_positive_polynomial_mul_hasDerivAt_zero
    {ι : Type*} [Finite ι]
    (negIdx conjIdx : ι ≃ ι)
    (w : ι → ℂ) (hw : Function.Injective w)
    (F : ℂ → ℂ) (df : ι → ℂ)
    (hF : ∀ i, HasDerivAt F (df i) (w i))
    (hf : ∀ i, F (w i) ≠ 0)
    (hwneg : ∀ i, w (negIdx i) = -w i)
    (hwconj : ∀ i, w (conjIdx i) = (starRingEnd ℂ) (w i))
    (hfneg : ∀ i, F (w (negIdx i)) = F (w i))
    (hdfneg : ∀ i, df (negIdx i) = -df i)
    (hfconj : ∀ i, F (w (conjIdx i)) = (starRingEnd ℂ) (F (w i)))
    (hdfconj : ∀ i, df (conjIdx i) = (starRingEnd ℂ) (df i)) :
    ∃ P : Polynomial ℂ,
      (∀ z, P.eval (-z) = P.eval z) ∧
      (∀ x : ℝ, ∃ t : ℝ, P.eval (x : ℂ) = (t : ℂ) ∧ 1 ≤ t) ∧
      (∀ x : ℝ, P.eval (x : ℂ) ≠ 0) ∧
      ∀ i, HasDerivAt (fun z => P.eval z * F z) 0 (w i) := by
  obtain ⟨P, hPneg, _, hPreal, hPne, hP⟩ :=
    exists_positive_real_even_polynomial_critical_packet negIdx conjIdx w hw
      (fun i => F (w i)) df hf hwneg hwconj hfneg hdfneg hfconj hdfconj
  refine ⟨P, hPneg, hPreal, hPne, fun i => ?_⟩
  apply ((Polynomial.hasDerivAt P (w i)).mul (hF i)).congr_deriv
  exact (hP i).2

/-! ## Polynomial gauges preserve the order-one envelope -/

/-- **The polynomial factor costs no order.**  Multiplying an entire function carrying the
order-one envelope by any polynomial leaves the same envelope with a larger constant. -/
theorem orderOneEnvelope_mul_polynomial {F : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C) (P : Polynomial ℂ)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ z : ℂ, ‖P.eval z * F z‖ ≤ Real.exp (C' * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  set A : ℝ := polynomialCoeffNormSum P with hA
  have hAnn : 0 ≤ A := by
    rw [hA, polynomialCoeffNormSum]
    positivity
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set d : ℕ := P.natDegree with hd
  set C₁ : ℝ := A / Real.log 2 + d with hC₁
  have hC₁nn : 0 ≤ C₁ := by positivity
  refine ⟨C + C₁, by linarith, fun z => ?_⟩
  have hr0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hlogle : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hLpos : 0 < Real.log (2 + ‖z‖) := lt_of_lt_of_le hlog2 hlogle
  have hbase : Real.log 2 ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := by nlinarith
  -- the coefficient sum
  have hAle : A ≤ Real.exp (A / Real.log 2 * ((1 + ‖z‖) * Real.log (2 + ‖z‖))) := by
    refine le_trans (by linarith [Real.add_one_le_exp A]) (Real.exp_le_exp.mpr ?_)
    have hdiv : 0 ≤ A / Real.log 2 := by positivity
    have : A / Real.log 2 * Real.log 2 ≤ A / Real.log 2 * ((1 + ‖z‖) * Real.log (2 + ‖z‖)) :=
      mul_le_mul_of_nonneg_left hbase hdiv
    rw [div_mul_cancel₀ _ hlog2.ne'] at this
    exact this
  -- the degree power
  have hpow : (1 + ‖z‖) ^ d ≤ Real.exp ((d : ℝ) * ((1 + ‖z‖) * Real.log (2 + ‖z‖))) := by
    have hbasepos : (0 : ℝ) < 1 + ‖z‖ := by linarith
    have hexp : (1 + ‖z‖) ^ d = Real.exp ((d : ℝ) * Real.log (1 + ‖z‖)) := by
      rw [Real.exp_nat_mul, Real.exp_log hbasepos]
    rw [hexp]
    refine Real.exp_le_exp.mpr ?_
    have h1 : Real.log (1 + ‖z‖) ≤ Real.log (2 + ‖z‖) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2 + ‖z‖) ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := by nlinarith
    have h3 : Real.log (1 + ‖z‖) ≤ (1 + ‖z‖) * Real.log (2 + ‖z‖) := le_trans h1 h2
    exact mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg d)
  have hPle : ‖P.eval z‖ ≤ A * (1 + ‖z‖) ^ d := norm_polynomial_eval_le P z
  have hprod : A * (1 + ‖z‖) ^ d ≤ Real.exp (C₁ * ((1 + ‖z‖) * Real.log (2 + ‖z‖))) := by
    have := mul_le_mul hAle hpow (by positivity) (Real.exp_nonneg _)
    rw [← Real.exp_add] at this
    refine le_trans this (Real.exp_le_exp.mpr ?_)
    rw [hC₁]
    ring_nf
    exact le_refl _
  rw [norm_mul]
  calc ‖P.eval z‖ * ‖F z‖
      ≤ (A * (1 + ‖z‖) ^ d) * Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :=
        mul_le_mul hPle (hbound z) (norm_nonneg _) (by positivity)
    _ ≤ Real.exp (C₁ * ((1 + ‖z‖) * Real.log (2 + ‖z‖)))
        * Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :=
        mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
    _ = Real.exp ((C + C₁) * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-! ## The exponential gauge and its cost -/

theorem expGauge_eq_zero_iff (Q F : ℂ → ℂ) (z : ℂ) :
    Complex.exp (Q z) * F z = 0 ↔ F z = 0 := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 (Complex.exp_ne_zero _)
    · exact h2
  · intro h
    rw [h, mul_zero]

/-- **The exponential gauge shifts the logarithmic derivative by `Q'`.**  It therefore generates
the same differential field as `F` does. -/
theorem logDeriv_expGauge {Q F : ℂ → ℂ} (hQ : Differentiable ℂ Q) (hF : Differentiable ℂ F)
    {z : ℂ} (hFz : F z ≠ 0) :
    logDeriv (fun w => Complex.exp (Q w) * F w) z = deriv Q z + logDeriv F z := by
  have hexp : Differentiable ℂ fun w => Complex.exp (Q w) := fun w => (hQ w).cexp
  rw [logDeriv_mul (f := fun w => Complex.exp (Q w)) (g := F) z
    (Complex.exp_ne_zero (Q z)) hFz (hexp z) (hF z)]
  congr 1
  rw [logDeriv_apply]
  have hd : HasDerivAt (fun w => Complex.exp (Q w)) (Complex.exp (Q z) * deriv Q z) z :=
    (hQ z).hasDerivAt.cexp
  rw [hd.deriv]
  field_simp

/-- **The exponential gauge leaves the order-one cage.**  If a zero-free exponential gauge keeps
both the divisor and the subquadratic proximity, the gauge itself is the exponential of an affine
function: no genuinely higher-degree exponential multiplier survives inside the cage. -/
theorem expGauge_affine_of_orderOne {Q F : ℂ → ℂ}
    (hQ : Differentiable ℂ Q) (hF : Differentiable ℂ F)
    (hFord : ∀ z, meromorphicOrderAt F z ≠ ⊤)
    (hGord : ∀ z, meromorphicOrderAt (fun w => Complex.exp (Q w) * F w) z ≠ ⊤)
    (hproxF : proximity F ⊤ =o[atTop] fun r : ℝ => r ^ 2)
    (hproxG : proximity (fun w => Complex.exp (Q w) * F w) ⊤ =o[atTop] fun r : ℝ => r ^ 2) :
    ∃ a b : ℂ, ∀ z, Complex.exp (Q z) = Complex.exp (a * z + b) := by
  have hexp : Differentiable ℂ fun w => Complex.exp (Q w) := fun w => (hQ w).cexp
  have hG : Differentiable ℂ fun w => Complex.exp (Q w) * F w := hexp.mul hF
  exact exists_expAffine_of_entire_quotient hF hG hexp hFord hGord
    (fun z => Complex.exp_ne_zero _) (fun z => rfl) hproxF hproxG

end RHTower.SpeiserGauge

/-! ## The gauge factor of a translated power -/

namespace RHTower.SpeiserGauge

open Polynomial

/-- **The gauge factorizes through every translate and every power.**  This is the identity that
lets a polynomial gauge be absorbed into the rational base field of a translation family. -/
theorem translate_pow_polynomial_mul (P : Polynomial ℂ) (F : ℂ → ℂ) (h : ℂ) (N : ℕ) (z : ℂ) :
    ((fun w => P.eval w * F w) (z + h)) ^ N
      = (P.comp (X + C h)).eval z ^ N * (F (z + h)) ^ N := by
  have hcomp : (P.comp (X + C h)).eval z = P.eval (z + h) := by
    rw [Polynomial.eval_comp]
    simp
  rw [hcomp, mul_pow]

/-- The gauge factor is a nonzero element of the rational base: the translate of a nonzero
polynomial is nonzero, hence so is each of its powers. -/
theorem translate_pow_ne_zero {P : Polynomial ℂ} (hP : P ≠ 0) (h : ℂ) (N : ℕ) :
    (P.comp (X + C h)) ^ N ≠ 0 := by
  refine pow_ne_zero N ?_
  intro hzero
  apply hP
  have hback : (P.comp (X + C h)).comp (X - C h) = P := by
    rw [Polynomial.comp_assoc]
    simp
  rw [hzero] at hback
  simpa using hback.symm

end RHTower.SpeiserGauge
