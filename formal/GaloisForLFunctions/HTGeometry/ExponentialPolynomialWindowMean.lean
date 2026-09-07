import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Window means of exponential polynomials with nonpositive real exponents

An exponential polynomial is a finite list of pairs `(C, λ)` evaluating to `Σ C e^{λ a}`.  When every
exponent has nonpositive real part, the integral over a window `[A, A + L]` with `A ≥ 0` differs from
`L` times the constant term (the sum of the coefficients with `λ = 0`) by at most twice the *decay
norm* `Σ_{λ ≠ 0} ‖C‖/‖λ‖`.  Hence the window mean converges to the constant term as the window
length grows, uniformly in the window position.  Sums, products, and scalar multiples of such
polynomials are again such polynomials, with the evaluation compatible with the operations.
-/

open MeasureTheory intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- An exponential polynomial: a finite list of coefficient–exponent pairs. -/
abbrev ExpPoly := List (ℂ × ℂ)

namespace ExpPoly

/-- Evaluation `Σ C e^{λ a}`. -/
def eval (P : ExpPoly) (a : ℝ) : ℂ :=
  (P.map fun p => p.1 * Complex.exp (p.2 * (a : ℂ))).sum

/-- The constant term: the sum of the coefficients with exponent `0`. -/
def constTerm (P : ExpPoly) : ℂ :=
  (P.map fun p => if p.2 = 0 then p.1 else 0).sum

/-- The decay norm `Σ_{λ ≠ 0} ‖C‖ / ‖λ‖`. -/
def decayNorm (P : ExpPoly) : ℝ :=
  (P.map fun p => if p.2 = 0 then 0 else ‖p.1‖ / ‖p.2‖).sum

/-- Every exponent has nonpositive real part. -/
def Decaying (P : ExpPoly) : Prop := ∀ p ∈ P, p.2.re ≤ 0

/-- Product of two exponential polynomials. -/
def mul (P Q : ExpPoly) : ExpPoly :=
  (P ×ˢ Q).map fun pq => (pq.1.1 * pq.2.1, pq.1.2 + pq.2.2)

/-- Scalar multiple. -/
def smul (c : ℂ) (P : ExpPoly) : ExpPoly := P.map fun p => (c * p.1, p.2)

@[simp] theorem eval_nil (a : ℝ) : eval ([] : ExpPoly) a = 0 := by simp [eval]

@[simp] theorem eval_cons (p : ℂ × ℂ) (P : ExpPoly) (a : ℝ) :
    eval (p :: P) a = p.1 * Complex.exp (p.2 * (a : ℂ)) + eval P a := by
  simp [eval]

theorem eval_append (P Q : ExpPoly) (a : ℝ) : eval (P ++ Q) a = eval P a + eval Q a := by
  induction P with
  | nil => simp
  | cons p P ih => simp [ih, add_assoc]

theorem eval_smul (c : ℂ) (P : ExpPoly) (a : ℝ) : eval (smul c P) a = c * eval P a := by
  induction P with
  | nil => simp [smul]
  | cons p P ih =>
    simp only [smul, List.map_cons, eval_cons] at ih ⊢
    rw [ih]
    ring

theorem eval_map_pair (p : ℂ × ℂ) (Q : ExpPoly) (a : ℝ) :
    eval (Q.map fun q => (p.1 * q.1, p.2 + q.2)) a
      = p.1 * Complex.exp (p.2 * (a : ℂ)) * eval Q a := by
  induction Q with
  | nil => simp
  | cons q Q ihq =>
    simp only [List.map_cons, eval_cons] at ihq ⊢
    rw [ihq, add_mul, Complex.exp_add]
    ring

theorem eval_mul (P Q : ExpPoly) (a : ℝ) : eval (mul P Q) a = eval P a * eval Q a := by
  induction P with
  | nil => simp [mul]
  | cons p P ih =>
    have hcons : mul (p :: P) Q = (Q.map fun q => (p.1 * q.1, p.2 + q.2)) ++ mul P Q := by
      simp [mul, List.product_cons]
    rw [hcons, eval_append, ih, eval_cons, add_mul, eval_map_pair]

theorem decaying_append {P Q : ExpPoly} (hP : Decaying P) (hQ : Decaying Q) :
    Decaying (P ++ Q) := by
  intro p hp
  rw [List.mem_append] at hp
  rcases hp with hp | hp
  · exact hP p hp
  · exact hQ p hp

theorem decaying_smul (c : ℂ) {P : ExpPoly} (hP : Decaying P) : Decaying (smul c P) := by
  intro p hp
  simp only [smul, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact hP q hq

theorem decaying_mul {P Q : ExpPoly} (hP : Decaying P) (hQ : Decaying Q) : Decaying (mul P Q) := by
  intro p hp
  simp only [mul, List.mem_map] at hp
  obtain ⟨xy, hxy, rfl⟩ := hp
  rcases xy with ⟨x, y⟩
  have hxy' : x ∈ P ∧ y ∈ Q := List.pair_mem_product.mp hxy
  simp only [Complex.add_re]
  linarith [hP x hxy'.1, hQ y hxy'.2]

theorem continuous_eval (P : ExpPoly) : Continuous (eval P) := by
  induction P with
  | nil =>
    have h : eval ([] : ExpPoly) = fun _ => (0 : ℂ) := by funext a; simp
    rw [h]
    exact continuous_const
  | cons p P ih =>
    have h : eval (p :: P) = fun a : ℝ => p.1 * Complex.exp (p.2 * (a : ℂ)) + eval P a := by
      funext a; simp
    rw [h]
    exact (continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).add ih

/-- The window integral of a single exponential, `λ ≠ 0`. -/
theorem integral_exp_window {lam : ℂ} (h : lam ≠ 0) (A L : ℝ) :
    ∫ a in A..(A + L), Complex.exp (lam * (a : ℂ))
      = (Complex.exp (lam * ((A + L : ℝ) : ℂ)) - Complex.exp (lam * (A : ℂ))) / lam :=
  integral_exp_mul_complex h

theorem norm_integral_exp_window_le {lam : ℂ} (h : lam ≠ 0) (hre : lam.re ≤ 0) {A L : ℝ}
    (hA : 0 ≤ A) (hL : 0 ≤ L) :
    ‖∫ a in A..(A + L), Complex.exp (lam * (a : ℂ))‖ ≤ 2 / ‖lam‖ := by
  rw [integral_exp_window h, norm_div]
  have hlam : 0 < ‖lam‖ := norm_pos_iff.mpr h
  rw [div_le_div_iff_of_pos_right hlam]
  refine le_trans (norm_sub_le _ _) ?_
  have e1 : ‖Complex.exp (lam * ((A + L : ℝ) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  have e2 : ‖Complex.exp (lam * (A : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith
  linarith

/-- **Window integral law.**  For a decaying exponential polynomial and a window `[A, A+L]` with
`A ≥ 0`, the integral is `L` times the constant term up to `2 · decayNorm`. -/
theorem norm_integral_sub_constTerm_le (P : ExpPoly) (hP : Decaying P) {A L : ℝ} (hA : 0 ≤ A)
    (hL : 0 ≤ L) :
    ‖(∫ a in A..(A + L), eval P a) - (L : ℂ) * constTerm P‖ ≤ 2 * decayNorm P := by
  induction P with
  | nil => simp [constTerm, decayNorm]
  | cons p P ih =>
    have hPd : Decaying P := fun q hq => hP q (List.mem_cons_of_mem _ hq)
    have hp : p.2.re ≤ 0 := hP p List.mem_cons_self
    have hint1 : IntervalIntegrable (fun a : ℝ => p.1 * Complex.exp (p.2 * (a : ℂ))) volume A (A + L) :=
      ((continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul Complex.continuous_ofReal)))).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (eval P) volume A (A + L) :=
      (continuous_eval P).intervalIntegrable _ _
    simp only [eval_cons]
    rw [integral_add hint1 hint2, intervalIntegral.integral_const_mul]
    simp only [constTerm, decayNorm, List.map_cons, List.sum_cons]
    have ih' := ih hPd
    simp only [constTerm, decayNorm] at ih'
    by_cases h0 : p.2 = 0
    · simp only [h0, if_true, zero_mul, Complex.exp_zero]
      have hconst : ∫ a in A..(A + L), (1 : ℂ) = (L : ℂ) := by
        simp
      rw [hconst]
      calc ‖p.1 * (L : ℂ) + (∫ a in A..(A + L), eval P a)
            - (L : ℂ) * (p.1 + (P.map fun q => if q.2 = 0 then q.1 else 0).sum)‖
          = ‖(∫ a in A..(A + L), eval P a)
              - (L : ℂ) * (P.map fun q => if q.2 = 0 then q.1 else 0).sum‖ := by
            congr 1; ring
        _ ≤ 2 * (P.map fun q => if q.2 = 0 then 0 else ‖q.1‖ / ‖q.2‖).sum := ih'
        _ = 2 * (0 + (P.map fun q => if q.2 = 0 then 0 else ‖q.1‖ / ‖q.2‖).sum) := by ring
    · simp only [h0, if_false]
      have hw := norm_integral_exp_window_le h0 hp hA hL
      calc ‖p.1 * (∫ a in A..(A + L), Complex.exp (p.2 * (a : ℂ))) + (∫ a in A..(A + L), eval P a)
            - (L : ℂ) * (0 + (P.map fun q => if q.2 = 0 then q.1 else 0).sum)‖
          = ‖p.1 * (∫ a in A..(A + L), Complex.exp (p.2 * (a : ℂ)))
              + ((∫ a in A..(A + L), eval P a)
                - (L : ℂ) * (P.map fun q => if q.2 = 0 then q.1 else 0).sum)‖ := by
            congr 1; ring
        _ ≤ ‖p.1 * (∫ a in A..(A + L), Complex.exp (p.2 * (a : ℂ)))‖
              + ‖(∫ a in A..(A + L), eval P a)
                - (L : ℂ) * (P.map fun q => if q.2 = 0 then q.1 else 0).sum‖ := norm_add_le _ _
        _ ≤ ‖p.1‖ * (2 / ‖p.2‖) + 2 * (P.map fun q => if q.2 = 0 then 0 else ‖q.1‖ / ‖q.2‖).sum := by
            rw [norm_mul]
            gcongr
        _ = 2 * (‖p.1‖ / ‖p.2‖ + (P.map fun q => if q.2 = 0 then 0 else ‖q.1‖ / ‖q.2‖).sum) := by
            ring

/-- The window mean of the real part converges to the real part of the constant term at rate
`2 · decayNorm / L`. -/
theorem abs_windowMean_re_sub_le (P : ExpPoly) (hP : Decaying P) {A L : ℝ} (hA : 0 ≤ A)
    (hL : 0 < L) :
    |(∫ a in A..(A + L), (eval P a).re) / L - (constTerm P).re| ≤ 2 * decayNorm P / L := by
  have h := norm_integral_sub_constTerm_le P hP hA hL.le
  have hre : (∫ a in A..(A + L), (eval P a).re)
      = (∫ a in A..(A + L), eval P a).re := by
    have := ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM
      ((continuous_eval P).intervalIntegrable (μ := volume) A (A + L))
    simpa [Complex.reCLM_apply] using this
  have hdiv : (∫ a in A..(A + L), eval P a).re / L - (constTerm P).re
      = ((∫ a in A..(A + L), eval P a).re - (constTerm P).re * L) / L := by
    field_simp
  rw [hre, hdiv, abs_div, abs_of_pos hL, div_le_div_iff_of_pos_right hL]
  calc |(∫ a in A..(A + L), eval P a).re - (constTerm P).re * L|
      = |((∫ a in A..(A + L), eval P a) - (L : ℂ) * constTerm P).re| := by
        congr 1
        simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero]
        ring
    _ ≤ ‖(∫ a in A..(A + L), eval P a) - (L : ℂ) * constTerm P‖ := Complex.abs_re_le_norm _
    _ ≤ 2 * decayNorm P := h

/-! ## Constant terms of products -/

theorem constTerm_nil : constTerm ([] : ExpPoly) = 0 := by simp [constTerm]

theorem constTerm_cons (p : ℂ × ℂ) (P : ExpPoly) :
    constTerm (p :: P) = (if p.2 = 0 then p.1 else 0) + constTerm P := by
  simp [constTerm]

theorem constTerm_append (P Q : ExpPoly) : constTerm (P ++ Q) = constTerm P + constTerm Q := by
  induction P with
  | nil => simp [constTerm]
  | cons p P ih => simp [constTerm_cons, ih, add_assoc]

theorem constTerm_smul (c : ℂ) (P : ExpPoly) : constTerm (smul c P) = c * constTerm P := by
  induction P with
  | nil => simp [smul, constTerm]
  | cons p P ih =>
    simp only [smul, List.map_cons, constTerm_cons] at ih ⊢
    rw [ih]
    split_ifs <;> ring

/-- The pairing sum of one entry against a polynomial. -/
def pairSum (p : ℂ × ℂ) (Q : ExpPoly) : ℂ :=
  (Q.map fun q => if p.2 + q.2 = 0 then p.1 * q.1 else 0).sum

theorem constTerm_map_pair (p : ℂ × ℂ) (Q : ExpPoly) :
    constTerm (Q.map fun q => (p.1 * q.1, p.2 + q.2)) = pairSum p Q := by
  induction Q with
  | nil => simp [constTerm, pairSum]
  | cons q Q ih =>
    simp only [List.map_cons, constTerm_cons, pairSum, List.sum_cons] at ih ⊢
    rw [ih]

theorem constTerm_mul (P Q : ExpPoly) :
    constTerm (mul P Q) = (P.map fun p => pairSum p Q).sum := by
  induction P with
  | nil => simp [mul, constTerm]
  | cons p P ih =>
    have hcons : mul (p :: P) Q = (Q.map fun q => (p.1 * q.1, p.2 + q.2)) ++ mul P Q := by
      simp [mul, List.product_cons]
    rw [hcons, constTerm_append, ih, constTerm_map_pair]
    simp

/-- Entries with negative real exponent do not pair to zero against a decaying polynomial. -/
theorem pairSum_eq_zero_of_re_neg {p : ℂ × ℂ} (hp : p.2.re < 0) {Q : ExpPoly}
    (hQ : Decaying Q) : pairSum p Q = 0 := by
  unfold pairSum
  apply List.sum_eq_zero
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  have h : p.2 + q.2 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.zero_re] at this
    linarith [hQ q hq]
  simp [h]

/-- The pairing sum of an entry with nonpositive real exponent against a decaying polynomial only
sees the entries with zero real exponent. -/
theorem pairSum_eq_pairSum_filter {p : ℂ × ℂ} (hp : p.2.re ≤ 0) {Q : ExpPoly} (hQ : Decaying Q) :
    pairSum p Q = pairSum p (Q.filter fun q => decide (q.2.re = 0)) := by
  induction Q with
  | nil => simp [pairSum]
  | cons q Q ih =>
    have hQd : Decaying Q := fun r hr => hQ r (List.mem_cons_of_mem _ hr)
    have hq : q.2.re ≤ 0 := hQ q List.mem_cons_self
    have ih' := ih hQd
    by_cases h0 : q.2.re = 0
    · simp only [pairSum, List.filter_cons, h0, decide_true, if_true, List.map_cons,
        List.sum_cons] at ih' ⊢
      rw [ih']
    · have hne : p.2 + q.2 ≠ 0 := by
        intro h0'
        have := congrArg Complex.re h0'
        simp only [Complex.add_re, Complex.zero_re] at this
        have hlt : q.2.re < 0 := lt_of_le_of_ne hq h0
        linarith
      simp only [pairSum, List.filter_cons, h0, decide_false, List.map_cons, List.sum_cons,
        if_neg hne, zero_add] at ih' ⊢
      exact ih'

/-- Summing a function that vanishes on entries with negative real exponent over a decaying
polynomial only sees the entries with zero real exponent. -/
theorem sum_map_eq_sum_map_filter {P : ExpPoly} (hP : Decaying P) (g : ℂ × ℂ → ℂ)
    (hg : ∀ p ∈ P, p.2.re < 0 → g p = 0) :
    (P.map g).sum = ((P.filter fun p => decide (p.2.re = 0)).map g).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    have hPd : Decaying P := fun r hr => hP r (List.mem_cons_of_mem _ hr)
    have hp : p.2.re ≤ 0 := hP p List.mem_cons_self
    have ih' := ih hPd fun r hr => hg r (List.mem_cons_of_mem _ hr)
    by_cases h0 : p.2.re = 0
    · simp only [List.filter_cons, h0, decide_true, if_true, List.map_cons, List.sum_cons]
      rw [ih']
    · have hlt : p.2.re < 0 := lt_of_le_of_ne hp h0
      simp only [List.filter_cons, h0, decide_false, List.map_cons, List.sum_cons,
        hg p List.mem_cons_self hlt, zero_add]
      exact ih'

theorem decaying_filter {P : ExpPoly} (hP : Decaying P) (f : ℂ × ℂ → Bool) :
    Decaying (P.filter f) := fun p hp => hP p (List.mem_of_mem_filter hp)

/-- **Constant terms of products only involve the zero-real-part entries.** -/
theorem constTerm_mul_eq_constTerm_mul_filter {P Q : ExpPoly} (hP : Decaying P) (hQ : Decaying Q) :
    constTerm (mul P Q)
      = constTerm (mul (P.filter fun p => decide (p.2.re = 0))
          (Q.filter fun q => decide (q.2.re = 0))) := by
  rw [constTerm_mul, constTerm_mul]
  have h1 : (P.map fun p => pairSum p Q).sum
      = (P.map fun p => pairSum p (Q.filter fun q => decide (q.2.re = 0))).sum := by
    congr 1
    refine List.map_congr_left fun p hp => ?_
    exact pairSum_eq_pairSum_filter (hP p hp) hQ
  rw [h1]
  exact sum_map_eq_sum_map_filter hP _ fun p _ hlt =>
    pairSum_eq_zero_of_re_neg hlt (decaying_filter hQ _)

/-! ## Decay norms of scalar multiples and products -/

/-- The coefficient sum `Σ ‖C‖`. -/
def coeffSum (P : ExpPoly) : ℝ := (P.map fun p => ‖p.1‖).sum

theorem coeffSum_nonneg (P : ExpPoly) : 0 ≤ coeffSum P := by
  unfold coeffSum
  apply List.sum_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨p, _, rfl⟩ := hx
  exact norm_nonneg _

theorem coeffSum_append (P Q : ExpPoly) : coeffSum (P ++ Q) = coeffSum P + coeffSum Q := by
  simp [coeffSum]

theorem coeffSum_cons (p : ℂ × ℂ) (P : ExpPoly) : coeffSum (p :: P) = ‖p.1‖ + coeffSum P := by
  simp [coeffSum]

theorem decayNorm_nonneg (P : ExpPoly) : 0 ≤ decayNorm P := by
  unfold decayNorm
  apply List.sum_nonneg
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨p, _, rfl⟩ := hx
  split_ifs
  · exact le_rfl
  · positivity

theorem decayNorm_cons (p : ℂ × ℂ) (P : ExpPoly) :
    decayNorm (p :: P) = (if p.2 = 0 then 0 else ‖p.1‖ / ‖p.2‖) + decayNorm P := by
  simp [decayNorm]

theorem decayNorm_append (P Q : ExpPoly) : decayNorm (P ++ Q) = decayNorm P + decayNorm Q := by
  simp [decayNorm]

theorem decayNorm_smul (c : ℂ) (P : ExpPoly) : decayNorm (smul c P) = ‖c‖ * decayNorm P := by
  induction P with
  | nil => simp [smul, decayNorm]
  | cons p P ih =>
    simp only [smul, List.map_cons, decayNorm_cons] at ih ⊢
    rw [ih]
    split_ifs
    · ring
    · rw [norm_mul]; ring

/-- The decay norm of the pairing of one entry against `Q`, when every nonzero pair sum has norm at
least `m`. -/
theorem decayNorm_map_pair_le (p : ℂ × ℂ) (Q : ExpPoly) {m : ℝ} (hm : 0 < m)
    (hQ : ∀ q ∈ Q, p.2 + q.2 ≠ 0 → m ≤ ‖p.2 + q.2‖) :
    decayNorm (Q.map fun q => (p.1 * q.1, p.2 + q.2)) ≤ ‖p.1‖ * coeffSum Q / m := by
  induction Q with
  | nil => simp [decayNorm, coeffSum]
  | cons q Q ih =>
    have ih' := ih fun r hr => hQ r (List.mem_cons_of_mem _ hr)
    simp only [List.map_cons, decayNorm_cons, coeffSum_cons]
    have hstep : (if p.2 + q.2 = 0 then 0 else ‖p.1 * q.1‖ / ‖p.2 + q.2‖) ≤ ‖p.1‖ * ‖q.1‖ / m := by
      split_ifs with h
      · positivity
      · rw [norm_mul]
        have hmq := hQ q List.mem_cons_self h
        have hpos : 0 < ‖p.2 + q.2‖ := lt_of_lt_of_le hm hmq
        rw [div_le_div_iff₀ hpos hm]
        have := mul_nonneg (norm_nonneg p.1) (norm_nonneg q.1)
        nlinarith
    calc (if p.2 + q.2 = 0 then 0 else ‖p.1 * q.1‖ / ‖p.2 + q.2‖)
          + decayNorm (Q.map fun q => (p.1 * q.1, p.2 + q.2))
        ≤ ‖p.1‖ * ‖q.1‖ / m + ‖p.1‖ * coeffSum Q / m := add_le_add hstep ih'
      _ = ‖p.1‖ * (‖q.1‖ + coeffSum Q) / m := by ring

/-- **Decay norm of a product.**  If every nonzero pair sum of exponents has norm at least `m`, then
`decayNorm (mul P Q) ≤ coeffSum P · coeffSum Q / m`. -/
theorem decayNorm_mul_le (P Q : ExpPoly) {m : ℝ} (hm : 0 < m)
    (h : ∀ p ∈ P, ∀ q ∈ Q, p.2 + q.2 ≠ 0 → m ≤ ‖p.2 + q.2‖) :
    decayNorm (mul P Q) ≤ coeffSum P * coeffSum Q / m := by
  induction P with
  | nil => simp [mul, decayNorm, coeffSum]
  | cons p P ih =>
    have ih' := ih fun r hr => h r (List.mem_cons_of_mem _ hr)
    have hcons : mul (p :: P) Q = (Q.map fun q => (p.1 * q.1, p.2 + q.2)) ++ mul P Q := by
      simp [mul, List.product_cons]
    rw [hcons, decayNorm_append, coeffSum_cons]
    have hp := decayNorm_map_pair_le p Q hm (h p List.mem_cons_self)
    calc decayNorm (Q.map fun q => (p.1 * q.1, p.2 + q.2)) + decayNorm (mul P Q)
        ≤ ‖p.1‖ * coeffSum Q / m + coeffSum P * coeffSum Q / m := add_le_add hp ih'
      _ = (‖p.1‖ + coeffSum P) * coeffSum Q / m := by ring

end ExpPoly

end

end GaloisForLFunctions.HTGeometry
