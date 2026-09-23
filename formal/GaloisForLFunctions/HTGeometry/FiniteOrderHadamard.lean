import GaloisForLFunctions.RHTower.ArgumentVariation
import GaloisForLFunctions.RHTower.EntireAutomorphism
import GaloisForLFunctions.HTGeometry.EntireLogarithm

/-!
# Finite-order Hadamard factorization for zero-free entire functions

Classical Hadamard theory says that a nowhere-vanishing entire function of finite order is the
exponential of a polynomial.  The corpus already owns the order-one special case
(`exists_linear_of_ne_zero_of_growth`); this module proves the statement at every finite order and
packages the growth side as a reusable envelope predicate.

## Main results

* `FiniteOrderEnvelope` — the predicate `∃ C ≥ 0, ∃ d, ∀ z, ‖f z‖ ≤ exp (C (1+‖z‖)^d)`;
* `FiniteOrderEnvelope.add/.mul/.const/.compAffine/.of_sq` — its closure properties;
* `exists_polynomial_exp_of_ne_zero_of_growth` — Hadamard's zero-free factorization at explicit
  growth data;
* `exists_polynomial_exp_of_ne_zero` — the same statement phrased through the envelope predicate.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Complex Metric

/-! ### The finite-order growth envelope -/

/-- A **finite-order growth envelope**: `‖f z‖ ≤ exp (C (1+‖z‖)^d)` for some nonnegative real `C`
and some natural number `d`.  This is exactly the statement that `f` has finite order, with the
order bounded by `d`. -/
def FiniteOrderEnvelope (f : ℂ → ℂ) : Prop :=
  ∃ (C : ℝ) (d : ℕ), 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ d)

/-- The envelope exponent is monotone in both parameters. -/
theorem envelope_exponent_le {C C' : ℝ} {d d' : ℕ} (hC : 0 ≤ C) (hCC : C ≤ C') (hdd : d ≤ d')
    (r : ℝ) (hr : 0 ≤ r) : C * (1 + r) ^ d ≤ C' * (1 + r) ^ d' := by
  have h1 : (1 : ℝ) ≤ 1 + r := by linarith
  have hpow : (1 + r) ^ d ≤ (1 + r) ^ d' := pow_le_pow_right₀ h1 hdd
  have hpos : (0 : ℝ) ≤ (1 + r) ^ d := by positivity
  calc C * (1 + r) ^ d ≤ C * (1 + r) ^ d' := mul_le_mul_of_nonneg_left hpow hC
    _ ≤ C' * (1 + r) ^ d' := by
        refine mul_le_mul_of_nonneg_right hCC ?_
        positivity

theorem FiniteOrderEnvelope.mono {f : ℂ → ℂ} (hf : FiniteOrderEnvelope f) (C' : ℝ) (d' : ℕ) :
    ∃ C ≥ C', ∃ d ≥ d', 0 ≤ C ∧ ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ d) := by
  obtain ⟨C, d, hC, hbound⟩ := hf
  refine ⟨max C (max C' 0), le_trans (le_max_left _ _) (le_max_right _ _), max d d',
    le_max_right _ _, le_trans (le_max_right _ _) (le_max_right _ _), fun z => ?_⟩
  refine le_trans (hbound z) (Real.exp_le_exp.mpr ?_)
  exact envelope_exponent_le hC (le_max_left _ _) (le_max_left _ _) _ (norm_nonneg z)

/-- Constants have a finite-order envelope. -/
theorem FiniteOrderEnvelope.const (a : ℂ) : FiniteOrderEnvelope (fun _ => a) := by
  refine ⟨‖a‖, 0, norm_nonneg a, fun z => ?_⟩
  rw [pow_zero, mul_one]
  exact le_trans (by linarith) (Real.add_one_le_exp ‖a‖)

/-- Products have a finite-order envelope. -/
theorem FiniteOrderEnvelope.mul {f g : ℂ → ℂ} (hf : FiniteOrderEnvelope f)
    (hg : FiniteOrderEnvelope g) : FiniteOrderEnvelope (fun z => f z * g z) := by
  obtain ⟨C₁, d₁, hC₁, hb₁⟩ := hf
  obtain ⟨C₂, d₂, hC₂, hb₂⟩ := hg
  refine ⟨C₁ + C₂, max d₁ d₂, by linarith, fun z => ?_⟩
  have hr : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have h1 : C₁ * (1 + ‖z‖) ^ d₁ ≤ C₁ * (1 + ‖z‖) ^ (max d₁ d₂) :=
    envelope_exponent_le hC₁ le_rfl (le_max_left _ _) _ hr
  have h2 : C₂ * (1 + ‖z‖) ^ d₂ ≤ C₂ * (1 + ‖z‖) ^ (max d₁ d₂) :=
    envelope_exponent_le hC₂ le_rfl (le_max_right _ _) _ hr
  calc ‖f z * g z‖ = ‖f z‖ * ‖g z‖ := norm_mul _ _
    _ ≤ Real.exp (C₁ * (1 + ‖z‖) ^ d₁) * Real.exp (C₂ * (1 + ‖z‖) ^ d₂) :=
        mul_le_mul (hb₁ z) (hb₂ z) (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (C₁ * (1 + ‖z‖) ^ d₁ + C₂ * (1 + ‖z‖) ^ d₂) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((C₁ + C₂) * (1 + ‖z‖) ^ (max d₁ d₂)) := by
        refine Real.exp_le_exp.mpr ?_
        have : (C₁ + C₂) * (1 + ‖z‖) ^ (max d₁ d₂)
            = C₁ * (1 + ‖z‖) ^ (max d₁ d₂) + C₂ * (1 + ‖z‖) ^ (max d₁ d₂) := by ring
        rw [this]; linarith

/-- Sums have a finite-order envelope. -/
theorem FiniteOrderEnvelope.add {f g : ℂ → ℂ} (hf : FiniteOrderEnvelope f)
    (hg : FiniteOrderEnvelope g) : FiniteOrderEnvelope (fun z => f z + g z) := by
  obtain ⟨C₁, d₁, hC₁, hb₁⟩ := hf
  obtain ⟨C₂, d₂, hC₂, hb₂⟩ := hg
  set C : ℝ := max C₁ C₂ with hC
  set d : ℕ := max d₁ d₂ with hd
  have hC0 : 0 ≤ C := le_trans hC₁ (le_max_left _ _)
  refine ⟨C + 1, d, by linarith, fun z => ?_⟩
  have hr : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ d := one_le_pow₀ (by linarith)
  have h1 : C₁ * (1 + ‖z‖) ^ d₁ ≤ C * (1 + ‖z‖) ^ d :=
    envelope_exponent_le hC₁ (le_max_left _ _) (le_max_left _ _) _ hr
  have h2 : C₂ * (1 + ‖z‖) ^ d₂ ≤ C * (1 + ‖z‖) ^ d :=
    envelope_exponent_le hC₂ (le_max_right _ _) (le_max_right _ _) _ hr
  have hlog : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  calc ‖f z + g z‖ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
    _ ≤ Real.exp (C * (1 + ‖z‖) ^ d) + Real.exp (C * (1 + ‖z‖) ^ d) := by
        refine add_le_add (le_trans (hb₁ z) (Real.exp_le_exp.mpr h1))
          (le_trans (hb₂ z) (Real.exp_le_exp.mpr h2))
    _ = 2 * Real.exp (C * (1 + ‖z‖) ^ d) := by ring
    _ = Real.exp (Real.log 2) * Real.exp (C * (1 + ‖z‖) ^ d) := by
        rw [Real.exp_log (by norm_num)]
    _ = Real.exp (Real.log 2 + C * (1 + ‖z‖) ^ d) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((C + 1) * (1 + ‖z‖) ^ d) := by
        refine Real.exp_le_exp.mpr ?_
        have : (C + 1) * (1 + ‖z‖) ^ d = C * (1 + ‖z‖) ^ d + (1 + ‖z‖) ^ d := by ring
        rw [this]; linarith

theorem FiniteOrderEnvelope.neg {f : ℂ → ℂ} (hf : FiniteOrderEnvelope f) :
    FiniteOrderEnvelope (fun z => -f z) := by
  obtain ⟨C, d, hC, hb⟩ := hf
  exact ⟨C, d, hC, fun z => by simpa using hb z⟩

theorem FiniteOrderEnvelope.sub {f g : ℂ → ℂ} (hf : FiniteOrderEnvelope f)
    (hg : FiniteOrderEnvelope g) : FiniteOrderEnvelope (fun z => f z - g z) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- Precomposition with an affine map preserves the finite-order envelope. -/
theorem FiniteOrderEnvelope.compAffine {f : ℂ → ℂ} (hf : FiniteOrderEnvelope f) (a b : ℂ) :
    FiniteOrderEnvelope (fun z => f (a * z + b)) := by
  obtain ⟨C, d, hC, hb⟩ := hf
  set M : ℝ := 1 + ‖a‖ + ‖b‖ with hM
  have hM1 : (1 : ℝ) ≤ M := by
    have := norm_nonneg a; have := norm_nonneg b; rw [hM]; linarith
  refine ⟨C * M ^ d, d, by positivity, fun z => ?_⟩
  refine le_trans (hb (a * z + b)) (Real.exp_le_exp.mpr ?_)
  have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hnorm : ‖a * z + b‖ ≤ ‖a‖ * ‖z‖ + ‖b‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul]
  have hkey : 1 + ‖a * z + b‖ ≤ M * (1 + ‖z‖) := by
    have ha : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
    have hbn : (0 : ℝ) ≤ ‖b‖ := norm_nonneg b
    have hexp : M * (1 + ‖z‖)
        = 1 + ‖a‖ + ‖a‖ * ‖z‖ + ‖b‖ + ‖b‖ * ‖z‖ + ‖z‖ := by rw [hM]; ring
    rw [hexp]
    linarith [mul_nonneg hbn hz]
  have hpow : (1 + ‖a * z + b‖) ^ d ≤ (M * (1 + ‖z‖)) ^ d :=
    pow_le_pow_left₀ (by positivity) hkey d
  calc C * (1 + ‖a * z + b‖) ^ d ≤ C * (M * (1 + ‖z‖)) ^ d :=
        mul_le_mul_of_nonneg_left hpow hC
    _ = C * M ^ d * (1 + ‖z‖) ^ d := by rw [mul_pow]; ring

/-- A square root of a finite-order function has a finite-order envelope. -/
theorem FiniteOrderEnvelope.of_sq {g : ℂ → ℂ} (h : FiniteOrderEnvelope (fun z => g z ^ (2 : ℕ))) :
    FiniteOrderEnvelope g := by
  obtain ⟨C, d, hC, hb⟩ := h
  refine ⟨C / 2, d, by linarith, fun z => ?_⟩
  have hsq : ‖g z‖ ^ (2 : ℕ) ≤ Real.exp (C * (1 + ‖z‖) ^ d) := by
    simpa [norm_pow] using hb z
  have hhalf : Real.sqrt (Real.exp (C * (1 + ‖z‖) ^ d))
      = Real.exp (C / 2 * (1 + ‖z‖) ^ d) := by
    rw [show Real.exp (C * (1 + ‖z‖) ^ d)
        = (Real.exp (C / 2 * (1 + ‖z‖) ^ d)) ^ (2 : ℕ) by rw [sq, ← Real.exp_add]; ring_nf]
    exact Real.sqrt_sq (Real.exp_nonneg _)
  have hstep := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), hhalf] at hstep

/-! ### Hadamard's zero-free factorization -/

/-- **Hadamard's zero-free factorization.**  A nowhere-vanishing entire function with a
finite-order growth envelope is the exponential of a polynomial.

The proof takes an entire logarithm `g` (`exists_entire_log_of_ne_zero`), turns the one-sided bound
on `Re g` into a two-sided bound by the Borel--Carathéodory inequality, and then invokes the
generalized Liouville theorem `exists_polynomial_of_polyGrowth`. -/
theorem exists_polynomial_exp_of_ne_zero_of_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) {C : ℝ} {d : ℕ} (hC : 0 ≤ C)
    (hgrow : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ d)) :
    ∃ p : Polynomial ℂ, ∀ z, f z = Complex.exp (p.eval z) := by
  obtain ⟨g, hgdiff, hg0, hfg⟩ := exists_entire_log_of_ne_zero hf hne
  have hf0 : ‖f 0‖ ≠ 0 := norm_ne_zero_iff.mpr (hne 0)
  have hf0pos : 0 < ‖f 0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hf0)
  -- the real part of the logarithm obeys the same envelope
  have hRe : ∀ w : ℂ, (g w).re ≤ C * (1 + ‖w‖) ^ d - Real.log ‖f 0‖ := by
    intro w
    have hnorm : ‖f w‖ = ‖f 0‖ * Real.exp ((g w).re) := by
      rw [hfg w, norm_mul, Complex.norm_exp]
    have hlog : Real.log ‖f 0‖ + (g w).re ≤ C * (1 + ‖w‖) ^ d := by
      have h1 : Real.log ‖f w‖ ≤ C * (1 + ‖w‖) ^ d := by
        have := Real.log_le_log (norm_pos_iff.mpr (hne w)) (hgrow w)
        rwa [Real.log_exp] at this
      rw [hnorm, Real.log_mul hf0 (Real.exp_ne_zero _), Real.log_exp] at h1
      exact h1
    linarith
  -- Borel--Carathéodory turns it into a two-sided polynomial norm bound
  have hbound : ∀ z : ℂ,
      ‖g z‖ ≤ (C * 3 ^ d + |1 - Real.log ‖f 0‖|) * (‖z‖ + 1) ^ (d + 1) := by
    intro z
    set R : ℝ := 2 * ‖z‖ + 2 with hR
    set A : ℝ := C * (3 + 2 * ‖z‖) ^ d - Real.log ‖f 0‖ + 1 with hA
    have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hRpos : 0 < R := by rw [hR]; linarith
    have hApos : 0 < A := by
      have hzero := hRe 0
      rw [hg0] at hzero
      simp only [norm_zero, Complex.zero_re, add_zero, one_pow, mul_one] at hzero
      have hmono : C ≤ C * (3 + 2 * ‖z‖) ^ d := by
        calc C = C * 1 ^ d := by rw [one_pow, mul_one]
          _ ≤ C * (3 + 2 * ‖z‖) ^ d :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by linarith) d) hC
      rw [hA]; linarith
    have hReA : ∀ w ∈ ball (0 : ℂ) R, (g w).re ≤ A := by
      intro w hw
      have hwn : ‖w‖ < R := by simpa [Complex.dist_eq] using hw
      have h1 := hRe w
      have hmono : C * (1 + ‖w‖) ^ d ≤ C * (3 + 2 * ‖z‖) ^ d := by
        refine mul_le_mul_of_nonneg_left ?_ hC
        refine pow_le_pow_left₀ (by positivity) ?_ d
        rw [hR] at hwn
        linarith
      rw [hA]
      linarith
    have hzball : z ∈ ball (0 : ℂ) R := by
      simp only [mem_ball, Complex.dist_eq, sub_zero]
      rw [hR]; linarith
    have hBC := RHTower.borel_caratheodory (g := g) (c := 0) (z := z) (R := R) (A := A)
      hgdiff.differentiableOn hReA (by rw [hg0]; simpa using hApos) hzball
    rw [hg0, sub_zero, sub_zero, Complex.zero_re, sub_zero] at hBC
    have hden : 2 * ‖z‖ / (R - ‖z‖) ≤ ‖z‖ := by
      rw [hR, div_le_iff₀ (by linarith)]
      nlinarith
    have hstep : ‖g z‖ ≤ ‖z‖ * A :=
      le_trans hBC (mul_le_mul_of_nonneg_right hden hApos.le)
    have h3 : (3 + 2 * ‖z‖) ^ d ≤ 3 ^ d * (‖z‖ + 1) ^ d := by
      rw [← mul_pow]
      refine pow_le_pow_left₀ (by linarith) (by linarith) d
    have hone' : (‖z‖ + 1) ≤ (‖z‖ + 1) ^ (d + 1) := by
      calc (‖z‖ + 1) = (‖z‖ + 1) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (‖z‖ + 1) ^ (d + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    have hzle : ‖z‖ ≤ ‖z‖ + 1 := by linarith
    have hK : 1 - Real.log ‖f 0‖ ≤ |1 - Real.log ‖f 0‖| := le_abs_self _
    have hK0 : 0 ≤ |1 - Real.log ‖f 0‖| := abs_nonneg _
    have hterm1 : ‖z‖ * (C * (3 + 2 * ‖z‖) ^ d) ≤ C * 3 ^ d * (‖z‖ + 1) ^ (d + 1) := by
      have h4 : C * (3 + 2 * ‖z‖) ^ d ≤ C * (3 ^ d * (‖z‖ + 1) ^ d) :=
        mul_le_mul_of_nonneg_left h3 hC
      have hc : (0 : ℝ) ≤ C * (3 + 2 * ‖z‖) ^ d := mul_nonneg hC (by positivity)
      calc ‖z‖ * (C * (3 + 2 * ‖z‖) ^ d)
          ≤ (‖z‖ + 1) * (C * (3 ^ d * (‖z‖ + 1) ^ d)) :=
            mul_le_mul hzle h4 hc (by linarith)
        _ = C * 3 ^ d * (‖z‖ + 1) ^ (d + 1) := by rw [pow_succ]; ring
    have hterm2 : ‖z‖ * (1 - Real.log ‖f 0‖) ≤
        |1 - Real.log ‖f 0‖| * (‖z‖ + 1) ^ (d + 1) := by
      calc ‖z‖ * (1 - Real.log ‖f 0‖) ≤ ‖z‖ * |1 - Real.log ‖f 0‖| :=
            mul_le_mul_of_nonneg_left hK hz0
        _ ≤ (‖z‖ + 1) ^ (d + 1) * |1 - Real.log ‖f 0‖| :=
            mul_le_mul_of_nonneg_right (hzle.trans hone') hK0
        _ = |1 - Real.log ‖f 0‖| * (‖z‖ + 1) ^ (d + 1) := mul_comm _ _
    have hexp : ‖z‖ * A ≤ (C * 3 ^ d + |1 - Real.log ‖f 0‖|) * (‖z‖ + 1) ^ (d + 1) := by
      have hsplit : ‖z‖ * A =
          ‖z‖ * (C * (3 + 2 * ‖z‖) ^ d) + ‖z‖ * (1 - Real.log ‖f 0‖) := by rw [hA]; ring
      have hrhs : (C * 3 ^ d + |1 - Real.log ‖f 0‖|) * (‖z‖ + 1) ^ (d + 1) =
          C * 3 ^ d * (‖z‖ + 1) ^ (d + 1) +
            |1 - Real.log ‖f 0‖| * (‖z‖ + 1) ^ (d + 1) := by ring
      rw [hsplit, hrhs]
      exact add_le_add hterm1 hterm2
    exact hstep.trans hexp
  obtain ⟨q, hq⟩ := RHTower.exists_polynomial_of_polyGrowth hgdiff hbound
  refine ⟨q + Polynomial.C (Complex.log (f 0)), fun z => ?_⟩
  rw [hfg z, Polynomial.eval_add, Polynomial.eval_C, ← hq z, Complex.exp_add,
    Complex.exp_log (hne 0)]
  ring

/-- **Hadamard's zero-free factorization**, phrased through the envelope predicate. -/
theorem exists_polynomial_exp_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) (henv : FiniteOrderEnvelope f) :
    ∃ p : Polynomial ℂ, ∀ z, f z = Complex.exp (p.eval z) := by
  obtain ⟨C, d, hC, hbound⟩ := henv
  exact exists_polynomial_exp_of_ne_zero_of_growth hf hne hC hbound

/-! ### Polynomials sit inside the envelope class -/

/-- The crude coefficient bound for a complex polynomial. -/
theorem norm_eval_le (p : Polynomial ℂ) (z : ℂ) :
    ‖p.eval z‖ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * (1 + ‖z‖) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans (pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖z‖ ≤ 1 + ‖z‖) i) ?_
  refine pow_le_pow_right₀ (by have := norm_nonneg z; linarith) ?_
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)

theorem exists_polynomial_norm_bound (p : Polynomial ℂ) :
    ∃ (M : ℝ) (d : ℕ), 0 ≤ M ∧ ∀ z : ℂ, ‖p.eval z‖ ≤ M * (1 + ‖z‖) ^ d :=
  ⟨_, p.natDegree, Finset.sum_nonneg fun _ _ => norm_nonneg _, norm_eval_le p⟩

/-- A polynomial has a finite-order envelope. -/
theorem finiteOrderEnvelope_polynomial (p : Polynomial ℂ) :
    FiniteOrderEnvelope (fun z => p.eval z) := by
  obtain ⟨M, d, hM, hbound⟩ := exists_polynomial_norm_bound p
  refine ⟨M, d, hM, fun z => ?_⟩
  refine le_trans (hbound z) (le_trans (by linarith) (Real.add_one_le_exp _))

/-- The exponential of a polynomial has a finite-order envelope. -/
theorem finiteOrderEnvelope_exp_polynomial (p : Polynomial ℂ) :
    FiniteOrderEnvelope (fun z => Complex.exp (p.eval z)) := by
  obtain ⟨M, d, hM, hbound⟩ := exists_polynomial_norm_bound p
  refine ⟨M, d, hM, fun z => ?_⟩
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr (le_trans (Complex.re_le_norm _) (hbound z))

end GaloisForLFunctions.HTGeometry
