import GaloisForLFunctions.ArithmeticScatteringHolography.TheKreinFluxLaw
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The Lax–Phillips semigroup and Kramers–Kronig

**The semigroup.** On a black hole the ringdown is a recurrence, so the Hankel operator of the echo train has rank two: every `3 × 3` minor of `R(n + m)` vanishes (`hankel_det_eq_zero`). This is
Kronecker's theorem, and the factorization `R(m + n) = a_n R(m + 1) + b_n R(m)` (`recurrence_shift`) is the Lax–Phillips semigroup: the compression of the wave group to the interaction space, a
`2 × 2` matrix `Z`, the companion of the denominator, with `det Z = q` (`lpMatrix_det`) and characteristic polynomial `z² - t z + q` (`lpMatrix_charpoly`). Its eigenvectors are the modes
(`lpMatrix_mode`). Over `ℤ` no finite rank exists, since no compact probe silences the horizon (`infinite_excited_modes`).

**The functional model.** The Hermitian Krein form is the metric of the model space. `Z` multiplies it by exactly `q` for every `t` (`kreinHerm_step`), so `Z/√q` is always unitary for it. It is a
Hilbert metric exactly under universal damping (`kreinHerm_nonneg_iff`), and its value on a mode is the **Krein signature**

  `H(1, z) = 2 (Im z)²`  (`kreinHerm_mode`):

positive on an oscillating mode, and zero on a real one. Modes can leave the circle only by colliding on the real axis, where their state is a neutral vector of the form. So the model space of a
fake is a Krein space, and that is the whole difference.

**Kramers–Kronig.** The causal variable makes the relation elementary: a function holomorphic on a disc has `∫ Re F cos nθ = ∫ Im F sin nθ`, by Cauchy (`kramers_kronig`). For the causal symbol, with
`F = log P` on a disc free of zeros, this is log-modulus against phase (`causal_symbol_kramers_kronig`). The disc reaches the universal circle `|w| = q^{-½}` exactly when there is no slow mode; beyond it, the
Bode integral is what remains.
-/

open Complex MeasureTheory
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

/-! ### The semigroup -/

section Algebra

variable {R : Type*} [CommRing R]

/-- **The Lax–Phillips matrix**: the companion of the denominator, acting on the state `(R_n, R_{n+1})`. -/
def lpMatrix (q t : R) : Matrix (Fin 2) (Fin 2) R := !![0, 1; -q, t]

theorem lpMatrix_mulVec (q t x y : R) : (lpMatrix q t).mulVec ![x, y] = ![y, t * y - q * x] := by
  ext i
  fin_cases i
  · simp [lpMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · simp [lpMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- **Liouville's law for the semigroup.** -/
theorem lpMatrix_det (q t : R) : (lpMatrix q t).det = q := by
  rw [lpMatrix, Matrix.det_fin_two_of]
  ring

/-- The spectrum of the semigroup is the set of modes. -/
theorem lpMatrix_charpoly (q t z : R) :
    (z • (1 : Matrix (Fin 2) (Fin 2) R) - lpMatrix q t).det = z ^ 2 - t * z + q := by
  rw [Matrix.det_fin_two]
  simp [lpMatrix]
  ring

/-- A mode is an eigenvector of the semigroup. -/
theorem lpMatrix_mode {q t z : R} (hz : z ^ 2 - t * z + q = 0) :
    (lpMatrix q t).mulVec ![1, z] = z • ![1, z] := by
  rw [lpMatrix_mulVec]
  ext i
  fin_cases i
  · simp
  · simp
    linear_combination -hz

/-- The coefficients of `π^n = a_n π + b_n`. -/
def shiftPair (q t : R) : ℕ → R × R
  | 0 => (0, 1)
  | n + 1 => (t * (shiftPair q t n).1 + (shiftPair q t n).2, -q * (shiftPair q t n).1)

/-- The expansion of the shift in the semigroup. -/
theorem recurrence_shift {q t : R} {r : ℕ → R} (hr : ∀ n, r (n + 2) = t * r (n + 1) - q * r n) :
    ∃ a b : ℕ → R, ∀ n m, r (m + n) = a n * r (m + 1) + b n * r m := by
  refine ⟨fun n => (shiftPair q t n).1, fun n => (shiftPair q t n).2, fun n => ?_⟩
  induction n with
  | zero =>
    intro m
    simp [shiftPair]
  | succ n ih =>
    intro m
    have h1 := ih (m + 1)
    rw [show m + (n + 1) = m + 1 + n by ring, h1, show m + 1 + 1 = m + 2 from rfl, hr m]
    simp only [shiftPair]
    ring

/-- **Kronecker: the Hankel operator of the echo train has rank two.** -/
theorem hankel_det_eq_zero {q t : R} {r : ℕ → R} (hr : ∀ n, r (n + 2) = t * r (n + 1) - q * r n)
    (n : Fin 3 → ℕ) (m : Fin 3 → ℕ) :
    (Matrix.of fun i j => r (m j + n i)).det = 0 := by
  obtain ⟨a, b, hab⟩ := recurrence_shift hr
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply]
  rw [hab (n 0) (m 0), hab (n 0) (m 1), hab (n 0) (m 2), hab (n 1) (m 0), hab (n 1) (m 1), hab (n 1) (m 2),
    hab (n 2) (m 0), hab (n 2) (m 1), hab (n 2) (m 2)]
  ring

end Algebra

/-! ### The functional model -/

/-- **The Hermitian Krein form**: the metric of the model space. -/
def kreinHerm (q t : ℝ) (x y : ℂ) : ℝ :=
  q * Complex.normSq x - t * (conj x * y).re + Complex.normSq y

/-- **`Z` multiplies the Krein form by exactly `q`, for every `t`.** -/
theorem kreinHerm_step (q t : ℝ) (x y : ℂ) :
    kreinHerm q t y ((t : ℂ) * y - (q : ℂ) * x) = q * kreinHerm q t x y := by
  unfold kreinHerm
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The form splits into the real form on the real and imaginary parts. -/
theorem kreinHerm_split (q t : ℝ) (x y : ℂ) :
    kreinHerm q t x y = kreinSquare q t x.re y.re + kreinSquare q t x.im y.im := by
  unfold kreinHerm kreinSquare
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- **The model space is a Hilbert space exactly under universal damping.** -/
theorem kreinHerm_nonneg_iff {q t : ℝ} : (∀ x y : ℂ, 0 ≤ kreinHerm q t x y) ↔ t ^ 2 ≤ 4 * q := by
  rw [← kreinSquare_nonneg_iff]
  constructor
  · intro h x y
    have := h (x : ℂ) (y : ℂ)
    rw [kreinHerm_split] at this
    simpa [kreinSquare] using this
  · intro h x y
    rw [kreinHerm_split]
    exact add_nonneg (h _ _) (h _ _)

/-- **The Krein signature of a mode.** `H(1, z) = 2 (Im z)²`: positive on an oscillating mode, and zero exactly when the mode is real. -/
theorem kreinHerm_mode {q t : ℝ} {z : ℂ} (hz : z ^ 2 - (t : ℂ) * z + (q : ℂ) = 0) :
    kreinHerm q t 1 z = 2 * z.im ^ 2 := by
  have hre := congrArg Complex.re hz
  simp only [sq, Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re] at hre
  unfold kreinHerm
  simp only [Complex.normSq_apply, map_one, one_mul]
  nlinarith [hre]

/-- **Along the semigroup the metric decays at exactly the universal rate**, on every black hole. -/
theorem kreinHerm_semigroup {q t : ℝ} (r : ℕ → ℂ)
    (hr : ∀ n, r (n + 2) = (t : ℂ) * r (n + 1) - (q : ℂ) * r n) (n : ℕ) :
    kreinHerm q t (r n) (r (n + 1)) = q ^ n * kreinHerm q t (r 0) (r 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 from rfl, hr n, kreinHerm_step, ih, pow_succ]
    ring

/-! ### Kramers–Kronig -/

/-- The Fourier coefficients of positive frequency of a holomorphic function on a circle vanish. -/
theorem integral_circle_exp_eq_zero {r : ℝ} (hr : 0 < r) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.closedBall 0 r)) {n : ℕ} (hn : 1 ≤ n) :
    ∫ θ in (0 : ℝ)..(2 * π), F (circleMap 0 r θ) * Complex.exp (((n : ℝ) * θ : ℝ) * I) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hg : DifferentiableOn ℂ (fun w => F w * w ^ m) (Metric.closedBall 0 r) :=
    hF.mul (differentiable_id.pow m).differentiableOn
  have hint := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable (c := 0) hr.le
    Set.countable_empty hg.continuousOn (fun z hz =>
      hg.differentiableAt (Metric.closedBall_mem_nhds_of_mem hz.1))
  rw [circleIntegral] at hint
  have hne : (I * (r : ℂ) ^ (m + 1)) ≠ 0 := by
    have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    exact mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ this)
  have key : ∫ θ in (0 : ℝ)..(2 * π), deriv (circleMap 0 r) θ •
      (F (circleMap 0 r θ) * circleMap 0 r θ ^ m) =
      (I * (r : ℂ) ^ (m + 1)) *
        ∫ θ in (0 : ℝ)..(2 * π), F (circleMap 0 r θ) * Complex.exp ((((m + 1 : ℕ) : ℝ) * θ : ℝ) * I) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have e1 : Complex.exp ((((m + 1 : ℕ) : ℝ) * θ : ℝ) * I) = Complex.exp (θ * I) ^ (m + 1) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    show deriv (circleMap 0 r) θ • _ = _
    rw [deriv_circleMap, e1, smul_eq_mul, circleMap_zero, mul_pow]
    ring
  rw [key] at hint
  exact (mul_eq_zero.mp hint).resolve_left hne

/-- **Kramers–Kronig.** On a circle inside the domain of a holomorphic function, the cosine coefficients of the real part are the sine coefficients of the imaginary part, and the
sine coefficients of the real part are minus the cosine coefficients of the imaginary part. -/
theorem kramers_kronig {r : ℝ} (hr : 0 < r) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Metric.closedBall 0 r)) {n : ℕ} (hn : 1 ≤ n) :
    (∫ θ in (0 : ℝ)..(2 * π), (F (circleMap 0 r θ)).re * Real.cos (n * θ)) =
        ∫ θ in (0 : ℝ)..(2 * π), (F (circleMap 0 r θ)).im * Real.sin (n * θ) ∧
      (∫ θ in (0 : ℝ)..(2 * π), (F (circleMap 0 r θ)).re * Real.sin (n * θ)) =
        -∫ θ in (0 : ℝ)..(2 * π), (F (circleMap 0 r θ)).im * Real.cos (n * θ) := by
  have hzero := integral_circle_exp_eq_zero hr hF hn
  have hcirc : Continuous fun θ : ℝ => F (circleMap 0 r θ) := by
    refine hF.continuousOn.comp_continuous (continuous_circleMap 0 r) fun θ => ?_
    simp [abs_of_pos hr]
  have hre : Continuous fun θ : ℝ => (F (circleMap 0 r θ)).re := Complex.continuous_re.comp hcirc
  have him : Continuous fun θ : ℝ => (F (circleMap 0 r θ)).im := Complex.continuous_im.comp hcirc
  have hcos : Continuous fun θ : ℝ => Real.cos (n * θ) := Real.continuous_cos.comp (by fun_prop)
  have hsin : Continuous fun θ : ℝ => Real.sin (n * θ) := Real.continuous_sin.comp (by fun_prop)
  have hexp (θ : ℝ) : F (circleMap 0 r θ) * Complex.exp (((n : ℝ) * θ : ℝ) * I) =
      (((F (circleMap 0 r θ)).re * Real.cos (n * θ) - (F (circleMap 0 r θ)).im * Real.sin (n * θ) : ℝ) : ℂ) +
        (((F (circleMap 0 r θ)).re * Real.sin (n * θ) + (F (circleMap 0 r θ)).im * Real.cos (n * θ) : ℝ) : ℂ) * I := by
    have hc : Complex.exp (((n : ℝ) * θ : ℝ) * I) =
        ((Real.cos (n * θ) : ℝ) : ℂ) + ((Real.sin (n * θ) : ℝ) : ℂ) * I := by
      rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
    rw [hc]
    generalize Real.cos (n * θ) = c
    generalize Real.sin (n * θ) = d
    generalize F (circleMap 0 r θ) = z
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im]
  simp only [hexp] at hzero
  have hi1 : IntervalIntegrable (fun θ : ℝ => (((F (circleMap 0 r θ)).re * Real.cos (n * θ) -
      (F (circleMap 0 r θ)).im * Real.sin (n * θ) : ℝ) : ℂ)) volume 0 (2 * π) :=
    (Complex.continuous_ofReal.comp ((hre.mul hcos).sub (him.mul hsin))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun θ : ℝ => (((F (circleMap 0 r θ)).re * Real.sin (n * θ) +
      (F (circleMap 0 r θ)).im * Real.cos (n * θ) : ℝ) : ℂ) * I) volume 0 (2 * π) :=
    ((Complex.continuous_ofReal.comp ((hre.mul hsin).add (him.mul hcos))).mul
      continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal] at hzero
  have hR := congrArg Complex.re hzero
  have hI := congrArg Complex.im hzero
  simp at hR hI
  have j1 : IntervalIntegrable (fun θ : ℝ => (F (circleMap 0 r θ)).re * Real.cos (n * θ)) volume 0 (2 * π) :=
    (hre.mul hcos).intervalIntegrable _ _
  have j2 : IntervalIntegrable (fun θ : ℝ => (F (circleMap 0 r θ)).im * Real.sin (n * θ)) volume 0 (2 * π) :=
    (him.mul hsin).intervalIntegrable _ _
  have j3 : IntervalIntegrable (fun θ : ℝ => (F (circleMap 0 r θ)).re * Real.sin (n * θ)) volume 0 (2 * π) :=
    (hre.mul hsin).intervalIntegrable _ _
  have j4 : IntervalIntegrable (fun θ : ℝ => (F (circleMap 0 r θ)).im * Real.cos (n * θ)) volume 0 (2 * π) :=
    (him.mul hcos).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub j1 j2] at hR
  rw [intervalIntegral.integral_add j3 j4] at hI
  exact ⟨by linarith, by linarith⟩

/-- **Kramers–Kronig for the causal symbol.** On a disc with no zero of `P(w) = (1 - a w)(1 - b w)`, the log-modulus of `P` determines its phase. -/
theorem causal_symbol_kramers_kronig {a b : ℂ} {r : ℝ} (hr : 0 < r) (ha : ‖a‖ * r < 1) (hb : ‖b‖ * r < 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ θ in (0 : ℝ)..(2 * π),
        Real.log ‖(1 - a * circleMap 0 r θ) * (1 - b * circleMap 0 r θ)‖ * Real.cos (n * θ)) =
      ∫ θ in (0 : ℝ)..(2 * π), (Complex.arg (1 - a * circleMap 0 r θ) + Complex.arg (1 - b * circleMap 0 r θ)) *
        Real.sin (n * θ) := by
  have hslit {c w : ℂ} (hc : ‖c‖ * r < 1) (hw : w ∈ Metric.closedBall (0 : ℂ) r) :
      1 - c * w ∈ Complex.slitPlane := by
    left
    have hw' : ‖w‖ ≤ r := by simpa using hw
    have h1 : ‖c * w‖ < 1 := by
      rw [norm_mul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hw' (norm_nonneg _)) hc
    have h2 := (Complex.abs_re_le_norm (c * w)).trans_lt h1
    simp only [Complex.sub_re, Complex.one_re]
    linarith [(abs_lt.mp h2).2]
  set F : ℂ → ℂ := fun w => Complex.log (1 - a * w) + Complex.log (1 - b * w) with hFdef
  have hF : DifferentiableOn ℂ F (Metric.closedBall 0 r) := by
    intro w hw
    have h1 : DifferentiableWithinAt ℂ (fun w => 1 - a * w) (Metric.closedBall 0 r) w := by fun_prop
    have h2 : DifferentiableWithinAt ℂ (fun w => 1 - b * w) (Metric.closedBall 0 r) w := by fun_prop
    exact (h1.clog (hslit ha hw)).add (h2.clog (hslit hb hw))
  have h := (kramers_kronig hr hF hn).1
  have hmem (θ : ℝ) : circleMap 0 r θ ∈ Metric.closedBall (0 : ℂ) r := by
    simp [abs_of_pos hr]
  have e1 (θ : ℝ) : (F (circleMap 0 r θ)).re =
      Real.log ‖(1 - a * circleMap 0 r θ) * (1 - b * circleMap 0 r θ)‖ := by
    have h1 := Complex.slitPlane_ne_zero (hslit ha (hmem θ))
    have h2 := Complex.slitPlane_ne_zero (hslit hb (hmem θ))
    simp only [hFdef, Complex.add_re, Complex.log_re]
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)]
  have e2 (θ : ℝ) : (F (circleMap 0 r θ)).im =
      Complex.arg (1 - a * circleMap 0 r θ) + Complex.arg (1 - b * circleMap 0 r θ) := by
    simp only [hFdef, Complex.add_im, Complex.log_im]
  simp only [e1, e2] at h
  exact h

end GaloisForLFunctions.ArithmeticScatteringHolography

end
