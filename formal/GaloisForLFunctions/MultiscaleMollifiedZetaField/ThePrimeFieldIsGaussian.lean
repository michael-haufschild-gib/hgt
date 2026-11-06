import GaloisForLFunctions.MultiscaleMollifiedZetaField.PrimeSumsAreSteinhausBelowTheWindow
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The prime field is Gaussian below the window

Let `F(t) = Σ_{p ∈ P} w(p) cos(t log p)` with `0 ≤ w ≤ 1`, `W = Σ_p w(p)²`. If `W → ∞` and `(A Y)^K = o(T)` for every `K`, then the distribution of `F/√(W/2)` on `[T, 2T]`
tends to the standard Gaussian (`tendsto_primeFieldLaw_gaussian`).

**Mechanism.**
* On the model the coordinates `Re X_p` are independent with mean `0` and variance `½`, so the characteristic function is a product, each factor being `exp(−a²/4)` up to `|a|³/4`
  (`norm_integral_cexp_phase_sub_le`, `norm_integral_cexp_modelField_sub_le`).
* The moment generating function of a factor is at most `cosh b ≤ exp(b²/2)`, which bounds even moments by `(2K)! λ^{−2K} 2 exp(λ² W/2)` (`integral_modelField_even_pow_le`).
* Taylor's theorem at order `2K`, with the sharp remainder `|y|^{2K}/(2K)!` of `norm_cexp_sub_sum_le`, compares the height average of `exp(ivF)` with the model through the first `2K`
  moments (`norm_mean_cexp_primeField_sub_le`). Those moments agree by `abs_mean_primeField_pow_sub_model_le`.
-/

noncomputable section

open Complex MeasureTheory Filter Set ProbabilityTheory Topology
open RHTower.SteinhausModel

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-! ### Taylor's theorem for the unimodular exponential -/

/-- The Taylor remainder of `e^{iy}`. -/
def expRemainder (n : ℕ) (y : ℝ) : ℂ :=
  cexp ((y : ℂ) * I) - ∑ k ∈ Finset.range n, ((y : ℂ) * I) ^ k / (k.factorial : ℂ)

theorem continuous_expRemainder (n : ℕ) : Continuous (expRemainder n) := by
  unfold expRemainder
  fun_prop

theorem hasDerivAt_expRemainder_succ (n : ℕ) (y : ℝ) :
    HasDerivAt (expRemainder (n + 1)) (I * expRemainder n y) y := by
  have hexp : HasDerivAt (fun y : ℝ => cexp ((y : ℂ) * I)) (cexp ((y : ℂ) * I) * I) y := by
    have h1 : HasDerivAt (fun z : ℂ => cexp (z * I)) (cexp ((y : ℂ) * I) * (1 * I)) (y : ℂ) :=
      ((hasDerivAt_id' (y : ℂ)).mul_const I).cexp
    simpa using h1.comp_ofReal
  have hsum : HasDerivAt
      (fun y : ℝ => ∑ k ∈ Finset.range (n + 1), ((y : ℂ) * I) ^ k / (k.factorial : ℂ))
      (I * ∑ k ∈ Finset.range n, ((y : ℂ) * I) ^ k / (k.factorial : ℂ)) y := by
    induction n with
    | zero =>
      simpa using hasDerivAt_const y (1 : ℂ)
    | succ n ih =>
      have hterm : HasDerivAt
          (fun y : ℝ => ((y : ℂ) * I) ^ (n + 1) / ((n + 1).factorial : ℂ))
          (I * (((y : ℂ) * I) ^ n / (n.factorial : ℂ))) y := by
        have h1 : HasDerivAt (fun z : ℂ => (z * I) ^ (n + 1) / ((n + 1).factorial : ℂ))
            (((n + 1 : ℕ) : ℂ) * ((y : ℂ) * I) ^ n * (1 * I) / ((n + 1).factorial : ℂ)) (y : ℂ) := by
          have := (((hasDerivAt_id' (y : ℂ)).mul_const I).pow (n + 1)).div_const
            ((n + 1).factorial : ℂ)
          simpa using this
        have h2 := h1.comp_ofReal
        refine h2.congr_deriv ?_
        have hne : ((n.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
        have hne2 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast n.succ_ne_zero
        rw [Nat.factorial_succ]
        push_cast
        push_cast at hne2
        field_simp
      have hfun : (fun y : ℝ => ∑ k ∈ Finset.range (n + 1 + 1),
          ((y : ℂ) * I) ^ k / (k.factorial : ℂ)) =
          fun y : ℝ => ∑ k ∈ Finset.range (n + 1), ((y : ℂ) * I) ^ k / (k.factorial : ℂ) +
            ((y : ℂ) * I) ^ (n + 1) / ((n + 1).factorial : ℂ) := by
        funext z
        rw [Finset.sum_range_succ]
      rw [hfun, Finset.sum_range_succ, mul_add]
      exact ih.add hterm
  have h := hexp.sub hsum
  refine h.congr_deriv ?_
  unfold expRemainder
  ring

theorem expRemainder_succ_zero (n : ℕ) : expRemainder (n + 1) 0 = 0 := by
  unfold expRemainder
  rw [Finset.sum_range_succ']
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one]
  rw [Finset.sum_eq_zero]
  · simp
  · intro k _
    simp

theorem expRemainder_neg (n : ℕ) (y : ℝ) :
    expRemainder n (-y) = (starRingEnd ℂ) (expRemainder n y) := by
  unfold expRemainder
  rw [map_sub, map_sum, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg, map_div₀, map_pow,
    Complex.conj_natCast]
  rw [show -(y : ℂ) * I = (y : ℂ) * -I by ring]

/-- **Taylor's theorem for `e^{iy}` with the sharp remainder.** `‖e^{iy} − Σ_{k<n} (iy)^k/k!‖ ≤ |y|^n/n!`, for every real `y`. -/
theorem norm_cexp_sub_sum_le (n : ℕ) (y : ℝ) :
    ‖expRemainder n y‖ ≤ |y| ^ n / (n.factorial : ℝ) := by
  have hpos : ∀ y : ℝ, 0 ≤ y → ‖expRemainder n y‖ ≤ y ^ n / (n.factorial : ℝ) := by
    induction n with
    | zero =>
      intro y _
      simp only [expRemainder, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
        Nat.factorial_zero, Nat.cast_one, div_one]
      rw [Complex.norm_exp_ofReal_mul_I]
    | succ n ih =>
      intro y hy
      have hB : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x ^ (n + 1) / ((n + 1).factorial : ℝ))
          (x ^ n / (n.factorial : ℝ)) x := by
        intro x
        have h1 := ((hasDerivAt_id' x).pow (n + 1)).div_const (((n + 1).factorial : ℕ) : ℝ)
        refine h1.congr_deriv ?_
        have hne : ((n.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
        have hne2 : ((n : ℝ) + 1) ≠ 0 := by positivity
        rw [Nat.factorial_succ]
        push_cast
        field_simp
      refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := y)
        (f' := fun x => I * expRemainder n x) (continuous_expRemainder _).continuousOn
        (fun x _ => (hasDerivAt_expRemainder_succ n x).hasDerivWithinAt) ?_ hB ?_
        ⟨hy, le_rfl⟩
      · rw [expRemainder_succ_zero, norm_zero]
        simp
      · intro x hx
        rw [norm_mul, Complex.norm_I, one_mul]
        exact ih x hx.1
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]
    exact hpos y hy
  · have h := hpos (-y) (by linarith)
    rw [expRemainder_neg, RCLike.norm_conj] at h
    rwa [abs_of_nonpos hy]

/-! ### One phase -/

/-- The real part of a Steinhaus coordinate. -/
def phase (p : ℕ) (ω : Omega) : ℝ := (X p ω).re

theorem measurable_phase (p : ℕ) : Measurable (phase p) :=
  Complex.measurable_re.comp (measurable_X p)

theorem abs_phase_le (p : ℕ) (ω : Omega) : |phase p ω| ≤ 1 := by
  have := Complex.abs_re_le_norm (X p ω)
  rwa [norm_X] at this

theorem phase_eq_cos {p : ℕ} (hp : p.Prime) (ω : Omega) :
    phase p ω = Real.cos (2 * Real.pi * ω p) := by
  unfold phase
  rw [GaloisForLFunctions.RHTower.X_prime_eq hp]
  have : ((2 * Real.pi : ℝ) : ℂ) * I * ((ω p : ℝ) : ℂ) = ((2 * Real.pi * ω p : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem integrable_of_bound_phase {f : Omega → ℂ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ ω, ‖f ω‖ ≤ C) : Integrable f steinhausMeasure :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)

theorem integral_X_eq_zero' {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    ∫ ω, X n ω ∂steinhausMeasure = 0 := by
  have h := integral_X_mul_conj (n := n) (m := 1) hn0 one_ne_zero
  simp only [X_one, map_one, mul_one, if_neg hn1] at h
  exact h

/-- The phase has mean zero. -/
theorem integral_phase_eq_zero {p : ℕ} (hp : p.Prime) :
    ∫ ω, phase p ω ∂steinhausMeasure = 0 := by
  have h := integral_X_eq_zero' hp.ne_zero hp.ne_one
  have hint : Integrable (fun ω => X p ω) steinhausMeasure :=
    integrable_of_bound_phase (measurable_X p) (fun ω => (norm_X p ω).le)
  have hre := congrArg Complex.re h
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint] at hre
  simpa [phase] using hre

/-- The phase has variance `½`. -/
theorem integral_phase_sq {p : ℕ} (hp : p.Prime) :
    ∫ ω, phase p ω ^ 2 ∂steinhausMeasure = 1 / 2 := by
  have hpt : ∀ ω, phase p ω ^ 2 = 1 / 2 + (1 / 2) * (X (p * p) ω).re := by
    intro ω
    rw [X_mul hp.ne_zero hp.ne_zero, Complex.mul_re]
    have hn : (X p ω).re ^ 2 + (X p ω).im ^ 2 = 1 := by
      have := Complex.sq_norm (X p ω)
      rw [norm_X, Complex.normSq_apply] at this
      nlinarith
    simp only [phase]
    nlinarith
  simp_rw [hpt]
  have hne0 : p * p ≠ 0 := mul_ne_zero hp.ne_zero hp.ne_zero
  have hne1 : p * p ≠ 1 := by
    have := hp.one_lt
    nlinarith
  have h := integral_X_eq_zero' hne0 hne1
  have hint : Integrable (fun ω => X (p * p) ω) steinhausMeasure :=
    integrable_of_bound_phase (measurable_X _) (fun ω => (norm_X _ ω).le)
  have hre := congrArg Complex.re h
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint] at hre
  have hreint : Integrable (fun ω => (X (p * p) ω).re) steinhausMeasure := hint.re
  rw [integral_add (integrable_const _) (hreint.const_mul _), integral_const_mul]
  have h0 : ∫ ω, (X (p * p) ω).re ∂steinhausMeasure = 0 := by simpa using hre
  rw [h0]
  simp

/-- **One factor of the characteristic function.** For `|a| ≤ 1`, `‖E exp(i a Re X_p) − exp(−a²/4)‖ ≤ |a|³/4`. -/
theorem norm_integral_cexp_phase_sub_le {p : ℕ} (hp : p.Prime) {a : ℝ} (ha : |a| ≤ 1) :
    ‖∫ ω, cexp (((a * phase p ω : ℝ) : ℂ) * I) ∂steinhausMeasure -
        ((Real.exp (-(a ^ 2 / 4)) : ℝ) : ℂ)‖ ≤ |a| ^ 3 / 4 := by
  have hmeas : Measurable fun ω => cexp (((a * phase p ω : ℝ) : ℂ) * I) := by
    have := (measurable_phase p).const_mul a
    exact Complex.continuous_exp.measurable.comp
      ((Complex.measurable_ofReal.comp this).mul_const I)
  have hint : Integrable (fun ω => cexp (((a * phase p ω : ℝ) : ℂ) * I)) steinhausMeasure :=
    integrable_of_bound_phase hmeas fun ω => (Complex.norm_exp_ofReal_mul_I _).le
  have hphase : Integrable (phase p) steinhausMeasure :=
    Integrable.of_bound (measurable_phase p).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => abs_phase_le p ω)
  have hphase2 : Integrable (fun ω => phase p ω ^ 2) steinhausMeasure :=
    Integrable.of_bound ((measurable_phase p).pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        have := abs_phase_le p ω
        nlinarith [abs_nonneg (phase p ω)])
  -- the second-order Taylor polynomial integrates to `1 − a²/4`
  have hpoly : ∫ ω, ((1 + ((a * phase p ω : ℝ) : ℂ) * I - ((a ^ 2 / 2 * phase p ω ^ 2 : ℝ) : ℂ))) ∂steinhausMeasure =
      ((1 - a ^ 2 / 4 : ℝ) : ℂ) := by
    have h1 : Integrable (fun ω => ((a * phase p ω : ℝ) : ℂ) * I) steinhausMeasure :=
      ((hphase.const_mul a).ofReal).mul_const I
    have h2 : Integrable (fun ω => ((a ^ 2 / 2 * phase p ω ^ 2 : ℝ) : ℂ)) steinhausMeasure :=
      (hphase2.const_mul _).ofReal
    have h0 : Integrable (fun ω => (1 : ℂ) + ((a * phase p ω : ℝ) : ℂ) * I) steinhausMeasure :=
      (integrable_const _).add h1
    rw [integral_sub h0 h2, integral_add (integrable_const _) h1,
      integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, integral_const_mul,
      integral_const_mul, integral_phase_eq_zero hp, integral_phase_sq hp]
    simp only [integral_const, probReal_univ, one_smul, mul_zero, Complex.ofReal_zero, zero_mul,
      add_zero]
    push_cast
    ring
  have hrem : ∀ ω, ‖cexp (((a * phase p ω : ℝ) : ℂ) * I) -
      (1 + ((a * phase p ω : ℝ) : ℂ) * I - ((a ^ 2 / 2 * phase p ω ^ 2 : ℝ) : ℂ))‖ ≤ |a| ^ 3 / 6 := by
    intro ω
    have h := norm_cexp_sub_sum_le 3 (a * phase p ω)
    have hexpand : expRemainder 3 (a * phase p ω) =
        cexp (((a * phase p ω : ℝ) : ℂ) * I) -
          (1 + ((a * phase p ω : ℝ) : ℂ) * I - ((a ^ 2 / 2 * phase p ω ^ 2 : ℝ) : ℂ)) := by
      unfold expRemainder
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
      push_cast
      have hI : I ^ 2 = -1 := Complex.I_sq
      ring_nf
      rw [hI]
      ring
    rw [hexpand] at h
    refine h.trans ?_
    have h3 : |a * phase p ω| ^ 3 ≤ |a| ^ 3 := by
      rw [abs_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_of_le_one_right (abs_nonneg a) (abs_phase_le p ω)) 3
    have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hfac]
    linarith
  have hpolyint : Integrable (fun ω => (1 + ((a * phase p ω : ℝ) : ℂ) * I -
      ((a ^ 2 / 2 * phase p ω ^ 2 : ℝ) : ℂ))) steinhausMeasure :=
    ((integrable_const _).add (((hphase.const_mul a).ofReal).mul_const I)).sub
      ((hphase2.const_mul _).ofReal)
  have hclose : ‖∫ ω, cexp (((a * phase p ω : ℝ) : ℂ) * I) ∂steinhausMeasure -
      ((1 - a ^ 2 / 4 : ℝ) : ℂ)‖ ≤ |a| ^ 3 / 6 := by
    rw [← hpoly, ← integral_sub hint hpolyint]
    refine (norm_integral_le_of_norm_le_const (Eventually.of_forall hrem)).trans ?_
    simp
  have hgauss : ‖((1 - a ^ 2 / 4 : ℝ) : ℂ) - ((Real.exp (-(a ^ 2 / 4)) : ℝ) : ℂ)‖ ≤ |a| ^ 3 / 16 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hx : |(-(a ^ 2 / 4))| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (by positivity)]
      have : a ^ 2 ≤ 1 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg a]
      linarith
    have hexp := Real.abs_exp_sub_one_sub_id_le hx
    have heq : (1 - a ^ 2 / 4) - Real.exp (-(a ^ 2 / 4)) =
        -(Real.exp (-(a ^ 2 / 4)) - 1 - (-(a ^ 2 / 4))) := by ring
    rw [heq, abs_neg]
    refine hexp.trans ?_
    have h4 : (-(a ^ 2 / 4)) ^ 2 = |a| ^ 4 / 16 := by
      rw [neg_sq, div_pow, ← sq_abs a]
      ring
    rw [h4]
    have h0 := abs_nonneg a
    have h5 : |a| ^ 4 ≤ |a| ^ 3 := by
      have : |a| ^ 4 = |a| ^ 3 * |a| := by ring
      rw [this]
      exact mul_le_of_le_one_right (by positivity) ha
    linarith
  calc _ ≤ ‖∫ ω, cexp (((a * phase p ω : ℝ) : ℂ) * I) ∂steinhausMeasure -
        ((1 - a ^ 2 / 4 : ℝ) : ℂ)‖ +
      ‖((1 - a ^ 2 / 4 : ℝ) : ℂ) - ((Real.exp (-(a ^ 2 / 4)) : ℝ) : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ |a| ^ 3 / 6 + |a| ^ 3 / 16 := add_le_add hclose hgauss
    _ ≤ |a| ^ 3 / 4 := by
        have : 0 ≤ |a| ^ 3 := by positivity
        linarith

/-- The moment generating function of one phase. -/
theorem integral_exp_phase_le {p : ℕ} (hp : p.Prime) (b : ℝ) :
    ∫ ω, Real.exp (b * phase p ω) ∂steinhausMeasure ≤ Real.exp (b ^ 2 / 2) := by
  have hmeas : Measurable fun ω => Real.exp (b * phase p ω) :=
    Real.measurable_exp.comp ((measurable_phase p).const_mul b)
  have hbd : ∀ ω, ‖Real.exp (b * phase p ω)‖ ≤ Real.exp |b| := by
    intro ω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    calc b * phase p ω ≤ |b * phase p ω| := le_abs_self _
      _ = |b| * |phase p ω| := abs_mul _ _
      _ ≤ |b| := mul_le_of_le_one_right (abs_nonneg b) (abs_phase_le p ω)
  have hint : Integrable (fun ω => Real.exp (b * phase p ω)) steinhausMeasure :=
    Integrable.of_bound hmeas.aestronglyMeasurable _ (Eventually.of_forall hbd)
  have hphase : Integrable (phase p) steinhausMeasure :=
    Integrable.of_bound (measurable_phase p).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => abs_phase_le p ω)
  have hpt : ∀ ω, Real.exp (b * phase p ω) ≤ Real.cosh b + phase p ω * Real.sinh b := by
    intro ω
    have h1 := abs_le.mp (abs_phase_le p ω)
    have hconv := convexOn_exp.2 (mem_univ b) (mem_univ (-b))
      (by linarith : 0 ≤ (1 + phase p ω) / 2) (by linarith : 0 ≤ (1 - phase p ω) / 2)
      (by ring)
    simp only [smul_eq_mul] at hconv
    have heq : (1 + phase p ω) / 2 * b + (1 - phase p ω) / 2 * -b = b * phase p ω := by ring
    rw [heq] at hconv
    refine hconv.trans (le_of_eq ?_)
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hI : Integrable (fun ω => Real.cosh b + phase p ω * Real.sinh b) steinhausMeasure :=
    (integrable_const _).add (hphase.mul_const _)
  have hle := integral_mono hint hI hpt
  rw [integral_add (integrable_const _) (hphase.mul_const _), integral_mul_const,
    integral_phase_eq_zero hp] at hle
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, zero_mul, add_zero] at hle
  exact hle.trans (Real.cosh_le_exp_half_sq b)

/-! ### The product over primes -/

theorem modelField_eq_sum_phase (w : ℕ → ℝ) (P : Finset ℕ) (ω : Omega) :
    modelField w P ω = ∑ p ∈ P, w p * phase p ω := rfl

/-- `Re X_p` depends only on the coordinate `p`. -/
theorem iIndepFun_cos : iIndepFun (fun (i : ℕ) (ω : Omega) => Real.cos (2 * Real.pi * ω i))
    steinhausMeasure := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (X := fun _ (x : ℝ) => Real.cos (2 * Real.pi * x))
    (fun _ => (Real.continuous_cos.comp (continuous_const.mul continuous_id)).measurable)
  exact h

/-- Independence over a finite set of primes, for an arbitrary factor at each prime. -/
theorem integral_prod_phase_eq {𝕜 : Type*} [RCLike 𝕜] {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℝ → 𝕜) (hf : ∀ p, Continuous (f p)) :
    ∫ ω, ∏ p ∈ P, f p (phase p ω) ∂steinhausMeasure =
      ∏ p ∈ P, ∫ ω, f p (phase p ω) ∂steinhausMeasure := by
  have hindep : iIndepFun (fun (i : P) (ω : Omega) => Real.cos (2 * Real.pi * ω i))
      steinhausMeasure :=
    iIndepFun_cos.precomp Subtype.val_injective
  have hmeas : ∀ i : P, AEMeasurable (fun ω : Omega => Real.cos (2 * Real.pi * ω i))
      steinhausMeasure := fun i =>
    (Real.continuous_cos.measurable.comp ((measurable_pi_apply _).const_mul _)).aemeasurable
  have h := hindep.integral_fun_prod_comp (f := fun i : P => f i) hmeas
    (fun i => (hf i).aestronglyMeasurable)
  have hL' : (fun ω : Omega => ∏ p ∈ P, f p (phase p ω)) =
      fun ω => ∏ i : P, f i (Real.cos (2 * Real.pi * ω i)) := by
    funext ω
    rw [← Finset.prod_coe_sort P]
    exact Finset.prod_congr rfl fun i _ => by rw [phase_eq_cos (hP i i.2)]
  rw [hL', h, ← Finset.prod_coe_sort P]
  refine Finset.prod_congr rfl fun i _ => ?_
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only
  rw [phase_eq_cos (hP i i.2)]

/-- The moment generating function of the model. -/
theorem integral_exp_modelField_le {w : ℕ → ℝ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (b : ℝ) :
    ∫ ω, Real.exp (b * modelField w P ω) ∂steinhausMeasure ≤
      Real.exp (b ^ 2 * (∑ p ∈ P, w p ^ 2) / 2) := by
  have hexp : (fun ω => Real.exp (b * modelField w P ω)) =
      fun ω => ∏ p ∈ P, (fun (p : ℕ) (x : ℝ) => Real.exp (b * w p * x)) p (phase p ω) := by
    funext ω
    rw [modelField_eq_sum_phase, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_congr rfl fun p _ => by ring_nf
  rw [hexp, integral_prod_phase_eq hP (fun (p : ℕ) (x : ℝ) => Real.exp (b * w p * x))
    (fun p => by fun_prop)]
  have hsum : b ^ 2 * (∑ p ∈ P, w p ^ 2) / 2 = ∑ p ∈ P, (b * w p) ^ 2 / 2 := by
    rw [Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => integral_nonneg fun ω => (Real.exp_pos _).le)
    fun p hp => ?_
  exact integral_exp_phase_le (hP p hp) (b * w p)

theorem measurable_modelField (w : ℕ → ℝ) (P : Finset ℕ) : Measurable (modelField w P) :=
  Finset.measurable_sum _ fun p _ => (measurable_phase p).const_mul _

theorem abs_modelField_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (P : Finset ℕ) (ω : Omega) :
    |modelField w P ω| ≤ ∑ p ∈ P, w p := by
  rw [modelField_eq_sum_phase]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [abs_mul, abs_of_nonneg (hw p)]
  exact mul_le_of_le_one_right (hw p) (abs_phase_le p ω)

theorem integrable_modelField_pow {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) (P : Finset ℕ) (j : ℕ) :
    Integrable (fun ω => modelField w P ω ^ j) steinhausMeasure :=
  Integrable.of_bound ((measurable_modelField w P).pow_const j).aestronglyMeasurable
    ((∑ p ∈ P, w p) ^ j) (Eventually.of_forall fun ω => by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (abs_modelField_le hw P ω) j)

/-- **Even moments of the model.** `E S^{2K} ≤ (2K)! λ^{−2K} 2 exp(λ² W/2)` for `λ > 0`. -/
theorem integral_modelField_even_pow_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (K : ℕ) {l : ℝ} (hl : 0 < l) :
    ∫ ω, modelField w P ω ^ (2 * K) ∂steinhausMeasure ≤
      ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ * (2 * Real.exp (l ^ 2 * (∑ p ∈ P, w p ^ 2) / 2)) := by
  have hbd : ∀ b : ℝ, Integrable (fun ω => Real.exp (b * modelField w P ω)) steinhausMeasure := by
    intro b
    refine Integrable.of_bound
      (Real.measurable_exp.comp ((measurable_modelField w P).const_mul b)).aestronglyMeasurable
      (Real.exp (|b| * ∑ p ∈ P, w p)) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    calc b * modelField w P ω ≤ |b * modelField w P ω| := le_abs_self _
      _ = |b| * |modelField w P ω| := abs_mul _ _
      _ ≤ |b| * ∑ p ∈ P, w p := mul_le_mul_of_nonneg_left (abs_modelField_le hw P ω) (abs_nonneg b)
  have hfac : (0 : ℝ) < ((2 * K).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpt : ∀ ω, modelField w P ω ^ (2 * K) ≤
      ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ *
        (Real.exp (l * modelField w P ω) + Real.exp (-l * modelField w P ω)) := by
    intro ω
    set s := modelField w P ω with hs
    have h1 := Real.pow_div_factorial_le_exp (x := l * |s|) (by positivity) (2 * K)
    have h2 : Real.exp (l * |s|) ≤ Real.exp (l * s) + Real.exp (-l * s) := by
      rcases le_total 0 s with h | h
      · rw [abs_of_nonneg h]
        linarith [Real.exp_pos (-l * s)]
      · rw [abs_of_nonpos h]
        have : l * -s = -l * s := by ring
        rw [this]
        linarith [Real.exp_pos (l * s)]
    have h3 : s ^ (2 * K) = |s| ^ (2 * K) := by
      rw [pow_mul, pow_mul, sq_abs]
    rw [mul_pow, div_le_iff₀ hfac] at h1
    have hlp : 0 < l ^ (2 * K) := by positivity
    have h4 : |s| ^ (2 * K) ≤ Real.exp (l * |s|) * ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ := by
      rw [le_mul_inv_iff₀ hlp, mul_comm]
      exact h1
    rw [h3]
    refine h4.trans ?_
    have h5 : 0 ≤ ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ := by positivity
    calc Real.exp (l * |s|) * ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹
        = ((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ * Real.exp (l * |s|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 h5
  have hI : Integrable (fun ω => Real.exp (l * modelField w P ω) +
      Real.exp (-l * modelField w P ω)) steinhausMeasure := (hbd l).add (hbd (-l))
  have hle := integral_mono (integrable_modelField_pow hw P (2 * K)) (hI.const_mul _) hpt
  rw [integral_const_mul, integral_add (hbd l) (hbd (-l))] at hle
  refine hle.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  have h1 := integral_exp_modelField_le (w := w) hP l
  have h2 := integral_exp_modelField_le (w := w) hP (-l)
  rw [neg_sq] at h2
  linarith

/-- Telescoping for products of numbers in the unit disc. -/
theorem norm_prod_sub_prod_le_sum {ι : Type*} (s : Finset ι) {f g : ι → ℂ} (hf : ∀ i ∈ s, ‖f i‖ ≤ 1)
    (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hF : ‖∏ i ∈ s, f i‖ ≤ 1 := by
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ => norm_nonneg _)
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hrec := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    have hga := hg a (Finset.mem_insert_self a s)
    have heq : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i =
        (f a - g a) * ∏ i ∈ s, f i + g a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) := by ring
    rw [heq]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ ≤ ‖f a - g a‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hF
    have h2 : ‖g a‖ * ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hga
    linarith

/-- **The characteristic function of the model.** If `|v w(p)| ≤ 1` for all `p ∈ P`, then `‖E exp(ivS) − exp(−v² W/4)‖ ≤ ¼ Σ_p |v w(p)|³`. -/
theorem norm_integral_cexp_modelField_sub_le {w : ℕ → ℝ} {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {v : ℝ} (hv : ∀ p ∈ P, |v * w p| ≤ 1) :
    ‖∫ ω, cexp (((v * modelField w P ω : ℝ) : ℂ) * I) ∂steinhausMeasure -
        ((Real.exp (-(v ^ 2 * (∑ p ∈ P, w p ^ 2) / 4)) : ℝ) : ℂ)‖ ≤
      (∑ p ∈ P, |v * w p| ^ 3) / 4 := by
  have hexp : (fun ω => cexp (((v * modelField w P ω : ℝ) : ℂ) * I)) =
      fun ω => ∏ p ∈ P, (fun (p : ℕ) (x : ℝ) => cexp (((v * w p * x : ℝ) : ℂ) * I)) p (phase p ω) := by
    funext ω
    rw [modelField_eq_sum_phase, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul,
      Complex.exp_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp only
    congr 2
    ring_nf
  rw [hexp, integral_prod_phase_eq hP (fun (p : ℕ) (x : ℝ) => cexp (((v * w p * x : ℝ) : ℂ) * I))
    (fun p => by fun_prop)]
  have hsum : Real.exp (-(v ^ 2 * (∑ p ∈ P, w p ^ 2) / 4)) =
      ∏ p ∈ P, Real.exp (-((v * w p) ^ 2 / 4)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hsum, Complex.ofReal_prod]
  refine (norm_prod_sub_prod_le_sum P ?_ ?_).trans ?_
  · intro p _
    refine (norm_integral_le_of_norm_le_const (C := 1) (Eventually.of_forall fun ω => ?_)).trans ?_
    · rw [Complex.norm_exp_ofReal_mul_I]
    · simp
  · intro p _
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (by
      have := sq_nonneg (v * w p)
      linarith)
  · rw [Finset.sum_div]
    refine Finset.sum_le_sum fun p hp => ?_
    have h := norm_integral_cexp_phase_sub_le (hP p hp) (hv p hp)
    convert h using 3

/-! ### From the model to heights -/

theorem continuous_primeField (w : ℕ → ℝ) (P : Finset ℕ) : Continuous (primeField w P) := by
  unfold primeField
  fun_prop

/-- `e^{iy}` is its Taylor polynomial plus the remainder. -/
theorem cexp_eq_sum_add_expRemainder (n : ℕ) (y : ℝ) :
    cexp ((y : ℂ) * I) =
      ∑ k ∈ Finset.range n, ((y : ℂ) * I) ^ k / (k.factorial : ℂ) + expRemainder n y := by
  unfold expRemainder
  ring

/-- The Taylor polynomial of `e^{ivx}` splits into moments of `x`. -/
theorem taylor_term_eq (v x : ℝ) (k : ℕ) :
    (((v * x : ℝ) : ℂ) * I) ^ k / (k.factorial : ℂ) =
      (((v : ℂ) * I) ^ k / (k.factorial : ℂ)) * ((x ^ k : ℝ) : ℂ) := by
  push_cast
  ring

theorem norm_coefficient_eq (v : ℝ) (k : ℕ) :
    ‖((v : ℂ) * I) ^ k / (k.factorial : ℂ)‖ = |v| ^ k / (k.factorial : ℝ) := by
  rw [norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
    Complex.norm_natCast]

/-- **From the model to heights.** The height average of `e^{ivF}` differs from the model by at most the moment defects below order `2K` and the two remainders. -/
theorem norm_mean_cexp_primeField_sub_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {Y : ℕ} (hY1 : 1 ≤ Y) (hY : ∀ p ∈ P, p ≤ Y) {T : ℝ} (hT : 0 < T)
    (v : ℝ) (K : ℕ) :
    ‖(T : ℂ)⁻¹ * (∫ t in T..(T + T), cexp (((v * primeField w P t : ℝ) : ℂ) * I)) -
        ∫ ω, cexp (((v * modelField w P ω : ℝ) : ℂ) * I) ∂steinhausMeasure‖ ≤
      ∑ j ∈ Finset.range (2 * K), |v| ^ j / (j.factorial : ℝ) * (2 * ((∑ p ∈ P, w p) * Y) ^ j / T) +
        |v| ^ (2 * K) / ((2 * K).factorial : ℝ) *
          (2 * (∫ ω, modelField w P ω ^ (2 * K) ∂steinhausMeasure) +
            2 * ((∑ p ∈ P, w p) * Y) ^ (2 * K) / T) := by
  have hP0 : ∀ p ∈ P, p ≠ 0 := fun p hp => (hP p hp).ne_zero
  set N := 2 * K with hN
  set F := primeField w P with hF
  set S := modelField w P with hS
  have hFc : Continuous F := continuous_primeField w P
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hSm : Measurable S := measurable_modelField w P
  -- the height side
  have hRc : Continuous fun t => expRemainder N (v * F t) :=
    (continuous_expRemainder N).comp (continuous_const.mul hFc)
  have hPolyInt : ∀ k ∈ Finset.range N, IntervalIntegrable (fun t : ℝ =>
      (((v * F t : ℝ) : ℂ) * I) ^ k / (k.factorial : ℂ)) volume T (T + T) := fun k _ => by
    have hc : Continuous fun t : ℝ => (((v * F t : ℝ) : ℂ) * I) ^ k / (k.factorial : ℂ) := by
      have : Continuous fun t : ℝ => ((v * F t : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_const.mul hFc)
      exact ((this.mul continuous_const).pow k).div_const _
    exact hc.intervalIntegrable _ _
  have hA : (T : ℂ)⁻¹ * (∫ t in T..(T + T), cexp (((v * F t : ℝ) : ℂ) * I)) =
      ∑ j ∈ Finset.range N, (((v : ℂ) * I) ^ j / (j.factorial : ℂ)) *
          ((T⁻¹ * ∫ t in T..(T + T), F t ^ j : ℝ) : ℂ) +
        (T : ℂ)⁻¹ * ∫ t in T..(T + T), expRemainder N (v * F t) := by
    simp_rw [cexp_eq_sum_add_expRemainder N]
    have hsumc : Continuous fun t : ℝ => ∑ k ∈ Finset.range N,
        (((v * F t : ℝ) : ℂ) * I) ^ k / (k.factorial : ℂ) := by
      have : Continuous fun t : ℝ => ((v * F t : ℝ) : ℂ) :=
        Complex.continuous_ofReal.comp (continuous_const.mul hFc)
      exact continuous_finsetSum _ fun k _ => ((this.mul continuous_const).pow k).div_const _
    rw [intervalIntegral.integral_add (hsumc.intervalIntegrable _ _)
      (hRc.intervalIntegrable _ _), intervalIntegral.integral_finsetSum hPolyInt, mul_add,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [taylor_term_eq]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    push_cast
    ring
  -- the model side
  have hRmeas : Measurable fun ω => expRemainder N (v * S ω) :=
    (continuous_expRemainder N).measurable.comp (hSm.const_mul v)
  have hRbd : ∀ ω, ‖expRemainder N (v * S ω)‖ ≤ |v * S ω| ^ N / (N.factorial : ℝ) := fun ω =>
    norm_cexp_sub_sum_le N _
  have hSpow : ∀ j, Integrable (fun ω => S ω ^ j) steinhausMeasure :=
    integrable_modelField_pow hw P
  have hSeven : ∀ ω, |v * S ω| ^ N = |v| ^ N * S ω ^ N := by
    intro ω
    rw [abs_mul, mul_pow]
    congr 1
    rw [hN, pow_mul, pow_mul, sq_abs]
  have hRint : Integrable (fun ω => expRemainder N (v * S ω)) steinhausMeasure := by
    refine Integrable.mono' (((hSpow N).const_mul (|v| ^ N)).div_const (N.factorial : ℝ))
      hRmeas.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    have := hRbd ω
    rwa [hSeven] at this
  have hPolyω : ∀ k ∈ Finset.range N, Integrable (fun ω =>
      (((v * S ω : ℝ) : ℂ) * I) ^ k / (k.factorial : ℂ)) steinhausMeasure := fun k _ => by
    simp_rw [taylor_term_eq]
    exact ((hSpow k).ofReal).const_mul _
  have hB : ∫ ω, cexp (((v * S ω : ℝ) : ℂ) * I) ∂steinhausMeasure =
      ∑ j ∈ Finset.range N, (((v : ℂ) * I) ^ j / (j.factorial : ℂ)) *
          ((∫ ω, S ω ^ j ∂steinhausMeasure : ℝ) : ℂ) +
        ∫ ω, expRemainder N (v * S ω) ∂steinhausMeasure := by
    simp_rw [cexp_eq_sum_add_expRemainder N]
    rw [integral_add (integrable_finsetSum _ hPolyω) hRint, integral_finsetSum _ hPolyω]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp_rw [taylor_term_eq]
    rw [integral_const_mul, integral_complex_ofReal]
  rw [hA, hB]
  have hsplit : ∑ j ∈ Finset.range N, (((v : ℂ) * I) ^ j / (j.factorial : ℂ)) *
          ((T⁻¹ * ∫ t in T..(T + T), F t ^ j : ℝ) : ℂ) +
        (T : ℂ)⁻¹ * (∫ t in T..(T + T), expRemainder N (v * F t)) -
      (∑ j ∈ Finset.range N, (((v : ℂ) * I) ^ j / (j.factorial : ℂ)) *
          ((∫ ω, S ω ^ j ∂steinhausMeasure : ℝ) : ℂ) +
        ∫ ω, expRemainder N (v * S ω) ∂steinhausMeasure) =
      ∑ j ∈ Finset.range N, (((v : ℂ) * I) ^ j / (j.factorial : ℂ)) *
          (((T⁻¹ * (∫ t in T..(T + T), F t ^ j) - ∫ ω, S ω ^ j ∂steinhausMeasure : ℝ) : ℂ)) +
        ((T : ℂ)⁻¹ * (∫ t in T..(T + T), expRemainder N (v * F t)) -
          ∫ ω, expRemainder N (v * S ω) ∂steinhausMeasure) := by
    have hdiff : ∑ j ∈ Finset.range N, (((v : ℂ) * I) ^ j / (j.factorial : ℂ)) *
          (((T⁻¹ * (∫ t in T..(T + T), F t ^ j) - ∫ ω, S ω ^ j ∂steinhausMeasure : ℝ) : ℂ)) =
        ∑ j ∈ Finset.range N, (((v : ℂ) * I) ^ j / (j.factorial : ℂ)) *
          ((T⁻¹ * ∫ t in T..(T + T), F t ^ j : ℝ) : ℂ) -
        ∑ j ∈ Finset.range N, (((v : ℂ) * I) ^ j / (j.factorial : ℂ)) *
          ((∫ ω, S ω ^ j ∂steinhausMeasure : ℝ) : ℂ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.ofReal_sub, mul_sub]
    rw [hdiff]
    ring
  rw [hsplit]
  have htrans := fun j => abs_mean_primeField_pow_sub_model_le hw hP0 hY1 hY hT j
  have hfirst : ‖∑ j ∈ Finset.range N, (((v : ℂ) * I) ^ j / (j.factorial : ℂ)) *
      (((T⁻¹ * (∫ t in T..(T + T), F t ^ j) - ∫ ω, S ω ^ j ∂steinhausMeasure : ℝ) : ℂ))‖ ≤
      ∑ j ∈ Finset.range N, |v| ^ j / (j.factorial : ℝ) * (2 * ((∑ p ∈ P, w p) * Y) ^ j / T) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_coefficient_eq, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (htrans j) (by positivity)
  -- the two remainders
  have hFeven : ∀ t, |v * F t| ^ N = |v| ^ N * F t ^ N := by
    intro t
    rw [abs_mul, mul_pow]
    congr 1
    rw [hN, pow_mul, pow_mul, sq_abs]
  have hFpowc : Continuous fun t => F t ^ N := hFc.pow N
  have hRt : ‖(T : ℂ)⁻¹ * ∫ t in T..(T + T), expRemainder N (v * F t)‖ ≤
      |v| ^ N / (N.factorial : ℝ) * (T⁻¹ * ∫ t in T..(T + T), F t ^ N) := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hT.le]
    have hle : ‖∫ t in T..(T + T), expRemainder N (v * F t)‖ ≤
        ∫ t in T..(T + T), |v| ^ N / (N.factorial : ℝ) * F t ^ N := by
      refine intervalIntegral.norm_integral_le_of_norm_le (by linarith)
        (Eventually.of_forall fun t _ => ?_) ((continuous_const.mul hFpowc).intervalIntegrable _ _)
      have := norm_cexp_sub_sum_le N (v * F t)
      rw [hFeven] at this
      calc _ ≤ _ := this
        _ = _ := by ring
    rw [intervalIntegral.integral_const_mul] at hle
    calc T⁻¹ * ‖∫ t in T..(T + T), expRemainder N (v * F t)‖
        ≤ T⁻¹ * (|v| ^ N / (N.factorial : ℝ) * ∫ t in T..(T + T), F t ^ N) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = _ := by ring
  have hRω : ‖∫ ω, expRemainder N (v * S ω) ∂steinhausMeasure‖ ≤
      |v| ^ N / (N.factorial : ℝ) * ∫ ω, S ω ^ N ∂steinhausMeasure := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hle : ∀ ω, ‖expRemainder N (v * S ω)‖ ≤ |v| ^ N / (N.factorial : ℝ) * S ω ^ N := by
      intro ω
      have := hRbd ω
      rw [hSeven] at this
      calc _ ≤ _ := this
        _ = _ := by ring
    rw [← integral_const_mul]
    exact integral_mono hRint.norm ((hSpow N).const_mul _) hle
  have hmomN := (abs_le.mp (htrans N)).2
  have hcoef : 0 ≤ |v| ^ N / (N.factorial : ℝ) := by positivity
  refine (norm_add_le _ _).trans (add_le_add hfirst ?_)
  refine (norm_sub_le _ _).trans ?_
  have h3 := mul_le_mul_of_nonneg_left
    (show T⁻¹ * (∫ t in T..(T + T), F t ^ N) ≤
      (∫ ω, S ω ^ N ∂steinhausMeasure) + 2 * ((∑ p ∈ P, w p) * Y) ^ N / T by linarith) hcoef
  calc _ ≤ |v| ^ N / (N.factorial : ℝ) * (T⁻¹ * ∫ t in T..(T + T), F t ^ N) +
        |v| ^ N / (N.factorial : ℝ) * ∫ ω, S ω ^ N ∂steinhausMeasure := add_le_add hRt hRω
    _ ≤ _ := by nlinarith

/-- **The characteristic function of the prime field converges to the Gaussian.** Along any sequence with `0 ≤ w ≤ 1`, `W = Σ w² → ∞` and `(A Y)^K/T → 0` for every `K`. -/
theorem tendsto_mean_cexp_primeField {T : ℕ → ℝ} {P : ℕ → Finset ℕ} {w : ℕ → ℕ → ℝ} {Y : ℕ → ℕ}
    (hT : ∀ n, 0 < T n) (hw0 : ∀ n m, 0 ≤ w n m) (hw1 : ∀ n m, w n m ≤ 1)
    (hP : ∀ n, ∀ p ∈ P n, p.Prime) (hY1 : ∀ n, 1 ≤ Y n) (hY : ∀ n, ∀ p ∈ P n, p ≤ Y n)
    (hW : Tendsto (fun n => ∑ p ∈ P n, w n p ^ 2) atTop atTop)
    (hsmall : ∀ K : ℕ, Tendsto (fun n => ((∑ p ∈ P n, w n p) * Y n) ^ K / T n) atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun n => (T n : ℂ)⁻¹ * ∫ t in T n..(T n + T n),
        cexp (((u / Real.sqrt ((∑ p ∈ P n, w n p ^ 2) / 2) * primeField (w n) (P n) t : ℝ) : ℂ) * I))
      atTop (𝓝 (cexp (-(u ^ 2 / 2 : ℝ) : ℂ))) := by
  obtain ⟨W, hWdef⟩ : ∃ W : ℕ → ℝ, W = fun n => ∑ p ∈ P n, w n p ^ 2 := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v : ℕ → ℝ, v = fun n => u / Real.sqrt (W n / 2) := ⟨_, rfl⟩
  rw [← hWdef] at hW
  have hv0 : Tendsto v atTop (𝓝 0) := by
    rw [hvdef]
    exact Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_sqrt_atTop.comp (hW.atTop_div_const two_pos))
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- choose the Taylor order
  have hhalf : Tendsto (fun K : ℕ => 4 * ((1 : ℝ) / 2) ^ K) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)).const_mul 4
    simpa using this
  obtain ⟨K, hKsmall, hKlarge, hK1⟩ : ∃ K : ℕ, 4 * ((1 : ℝ) / 2) ^ K < ε / 4 ∧
      2 * Real.exp 1 * u ^ 2 ≤ K ∧ 1 ≤ K := by
    have h1 := hhalf.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))
    have h2 := tendsto_natCast_atTop_atTop (R := ℝ).eventually_ge_atTop (2 * Real.exp 1 * u ^ 2)
    obtain ⟨K, hK1, hK2, hK3⟩ := (h1.and (h2.and (eventually_ge_atTop 1))).exists
    exact ⟨K, hK1, hK2, hK3⟩
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  -- the finite moment defects
  have hdefect : Tendsto (fun n => ∑ j ∈ Finset.range (2 * K),
      2 * (((∑ p ∈ P n, w n p) * Y n) ^ j / T n)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range (2 * K)) (fun j _ => (hsmall j).const_mul 2)
    simpa using this
  have hlast : Tendsto (fun n => 2 * (((∑ p ∈ P n, w n p) * Y n) ^ (2 * K) / T n)) atTop (𝓝 0) := by
    simpa using (hsmall (2 * K)).const_mul 2
  have hcube : Tendsto (fun n => |v n| * (2 * u ^ 2) / 4) atTop (𝓝 0) := by
    have := ((hv0.abs).mul_const (2 * u ^ 2)).div_const 4
    simpa using this
  have hevW := hW.eventually_gt_atTop 0
  have hevv : ∀ᶠ n in atTop, |v n| ≤ 1 := by
    have := hv0.abs.eventually (gt_mem_nhds (by simp : |(0 : ℝ)| < 1))
    exact this.mono fun n hn => hn.le
  have hev1 := hdefect.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 8))
  have hev2 := hlast.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 8))
  have hev3 := hcube.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hevW.and (hevv.and (hev1.and (hev2.and hev3))))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hWn, hvn, h1n, h2n, h3n⟩ := hN n hn
  have hvsq : v n ^ 2 * W n = 2 * u ^ 2 := by
    rw [hvdef]
    simp only
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  -- model
  have hvw : ∀ p ∈ P n, |v n * w n p| ≤ 1 := by
    intro p _
    rw [abs_mul, abs_of_nonneg (hw0 n p)]
    calc |v n| * w n p ≤ 1 * 1 := mul_le_mul hvn (hw1 n p) (hw0 n p) zero_le_one
      _ = 1 := one_mul 1
  have hmodel := norm_integral_cexp_modelField_sub_le (hP n) hvw
  have hWeq : ∑ p ∈ P n, w n p ^ 2 = W n := by rw [hWdef]
  rw [hWeq] at hmodel
  have hgauss : v n ^ 2 * W n / 4 = u ^ 2 / 2 := by rw [hvsq]; ring
  rw [hgauss] at hmodel
  have hsum3 : (∑ p ∈ P n, |v n * w n p| ^ 3) / 4 ≤ |v n| * (2 * u ^ 2) / 4 := by
    refine div_le_div_of_nonneg_right ?_ (by norm_num)
    have : ∑ p ∈ P n, |v n * w n p| ^ 3 ≤ ∑ p ∈ P n, |v n| * (v n ^ 2 * w n p ^ 2) := by
      refine Finset.sum_le_sum fun p _ => ?_
      rw [abs_mul, abs_of_nonneg (hw0 n p), mul_pow]
      have hw3 : w n p ^ 3 ≤ w n p ^ 2 := by
        have h := hw0 n p
        have h' := hw1 n p
        nlinarith [mul_nonneg h h]
      have ha : |v n| ^ 3 = |v n| * v n ^ 2 := by
        rw [← sq_abs (v n)]
        ring
      rw [ha, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw3 (sq_nonneg _)) (abs_nonneg _)
    refine this.trans (le_of_eq ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, hWeq, hvsq]
  -- height
  have hheight := norm_mean_cexp_primeField_sub_le (hw0 n) (hP n) (hY1 n) (hY n) (hT n) (v n) K
  -- the moment remainder
  have hmoment : |v n| ^ (2 * K) / ((2 * K).factorial : ℝ) *
      (2 * ∫ ω, modelField (w n) (P n) ω ^ (2 * K) ∂steinhausMeasure) ≤ 4 * ((1 : ℝ) / 2) ^ K := by
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.sqrt (2 * K / W n) := ⟨_, rfl⟩
    have hl2 : l ^ 2 = 2 * K / W n := by
      rw [hl, Real.sq_sqrt (by positivity)]
    have hl0 : 0 < l := by
      rw [hl]
      exact Real.sqrt_pos.mpr (by positivity)
    have hM := integral_modelField_even_pow_le (hw0 n) (hP n) K hl0
    rw [hWeq] at hM
    have hexp : l ^ 2 * W n / 2 = K := by
      rw [hl2]
      field_simp
    rw [hexp] at hM
    have hfac : (0 : ℝ) < ((2 * K).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hv2K : |v n| ^ (2 * K) = (v n ^ 2) ^ K := by rw [pow_mul, sq_abs]
    have hl2K : l ^ (2 * K) = (l ^ 2) ^ K := by rw [pow_mul]
    have hratio : v n ^ 2 / l ^ 2 = u ^ 2 / K := by
      rw [hl2]
      have hv2 : v n ^ 2 = 2 * u ^ 2 / W n := by
        rw [eq_div_iff hWn.ne']
        exact hvsq
      rw [hv2]
      field_simp
    calc |v n| ^ (2 * K) / ((2 * K).factorial : ℝ) *
          (2 * ∫ ω, modelField (w n) (P n) ω ^ (2 * K) ∂steinhausMeasure)
        ≤ |v n| ^ (2 * K) / ((2 * K).factorial : ℝ) *
          (2 * (((2 * K).factorial : ℝ) * (l ^ (2 * K))⁻¹ * (2 * Real.exp K))) := by
          gcongr
      _ = 4 * ((v n ^ 2 / l ^ 2) * Real.exp 1) ^ K := by
          rw [hv2K, hl2K, mul_pow, div_pow, ← Real.exp_nat_mul, mul_one]
          field_simp
          ring
      _ = 4 * ((u ^ 2 / K) * Real.exp 1) ^ K := by rw [hratio]
      _ ≤ 4 * ((1 : ℝ) / 2) ^ K := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          refine pow_le_pow_left₀ (by positivity) ?_ K
          rw [div_mul_eq_mul_div, div_le_iff₀ hK0]
          linarith
  -- assemble
  have hbound : ‖(T n : ℂ)⁻¹ * (∫ t in T n..(T n + T n),
      cexp (((v n * primeField (w n) (P n) t : ℝ) : ℂ) * I)) -
      cexp (-(u ^ 2 / 2 : ℝ) : ℂ)‖ < ε := by
    have hF1 : ∑ j ∈ Finset.range (2 * K), |v n| ^ j / (j.factorial : ℝ) *
        (2 * ((∑ p ∈ P n, w n p) * Y n) ^ j / T n) ≤
        ∑ j ∈ Finset.range (2 * K), 2 * (((∑ p ∈ P n, w n p) * Y n) ^ j / T n) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hA0 : 0 ≤ (∑ p ∈ P n, w n p) * Y n :=
        mul_nonneg (Finset.sum_nonneg fun p _ => hw0 n p) (Nat.cast_nonneg _)
      have hnn : 0 ≤ 2 * (((∑ p ∈ P n, w n p) * Y n) ^ j / T n) := by
        have := hT n
        positivity
      have hcoef : |v n| ^ j / (j.factorial : ℝ) ≤ 1 := by
        have h1 : |v n| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg _) hvn
        have h2 : (1 : ℝ) ≤ (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
        exact (div_le_one (by linarith)).mpr (by linarith)
      calc _ = |v n| ^ j / (j.factorial : ℝ) * (2 * (((∑ p ∈ P n, w n p) * Y n) ^ j / T n)) := by
            ring
        _ ≤ 1 * (2 * (((∑ p ∈ P n, w n p) * Y n) ^ j / T n)) :=
            mul_le_mul_of_nonneg_right hcoef hnn
        _ = _ := one_mul _
    have hA0 : 0 ≤ (∑ p ∈ P n, w n p) * Y n :=
      mul_nonneg (Finset.sum_nonneg fun p _ => hw0 n p) (Nat.cast_nonneg _)
    have hT0 := hT n
    have hF2 : |v n| ^ (2 * K) / ((2 * K).factorial : ℝ) *
        (2 * ((∑ p ∈ P n, w n p) * Y n) ^ (2 * K) / T n) ≤
        2 * (((∑ p ∈ P n, w n p) * Y n) ^ (2 * K) / T n) := by
      have hnn : 0 ≤ 2 * (((∑ p ∈ P n, w n p) * Y n) ^ (2 * K) / T n) := by positivity
      have hcoef : |v n| ^ (2 * K) / ((2 * K).factorial : ℝ) ≤ 1 := by
        have h1 : |v n| ^ (2 * K) ≤ 1 := pow_le_one₀ (abs_nonneg _) hvn
        have h2 : (1 : ℝ) ≤ ((2 * K).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
        exact (div_le_one (by linarith)).mpr (by linarith)
      calc _ = |v n| ^ (2 * K) / ((2 * K).factorial : ℝ) *
            (2 * (((∑ p ∈ P n, w n p) * Y n) ^ (2 * K) / T n)) := by ring
        _ ≤ 1 * (2 * (((∑ p ∈ P n, w n p) * Y n) ^ (2 * K) / T n)) :=
            mul_le_mul_of_nonneg_right hcoef hnn
        _ = _ := one_mul _
    have hdist := norm_sub_le_norm_sub_add_norm_sub
      ((T n : ℂ)⁻¹ * (∫ t in T n..(T n + T n),
        cexp (((v n * primeField (w n) (P n) t : ℝ) : ℂ) * I)))
      (∫ ω, cexp (((v n * modelField (w n) (P n) ω : ℝ) : ℂ) * I) ∂steinhausMeasure)
      (cexp (-(u ^ 2 / 2 : ℝ) : ℂ))
    have hgaussc : ((Real.exp (-(u ^ 2 / 2)) : ℝ) : ℂ) = cexp (-(u ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hgaussc] at hmodel
    have hexpand : |v n| ^ (2 * K) / ((2 * K).factorial : ℝ) *
        (2 * (∫ ω, modelField (w n) (P n) ω ^ (2 * K) ∂steinhausMeasure) +
          2 * ((∑ p ∈ P n, w n p) * Y n) ^ (2 * K) / T n) =
        |v n| ^ (2 * K) / ((2 * K).factorial : ℝ) *
          (2 * ∫ ω, modelField (w n) (P n) ω ^ (2 * K) ∂steinhausMeasure) +
        |v n| ^ (2 * K) / ((2 * K).factorial : ℝ) *
          (2 * ((∑ p ∈ P n, w n p) * Y n) ^ (2 * K) / T n) := by ring
    rw [hexpand] at hheight
    linarith
  rw [dist_eq_norm]
  have hvn' : v n = u / Real.sqrt ((∑ p ∈ P n, w n p ^ 2) / 2) := by
    rw [hvdef, hWdef]
  rw [← hvn']
  exact hbound

/-! ### The law on a window of heights -/

/-- Normalized Lebesgue measure on `(T, 2T]`. -/
def windowMeasure (T : ℝ) : Measure ℝ := ENNReal.ofReal T⁻¹ • volume.restrict (Ioc T (T + T))

theorem isProbabilityMeasure_windowMeasure {T : ℝ} (hT : 0 < T) :
    IsProbabilityMeasure (windowMeasure T) := by
  constructor
  simp only [windowMeasure, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Ioc, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), add_sub_cancel_right, inv_mul_cancel₀ hT.ne',
    ENNReal.ofReal_one]

/-- The law of `f` on the window `(T, 2T]`. -/
def windowLaw {T : ℝ} (hT : 0 < T) (f : ℝ → ℝ) (hf : Measurable f) : ProbabilityMeasure ℝ :=
  haveI := isProbabilityMeasure_windowMeasure hT
  ⟨(windowMeasure T).map f, Measure.isProbabilityMeasure_map hf.aemeasurable⟩

theorem charFun_windowLaw {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hf : Measurable f) (u : ℝ) :
    charFun ((windowLaw hT f hf : ProbabilityMeasure ℝ) : Measure ℝ) u =
      (T : ℂ)⁻¹ * ∫ t in T..(T + T), cexp (((u * f t : ℝ) : ℂ) * I) := by
  have hT2 : T ≤ T + T := by linarith
  simp only [windowLaw, ProbabilityMeasure.coe_mk]
  rw [charFun_apply_real, integral_map hf.aemeasurable
    (by fun_prop : AEStronglyMeasurable _ _), windowMeasure, integral_smul_measure,
    intervalIntegral.integral_of_le hT2, ENNReal.toReal_ofReal (by positivity)]
  rw [Complex.real_smul]
  push_cast
  congr 1

/-- **The prime field is Gaussian.** Along any sequence with `0 ≤ w ≤ 1`, `W = Σ w² → ∞` and `(A Y)^K/T → 0` for all `K`, the law of `F/√(W/2)` on `(T, 2T]` tends to the standard Gaussian. -/
theorem tendsto_primeFieldLaw_gaussian {T : ℕ → ℝ} {P : ℕ → Finset ℕ} {w : ℕ → ℕ → ℝ} {Y : ℕ → ℕ}
    (hT : ∀ n, 0 < T n) (hw0 : ∀ n m, 0 ≤ w n m) (hw1 : ∀ n m, w n m ≤ 1)
    (hP : ∀ n, ∀ p ∈ P n, p.Prime) (hY1 : ∀ n, 1 ≤ Y n) (hY : ∀ n, ∀ p ∈ P n, p ≤ Y n)
    (hW : Tendsto (fun n => ∑ p ∈ P n, w n p ^ 2) atTop atTop)
    (hsmall : ∀ K : ℕ, Tendsto (fun n => ((∑ p ∈ P n, w n p) * Y n) ^ K / T n) atTop (𝓝 0)) :
    Tendsto (fun n => windowLaw (hT n)
        (fun t => primeField (w n) (P n) t / Real.sqrt ((∑ p ∈ P n, w n p ^ 2) / 2))
        ((continuous_primeField (w n) (P n)).measurable.div_const _))
      atTop (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun fun u => ?_
  have hlim : charFun (gaussianReal 0 1) u = cexp (-(u ^ 2 / 2 : ℝ) : ℂ) := by
    rw [charFun_gaussianReal]
    congr 1
    push_cast
    ring
  have hgoal := tendsto_mean_cexp_primeField hT hw0 hw1 hP hY1 hY hW hsmall u
  simp only [ProbabilityMeasure.coe_mk]
  rw [hlim]
  refine hgoal.congr fun n => ?_
  rw [charFun_windowLaw]
  congr 2
  funext t
  congr 2
  push_cast
  ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
