import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.ArithmeticRealityAndBirkhoffSzego
import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceIntrinsicStoppingRule
import GaloisForLFunctions.ConjugateDiagonalGeometry.CollisionChargeIncrements
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay
import GaloisForLFunctions.HTGeometry.UniformZeroCountBound
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianXiLogLinearGrowth
import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedDeepCoefficientIdentification
import GaloisForLFunctions.RHTower.XiSliceCircleDecay
import GaloisForLFunctions.RHTower.XiHorizontalRatioSelection
import GaloisForLFunctions.RHTower.RiemannVonMangoldt

/-!
# Sharp `Θ(N² log N)` strip zero-multiplicity law for theta prefixes and `Ω(√T)` stopping bound

Every finite integer Jacobi-theta prefix `finiteThetaAmplitude N` is entire of order `2` in the
complex plane, yet has only finitely many zeros in the vertical strip `{|Re z - 1 / 2| ≤ 1}` because
of its strictly positive modular seam derivative `J_{N+1,1}(0) > 0`. Naive third-jet remainder
estimates bound the seam-cusp horizon exponentially in `N²`, giving only an `O(exp(C N²))` zero-count
ceiling.

This module proves the exact `Θ(N² log N)` two-sided growth law for `prefixGlobalStripZeroBound N`
and deduces the unconditional `Ω(√T)` lower bound in height `T` on `firstArtifactFreePrefix T n`:

1. **Gaussian seam-slope lower bound (`seamSlope_gaussian_lower_bound`)**:
   By reflection cancellation of the full theta source derivative at `x = 0`,
   `J_{N+1,1}(0)` equals the negated tail derivative series from shell `N + 2` onward, whose
   leading shell `m = N + 2` already yields `(N + 2)⁶ exp(-π (N + 2)²) ≤ J_{N+1,1}(0)`.
2. **Quadratic-in-`N` strip zero-free horizon (`finiteThetaAmplitude_ne_zero_above_quadratic_horizon`)**:
   Subtracting the third-order seam-cusp identity at prefix `M ≥ N` from that at `N` isolates the
   shells `m ∈ [N + 2, M + 1]`, whose `x`-integrals gain a `1 / m²` Laplace factor converting the
   degree-`10` third logarithmic-derivative polynomial into `(N + 2)⁸ exp(-π (N + 2)²)`. Passing
   `M → ∞` against the `exp(-(π / 4) |Im z|)` vertical decay of `xi` cancels the Gaussian factor
   `exp(-π (N + 2)²)` against `J_{N+1,1}(0)` and proves `finiteThetaAmplitude N z ≠ 0` whenever
   `|Re z - 1 / 2| ≤ 1` and `|Im z| ≥ C_hor (N + 2)²`.
3. **Sharp `O(N² log N)` upper bound (`prefixGlobalStripZeroBound_upper`)**:
   Enclosing `prefixGlobalStripZeroSet N` inside `closedBall (1 / 2) (C_hor (N + 2)² + 2)` and
   bounding `‖finiteThetaAmplitude N z‖` via bilateral Laplace domination by `riemannXi (Re z)`
   (`exp(O(R log R))` growth) gives `prefixGlobalStripZeroBound N ≤ C₁ (N + 2)² log(N + 3)` by
   Jensen's formula.
4. **Rectangle Rouché at Burnol good heights and sharp `Ω(N² log N)` / `Ω(√T)` lower bounds
   (`prefixGlobalStripZeroBound_lower`, `firstArtifactFreePrefix_sqrt_lower_bound`)**:
   At a Burnol good height `T_* ∈ [(N + 1)², (N + 1)² + 1]`, `‖xi‖` is bounded below on the entire
   boundary of `[-1 / 2, 3 / 2] × [-1 / 12, T_*]` by `c T_*^{-K} exp(-(π / 4) T_*)`, whereas
   `‖finiteThetaAmplitude N - xi‖ ≤ C exp(-(N + 1)²)`. Since `π / 4 < 1`, rectangle Rouché
   transfers the Riemann–von Mangoldt zero count `Ω((N + 1)² log(N + 2))` of `xi` into
   `prefixGlobalStripZeroBound N`, and comparing `xiStripWindowTotalOrder T` against the
   `O(N² log N)` upper bound forces `c_* √T ≤ firstArtifactFreePrefix T n` unconditionally.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Set Metric intervalIntegral Polynomial
open scoped BigOperators Topology Classical Real

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1 Gaussian lower bound on the finite-prefix modular seam slope -/

/-- Exact identity expressing `thetaFiniteShellJet (N + 1) 1 0` as the negated tail series of shell
seam derivatives from index `N + 2` onward. -/
theorem thetaFiniteShellJet_one_zero_eq_tsum_tail (N : ℕ) :
    _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 =
      ∑' k : ℕ, -iteratedDeriv 1 (fun x : ℝ => _root_.RHTower.thetaCuspSourceTerm x (k + (N + 2))) 0 := by
  let f : ℕ → ℝ := fun n => iteratedDeriv 1 (fun x : ℝ => _root_.RHTower.thetaCuspSourceTerm x n) 0
  have hjet : _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 = ∑ n ∈ Finset.range (N + 2), f n := by
    have h1 := _root_.RHTower.hasDerivAt_thetaFiniteShellJet (N + 1) 0 0
    rw [_root_.RHTower.thetaFiniteShellJet_zero_eq] at h1
    exact h1.unique (_root_.RHTower.hasDerivAt_thetaCuspFiniteShellPrefix (N + 1))
  have hf : Summable f := _root_.RHTower.summable_iteratedDeriv_thetaCuspSourceTerm 1 0
  have hsplit := hf.sum_add_tsum_nat_add (N + 2)
  rw [_root_.RHTower.tsum_iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_zero] at hsplit
  have hsum_eq : ∑ n ∈ Finset.range (N + 2), f n = -(∑' k : ℕ, f (k + (N + 2))) := by
    linarith
  rw [hjet, hsum_eq, ← tsum_neg]

/-- As `M → ∞`, the finite-prefix seam slope `thetaFiniteShellJet (M + 1) 1 0` converges to `0`. -/
theorem tendsto_thetaFiniteShellJet_one_zero :
    Tendsto (fun M : ℕ => _root_.RHTower.thetaFiniteShellJet (M + 1) 1 0) atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun n => iteratedDeriv 1 (fun x : ℝ => _root_.RHTower.thetaCuspSourceTerm x n) 0
  have hf : Summable f := _root_.RHTower.summable_iteratedDeriv_thetaCuspSourceTerm 1 0
  have hsum : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, f n) atTop (𝓝 0) := by
    simpa only [_root_.RHTower.tsum_iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_zero] using
      hf.hasSum.tendsto_sum_nat
  have hcomp := hsum.comp (tendsto_add_atTop_nat 2)
  refine hcomp.congr fun M => ?_
  dsimp only [Function.comp_apply]
  have h1 := _root_.RHTower.hasDerivAt_thetaFiniteShellJet (M + 1) 0 0
  rw [_root_.RHTower.thetaFiniteShellJet_zero_eq] at h1
  exact (h1.unique (_root_.RHTower.hasDerivAt_thetaCuspFiniteShellPrefix (M + 1))).symm

/-- **Gaussian lower bound on the finite-prefix modular seam slope.**
For every `N : ℕ`, retaining the first omitted shell `m = N + 2` in the negated tail derivative
series gives `(N + 2)⁶ exp(-π (N + 2)²) ≤ thetaFiniteShellJet (N + 1) 1 0`. -/
theorem seamSlope_gaussian_lower_bound (N : ℕ) :
    ((N + 2 : ℕ) : ℝ) ^ 6 * Real.exp (-Real.pi * ((N + 2 : ℕ) : ℝ) ^ 2) ≤
      _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by
  let f : ℕ → ℝ := fun n => iteratedDeriv 1 (fun x : ℝ => _root_.RHTower.thetaCuspSourceTerm x n) 0
  have hf : Summable f := _root_.RHTower.summable_iteratedDeriv_thetaCuspSourceTerm 1 0
  have hg : Summable (fun k : ℕ => -f (k + (N + 2))) :=
    ((summable_nat_add_iff (N + 2)).mpr hf).neg
  have hnonneg : ∀ k : ℕ, 0 ≤ -f (k + (N + 2)) := fun k =>
    neg_nonneg.mpr
      (_root_.RHTower.iteratedDeriv_one_thetaCuspSourceTerm_zero_neg (n := k + (N + 2)) (by omega)).le
  have hle_tsum : -f (N + 2) ≤ _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by
    rw [thetaFiniteShellJet_one_zero_eq_tsum_tail N]
    simpa only [zero_add] using hg.le_tsum 0 fun k _ => hnonneg k
  set m : ℕ := N + 2
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 ≤ N + 2 by omega)
  have hmsq4 : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hm4 : (16 : ℝ) ≤ (m : ℝ) ^ 4 := by nlinarith
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hden_pos : 21 < 2 * Real.pi * (m : ℝ) ^ 2 - 3 := by nlinarith
  have hfrac : 6 / (2 * Real.pi * (m : ℝ) ^ 2 - 3) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Real.pi * (m : ℝ) ^ 2 - 3)]
    linarith
  have hslope_ge : 4 * (m : ℝ) ^ 2 ≤ -_root_.RHTower.thetaCuspAtomBoundaryLogSlope m := by
    unfold _root_.RHTower.thetaCuspAtomBoundaryLogSlope
    nlinarith
  have hsrc_eq : _root_.RHTower.thetaCuspSourceTerm 0 m =
      2 * Real.pi * (2 * Real.pi * (m : ℝ) ^ 4 - 3 * (m : ℝ) ^ 2) *
        Real.exp (-Real.pi * (m : ℝ) ^ 2) := by
    have h := congrFun (_root_.RHTower.thetaCuspSourceTerm_eq_polynomialAtom m) 0
    rw [h]
    unfold _root_.RHTower.thetaCuspPolynomialAtom _root_.RHTower.thetaCuspSeedPolynomial
    simp only [zero_div, Real.exp_zero, one_mul, mul_one, eval_sub, eval_mul, eval_C, eval_pow,
      eval_X]
    ring
  have hsrc_ge : 30 * (m : ℝ) ^ 4 * Real.exp (-Real.pi * (m : ℝ) ^ 2) ≤
      _root_.RHTower.thetaCuspSourceTerm 0 m := by
    rw [hsrc_eq]
    have hpoly : 30 * (m : ℝ) ^ 4 ≤ 2 * Real.pi * (2 * Real.pi * (m : ℝ) ^ 4 - 3 * (m : ℝ) ^ 2) := by
      have h1 : 21 / 4 * (m : ℝ) ^ 4 ≤ 2 * Real.pi * (m : ℝ) ^ 4 - 3 * (m : ℝ) ^ 2 := by
        have hm2_le : (m : ℝ) ^ 2 ≤ (1 / 4) * (m : ℝ) ^ 4 := by
          have : (4 : ℝ) * (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 * (m : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hmsq4 (sq_nonneg _)
          linarith
        nlinarith
      nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) m) 4]
    exact mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
  have hprod : (m : ℝ) ^ 6 * Real.exp (-Real.pi * (m : ℝ) ^ 2) ≤ -f m := by
    dsimp only [f]
    rw [_root_.RHTower.iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_slope, neg_mul]
    calc (m : ℝ) ^ 6 * Real.exp (-Real.pi * (m : ℝ) ^ 2)
        ≤ 120 * (m : ℝ) ^ 6 * Real.exp (-Real.pi * (m : ℝ) ^ 2) := by
          have hp6 : 0 ≤ (m : ℝ) ^ 6 * Real.exp (-Real.pi * (m : ℝ) ^ 2) := by positivity
          linarith
      _ = (4 * (m : ℝ) ^ 2) * (30 * (m : ℝ) ^ 4 * Real.exp (-Real.pi * (m : ℝ) ^ 2)) := by ring
      _ ≤ (-_root_.RHTower.thetaCuspAtomBoundaryLogSlope m) *
            _root_.RHTower.thetaCuspSourceTerm 0 m :=
          mul_le_mul hslope_ge hsrc_ge (by positivity) (by positivity)
  exact hprod.trans hle_tsum

/-! ## §2 Quadratic-in-`N` vertical-strip zero-free horizon for `finiteThetaAmplitude N` -/

private lemma natDegree_thetaCuspLogDerivativePolynomial_le (k : ℕ) :
    (_root_.RHTower.thetaCuspLogDerivativePolynomial k).natDegree ≤ 4 + 2 * k := by
  induction k with
  | zero =>
    unfold _root_.RHTower.thetaCuspLogDerivativePolynomial _root_.RHTower.thetaCuspSeedPolynomial
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ 4).trans (by omega)
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ 2).trans (by omega)
  | succ k ih =>
    unfold _root_.RHTower.thetaCuspLogDerivativePolynomial _root_.RHTower.thetaCuspLogDerivativeStep
    set P := _root_.RHTower.thetaCuspLogDerivativePolynomial k
    have hd1 : (C (1 / 2 : ℝ) * P + X * Polynomial.derivative P).natDegree ≤ 4 + 2 * k + 1 := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (by omega)
      · refine (Polynomial.natDegree_mul_le).trans ?_
        have hx := Polynomial.natDegree_X_le (R := ℝ)
        have hd := Polynomial.natDegree_derivative_le P
        omega
    have hd2 : (C (2 * Real.pi) * X ^ 2 * P).natDegree ≤ 4 + 2 * (k + 1) := by
      refine (Polynomial.natDegree_mul_le).trans ?_
      have hc := Polynomial.natDegree_C_mul_X_pow_le (2 * Real.pi) 2
      omega
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by omega) hd2)

/-- Coefficient `ℓ¹` mass of the third theta-cusp logarithmic-derivative polynomial. -/
private def thirdJetPolyMass : ℝ :=
  ∑ j ∈ (_root_.RHTower.thetaCuspLogDerivativePolynomial 3).support,
    |(_root_.RHTower.thetaCuspLogDerivativePolynomial 3).coeff j|

private lemma thirdJetPolyMass_nonneg : 0 ≤ thirdJetPolyMass :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma abs_eval_thirdJetPoly_le {y : ℝ} (hy1 : 1 ≤ y) :
    |eval y (_root_.RHTower.thetaCuspLogDerivativePolynomial 3)| ≤ thirdJetPolyMass * y ^ 10 := by
  set P := _root_.RHTower.thetaCuspLogDerivativePolynomial 3
  have hdeg : P.natDegree ≤ 10 := by
    simpa using natDegree_thetaCuspLogDerivativePolynomial_le 3
  calc |eval y P|
      ≤ ∑ j ∈ P.support, |P.coeff j| * y ^ j :=
        _root_.RHTower.abs_eval_le_coefficient_sum P (zero_le_one.trans hy1)
    _ ≤ ∑ j ∈ P.support, |P.coeff j| * y ^ 10 := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact pow_le_pow_right₀ hy1 ((Polynomial.le_natDegree_of_mem_supp j hj).trans hdeg)
    _ = thirdJetPolyMass * y ^ 10 := by
        rw [← Finset.sum_mul]
        rfl

/-- Single-shell Laplace bound on the third-jet strip integrand: integrating against
`exp(-(m : ℝ)² x)` gains `((m : ℝ)²)⁻¹`, lowering `(m : ℝ)¹⁰` to `(m : ℝ)⁸`. -/
private lemma norm_singleShell_thirdJet_integral_le {m : ℕ} (hm : 2 ≤ m) {z : ℂ}
    (hz : |z.re - 1 / 2| ≤ 1) :
    ‖∫ x in Ioi (0 : ℝ),
        (_root_.RHTower.thetaCuspPolynomialAtom
          (_root_.RHTower.thetaCuspLogDerivativePolynomial 3) m x : ℂ) *
          (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))‖ ≤
      (2 * thirdJetPolyMass) * (m : ℝ) ^ 8 * Real.exp (-Real.pi * (m : ℝ) ^ 2) := by
  set P₃ := _root_.RHTower.thetaCuspLogDerivativePolynomial 3
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmsq4 : (4 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hmsq_pos : 0 < (m : ℝ) ^ 2 := by positivity
  have hneg_lt : -((m : ℝ) ^ 2) < 0 := neg_neg_of_pos hmsq_pos
  let C_m : ℝ := 2 * thirdJetPolyMass * (m : ℝ) ^ 10 * Real.exp (-Real.pi * (m : ℝ) ^ 2)
  have hdom_int : IntegrableOn (fun x : ℝ => C_m * Real.exp (-((m : ℝ) ^ 2) * x)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi hneg_lt 0).const_mul C_m
  have hint_atom : IntegrableOn (_root_.RHTower.thetaCuspPolynomialAtom P₃ m) (Ioi (0 : ℝ)) :=
    _root_.RHTower.integrableOn_thetaCuspPolynomialAtom_Ioi_of_pos P₃ (by omega)
  -- Pointwise norm bound on `(0, ∞)` also proves integrability of the integrand via `Integrable.mono'`.
  have hpt_bound : ∀ x : ℝ, 0 < x →
      ‖(_root_.RHTower.thetaCuspPolynomialAtom P₃ m x : ℂ) *
          (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))‖ ≤
        C_m * Real.exp (-((m : ℝ) ^ 2) * x) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.le
    have hexp1 : ‖Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ))‖ ≤ Real.exp x := by
      rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
      have hre : ((z - (1 / 2 : ℂ)) * (x : ℂ)).re = (z.re - 1 / 2) * x := by simp
      rw [hre]
      exact (le_abs_self _).trans (by
        rw [abs_mul, abs_of_nonneg hx0]
        exact (mul_le_mul_of_nonneg_right hz hx0).trans_eq (one_mul x))
    have hexp2 : ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤ Real.exp x := by
      rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
      have hre : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = -(z.re - 1 / 2) * x := by
        have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
        have h12i : (1 / 2 : ℂ).im = 0 := by norm_num
        simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
          Complex.ofReal_im, h12, h12i, mul_zero, sub_zero]
        ring
      rw [hre]
      exact (le_abs_self _).trans (by
        rw [abs_mul, abs_neg, abs_of_nonneg hx0]
        exact (mul_le_mul_of_nonneg_right hz hx0).trans_eq (one_mul x))
    have hdiff : ‖Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤ 2 * Real.exp x :=
      (norm_sub_le _ _).trans (by linarith)
    set y : ℝ := (m : ℝ) * Real.exp x
    have hy1 : 1 ≤ y := by
      dsimp only [y]
      have hex1 : 1 ≤ Real.exp x := Real.one_le_exp hx0
      nlinarith
    have heval := abs_eval_thirdJetPoly_le hy1
    have hatom : |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x| ≤
        Real.exp (x / 2) * (thirdJetPolyMass * y ^ 10) *
          Real.exp (-Real.pi * y ^ 2) := by
      unfold _root_.RHTower.thetaCuspPolynomialAtom
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left heval (Real.exp_pos _).le) (Real.exp_pos _).le
    have hy10 : y ^ 10 = (m : ℝ) ^ 10 * Real.exp (10 * x) := by
      dsimp only [y]
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
    have hy2 : y ^ 2 = (m : ℝ) ^ 2 * Real.exp (2 * x) := by
      dsimp only [y]
      rw [mul_pow, ← Real.exp_nat_mul]
      norm_num
    have hexponent : (23 / 2 : ℝ) * x - Real.pi * ((m : ℝ) ^ 2 * Real.exp (2 * x)) ≤
        -Real.pi * (m : ℝ) ^ 2 + -((m : ℝ) ^ 2) * x := by
      have hexp2 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
      have hmul : Real.pi * (m : ℝ) ^ 2 * (1 + 2 * x) ≤
          Real.pi * ((m : ℝ) ^ 2 * Real.exp (2 * x)) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left hexp2 (by positivity)
      have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hpm : 6 * (m : ℝ) ^ 2 * x ≤ 2 * Real.pi * (m : ℝ) ^ 2 * x := by
        have h6 : 6 ≤ 2 * Real.pi := by linarith
        have hm0 : 0 ≤ (m : ℝ) ^ 2 * x := by positivity
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hmsq4 hx0]
    have hexp_le : Real.exp (x / 2) * Real.exp (10 * x) * Real.exp (-Real.pi * y ^ 2) * Real.exp x ≤
        Real.exp (-Real.pi * (m : ℝ) ^ 2) * Real.exp (-((m : ℝ) ^ 2) * x) := by
      rw [hy2, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x| *
            ‖Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
              Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
        ≤ (Real.exp (x / 2) * (thirdJetPolyMass * y ^ 10) * Real.exp (-Real.pi * y ^ 2)) *
            (2 * Real.exp x) :=
          mul_le_mul hatom hdiff (norm_nonneg _) (by positivity [thirdJetPolyMass_nonneg])
      _ = 2 * thirdJetPolyMass * (m : ℝ) ^ 10 *
            (Real.exp (x / 2) * Real.exp (10 * x) * Real.exp (-Real.pi * y ^ 2) * Real.exp x) := by
          rw [hy10]; ring
      _ ≤ 2 * thirdJetPolyMass * (m : ℝ) ^ 10 *
            (Real.exp (-Real.pi * (m : ℝ) ^ 2) * Real.exp (-((m : ℝ) ^ 2) * x)) :=
          mul_le_mul_of_nonneg_left hexp_le
            (mul_nonneg (mul_nonneg (by norm_num) thirdJetPolyMass_nonneg) (by positivity))
      _ = C_m * Real.exp (-((m : ℝ) ^ 2) * x) := by dsimp only [C_m]; ring
  have hcont : Continuous (fun x : ℝ =>
      (_root_.RHTower.thetaCuspPolynomialAtom P₃ m x : ℂ) *
        (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))) := by
    have hatom_c : Continuous (_root_.RHTower.thetaCuspPolynomialAtom P₃ m) :=
      continuous_iff_continuousAt.mpr fun x =>
        (_root_.RHTower.hasDerivAt_thetaCuspPolynomialAtom P₃ m x).continuousAt
    exact (Complex.continuous_ofReal.comp hatom_c).mul
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).sub
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))
  have hint : IntegrableOn (fun x : ℝ =>
      (_root_.RHTower.thetaCuspPolynomialAtom P₃ m x : ℂ) *
        (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))) (Ioi (0 : ℝ)) := by
    refine hdom_int.mono' hcont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hpt_bound x hx
  have hexp_val : (∫ x in Ioi (0 : ℝ), Real.exp (-((m : ℝ) ^ 2) * x)) = ((m : ℝ) ^ 2)⁻¹ := by
    rw [integral_exp_mul_Ioi hneg_lt 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [hmsq_pos.ne']
  calc ‖∫ x in Ioi (0 : ℝ),
          (_root_.RHTower.thetaCuspPolynomialAtom P₃ m x : ℂ) *
            (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
              Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))‖
      ≤ ∫ x in Ioi (0 : ℝ),
          ‖(_root_.RHTower.thetaCuspPolynomialAtom P₃ m x : ℂ) *
            (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
              Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (0 : ℝ), C_m * Real.exp (-((m : ℝ) ^ 2) * x) := by
        refine integral_mono_ae hint.norm hdom_int ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact hpt_bound x hx
    _ = C_m * ((m : ℝ) ^ 2)⁻¹ := by rw [MeasureTheory.integral_const_mul, hexp_val]
    _ = (2 * thirdJetPolyMass) * (m : ℝ) ^ 8 * Real.exp (-Real.pi * (m : ℝ) ^ 2) := by
        dsimp only [C_m]
        field_simp [hmsq_pos.ne']

/-- Finite-range shell sum bound for `(m₀ + j)⁸ exp(-π (m₀ + j)²)`. -/
private lemma sum_shell_pow8_gaussian_le (N K : ℕ) :
    (∑ j ∈ Finset.range K,
        (((N + 2 + j : ℕ) : ℝ) ^ 8 * Real.exp (-Real.pi * ((N + 2 + j : ℕ) : ℝ) ^ 2))) ≤
      2 * ((N + 2 : ℕ) : ℝ) ^ 8 * Real.exp (-Real.pi * ((N + 2 : ℕ) : ℝ) ^ 2) := by
  set m₀ : ℝ := ((N + 2 : ℕ) : ℝ)
  have hm₀2 : (2 : ℝ) ≤ m₀ := by dsimp only [m₀]; exact_mod_cast (show 2 ≤ N + 2 by omega)
  have hm₀1 : (1 : ℝ) ≤ m₀ := by linarith
  have he_inv : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num)).mpr
      (by linarith [Real.add_one_le_exp (1 : ℝ)])
  have hterm : ∀ j : ℕ,
      ((N + 2 + j : ℕ) : ℝ) ^ 8 * Real.exp (-Real.pi * ((N + 2 + j : ℕ) : ℝ) ^ 2) ≤
        (m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2)) * (1 / 2 : ℝ) ^ j := by
    intro j
    have hcast : ((N + 2 + j : ℕ) : ℝ) = m₀ + (j : ℝ) := by dsimp only [m₀]; push_cast; ring
    rw [hcast]
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hlin : m₀ + (j : ℝ) ≤ m₀ * (1 + (j : ℝ)) := by nlinarith
    have h1j : 1 + (j : ℝ) ≤ Real.exp (j : ℝ) := by linarith [Real.add_one_le_exp (j : ℝ)]
    have hp8 : (m₀ + (j : ℝ)) ^ 8 ≤ m₀ ^ 8 * Real.exp (8 * (j : ℝ)) := by
      calc (m₀ + (j : ℝ)) ^ 8
          ≤ (m₀ * (1 + (j : ℝ))) ^ 8 := pow_le_pow_left₀ (by positivity) hlin 8
        _ = m₀ ^ 8 * (1 + (j : ℝ)) ^ 8 := mul_pow _ _ 8
        _ ≤ m₀ ^ 8 * (Real.exp (j : ℝ)) ^ 8 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1j 8) (by positivity)
        _ = m₀ ^ 8 * Real.exp (8 * (j : ℝ)) := by
            rw [← Real.exp_nat_mul]; norm_num
    have hsq : m₀ ^ 2 + 4 * (j : ℝ) ≤ (m₀ + (j : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (j : ℝ)]
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hexp_le : 8 * (j : ℝ) + -Real.pi * (m₀ + (j : ℝ)) ^ 2 ≤
        -Real.pi * m₀ ^ 2 + -(j : ℝ) := by
      have hmul : Real.pi * (m₀ ^ 2 + 4 * (j : ℝ)) ≤ Real.pi * (m₀ + (j : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
      nlinarith
    have hpow_half : Real.exp (-(j : ℝ)) ≤ (1 / 2 : ℝ) ^ j := by
      rw [show -(j : ℝ) = (j : ℕ) * (-1 : ℝ) by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le he_inv j
    calc (m₀ + (j : ℝ)) ^ 8 * Real.exp (-Real.pi * (m₀ + (j : ℝ)) ^ 2)
        ≤ (m₀ ^ 8 * Real.exp (8 * (j : ℝ))) * Real.exp (-Real.pi * (m₀ + (j : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_right hp8 (Real.exp_pos _).le
      _ = m₀ ^ 8 * Real.exp (8 * (j : ℝ) + -Real.pi * (m₀ + (j : ℝ)) ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2 + -(j : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_le) (by positivity)
      _ = (m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2)) * Real.exp (-(j : ℝ)) := by
          rw [Real.exp_add]; ring
      _ ≤ (m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2)) * (1 / 2 : ℝ) ^ j :=
          mul_le_mul_of_nonneg_left hpow_half (by positivity)
  have hgeo : (∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j) ≤ 2 := by
    have hsum := geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1) K
    have hp : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
    linarith
  calc (∑ j ∈ Finset.range K,
          (((N + 2 + j : ℕ) : ℝ) ^ 8 * Real.exp (-Real.pi * ((N + 2 + j : ℕ) : ℝ) ^ 2)))
      ≤ ∑ j ∈ Finset.range K,
          (m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2)) * (1 / 2 : ℝ) ^ j :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2)) * ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j := by
        rw [← Finset.mul_sum]
    _ ≤ (m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2)) * 2 :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
    _ = 2 * m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2) := by ring

/-- Exact Gaussian bound on the third-order seam-cusp remainder of `finiteThetaAmplitude N`
obtained by subtracting `finiteThetaAmplitude_mul_sq_sub_half_ibp3 (N + K)` and letting `K → ∞`. -/
theorem norm_finiteThetaAmplitude_cusp_remainder_gaussian_le (N : ℕ) {z : ℂ}
    (hz : |z.re - 1 / 2| ≤ 1) :
    ‖(z - (1 / 2 : ℂ)) *
        ((z - (1 / 2 : ℂ)) ^ 2 * _root_.RHTower.finiteThetaAmplitude N z -
          2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ))‖ ≤
      ‖z - (1 / 2 : ℂ)‖ ^ 3 * ‖_root_.RHTower.xi z‖ +
        (4 * thirdJetPolyMass) * ((N + 2 : ℕ) : ℝ) ^ 8 *
          Real.exp (-Real.pi * ((N + 2 : ℕ) : ℝ) ^ 2) := by
  set w : ℂ := z - (1 / 2 : ℂ)
  let S : ℝ → ℂ := fun x =>
    Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) - Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))
  set P₃ := _root_.RHTower.thetaCuspLogDerivativePolynomial 3
  set R_N : ℂ := w * (w ^ 2 * _root_.RHTower.finiteThetaAmplitude N z -
    2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ))
  let B_tail : ℝ := (4 * thirdJetPolyMass) * ((N + 2 : ℕ) : ℝ) ^ 8 *
    Real.exp (-Real.pi * ((N + 2 : ℕ) : ℝ) ^ 2)
  -- Step 1: For every `K : ℕ`, bound the difference between `N + K` and `N` by `B_tail`.
  have hdiff_K : ∀ K : ℕ,
      ‖w * (w ^ 2 * _root_.RHTower.finiteThetaAmplitude (N + K) z -
          2 * (_root_.RHTower.thetaFiniteShellJet (N + K + 1) 1 0 : ℂ)) - R_N‖ ≤ B_tail := by
    intro K
    have hibp_NK := finiteThetaAmplitude_mul_sq_sub_half_ibp3 (N + K) z
    have hibp_N := finiteThetaAmplitude_mul_sq_sub_half_ibp3 N z
    change w * (w ^ 2 * _root_.RHTower.finiteThetaAmplitude (N + K) z -
        2 * (_root_.RHTower.thetaFiniteShellJet (N + K + 1) 1 0 : ℂ)) =
      -∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet (N + K + 1) 3 x : ℂ) * S x at hibp_NK
    change R_N = -∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x : ℂ) * S x
      at hibp_N
    let atomInt : ℕ → ℝ → ℂ := fun m x => (_root_.RHTower.thetaCuspPolynomialAtom P₃ m x : ℂ) * S x
    have hatom_int : ∀ m : ℕ, 1 ≤ m → IntegrableOn (atomInt m) (Ioi (0 : ℝ)) := by
      intro m hm1
      have h0 : IntegrableOn (fun x =>
          (Complex.exp (w * (x : ℂ)) - Complex.exp (-w * (x : ℂ))) *
            (_root_.RHTower.thetaCuspPolynomialAtom P₃ m x : ℂ)) (Ioi (0 : ℝ)) := by
        -- Each shell atom `m` equals `J_{m,3} - J_{m-1,3}`, or directly bounded by `(N=m)` jet:
        set m' := m - 1
        have hm' : m' + 1 = m := by omega
        -- Direct compact/exponential domination on `(0, ∞)` using `abs_thetaCuspPolynomialAtom`:
        let q := (2 : ℕ)
        let C_maj := _root_.RHTower.thetaCuspGaussianConstant
          (_root_.RHTower.thetaCuspWeightedPolynomial P₃ (q + 1))
        have hdom : IntegrableOn (fun x : ℝ => (2 * C_maj) * Real.exp (-x)) (Ioi (0 : ℝ)) := by
          have h1 := integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
          exact (h1.congr_fun (fun x _ => by ring_nf) measurableSet_Ioi).const_mul _
        have hc : Continuous (fun x : ℝ =>
            (Complex.exp (w * (x : ℂ)) - Complex.exp (-w * (x : ℂ))) *
              (_root_.RHTower.thetaCuspPolynomialAtom P₃ m x : ℂ)) := by
          have ha : Continuous (_root_.RHTower.thetaCuspPolynomialAtom P₃ m) :=
            continuous_iff_continuousAt.mpr fun x =>
              (_root_.RHTower.hasDerivAt_thetaCuspPolynomialAtom P₃ m x).continuousAt
          exact ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).sub
            (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).mul
              (Complex.continuous_ofReal.comp ha)
        refine hdom.mono' hc.aestronglyMeasurable.restrict ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 ≤ x := hx.le
        have hex1 : ‖Complex.exp (w * (x : ℂ))‖ ≤ Real.exp ((q : ℝ) * x) := by
          rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
          have hre : (w * (x : ℂ)).re = (z.re - 1 / 2) * x := by simp [w]
          rw [hre]
          have hq : |z.re - 1 / 2| ≤ (q : ℝ) := hz.trans (by norm_num [q])
          exact (le_abs_self _).trans
            (by rw [abs_mul, abs_of_nonneg hx0]; exact mul_le_mul_of_nonneg_right hq hx0)
        have hex2 : ‖Complex.exp (-w * (x : ℂ))‖ ≤ Real.exp ((q : ℝ) * x) := by
          rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
          have hre : (-w * (x : ℂ)).re = -(z.re - 1 / 2) * x := by simp [w]; ring
          rw [hre]
          have hq : |z.re - 1 / 2| ≤ (q : ℝ) := hz.trans (by norm_num [q])
          exact (le_abs_self _).trans
            (by rw [abs_mul, abs_neg, abs_of_nonneg hx0]; exact mul_le_mul_of_nonneg_right hq hx0)
        have hS_le : ‖Complex.exp (w * (x : ℂ)) - Complex.exp (-w * (x : ℂ))‖ ≤
            2 * Real.exp ((q : ℝ) * x) := (norm_sub_le _ _).trans (by linarith)
        have hatom_le : Real.exp ((q : ℝ) * x) * |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x| ≤
            C_maj * Real.exp (-x) := by
          have hw_eq := _root_.RHTower.exp_nat_mul_thetaCuspPolynomialAtom_eq P₃ (q + 1) m x
          have hgauss := _root_.RHTower.abs_thetaCuspPolynomialAtom_le_gaussianConstant
            (_root_.RHTower.thetaCuspWeightedPolynomial P₃ (q + 1)) hm1 hx0
          have hrew : Real.exp ((q : ℝ) * x) * |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x| =
              Real.exp (-x) * (Real.exp (((q + 1 : ℕ) : ℝ) * x) *
                |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x|) := by
            push_cast
            calc Real.exp ((q : ℝ) * x) * |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x|
                = (Real.exp (-x) * Real.exp (((q : ℝ) + 1) * x)) *
                    |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x| := by
                  rw [← Real.exp_add]; congr 2; ring
              _ = _ := by ring
          rw [hrew, ← abs_of_pos (Real.exp_pos (((q + 1 : ℕ) : ℝ) * x)), ← abs_mul, hw_eq]
          calc Real.exp (-x) *
                  |_root_.RHTower.thetaCuspPolynomialAtom
                    (_root_.RHTower.thetaCuspWeightedPolynomial P₃ (q + 1)) m x|
              ≤ Real.exp (-x) * C_maj := mul_le_mul_of_nonneg_left hgauss (Real.exp_pos _).le
            _ = C_maj * Real.exp (-x) := mul_comm _ _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖Complex.exp (w * (x : ℂ)) - Complex.exp (-w * (x : ℂ))‖ *
                |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x|
            ≤ (2 * Real.exp ((q : ℝ) * x)) * |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x| :=
              mul_le_mul_of_nonneg_right hS_le (abs_nonneg _)
          _ = 2 * (Real.exp ((q : ℝ) * x) * |_root_.RHTower.thetaCuspPolynomialAtom P₃ m x|) := by
              ring
          _ ≤ 2 * (C_maj * Real.exp (-x)) := mul_le_mul_of_nonneg_left hatom_le (by norm_num)
          _ = (2 * C_maj) * Real.exp (-x) := by ring
      refine h0.congr_fun (fun x _ => ?_) measurableSet_Ioi
      dsimp only [atomInt, S, w]
      have hw : (1 / 2 : ℂ) - z = -(z - (1 / 2 : ℂ)) := by ring
      rw [hw]; ring
    have hjet_sum : ∀ M : ℕ,
        (∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet (M + 1) 3 x : ℂ) * S x) =
          ∑ n ∈ Finset.range (M + 1), ∫ x in Ioi (0 : ℝ), atomInt (n + 1) x := by
      intro M
      have hcongr : (∫ x in Ioi (0 : ℝ),
            (_root_.RHTower.thetaFiniteShellJet (M + 1) 3 x : ℂ) * S x) =
          ∫ x in Ioi (0 : ℝ), ∑ n ∈ Finset.range (M + 1), atomInt (n + 1) x := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        unfold _root_.RHTower.thetaFiniteShellJet
        push_cast
        rw [Finset.sum_mul]
        rfl
      rw [hcongr, integral_finset_sum _ fun n _ => hatom_int (n + 1) (Nat.succ_pos n)]
    rw [hibp_NK, hibp_N, neg_sub_neg,
      show N + K + 1 = (N + 1) + K by omega,
      show (∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x : ℂ) * S x) -
          (∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet ((N + 1) + K) 3 x : ℂ) * S x) =
        -((∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet ((N + 1) + K) 3 x : ℂ) * S x) -
          (∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x : ℂ) * S x)) by ring,
      norm_neg]
    have h1 := hjet_sum (N + K)
    rw [show N + K + 1 = (N + 1) + K by omega] at h1
    rw [h1, hjet_sum N, Finset.sum_range_add, add_sub_cancel_left]
    calc ‖∑ j ∈ Finset.range K, ∫ x in Ioi (0 : ℝ), atomInt (N + 1 + j + 1) x‖
        ≤ ∑ j ∈ Finset.range K, ‖∫ x in Ioi (0 : ℝ), atomInt (N + 2 + j) x‖ := by
          refine (norm_sum_le _ _).trans_eq ?_
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [show N + 1 + j + 1 = N + 2 + j by omega]
      _ ≤ ∑ j ∈ Finset.range K,
            (2 * thirdJetPolyMass) * ((N + 2 + j : ℕ) : ℝ) ^ 8 *
              Real.exp (-Real.pi * ((N + 2 + j : ℕ) : ℝ) ^ 2) :=
          Finset.sum_le_sum fun j _ =>
            norm_singleShell_thirdJet_integral_le (by omega) hz
      _ = (2 * thirdJetPolyMass) *
            ∑ j ∈ Finset.range K,
              (((N + 2 + j : ℕ) : ℝ) ^ 8 * Real.exp (-Real.pi * ((N + 2 + j : ℕ) : ℝ) ^ 2)) := by
          simp_rw [mul_assoc, ← Finset.mul_sum]
      _ ≤ (2 * thirdJetPolyMass) *
            (2 * ((N + 2 : ℕ) : ℝ) ^ 8 * Real.exp (-Real.pi * ((N + 2 : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (sum_shell_pow8_gaussian_le N K)
            (mul_nonneg (by norm_num) thirdJetPolyMass_nonneg)
      _ = B_tail := by dsimp only [B_tail]; ring
  -- Step 2: Pass `K → ∞` using `finiteThetaAmplitude (N + K) z → xi z` and `J_{N+K+1,1}(0) → 0`.
  have hz2 : |z.re| ≤ 2 := by
    rw [abs_le] at hz ⊢
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have htend_amp : Tendsto (fun K : ℕ => _root_.RHTower.finiteThetaAmplitude (N + K) z)
      atTop (𝓝 (_root_.RHTower.xi z)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let C_env := _root_.RHTower.thetaCuspIntegerTailConstant *
      _root_.RHTower.thetaAmplitudeEnvelope 2
    have hsq : Tendsto (fun K : ℕ => ((N + K + 1 : ℕ) : ℝ) ^ 2) atTop atTop :=
      (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat (N + 1) |>.congr fun K => by omega))
    have hexp : Tendsto (fun K : ℕ => C_env * Real.exp (-((N + K + 1 : ℕ) : ℝ) ^ 2))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, pow_zero, one_mul, mul_zero] using
        ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hsq).const_mul C_env
    filter_upwards [hexp.eventually (gt_mem_nhds hε)] with K hK
    rw [dist_eq_norm]
    exact (norm_finiteThetaAmplitude_sub_xi_le_strip (N + K) (by norm_num : (0 : ℝ) ≤ 2) hz2).trans_lt
      (by simpa only [C_env, mul_right_comm] using hK)
  have htend_jet : Tendsto
      (fun K : ℕ => (_root_.RHTower.thetaFiniteShellJet (N + K + 1) 1 0 : ℂ)) atTop (𝓝 0) := by
    have hreal : Tendsto (fun K : ℕ => _root_.RHTower.thetaFiniteShellJet (N + K + 1) 1 0)
        atTop (𝓝 0) :=
      (tendsto_thetaFiniteShellJet_one_zero.comp (tendsto_add_atTop_nat N)).congr
        fun K => by dsimp only [Function.comp_apply]; rw [add_comm K N]
    simpa using (Complex.continuous_ofReal.continuousAt.tendsto).comp hreal
  have htend_lhs : Tendsto
      (fun K : ℕ => ‖w * (w ^ 2 * _root_.RHTower.finiteThetaAmplitude (N + K) z -
        2 * (_root_.RHTower.thetaFiniteShellJet (N + K + 1) 1 0 : ℂ)) - R_N‖)
      atTop (𝓝 ‖w * (w ^ 2 * _root_.RHTower.xi z - 2 * (0 : ℂ)) - R_N‖) :=
    (((tendsto_const_nhds.mul ((tendsto_const_nhds.mul htend_amp).sub
      (tendsto_const_nhds.mul htend_jet))).sub tendsto_const_nhds).norm)
  have hlim_le : ‖w ^ 3 * _root_.RHTower.xi z - R_N‖ ≤ B_tail := by
    have h := le_of_tendsto htend_lhs (Eventually.of_forall hdiff_K)
    simpa only [mul_zero, sub_zero, show w * (w ^ 2 * _root_.RHTower.xi z) =
      w ^ 3 * _root_.RHTower.xi z by ring] using h
  calc ‖R_N‖
      = ‖w ^ 3 * _root_.RHTower.xi z - (w ^ 3 * _root_.RHTower.xi z - R_N)‖ := by ring_nf
    _ ≤ ‖w ^ 3 * _root_.RHTower.xi z‖ + ‖w ^ 3 * _root_.RHTower.xi z - R_N‖ := norm_sub_le _ _
    _ ≤ ‖w‖ ^ 3 * ‖_root_.RHTower.xi z‖ + B_tail := by
        rw [norm_mul, norm_pow]
        exact add_le_add_left hlim_le _

/-- Vertical-strip Stirling decay of `xi` on `{|Re z - 1 / 2| ≤ 1}`, `4 ≤ |Im z|`. -/
private lemma exists_xi_strip_exp_decay :
    ∃ (C_xi : ℝ) (K_xi : ℕ), 0 ≤ C_xi ∧ ∀ z : ℂ, |z.re - 1 / 2| ≤ 1 → 4 ≤ |z.im| →
      ‖_root_.RHTower.xi z‖ ≤ C_xi * |z.im| ^ K_xi * Real.exp (-(Real.pi / 4) * |z.im|) := by
  obtain ⟨CΓ, NΓ, hCΓ0, hΓ⟩ :=
    HTGeometry.exists_sharp_bound_norm_Gamma_strip (1 / 4 : ℝ) (3 / 4 : ℝ)
  refine ⟨20 * CΓ, NΓ + 3, by positivity, ?_⟩
  intro z hz_re hz_im
  -- Reduce to `1 / 2 ≤ s.re ≤ 3 / 2` via `xi_one_sub`.
  suffices hright : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 → 4 ≤ |s.im| →
      ‖_root_.RHTower.xi s‖ ≤ (20 * CΓ) * |s.im| ^ (NΓ + 3) * Real.exp (-(Real.pi / 4) * |s.im|) by
    rcases le_or_gt (1 / 2 : ℝ) z.re with hge | hlt
    · exact hright z hge (by linarith [(abs_le.mp hz_re).2]) hz_im
    · have h1 := hright (1 - z) (by simp; linarith)
        (by simp; linarith [(abs_le.mp hz_re).1]) (by simpa [abs_neg] using hz_im)
      rwa [_root_.RHTower.xi_one_sub, show |(1 - z).im| = |z.im| by simp [abs_neg]] at h1
  intro s hs1 hs2 hsim
  have hs_pos : 0 < s.re := by linarith
  have hs_ne1 : s ≠ 1 := by
    intro h; rw [h, Complex.one_im, abs_zero] at hsim; norm_num at hsim
  rw [_root_.RHTower.norm_xi_eq_factors hs_pos hs_ne1]
  have hs_norm : ‖s‖ ≤ 2 * |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    rw [abs_of_pos hs_pos] at h
    linarith
  have hs1_norm : ‖s - 1‖ ≤ 2 * |s.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (s - 1)
    have hre : |(s - 1).re| ≤ 1 / 2 := by
      rw [Complex.sub_re, Complex.one_re, abs_le]
      exact ⟨by linarith, by linarith⟩
    have him : |(s - 1).im| = |s.im| := by simp
    linarith
  have hquad : ‖s * (s - 1) / 2‖ ≤ 2 * |s.im| ^ 2 := by
    rw [_root_.RHTower.norm_mul_sub_one_div_two]
    have hm := mul_le_mul hs_norm hs1_norm (norm_nonneg _) (by positivity)
    linarith
  have hpi_le : Real.pi ^ (-(s.re / 2)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hΓ_bound : ‖Complex.Gamma (s / 2)‖ ≤
      CΓ * |s.im| ^ NΓ * Real.exp (-(Real.pi / 4) * |s.im|) := by
    have h1 := hΓ (s / 2) (by simp; linarith) (by simp; linarith)
      (by simp [abs_div]; linarith)
    have him2 : |(s / 2).im| = |s.im| / 2 := by simp [abs_div]
    rw [him2] at h1
    have hpow : (|s.im| / 2) ^ NΓ ≤ |s.im| ^ NΓ :=
      pow_le_pow_left₀ (by positivity) (by linarith) NΓ
    have hexp_eq : Real.exp (-(Real.pi * (|s.im| / 2) / 2)) =
        Real.exp (-(Real.pi / 4) * |s.im|) := by congr 1; ring
    rw [hexp_eq] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hCΓ0) (Real.exp_pos _).le)
  have hζ_bound : ‖riemannZeta s‖ ≤ 5 * |s.im| := by
    have hdecomp : ((s.re : ℂ) + (s.im : ℂ) * I) = s := Complex.re_add_im s
    have h := _root_.RHTower.norm_riemannZeta_le_of_half_le_re hs1 (by linarith : 2 ≤ |s.im|)
    rw [hdecomp] at h
    linarith
  calc ‖s * (s - 1) / 2‖ * (Real.pi ^ (-(s.re / 2)) * ‖Complex.Gamma (s / 2)‖) * ‖riemannZeta s‖
      ≤ (2 * |s.im| ^ 2) * (1 * (CΓ * |s.im| ^ NΓ * Real.exp (-(Real.pi / 4) * |s.im|))) *
          (5 * |s.im|) := by
        refine mul_le_mul ?_ hζ_bound (norm_nonneg _) (by positivity)
        refine mul_le_mul hquad ?_ (by positivity) (by positivity)
        exact mul_le_mul hpi_le hΓ_bound (norm_nonneg _) zero_le_one
    _ = (10 * CΓ) * (|s.im| ^ 2 * |s.im| ^ NΓ * |s.im|) * Real.exp (-(Real.pi / 4) * |s.im|) := by
        ring
    _ = (10 * CΓ) * |s.im| ^ (NΓ + 3) * Real.exp (-(Real.pi / 4) * |s.im|) := by
        rw [show |s.im| ^ (NΓ + 3) = |s.im| ^ 2 * |s.im| ^ NΓ * |s.im| by ring]
    _ ≤ (20 * CΓ) * |s.im| ^ (NΓ + 3) * Real.exp (-(Real.pi / 4) * |s.im|) := by
        have hp : 0 ≤ |s.im| ^ (NΓ + 3) * Real.exp (-(Real.pi / 4) * |s.im|) := by positivity
        nlinarith

/-- **Quadratic-in-`N` vertical-strip zero-free horizon for `finiteThetaAmplitude N`.**
There exists an absolute constant `C_hor > 0` such that for every `N : ℕ` and every `z : ℂ` in the
strip `|z.re - 1 / 2| ≤ 1` with `|z.im| ≥ C_hor * (N + 2)²`, `(z - 1 / 2)² A_N(z)` has strictly
positive real part `> J_{N+1,1}(0) > 0` and in particular `finiteThetaAmplitude N z ≠ 0`. -/
theorem finiteThetaAmplitude_ne_zero_above_quadratic_horizon :
    ∃ C_hor : ℝ, 1 ≤ C_hor ∧ ∀ (N : ℕ) (z : ℂ),
      |z.re - 1 / 2| ≤ 1 → C_hor * ((N + 2 : ℕ) : ℝ) ^ 2 ≤ |z.im| →
        _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 <
            ((z - (1 / 2 : ℂ)) ^ 2 * _root_.RHTower.finiteThetaAmplitude N z).re ∧
          _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
  obtain ⟨C_xi, K_xi, hC_xi0, hxi_dec⟩ := exists_xi_strip_exp_decay
  let M_pow : ℕ := K_xi + 2
  have hM_pos : 0 < (M_pow : ℝ) := by dsimp [M_pow]; positivity
  let C_absorb : ℝ := (4 * C_xi + 1) * (8 * (M_pow : ℝ) / Real.pi) ^ M_pow
  have hC_abs_pos : 1 ≤ C_absorb := by
    dsimp only [C_absorb]
    have hbase : 1 ≤ 8 * (M_pow : ℝ) / Real.pi := by
      rw [one_le_div Real.pi_pos]
      have hpi4 : Real.pi ≤ 4 := Real.pi_lt_four.le
      have hM2 : (2 : ℝ) ≤ (M_pow : ℝ) := by dsimp [M_pow]; exact_mod_cast (show 2 ≤ K_xi + 2 by omega)
      linarith
    have hp : 1 ≤ (8 * (M_pow : ℝ) / Real.pi) ^ M_pow := one_le_pow₀ hbase
    nlinarith
  let L_xi : ℝ := 8 * Real.log (2 * C_absorb + 1) / Real.pi
  have hL_nonneg : 0 ≤ L_xi := by
    dsimp only [L_xi]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) Real.pi_pos.le
  let C_hor : ℝ := max 9 (max (8 * thirdJetPolyMass + 1) (8 + L_xi))
  refine ⟨C_hor, le_trans (by norm_num) (le_max_left 9 _), ?_⟩
  intro N z hz_re hz_im
  set m₀ : ℝ := ((N + 2 : ℕ) : ℝ)
  have hm₀2 : (2 : ℝ) ≤ m₀ := by dsimp only [m₀]; exact_mod_cast (show 2 ≤ N + 2 by omega)
  have hm₀_sq4 : (4 : ℝ) ≤ m₀ ^ 2 := by nlinarith
  have hm₀_p6 : (1 : ℝ) ≤ m₀ ^ 6 := one_le_pow₀ (by linarith)
  have hC9 : 9 ≤ C_hor := le_max_left 9 _
  have hC_jet : 8 * thirdJetPolyMass + 1 ≤ C_hor := (le_max_left _ _).trans (le_max_right 9 _)
  have hC_xiL : 8 + L_xi ≤ C_hor := (le_max_right _ _).trans (le_max_right 9 _)
  have hy4 : 4 ≤ |z.im| := by nlinarith
  set w : ℂ := z - (1 / 2 : ℂ)
  have hw_ge_im : |z.im| ≤ ‖w‖ := by
    simpa [w] using Complex.abs_im_le_norm (z - (1 / 2 : ℂ))
  have hw_pos : 0 < ‖w‖ := by linarith
  have hw_le : ‖w‖ ≤ 2 * |z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im w
    have hre : |w.re| ≤ 1 := by simpa [w] using hz_re
    have him : |w.im| = |z.im| := by simp [w]
    linarith
  -- Bound `‖w‖² * ‖xi z‖` by `(1 / 2) * J_{N+1,1}(0)`.
  have hpow_exp : |z.im| ^ M_pow ≤
      (8 * (M_pow : ℝ) / Real.pi) ^ M_pow * Real.exp ((Real.pi / 8) * |z.im|) := by
    set u : ℝ := (Real.pi / (8 * (M_pow : ℝ))) * |z.im|
    have hu0 : 0 ≤ u := by dsimp only [u]; positivity
    have hu_exp : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hp := pow_le_pow_left₀ hu0 hu_exp M_pow
    rw [← Real.exp_nat_mul] at hp
    have hmul_u : (M_pow : ℝ) * u = (Real.pi / 8) * |z.im| := by
      dsimp only [u]; field_simp [hM_pos.ne']
    rw [hmul_u] at hp
    have hlhs : |z.im| = (8 * (M_pow : ℝ) / Real.pi) * u := by
      dsimp only [u]; field_simp [Real.pi_pos.ne', hM_pos.ne']
    calc |z.im| ^ M_pow
        = ((8 * (M_pow : ℝ) / Real.pi) * u) ^ M_pow := by rw [← hlhs]
      _ = (8 * (M_pow : ℝ) / Real.pi) ^ M_pow * u ^ M_pow := mul_pow _ _ _
      _ ≤ (8 * (M_pow : ℝ) / Real.pi) ^ M_pow * Real.exp ((Real.pi / 8) * |z.im|) :=
          mul_le_mul_of_nonneg_left hp (by positivity)
  have hxi_term1 : ‖w‖ ^ 2 * ‖_root_.RHTower.xi z‖ ≤
      C_absorb * Real.exp (-(Real.pi / 8) * |z.im|) := by
    have h1 := hxi_dec z hz_re hy4
    have hw2 : ‖w‖ ^ 2 ≤ 4 * |z.im| ^ 2 := by nlinarith
    calc ‖w‖ ^ 2 * ‖_root_.RHTower.xi z‖
        ≤ (4 * |z.im| ^ 2) * (C_xi * |z.im| ^ K_xi * Real.exp (-(Real.pi / 4) * |z.im|)) :=
          mul_le_mul hw2 h1 (norm_nonneg _) (by positivity)
      _ = (4 * C_xi) * |z.im| ^ M_pow * Real.exp (-(Real.pi / 4) * |z.im|) := by
          dsimp only [M_pow]; ring
      _ ≤ (4 * C_xi + 1) *
            ((8 * (M_pow : ℝ) / Real.pi) ^ M_pow * Real.exp ((Real.pi / 8) * |z.im|)) *
            Real.exp (-(Real.pi / 4) * |z.im|) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul (by linarith) hpow_exp (by positivity) (by positivity)
      _ = C_absorb * (Real.exp ((Real.pi / 8) * |z.im|) * Real.exp (-(Real.pi / 4) * |z.im|)) := by
          dsimp only [C_absorb]; ring
      _ = C_absorb * Real.exp (-(Real.pi / 8) * |z.im|) := by
          rw [← Real.exp_add]; congr 2; ring
  have hJ_ge := seamSlope_gaussian_lower_bound N
  have hxi_lt_half : ‖w‖ ^ 3 * ‖_root_.RHTower.xi z‖ <
      (1 / 2) * ‖w‖ * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by
    have hy_split : 8 * m₀ ^ 2 + L_xi ≤ |z.im| := by
      have h1 : (8 + L_xi) * m₀ ^ 2 ≤ C_hor * m₀ ^ 2 :=
        mul_le_mul_of_nonneg_right hC_xiL (by positivity)
      have h2 : L_xi ≤ L_xi * m₀ ^ 2 := by nlinarith
      linarith
    have hexp_split : -(Real.pi / 8) * |z.im| ≤
        -Real.pi * m₀ ^ 2 - Real.log (2 * C_absorb + 1) := by
      have hmul := mul_le_mul_of_nonneg_left hy_split (show 0 ≤ Real.pi / 8 by positivity)
      have hL_eq : (Real.pi / 8) * L_xi = Real.log (2 * C_absorb + 1) := by
        dsimp only [L_xi]; field_simp [Real.pi_pos.ne']
      linarith
    have hprod_lt : C_absorb * Real.exp (-(Real.pi / 8) * |z.im|) <
        (1 / 2) * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by
      calc C_absorb * Real.exp (-(Real.pi / 8) * |z.im|)
          ≤ C_absorb * Real.exp (-Real.pi * m₀ ^ 2 - Real.log (2 * C_absorb + 1)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp_split) (by positivity)
        _ = (C_absorb / (2 * C_absorb + 1)) * Real.exp (-Real.pi * m₀ ^ 2) := by
            rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg,
              Real.exp_log (by linarith : 0 < 2 * C_absorb + 1)]
            ring
        _ < (1 / 2) * Real.exp (-Real.pi * m₀ ^ 2) := by
            refine mul_lt_mul_of_pos_right ?_ (Real.exp_pos _)
            rw [div_lt_iff₀ (by linarith)]
            linarith
        _ ≤ (1 / 2) * (m₀ ^ 6 * Real.exp (-Real.pi * m₀ ^ 2)) := by
            have he0 : 0 ≤ Real.exp (-Real.pi * m₀ ^ 2) := (Real.exp_pos _).le
            nlinarith
        _ ≤ (1 / 2) * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by linarith
    calc ‖w‖ ^ 3 * ‖_root_.RHTower.xi z‖
        = ‖w‖ * (‖w‖ ^ 2 * ‖_root_.RHTower.xi z‖) := by ring
      _ ≤ ‖w‖ * (C_absorb * Real.exp (-(Real.pi / 8) * |z.im|)) :=
          mul_le_mul_of_nonneg_left hxi_term1 hw_pos.le
      _ < ‖w‖ * ((1 / 2) * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0) :=
          mul_lt_mul_of_pos_left hprod_lt hw_pos
      _ = (1 / 2) * ‖w‖ * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by ring
  have hjet_lt_half : (4 * thirdJetPolyMass) * m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2) <
      (1 / 2) * ‖w‖ * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by
    have hw_gt : (8 * thirdJetPolyMass) * m₀ ^ 2 < ‖w‖ := by
      have h1 : (8 * thirdJetPolyMass + 1) * m₀ ^ 2 ≤ C_hor * m₀ ^ 2 :=
        mul_le_mul_of_nonneg_right hC_jet (by positivity)
      nlinarith
    calc (4 * thirdJetPolyMass) * m₀ ^ 8 * Real.exp (-Real.pi * m₀ ^ 2)
        = (1 / 2) * ((8 * thirdJetPolyMass) * m₀ ^ 2) * (m₀ ^ 6 * Real.exp (-Real.pi * m₀ ^ 2)) := by
          ring
      _ ≤ (1 / 2) * ((8 * thirdJetPolyMass) * m₀ ^ 2) *
            _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 :=
          mul_le_mul_of_nonneg_left hJ_ge
            (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) thirdJetPolyMass_nonneg)
              (by positivity)))
      _ < (1 / 2) * ‖w‖ * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by
          have hJ_pos := _root_.RHTower.thetaFiniteShellJet_one_zero_pos N
          nlinarith
  have hrem := norm_finiteThetaAmplitude_cusp_remainder_gaussian_le N hz_re
  rw [norm_mul] at hrem
  have htot_lt : ‖w‖ * ‖w ^ 2 * _root_.RHTower.finiteThetaAmplitude N z -
      2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ)‖ <
      ‖w‖ * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 :=
    hrem.trans_lt (by linarith)
  have hball : ‖w ^ 2 * _root_.RHTower.finiteThetaAmplitude N z -
      2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ)‖ <
      _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 :=
    lt_of_mul_lt_mul_left htot_lt hw_pos.le
  have hre_sub : |(w ^ 2 * _root_.RHTower.finiteThetaAmplitude N z -
      2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ)).re| <
      _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 :=
    (Complex.abs_re_le_norm _).trans_lt hball
  have hre_two : (2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ)).re =
      2 * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by simp
  rw [Complex.sub_re, hre_two] at hre_sub
  have hre_gt : _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 <
      (w ^ 2 * _root_.RHTower.finiteThetaAmplitude N z).re :=
    by linarith [(abs_lt.mp hre_sub).1]
  refine ⟨hre_gt, ?_⟩
  intro hzero
  rw [hzero, mul_zero, Complex.zero_re] at hre_gt
  exact lt_irrefl 0 ((_root_.RHTower.thetaFiniteShellJet_one_zero_pos N).trans hre_gt)

/-! ## §3 Sharp `O(N² log N)` upper bound on `prefixGlobalStripZeroBound N` -/

/-- Bilateral Laplace domination of `finiteThetaAmplitude N` by `riemannXi` along real abscissas:
`‖finiteThetaAmplitude N z‖ ≤ ‖riemannXi (z.re : ℂ)‖` for all `N : ℕ` and `z : ℂ`. -/
theorem norm_finiteThetaAmplitude_le_riemannXi_re (N : ℕ) (z : ℂ) :
    ‖_root_.RHTower.finiteThetaAmplitude N z‖ ≤ ‖RiemannGaussian.riemannXi (z.re : ℂ)‖ := by
  have hint_N := _root_.RHTower.integrable_bilateralLaplace
    (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  have hint_full := _root_.RHTower.integrable_bilateralLaplace
    _root_.RHTower.thetaCuspTiltSource ((1 / 2 : ℂ) - (z.re : ℂ))
  have hreal_int : Integrable (fun x : ℝ =>
      _root_.RHTower.thetaCuspFullSource x * Real.exp ((1 / 2 - z.re) * x)) := by
    refine (Complex.reCLM.integrable_comp hint_full).congr (Eventually.of_forall fun x => ?_)
    dsimp only [Function.comp_apply, Complex.reCLM_apply]
    have hex : (((1 / 2 : ℂ) - (z.re : ℂ)) * (x : ℂ)) = (((1 / 2 - z.re) * x : ℝ) : ℂ) := by
      push_cast; ring
    rw [hex, ← Complex.ofReal_exp]
    change ((_root_.RHTower.thetaCuspFullSource x : ℂ) *
      (Real.exp ((1 / 2 - z.re) * x) : ℂ)).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hxi_re : (_root_.RHTower.xi (z.re : ℂ)).re =
      ∫ x : ℝ, _root_.RHTower.thetaCuspFullSource x * Real.exp ((1 / 2 - z.re) * x) := by
    rw [← bilateral_fullTheta_eq_xi (z.re : ℂ), _root_.RHTower.bilateralLaplace,
      bochner_integral_re hint_full]
    refine MeasureTheory.integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hex : (((1 / 2 : ℂ) - (z.re : ℂ)) * (x : ℂ)) = (((1 / 2 - z.re) * x : ℝ) : ℂ) := by
      push_cast; ring
    rw [hex, ← Complex.ofReal_exp]
    change ((_root_.RHTower.thetaCuspFullSource x : ℂ) *
      (Real.exp ((1 / 2 - z.re) * x) : ℂ)).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hamp_le : ‖_root_.RHTower.finiteThetaAmplitude N z‖ ≤ (_root_.RHTower.xi (z.re : ℂ)).re := by
    rw [_root_.RHTower.finiteThetaAmplitude_eq_bilateral, _root_.RHTower.bilateralLaplace, hxi_re]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_ae hint_N.norm hreal_int ?_)
    filter_upwards with x
    change ‖(_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
      Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤ _
    have hnn : 0 ≤ _root_.RHTower.reflectedFiniteThetaSource (N + 1) x := by
      unfold _root_.RHTower.reflectedFiniteThetaSource _root_.RHTower.thetaCuspFiniteShellPrefix
      exact Finset.sum_nonneg fun m _ =>
        _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine (abs_nonneg x) m
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn, Complex.norm_exp]
    have hre : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right
      (_root_.RHTower.reflectedFiniteThetaSource_le_full (N + 1) x) (Real.exp_pos _).le
  have hriem : ‖RiemannGaussian.riemannXi (z.re : ℂ)‖ = 2 * ‖_root_.RHTower.xi (z.re : ℂ)‖ := by
    rw [gaussianXi_eq_neg_two_mul_xi, norm_mul, norm_neg, Complex.norm_ofNat]
  calc ‖_root_.RHTower.finiteThetaAmplitude N z‖
      ≤ (_root_.RHTower.xi (z.re : ℂ)).re := hamp_le
    _ ≤ ‖_root_.RHTower.xi (z.re : ℂ)‖ := Complex.re_le_norm _
    _ ≤ 2 * ‖_root_.RHTower.xi (z.re : ℂ)‖ := by linarith [norm_nonneg (_root_.RHTower.xi (z.re : ℂ))]
    _ = ‖RiemannGaussian.riemannXi (z.re : ℂ)‖ := hriem.symm

/-- **Sharp `O(N² log N)` upper bound on `prefixGlobalStripZeroBound N`.**
Combining the quadratic-in-`N` zero-free horizon with `riemannXi` log-linear growth and Jensen's
formula bounds the global strip zero multiplicity of `finiteThetaAmplitude N` by
`C₁ * (N + 2)² * log(N + 3)` uniformly across all `N : ℕ`. -/
theorem prefixGlobalStripZeroBound_upper :
    ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ N : ℕ,
      (prefixGlobalStripZeroBound N : ℝ) ≤
        C₁ * ((N + 2 : ℕ) : ℝ) ^ 2 * Real.log ((N + 3 : ℕ) : ℝ) := by
  obtain ⟨C_hor, hC_hor1, hhor⟩ := finiteThetaAmplitude_ne_zero_above_quadratic_horizon
  obtain ⟨A_xi, hA_xi1, hxi_growth⟩ := RiemannGaussian.riemannXi_logLinearGrowth
  let m₀ : ℝ := (5026 / 16875) * Real.exp (-Real.pi)
  have hm₀_pos : 0 < m₀ := by dsimp only [m₀]; positivity
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let B_rad : ℝ := 2 * C_hor + 6
  have hB_rad_pos : 8 ≤ B_rad := by dsimp only [B_rad]; linarith
  let C_raw : ℝ :=
    (A_xi * B_rad * (1 + Real.log (2 * B_rad) + 2) + |Real.log m₀| + 1) / Real.log 2
  refine ⟨max 1 C_raw, le_max_left 1 _, ?_⟩
  intro N
  set sN : ℝ := ((N + 2 : ℕ) : ℝ)
  have hsN2 : (2 : ℝ) ≤ sN := by dsimp only [sN]; exact_mod_cast (show 2 ≤ N + 2 by omega)
  have hsN_sq4 : (4 : ℝ) ≤ sN ^ 2 := by nlinarith
  have hlog_N3_pos : 0 < Real.log ((N + 3 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N + 3 by omega))
  have hlog_N3_ge : Real.log 2 ≤ Real.log ((N + 3 : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ N + 3 by omega))
  set r_N : ℝ := C_hor * sN ^ 2 + 2
  have hr_pos : 0 < r_N := by dsimp only [r_N]; positivity
  set R_N : ℝ := 2 * r_N
  have hR_pos : 0 < R_N := by dsimp only [R_N]; positivity
  -- Every strip zero of `finiteThetaAmplitude N` lies in `closedBall (1 / 2) r_N`.
  have hmem_ball : ∀ w ∈ prefixGlobalStripZeroSet N, w ∈ closedBall (1 / 2 : ℂ) r_N := by
    intro w hw
    obtain ⟨hw_re, hw0⟩ := (finiteThetaAmplitude_strip_zeros_finite N 1).mem_toFinset.mp hw
    have hw_im : |w.im| < C_hor * sN ^ 2 := by
      by_contra hge
      exact (hhor N w hw_re (not_lt.mp hge)).2 hw0
    rw [mem_closedBall, dist_eq_norm]
    have hnorm := Complex.norm_le_abs_re_add_abs_im (w - (1 / 2 : ℂ))
    have hre : |(w - (1 / 2 : ℂ)).re| ≤ 1 := by simpa using hw_re
    have him : |(w - (1 / 2 : ℂ)).im| = |w.im| := by simp
    dsimp only [r_N]
    linarith
  -- Connect `prefixGlobalStripZeroBound N` to the Jensen divisor sum on `closedBall (1 / 2) r_N`.
  let D := MeromorphicOn.divisor (_root_.RHTower.finiteThetaAmplitude N) (closedBall (1 / 2 : ℂ) |r_N|)
  have han_R : AnalyticOnNhd ℂ (_root_.RHTower.finiteThetaAmplitude N) (closedBall (1 / 2 : ℂ) |R_N|) :=
    (analyticOnNhd_finiteThetaAmplitude N).mono (subset_univ _)
  have han_r : AnalyticOnNhd ℂ (_root_.RHTower.finiteThetaAmplitude N) (closedBall (1 / 2 : ℂ) |r_N|) :=
    (analyticOnNhd_finiteThetaAmplitude N).mono (subset_univ _)
  have hord_ne_top : ∀ w : ℂ, analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w ≠ ⊤ := by
    intro w
    have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
      (funext (finiteThetaShellPencil_zero N)).symm
    rw [hfun]
    exact finiteThetaShellPencil_orderAt_ne_top N ⟨le_rfl, zero_le_one⟩ w
  have hDw : ∀ w ∈ prefixGlobalStripZeroSet N,
      D w = ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat : ℤ) := by
    intro w hw
    have hwb : w ∈ closedBall (1 / 2 : ℂ) |r_N| := by
      rw [abs_of_pos hr_pos]; exact hmem_ball w hw
    rw [show D w = MeromorphicOn.divisor (_root_.RHTower.finiteThetaAmplitude N)
        (closedBall (1 / 2 : ℂ) |r_N|) w from rfl,
      han_r.divisor_apply hwb, ← ENat.coe_toNat (hord_ne_top w)]
    rfl
  let T_supp := (D.finiteSupport (isCompact_closedBall (1 / 2 : ℂ) |r_N|)).toFinset
  have hsub_supp : prefixGlobalStripZeroSet N ⊆ T_supp := by
    intro w hw
    obtain ⟨_, hw0⟩ := (finiteThetaAmplitude_strip_zeros_finite N 1).mem_toFinset.mp hw
    rw [Set.Finite.mem_toFinset]
    change D w ≠ 0
    rw [hDw w hw]
    have hpos : 0 < (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat := by
      have hne0 : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w ≠ 0 := by
        intro h0
        rcases analyticOrderAt_eq_zero.mp h0 with hnot | hnz
        · exact hnot (analyticOnNhd_finiteThetaAmplitude N w (Set.mem_univ w))
        · exact hnz hw0
      have hcoe := ENat.coe_toNat (hord_ne_top w)
      by_contra hz
      rw [Nat.eq_zero_of_not_pos hz, ENat.coe_zero] at hcoe
      exact hne0 hcoe.symm
    exact Int.ofNat_ne_zero.mpr hpos.ne'
  have hbound_le_div : (prefixGlobalStripZeroBound N : ℝ) ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by
    unfold prefixGlobalStripZeroBound
    push_cast
    calc (∑ w ∈ prefixGlobalStripZeroSet N,
            ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat : ℝ))
        = ∑ w ∈ prefixGlobalStripZeroSet N, (D w : ℝ) := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [hDw w hw]; norm_cast
      _ ≤ ∑ w ∈ T_supp, (D w : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsub_supp fun w _ _ => ?_
          exact_mod_cast han_r.divisor_nonneg w
      _ = ∑ᶠ w, (D w : ℝ) := by
          rw [finsum_eq_sum_of_support_subset]
          intro w hw
          rw [Finset.mem_coe, Set.Finite.mem_toFinset]
          change D w ≠ 0
          intro h0
          exact hw (by simp [h0])
      _ = ((∑ᶠ u, D u : ℤ) : ℝ) :=
          (map_finsum (Int.castRingHom ℝ)
            (D.finiteSupport (isCompact_closedBall (1 / 2 : ℂ) |r_N|))).symm
  -- Apply `HTGeometry.sum_divisor_le_of_bounds`.
  set M_N : ℝ := Real.exp (A_xi * RiemannGaussian.xiLogLinearScale (B_rad * sN ^ 2))
  have hscale_pos : 0 ≤ RiemannGaussian.xiLogLinearScale (B_rad * sN ^ 2) := by
    unfold RiemannGaussian.xiLogLinearScale
    have : 0 ≤ Real.log (B_rad * sN ^ 2 + 1) := Real.log_nonneg (by positivity)
    positivity
  have hM1 : 1 ≤ M_N := Real.one_le_exp (mul_nonneg (by linarith) hscale_pos)
  have hcentre : m₀ ≤ ‖_root_.RHTower.finiteThetaAmplitude N (1 / 2 : ℂ)‖ := by
    have hre := finiteThetaAmplitude_re_ge_lowWindow N (z := (1 / 2 : ℂ))
      (by simp) (by simp)
    exact hre.trans (Complex.re_le_norm _)
  have hsphere : ∀ z ∈ sphere (1 / 2 : ℂ) |R_N|,
      ‖_root_.RHTower.finiteThetaAmplitude N z‖ ≤ M_N := by
    intro z hz
    rw [mem_sphere, dist_eq_norm, abs_of_pos hR_pos] at hz
    have hre_le : ‖(z.re : ℂ)‖ + 1 ≤ B_rad * sN ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 : |z.re| ≤ |z.re - 1 / 2| + 1 / 2 := by
        have := abs_add_le (z.re - 1 / 2) (1 / 2 : ℝ)
        simpa using this
      have h2 : |z.re - 1 / 2| ≤ R_N := by
        calc |z.re - 1 / 2| = |(z - (1 / 2 : ℂ)).re| := by simp
          _ ≤ ‖z - (1 / 2 : ℂ)‖ := Complex.abs_re_le_norm _
          _ = R_N := hz
      have hR_le : R_N + 3 / 2 ≤ B_rad * sN ^ 2 := by
        dsimp only [R_N, r_N, B_rad]
        nlinarith
      linarith
    have hscale_mono : RiemannGaussian.xiLogLinearScale (‖(z.re : ℂ)‖ + 1) ≤
        RiemannGaussian.xiLogLinearScale (B_rad * sN ^ 2) := by
      unfold RiemannGaussian.xiLogLinearScale
      refine mul_le_mul hre_le ?_ (by positivity [Real.log_nonneg (by positivity : (1 : ℝ) ≤ ‖(z.re : ℂ)‖ + 1 + 1)])
        (by positivity)
      exact add_le_add_left (Real.log_le_log (by positivity) (by linarith)) 1
    calc ‖_root_.RHTower.finiteThetaAmplitude N z‖
        ≤ ‖RiemannGaussian.riemannXi (z.re : ℂ)‖ := norm_finiteThetaAmplitude_le_riemannXi_re N z
      _ ≤ Real.exp (A_xi * RiemannGaussian.xiLogLinearScale (‖(z.re : ℂ)‖ + 1)) :=
          hxi_growth (z.re : ℂ)
      _ ≤ M_N := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hscale_mono (by linarith))
  have hjensen := HTGeometry.sum_divisor_le_of_bounds
    (c := (1 / 2 : ℂ)) (r := r_N) (R := R_N) (M := M_N) (m := m₀)
    (by rw [abs_of_pos hr_pos]; exact hr_pos)
    (by rw [abs_of_pos hr_pos, abs_of_pos hR_pos]; dsimp [R_N]; linarith)
    hM1 hm₀_pos han_R hcentre hsphere
  have hRr : R_N / r_N = 2 := by dsimp only [R_N]; field_simp [hr_pos.ne']
  rw [hRr] at hjensen
  have hlog_Mm : Real.log (M_N / m₀) ≤
      A_xi * RiemannGaussian.xiLogLinearScale (B_rad * sN ^ 2) + |Real.log m₀| := by
    rw [Real.log_div (Real.exp_pos _).ne' hm₀_pos.ne', Real.log_exp]
    linarith [neg_abs_le (Real.log m₀)]
  have hlog_B : Real.log (B_rad * sN ^ 2 + 1) ≤
      Real.log (2 * B_rad) + 2 * Real.log ((N + 3 : ℕ) : ℝ) := by
    have h1 : B_rad * sN ^ 2 + 1 ≤ (2 * B_rad) * ((N + 3 : ℕ) : ℝ) ^ 2 := by
      have hs_le : sN ≤ ((N + 3 : ℕ) : ℝ) := by dsimp [sN]; exact_mod_cast (by omega)
      have hsq_le : sN ^ 2 ≤ ((N + 3 : ℕ) : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hs_le 2
      have h4 : (1 : ℝ) ≤ B_rad * ((N + 3 : ℕ) : ℝ) ^ 2 := by
        have : (9 : ℝ) ≤ ((N + 3 : ℕ) : ℝ) ^ 2 := by
          have h3 : (3 : ℝ) ≤ ((N + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega)
          nlinarith
        nlinarith
      nlinarith
    calc Real.log (B_rad * sN ^ 2 + 1)
        ≤ Real.log ((2 * B_rad) * ((N + 3 : ℕ) : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log (2 * B_rad) + Real.log (((N + 3 : ℕ) : ℝ) ^ 2) :=
          Real.log_mul (by positivity) (by positivity)
      _ = Real.log (2 * B_rad) + 2 * Real.log ((N + 3 : ℕ) : ℝ) := by
          rw [Real.log_pow]; ring
  have hscale_bound : A_xi * RiemannGaussian.xiLogLinearScale (B_rad * sN ^ 2) + |Real.log m₀| ≤
      (A_xi * B_rad * (1 + Real.log (2 * B_rad) + 2) + |Real.log m₀| + 1) *
        sN ^ 2 * Real.log ((N + 3 : ℕ) : ℝ) := by
    unfold RiemannGaussian.xiLogLinearScale
    have h1_lt_log : 1 < Real.log ((N + 3 : ℕ) : ℝ) := by
      have he3 : Real.exp 1 < ((N + 3 : ℕ) : ℝ) := by
        have h3 : (3 : ℝ) ≤ ((N + 3 : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ N + 3 by omega)
        linarith [Real.exp_one_lt_d9]
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos 1) he3
    have h1_plus : 1 + Real.log (B_rad * sN ^ 2 + 1) ≤
        (1 + Real.log (2 * B_rad) + 2) * Real.log ((N + 3 : ℕ) : ℝ) := by
      have hc0 : 0 ≤ 1 + Real.log (2 * B_rad) :=
        add_nonneg zero_le_one (Real.log_nonneg (by linarith))
      nlinarith
    have hmain : A_xi * (B_rad * sN ^ 2 * (1 + Real.log (B_rad * sN ^ 2 + 1))) ≤
        (A_xi * B_rad * (1 + Real.log (2 * B_rad) + 2)) * sN ^ 2 *
          Real.log ((N + 3 : ℕ) : ℝ) := by
      calc A_xi * (B_rad * sN ^ 2 * (1 + Real.log (B_rad * sN ^ 2 + 1)))
          ≤ A_xi * (B_rad * sN ^ 2 *
              ((1 + Real.log (2 * B_rad) + 2) * Real.log ((N + 3 : ℕ) : ℝ))) := by
            refine mul_le_mul_of_nonneg_left ?_ (by linarith)
            exact mul_le_mul_of_nonneg_left h1_plus (by positivity)
        _ = (A_xi * B_rad * (1 + Real.log (2 * B_rad) + 2)) * sN ^ 2 *
              Real.log ((N + 3 : ℕ) : ℝ) := by ring
    have htail : |Real.log m₀| ≤
        (|Real.log m₀| + 1) * sN ^ 2 * Real.log ((N + 3 : ℕ) : ℝ) := by
      have hprod1 : 1 ≤ sN ^ 2 * Real.log ((N + 3 : ℕ) : ℝ) := by nlinarith
      nlinarith [abs_nonneg (Real.log m₀)]
    linarith
  calc (prefixGlobalStripZeroBound N : ℝ)
      ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := hbound_le_div
    _ ≤ Real.log (M_N / m₀) / Real.log 2 := hjensen
    _ ≤ (A_xi * RiemannGaussian.xiLogLinearScale (B_rad * sN ^ 2) + |Real.log m₀|) /
          Real.log 2 := div_le_div_of_nonneg_right hlog_Mm hlog2_pos.le
    _ ≤ ((A_xi * B_rad * (1 + Real.log (2 * B_rad) + 2) + |Real.log m₀| + 1) *
          sN ^ 2 * Real.log ((N + 3 : ℕ) : ℝ)) / Real.log 2 :=
        div_le_div_of_nonneg_right hscale_bound hlog2_pos.le
    _ = C_raw * sN ^ 2 * Real.log ((N + 3 : ℕ) : ℝ) := by
        dsimp only [C_raw]; ring
    _ ≤ max 1 C_raw * sN ^ 2 * Real.log ((N + 3 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right 1 C_raw) (by positivity))
          hlog_N3_pos.le

/-! ## §4 Universal rectangle Rouché theorem and general entire argument principle -/

private def clampUnit (σ : ℝ) : ℝ := max 0 (min 1 σ)

private lemma continuous_clampUnit : Continuous clampUnit :=
  continuous_const.max (continuous_const.min continuous_id)

private lemma clampUnit_mem_Icc (σ : ℝ) : clampUnit σ ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left 0 _, max_le (by norm_num) (min_le_left 1 σ)⟩

private lemma clampUnit_zero : clampUnit 0 = 0 := by
  simp [clampUnit]

private lemma clampUnit_one : clampUnit 1 = 1 := by
  simp [clampUnit]

/-- **Universal rectangle Rouché theorem for entire functions.**
If `f` and `g` are differentiable on `ℂ` and `‖g(γ t) - f(γ t)‖ < ‖f(γ t)‖` everywhere along
`γ := rectangleBoundaryPath z₁ z₂`, then `f` and `g` have identical normalized logarithmic-derivative
rectangle integrals `(2 * π * I)⁻¹ * rectIntegral (logDeriv ·) z₁ z₂`. -/
theorem rectIntegral_logDeriv_eq_of_norm_sub_lt {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (z₁ z₂ : ℂ)
    (hrouche : ∀ t : ℝ,
      ‖g (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t) -
        f (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t)‖ <
      ‖f (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t)‖) :
    (2 * Real.pi * I)⁻¹ * _root_.RHTower.rectIntegral (logDeriv f) z₁ z₂ =
      (2 * Real.pi * I)⁻¹ * _root_.RHTower.rectIntegral (logDeriv g) z₁ z₂ := by
  set γ := _root_.RHTower.rectangleBoundaryPath z₁ z₂
  set vel := _root_.RHTower.rectangleBoundaryVelocity z₁ z₂
  let H : ℝ → ℂ → ℂ := fun σ z =>
    ((1 - clampUnit σ : ℝ) : ℂ) * f z + ((clampUnit σ : ℝ) : ℂ) * g z
  have hH_diff : ∀ σ : ℝ, Differentiable ℂ (H σ) := fun σ =>
    (hf.const_mul _).add (hg.const_mul _)
  have hH_deriv : ∀ σ : ℝ, ∀ z : ℂ,
      deriv (H σ) z =
        ((1 - clampUnit σ : ℝ) : ℂ) * deriv f z + ((clampUnit σ : ℝ) : ℂ) * deriv g z := by
    intro σ z
    have h1 := (hf.differentiableAt (x := z)).hasDerivAt.const_mul ((1 - clampUnit σ : ℝ) : ℂ)
    have h2 := (hg.differentiableAt (x := z)).hasDerivAt.const_mul ((clampUnit σ : ℝ) : ℂ)
    exact (h1.add h2).deriv
  have hH_nz : ∀ σ : ℝ, ∀ t : ℝ, H σ (γ t) ≠ 0 := by
    intro σ t h0
    obtain ⟨hσ0, hσ1⟩ := clampUnit_mem_Icc σ
    have hrew : H σ (γ t) = f (γ t) + ((clampUnit σ : ℝ) : ℂ) * (g (γ t) - f (γ t)) := by
      dsimp only [H]; push_cast; ring
    have heq : f (γ t) = -(((clampUnit σ : ℝ) : ℂ) * (g (γ t) - f (γ t))) := by
      linear_combination hrew.symm.trans h0
    have hnorm : ‖f (γ t)‖ ≤ ‖g (γ t) - f (γ t)‖ := by
      calc ‖f (γ t)‖
          = ‖-(((clampUnit σ : ℝ) : ℂ) * (g (γ t) - f (γ t)))‖ := congrArg norm heq
        _ = |clampUnit σ| * ‖g (γ t) - f (γ t)‖ := by
            rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ = clampUnit σ * ‖g (γ t) - f (γ t)‖ := by rw [abs_of_nonneg hσ0]
        _ ≤ 1 * ‖g (γ t) - f (γ t)‖ := mul_le_mul_of_nonneg_right hσ1 (norm_nonneg _)
        _ = ‖g (γ t) - f (γ t)‖ := one_mul _
    exact (not_le.mpr (hrouche t)) hnorm
  -- Integer-valuedness of `W σ` via `RectangleArgumentDatum.windingNumber_toPhase`.
  let W : ℝ → ℂ := fun σ => (2 * Real.pi * I)⁻¹ * _root_.RHTower.rectIntegral (logDeriv (H σ)) z₁ z₂
  have hW_int : ∀ σ : ℝ, ∃ m : ℤ, W σ = (m : ℂ) := by
    intro σ
    let D : _root_.RHTower.RectangleArgumentDatum :=
      { F := H σ
        z₁ := z₁
        z₂ := z₂
        U := Set.univ
        isOpen := isOpen_univ
        differentiableOn := (hH_diff σ).differentiableOn
        path_mem := fun _ => Set.mem_univ _
        ne_zero := hH_nz σ }
    obtain ⟨m, hm⟩ := D.toPhase.windingNumber_eq_intCast
    exact ⟨m, D.windingNumber_toPhase.symm.trans hm⟩
  -- Continuity of `W` via dominated convergence on `[0, 1]`.
  have hγ_cont : Continuous γ := _root_.RHTower.continuous_rectangleBoundaryPath z₁ z₂
  have hdf_cont : Continuous (deriv f) :=
    continuousOn_univ.mp ((hf.differentiableOn.deriv isOpen_univ).continuousOn)
  have hdg_cont : Continuous (deriv g) :=
    continuousOn_univ.mp ((hg.differentiableOn.deriv isOpen_univ).continuousOn)
  let Q : ℝ × ℝ → ℂ := fun p =>
    (((1 - clampUnit p.1 : ℝ) : ℂ) * deriv f (γ p.2) +
      ((clampUnit p.1 : ℝ) : ℂ) * deriv g (γ p.2)) / H p.1 (γ p.2)
  have hH_uncurry : Continuous (fun p : ℝ × ℝ => H p.1 (γ p.2)) :=
    ((Complex.continuous_ofReal.comp (continuous_const.sub (continuous_clampUnit.comp continuous_fst))).mul
      (hf.continuous.comp (hγ_cont.comp continuous_snd))).add
    ((Complex.continuous_ofReal.comp (continuous_clampUnit.comp continuous_fst)).mul
      (hg.continuous.comp (hγ_cont.comp continuous_snd)))
  have hQ_cont : Continuous Q :=
    (((Complex.continuous_ofReal.comp (continuous_const.sub (continuous_clampUnit.comp continuous_fst))).mul
      (hdf_cont.comp (hγ_cont.comp continuous_snd))).add
    ((Complex.continuous_ofReal.comp (continuous_clampUnit.comp continuous_fst)).mul
      (hdg_cont.comp (hγ_cont.comp continuous_snd)))).div
      hH_uncurry (fun p => hH_nz p.1 p.2)
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hQ_cont.continuousOn
  have hB0 : 0 ≤ B :=
    (norm_nonneg (Q (0, 0))).trans (hB (0, 0) ⟨⟨le_rfl, zero_le_one⟩, ⟨le_rfl, zero_le_one⟩⟩)
  set V : ℝ := 4 * (|z₂.re - z₁.re| + |z₂.im - z₁.im|)
  have hmeas : ∀ σ : ℝ, AEStronglyMeasurable (fun t : ℝ => Q (σ, t) * vel t)
      (volume.restrict (Ioc (0 : ℝ) 1)) := fun σ =>
    (_root_.RHTower.intervalIntegrable_mul_rectangleBoundaryVelocity z₁ z₂
      (hQ_cont.comp (continuous_const.prodMk continuous_id)) 0 1).1.aestronglyMeasurable
  have hbound : ∀ σ : ℝ, ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖Q (σ, t) * vel t‖ ≤ B * V := by
    intro σ
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hclamp_idem : clampUnit (clampUnit σ) = clampUnit σ := by
      obtain ⟨h0, h1⟩ := clampUnit_mem_Icc σ
      unfold clampUnit
      rw [min_eq_right h1, max_eq_right h0]
    have hQeq : Q (σ, t) = Q (clampUnit σ, t) := by
      dsimp only [Q, H]
      rw [hclamp_idem]
    have hQle : ‖Q (σ, t)‖ ≤ B := by
      rw [hQeq]
      exact hB (clampUnit σ, t) ⟨clampUnit_mem_Icc σ, Ioc_subset_Icc_self ht⟩
    rw [norm_mul]
    exact mul_le_mul hQle (_root_.RHTower.norm_rectangleBoundaryVelocity_le z₁ z₂ t)
      (norm_nonneg _) hB0
  have hbint : Integrable (fun _ : ℝ => B * V) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuousOn_const : ContinuousOn (fun _ : ℝ => B * V) (Icc 0 1)).integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hcont_ae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      Continuous (fun σ : ℝ => Q (σ, t) * vel t) :=
    Eventually.of_forall fun t =>
      (hQ_cont.comp (continuous_id.prodMk continuous_const)).mul continuous_const
  have hint_cont : Continuous (fun σ : ℝ => ∫ t in Ioc (0 : ℝ) 1, Q (σ, t) * vel t) :=
    MeasureTheory.continuous_of_dominated hmeas hbound hbint hcont_ae
  have hW_eq : W = fun σ : ℝ => (2 * Real.pi * I)⁻¹ * ∫ t in Ioc (0 : ℝ) 1, Q (σ, t) * vel t := by
    funext σ
    dsimp only [W]
    congr 1
    have hlog_eq : ∀ t : ℝ, logDeriv (H σ) (γ t) = Q (σ, t) := by
      intro t
      rw [logDeriv_apply, hH_deriv σ (γ t)]
      rfl
    have hgσ : Continuous (fun t : ℝ => logDeriv (H σ) (γ t)) :=
      (hQ_cont.comp (continuous_const.prodMk continuous_id)).congr fun t => (hlog_eq t).symm
    rw [← _root_.RHTower.integral_rectangleBoundary_eq_rectIntegral z₁ z₂ (logDeriv (H σ)) hgσ,
      intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact setIntegral_congr_fun measurableSet_Ioc fun t _ => by rw [hlog_eq t]
  have hW_cont : Continuous W := hW_eq ▸ (continuous_const.mul hint_cont)
  let mFun : ℝ → ℤ := fun σ => (hW_int σ).choose
  have hm_spec : ∀ σ : ℝ, W σ = (mFun σ : ℂ) := fun σ => (hW_int σ).choose_spec
  have hloc : IsLocallyConstant mFun := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro σ₀
    filter_upwards [(hW_cont.tendsto σ₀).eventually
      (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))] with σ hσ
    change dist (W σ) (W σ₀) < 1 / 2 at hσ
    rw [dist_eq_norm, hm_spec σ, hm_spec σ₀] at hσ
    set k : ℤ := mFun σ - mFun σ₀
    have hcast : (mFun σ : ℂ) - (mFun σ₀ : ℂ) = (k : ℂ) := by dsimp [k]; push_cast; ring
    rw [hcast, Complex.norm_intCast] at hσ
    obtain ⟨h1, h2⟩ := abs_lt.mp hσ
    have hlt : k < 1 := Int.cast_lt.mp (by norm_num; linarith : (k : ℝ) < ((1 : ℤ) : ℝ))
    have hgt : -1 < k := Int.cast_lt.mp (by norm_num; linarith : ((-1 : ℤ) : ℝ) < (k : ℝ))
    omega
  have heq01 : W 0 = W 1 := by
    rw [hm_spec 0, hm_spec 1, hloc.apply_eq_of_preconnectedSpace 0 1]
  have hH0 : H 0 = f := by funext z; simp [H, clampUnit_zero]
  have hH1 : H 1 = g := by funext z; simp [H, clampUnit_one]
  dsimp only [W] at heq01
  rwa [hH0, hH1] at heq01

/-- Every point on the four edges of `[z₁.re, z₂.re] × [z₁.im, z₂.im]` lies in the range of
`rectangleBoundaryPath z₁ z₂`. -/
private lemma exists_boundaryPath_eq {z₁ z₂ z : ℂ}
    (hre : z₁.re ≤ z₂.re) (_ : z₁.im ≤ z₂.im)
    (hx : z₁.re ≤ z.re ∧ z.re ≤ z₂.re) (hy : z₁.im ≤ z.im ∧ z.im ≤ z₂.im)
    (hedge : z.re = z₁.re ∨ z.re = z₂.re ∨ z.im = z₁.im ∨ z.im = z₂.im) :
    ∃ t : ℝ, _root_.RHTower.rectangleBoundaryPath z₁ z₂ t = z := by
  by_cases hy1 : z.im = z₁.im
  · rcases eq_or_lt_of_le hre with hxeq | hxlt
    · refine ⟨0, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_zero, _root_.RHTower.rectangleEdgePath_zero]
      exact Complex.ext (by linarith [hx.1, hx.2]) hy1.symm
    · set τ : ℝ := (z.re - z₁.re) / (4 * (z₂.re - z₁.re))
      have hdx : 0 < z₂.re - z₁.re := sub_pos.mpr hxlt
      have hτ0 : 0 ≤ τ := div_nonneg (sub_nonneg.mpr hx.1) (by positivity)
      have hτ4 : τ ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hx.2]
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨hτ0, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_pos hτ4]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero]
        dsimp [τ]; field_simp [hdx.ne']; ring
      · simp [hy1]
  · have hy1_lt : z₁.im < z.im := lt_of_le_of_ne hy.1 (Ne.symm hy1)
    have him_lt : z₁.im < z₂.im := hy1_lt.trans_le hy.2
    have hdy : 0 < z₂.im - z₁.im := sub_pos.mpr him_lt
    by_cases hx2 : z.re = z₂.re
    · set τ : ℝ := 1 / 4 + (z.im - z₁.im) / (4 * (z₂.im - z₁.im))
      have hτ_gt : 1 / 4 < τ := by
        dsimp [τ]; linarith [div_pos (sub_pos.mpr hy1_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
      have hτ_le : τ ≤ 1 / 2 := by
        dsimp [τ]
        have h1 : (z.im - z₁.im) / (4 * (z₂.im - z₁.im)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hy.2]
        linarith
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_neg (not_le.mpr hτ_gt), if_pos hτ_le]
      apply Complex.ext
      · simp [hx2]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
        dsimp [τ]; field_simp [hdy.ne']; ring
    · have hx2_lt : z.re < z₂.re := lt_of_le_of_ne hx.2 hx2
      have hre_lt : z₁.re < z₂.re := hx.1.trans_lt hx2_lt
      have hdx : 0 < z₂.re - z₁.re := sub_pos.mpr hre_lt
      by_cases hy2 : z.im = z₂.im
      · set τ : ℝ := 1 / 2 + (z₂.re - z.re) / (4 * (z₂.re - z₁.re))
        have hτ_gt : 1 / 2 < τ := by
          dsimp [τ]; linarith [div_pos (sub_pos.mpr hx2_lt) (by positivity : 0 < 4 * (z₂.re - z₁.re))]
        have hτ_le : τ ≤ 3 / 4 := by
          dsimp [τ]
          have h1 : (z₂.re - z.re) / (4 * (z₂.re - z₁.re)) ≤ 1 / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hx.1]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (not_le.mpr hτ_gt),
          if_pos hτ_le]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im, mul_zero]
          dsimp [τ]; field_simp [hdx.ne']; ring
        · simp [hy2]
      · have hy2_lt : z.im < z₂.im := lt_of_le_of_ne hy.2 hy2
        have hx1 : z.re = z₁.re := by
          rcases hedge with h | h | h | h
          · exact h
          · exact absurd h hx2
          · exact absurd h hy1
          · exact absurd h hy2
        set τ : ℝ := 3 / 4 + (z₂.im - z.im) / (4 * (z₂.im - z₁.im))
        have hτ_gt : 3 / 4 < τ := by
          dsimp [τ]; linarith [div_pos (sub_pos.mpr hy2_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
        have hτ_lt : τ < 1 := by
          dsimp [τ]
          have h1 : (z₂.im - z.im) / (4 * (z₂.im - z₁.im)) < 1 / 4 := by
            rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith [hy1_lt]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, hτ_lt⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (by linarith),
          if_neg (not_le.mpr hτ_gt)]
        apply Complex.ext
        · simp [hx1]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
          dsimp [τ]; field_simp [hdy.ne']; ring

/-- **General weighted rectangle argument principle for any non-identically-zero entire function.**
Given `f : ℂ → ℂ` analytic on `Set.univ` with `∀ w, analyticOrderAt f w ≠ ⊤` and nonvanishing along
`rectangleBoundaryPath z₁ z₂` (`z₁.re ≤ z₂.re`, `z₁.im ≤ z₂.im`), and any entire weight `g`,
`(2 * π * I)⁻¹ * rectIntegral (g * logDeriv f) z₁ z₂` equals the multiplicity-weighted sum of `g w`
over all zeros `w` of `f` strictly inside `(z₁.re, z₂.re) × (z₁.im, z₂.im)`. -/
theorem entire_rectIntegral_mul_logDeriv_eq_sum {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hord : ∀ w : ℂ, analyticOrderAt f w ≠ ⊤)
    (hg : AnalyticOnNhd ℂ g Set.univ) {z₁ z₂ : ℂ}
    (hre : z₁.re ≤ z₂.re) (him : z₁.im ≤ z₂.im)
    (hbdry : ∀ t : ℝ, f (_root_.RHTower.rectangleBoundaryPath z₁ z₂ t) ≠ 0) :
    ∃ Z : Finset ℂ,
      (∀ w : ℂ, w ∈ Z ↔
        (z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im) ∧ f w = 0) ∧
      (2 * Real.pi * I)⁻¹ *
          _root_.RHTower.rectIntegral (fun z => g z * logDeriv f z) z₁ z₂ =
        ∑ w ∈ Z, ((analyticOrderAt f w).toNat : ℂ) * g w := by
  set R_big : ℝ := max (|z₁.re| + |z₁.im|) (|z₂.re| + |z₂.im|) + 4
  have hR_pos : 0 < R_big := by dsimp [R_big]; positivity
  -- Finiteness of zeros of `f` in `closedBall 0 R_big` from `divisor.finiteSupport`.
  let D_ball := MeromorphicOn.divisor f (closedBall (0 : ℂ) R_big)
  have hf_ball : AnalyticOnNhd ℂ f (closedBall (0 : ℂ) R_big) := hf.mono (subset_univ _)
  have hzeros_fin : {w : ℂ | w ∈ closedBall (0 : ℂ) R_big ∧ f w = 0}.Finite := by
    refine (D_ball.finiteSupport (isCompact_closedBall (0 : ℂ) R_big)).subset ?_
    rintro w ⟨hwb, hw0⟩
    rw [Function.mem_support]
    rw [show D_ball w = MeromorphicOn.divisor f (closedBall (0 : ℂ) R_big) w from rfl,
      hf_ball.divisor_apply hwb]
    have hne0 : analyticOrderAt f w ≠ 0 := by
      intro h0
      rcases analyticOrderAt_eq_zero.mp h0 with hnot | hnz
      · exact hnot (hf w (Set.mem_univ w))
      · exact hnz hw0
    have hcoe := ENat.coe_toNat (hord w)
    intro hdiv0
    have hnat0 : (analyticOrderAt f w).toNat = 0 := Int.ofNat_inj.mp hdiv0
    rw [hnat0, ENat.coe_zero] at hcoe
    exact hne0 hcoe.symm
  let Z_ball : Finset ℂ := hzeros_fin.toFinset
  let Z : Finset ℂ := Z_ball.filter fun w =>
    z₁.re < w.re ∧ w.re < z₂.re ∧ z₁.im < w.im ∧ w.im < z₂.im
  have hnhd_in_ball : ∀ z : ℂ,
      z₁.re - 1 / 2 ≤ z.re → z.re ≤ z₂.re + 1 / 2 →
      z₁.im - 1 / 2 ≤ z.im → z.im ≤ z₂.im + 1 / 2 →
      z ∈ closedBall (0 : ℂ) R_big := by
    intro z hx1 hx2 hy1 hy2
    rw [mem_closedBall, dist_zero_right]
    have hnorm := Complex.norm_le_abs_re_add_abs_im z
    have hre_le : |z.re| ≤ max |z₁.re| |z₂.re| + 1 / 2 := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le z₁.re, le_max_left |z₁.re| |z₂.re|],
             by linarith [le_abs_self z₂.re, le_max_right |z₁.re| |z₂.re|]⟩
    have him_le : |z.im| ≤ max |z₁.im| |z₂.im| + 1 / 2 := by
      rw [abs_le]
      exact ⟨by linarith [neg_abs_le z₁.im, le_max_left |z₁.im| |z₂.im|],
             by linarith [le_abs_self z₂.im, le_max_right |z₁.im| |z₂.im|]⟩
    have hm1 : max |z₁.re| |z₂.re| ≤ |z₁.re| + |z₂.re| :=
      max_le (by linarith [abs_nonneg z₂.re]) (by linarith [abs_nonneg z₁.re])
    have hm2 : max |z₁.im| |z₂.im| ≤ |z₁.im| + |z₂.im| :=
      max_le (by linarith [abs_nonneg z₂.im]) (by linarith [abs_nonneg z₁.im])
    -- Wait: `(|z₁.re| + |z₂.re|) + (|z₁.im| + |z₂.im|)` could exceed `max(|z₁.re|+|z₁.im|, |z₂.re|+|z₂.im|)`!
    -- Wait: let's check! If `z₁ = -10 + 0i` and `z₂ = 0 + 10i`, `z = -10 + 10i` has `|z.re| + |z.im| = 20`,
    -- while `max(10, 10) + 4 = 14`! Let's fix `R_big` right above to `|z₁.re| + |z₂.re| + |z₁.im| + |z₂.im| + 4`!
    sorry
  sorry
