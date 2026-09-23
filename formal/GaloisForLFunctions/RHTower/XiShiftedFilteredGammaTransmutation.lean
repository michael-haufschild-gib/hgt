import GaloisForLFunctions.RHTower.XiShiftedHankelHeatResolventBridge
import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion

/-!
# Exact polynomial-filtered Gamma transmutation for shifted Xi Hankel forms

This module formalizes the load-bearing identity behind the parabolic Route U horizon.  Given
`p(X) = ∑ᵢ cᵢ Xⁱ`, the shifted reversal

`Q(W) = ∑ᵢ cᵢ (W + y)^(d-i)`

is inserted into the Xi heat trace before Gamma averaging.  Its powers cancel exactly against
the shifted resolvent denominator, so the Gamma integral is the original shifted reciprocal
Hankel quadratic.  Absolute convergence and integral--divisor interchange are proved from the
literal Xi divisor; no sign hypothesis and no RH premise enter.

This is stronger than the unfiltered heat--resolvent bridge: filtering and averaging are performed
in the mathematically required order rather than replaced by an indefinite divided-factorial
carrier.
-/

open Complex Polynomial MeasureTheory Set
open scoped BigOperators

namespace RHTower
noncomputable section

private lemma pow_mul_inv_pow_eq_pow_sub {a : ℂ} (ha : a ≠ 0)
    {i d : ℕ} (hi : i ≤ d) :
    a ^ d * (a⁻¹) ^ i = a ^ (d - i) := by
  rw [inv_pow]
  rw [← div_eq_mul_inv, div_eq_mul_inv, ← pow_sub₀ a ha hi]

private lemma filtered_power_cancel {a v : ℂ} (ha : a ≠ 0) (M d : ℕ) :
    (a ^ d * v) ^ (2 : ℕ) * (a⁻¹) ^ (2 * M + 2 * d + 1) =
      a⁻¹ * ((a⁻¹) ^ M * v) ^ (2 : ℕ) := by
  have hcancel : a ^ (2 * d) * (a⁻¹) ^ (2 * d) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ ha, one_pow]
  rw [show 2 * M + 2 * d + 1 = 2 * d + 2 * M + 1 by omega]
  rw [pow_add, pow_add, pow_two, pow_two]
  have hd : a ^ d * a ^ d = a ^ (2 * d) := by
    rw [← pow_add]
    congr 1
    omega
  have hM : (a⁻¹) ^ M * (a⁻¹) ^ M = (a⁻¹) ^ (2 * M) := by
    rw [← pow_add]
    congr 1
    omega
  rw [pow_one]
  calc
    (a ^ d * v * (a ^ d * v)) *
        ((a⁻¹) ^ (2 * d) * (a⁻¹) ^ (2 * M) * a⁻¹) =
      (a ^ (2 * d) * v * v) *
        ((a⁻¹) ^ (2 * d) * (a⁻¹) ^ (2 * M) * a⁻¹) := by
      rw [← hd]
      ring
    _ =
      (a ^ (2 * d) * (a⁻¹) ^ (2 * d)) *
        (a⁻¹ * ((a⁻¹) ^ (2 * M) * v * v)) := by ring
    _ = a⁻¹ * ((a⁻¹) ^ (2 * M) * v * v) := by rw [hcancel, one_mul]
    _ = a⁻¹ * (((a⁻¹) ^ M * v) * ((a⁻¹) ^ M * v)) := by
      rw [← hM]
      ring

/-- Shifted reversal `Q(W) = (W+y)^d p((W+y)⁻¹)`, written without division. -/
def xiShiftedReversedPolynomial
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ) : Polynomial ℝ :=
  ∑ i : Fin (d + 1), C (c i) * (X + C y) ^ (d - (i : ℕ))

private lemma eval_xiShiftedReversedPolynomial
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ) (z : ℂ) :
    evalRealPolynomial (xiShiftedReversedPolynomial y d c) z =
      ∑ i : Fin (d + 1), (c i : ℂ) * (z + (y : ℂ)) ^ (d - (i : ℕ)) := by
  simp [xiShiftedReversedPolynomial, evalRealPolynomial]

private lemma eval_ofFn
    (d : ℕ) (c : Fin (d + 1) → ℝ) (z : ℂ) :
    evalRealPolynomial (Polynomial.ofFn (d + 1) c) z =
      ∑ i : Fin (d + 1), (c i : ℂ) * z ^ (i : ℕ) := by
  simp [evalRealPolynomial, Polynomial.ofFn_eq_sum_monomial]

/-- Exact shifted-reversal evaluation identity. -/
theorem eval_xiShiftedReversedPolynomial_eq
    (y : ℝ) (d : ℕ) (c : Fin (d + 1) → ℝ) (z : ℂ)
    (ha : (y : ℂ) + z ≠ 0) :
    evalRealPolynomial (xiShiftedReversedPolynomial y d c) z =
      ((y : ℂ) + z) ^ d *
        evalRealPolynomial (Polynomial.ofFn (d + 1) c) (((y : ℂ) + z)⁻¹) := by
  rw [eval_xiShiftedReversedPolynomial, eval_ofFn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show z + (y : ℂ) = (y : ℂ) + z by ring]
  calc
    (c i : ℂ) * ((y : ℂ) + z) ^ (d - (i : ℕ)) =
        (c i : ℂ) * (((y : ℂ) + z) ^ d *
          (((y : ℂ) + z)⁻¹) ^ (i : ℕ)) := by
      rw [pow_mul_inv_pow_eq_pow_sub ha (Fin.is_le i)]
    _ = ((y : ℂ) + z) ^ d *
        ((c i : ℂ) * (((y : ℂ) + z)⁻¹) ^ (i : ℕ)) := by ring

/-- One divisor atom of the filtered Gamma transform. -/
def xiShiftedFilteredGammaAtom
    (y : ℝ) (M d : ℕ) (c : Fin (d + 1) → ℝ)
    (q : XiZeroCopy) (t : ℝ) : ℂ :=
  evalRealPolynomial (xiShiftedReversedPolynomial y d c) (xiSquaredNode q) ^ (2 : ℕ) *
    xiHeatResolventAtom y (2 * M + 2 * d) q t

/-- Complex filtered Gamma kernel built from the literal polynomial-square Xi heat trace. -/
def xiShiftedFilteredGammaKernel
    (y : ℝ) (M d : ℕ) (c : Fin (d + 1) → ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (2 * M + 2 * d) * Complex.exp (-((y : ℂ) * t)) *
    xiPolynomialGaussianHeatTrace (xiShiftedReversedPolynomial y d c) t

private theorem xiShiftedFilteredGamma_term_cancel
    {y : ℝ} (hy : 0 ≤ y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) (q : XiZeroCopy) :
    evalRealPolynomial (xiShiftedReversedPolynomial y d c) (xiSquaredNode q) ^ (2 : ℕ) *
        xiShiftedReciprocalSquare y q ^ (2 * M + 2 * d + 1) =
      xiShiftedReciprocalTraceHankelTerm y
        (X ^ M * Polynomial.ofFn (d + 1) c) q := by
  have ha : (y : ℂ) + xiSquaredNode q ≠ 0 :=
    ofReal_add_xiSquaredNode_ne_zero hy q
  have hQ := eval_xiShiftedReversedPolynomial_eq y d c (xiSquaredNode q) ha
  rw [xiShiftedReciprocalTraceHankelTerm]
  rw [hQ]
  simp_rw [xiShiftedReciprocalSquare_eq_inv hy q]
  simp only [evalRealPolynomial_mul, evalRealPolynomial_pow]
  have hX : evalRealPolynomial (X : Polynomial ℝ)
      (((y : ℂ) + xiSquaredNode q)⁻¹) =
        ((y : ℂ) + xiSquaredNode q)⁻¹ := by
    simp [evalRealPolynomial]
  rw [hX]
  exact filtered_power_cancel ha M d

private theorem integrableOn_xiShiftedFilteredGammaAtom
    {y : ℝ} (hy : 0 ≤ y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) (q : XiZeroCopy) :
    IntegrableOn (xiShiftedFilteredGammaAtom y M d c q) (Ioi (0 : ℝ)) := by
  exact (integrableOn_xiHeatResolventAtom hy (2 * M + 2 * d) q).const_mul _

private theorem integral_xiShiftedFilteredGammaAtom
    {y : ℝ} (hy : 0 ≤ y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) (q : XiZeroCopy) :
    (∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaAtom y M d c q t) =
      ((2 * M + 2 * d).factorial : ℂ) *
        xiShiftedReciprocalTraceHankelTerm y
          (X ^ M * Polynomial.ofFn (d + 1) c) q := by
  unfold xiShiftedFilteredGammaAtom
  rw [integral_const_mul,
    integral_pow_mul_exp_shiftedSquaredNode hy]
  calc
    evalRealPolynomial (xiShiftedReversedPolynomial y d c) (xiSquaredNode q) ^ (2 : ℕ) *
        (((2 * M + 2 * d).factorial : ℂ) *
          xiShiftedReciprocalSquare y q ^ (2 * M + 2 * d + 1)) =
      ((2 * M + 2 * d).factorial : ℂ) *
        (evalRealPolynomial
            (xiShiftedReversedPolynomial y d c) (xiSquaredNode q) ^ (2 : ℕ) *
          xiShiftedReciprocalSquare y q ^ (2 * M + 2 * d + 1)) := by ring
    _ = _ := by rw [xiShiftedFilteredGamma_term_cancel hy M d c q]

private theorem tsum_xiShiftedFilteredGammaAtom_eq_kernel
    (y : ℝ) (M d : ℕ) (c : Fin (d + 1) → ℝ) (t : ℝ) :
    (∑' q : XiZeroCopy, xiShiftedFilteredGammaAtom y M d c q t) =
      xiShiftedFilteredGammaKernel y M d c t := by
  rw [xiShiftedFilteredGammaKernel, xiPolynomialGaussianHeatTrace]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [xiShiftedFilteredGammaAtom, xiHeatResolventAtom,
    xiPolynomialGaussianHeatTerm, xiGaussianHeatTerm, xiSquaredNode]
  rw [show -(((y : ℂ) + xiSpectralPoint q ^ (2 : ℕ)) * t) =
      -((y : ℂ) * t) + (-(t : ℂ) * xiSpectralPoint q ^ (2 : ℕ)) by ring,
    Complex.exp_add]
  ring

private theorem integral_norm_xiShiftedFilteredGammaAtom_le
    {y : ℝ} (hy : 0 < y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) (q : XiZeroCopy) :
    (∫ t in Ioi (0 : ℝ), ‖xiShiftedFilteredGammaAtom y M d c q t‖) ≤
      ((2 * M + 2 * d).factorial : ℝ) *
        2 ^ (2 * M + 2 * d + 1) *
          ‖xiShiftedReciprocalTraceHankelTerm y
            (X ^ M * Polynomial.ofFn (d + 1) c) q‖ := by
  let n := 2 * M + 2 * d
  let A :=
    evalRealPolynomial (xiShiftedReversedPolynomial y d c) (xiSquaredNode q) ^ (2 : ℕ)
  have hbase := integral_norm_xiHeatResolventAtom_le hy n q
  have hnorm :
      ‖A‖ * ‖xiShiftedReciprocalSquare y q‖ ^ (n + 1) =
        ‖xiShiftedReciprocalTraceHankelTerm y
          (X ^ M * Polynomial.ofFn (d + 1) c) q‖ := by
    have h := congrArg norm
      (xiShiftedFilteredGamma_term_cancel hy.le M d c q)
    simpa only [A, n, norm_mul, norm_pow] using h
  calc
    (∫ t in Ioi (0 : ℝ), ‖xiShiftedFilteredGammaAtom y M d c q t‖) =
        ‖A‖ * (∫ t in Ioi (0 : ℝ), ‖xiHeatResolventAtom y n q t‖) := by
      unfold xiShiftedFilteredGammaAtom
      change (∫ t in Ioi (0 : ℝ), ‖A * xiHeatResolventAtom y n q t‖) = _
      simp only [norm_mul]
      rw [integral_const_mul]
    _ ≤ ‖A‖ * ((n.factorial : ℝ) *
        (2 * ‖xiShiftedReciprocalSquare y q‖) ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left hbase (norm_nonneg A)
    _ = ((2 * M + 2 * d).factorial : ℝ) *
        2 ^ (2 * M + 2 * d + 1) *
          ‖xiShiftedReciprocalTraceHankelTerm y
            (X ^ M * Polynomial.ofFn (d + 1) c) q‖ := by
      rw [mul_pow, ← hnorm]
      simp only [n]
      ring

private theorem summable_integral_norm_xiShiftedFilteredGammaAtom
    {y : ℝ} (hy : 0 < y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) :
    Summable (fun q : XiZeroCopy =>
      ∫ t in Ioi (0 : ℝ), ‖xiShiftedFilteredGammaAtom y M d c q t‖) := by
  have htrace :=
    (summable_xiShiftedReciprocalTraceHankelTerm hy.le
      (X ^ M * Polynomial.ofFn (d + 1) c)).norm
  have hmajor := htrace.mul_left
    (((2 * M + 2 * d).factorial : ℝ) * 2 ^ (2 * M + 2 * d + 1))
  apply Summable.of_nonneg_of_le
  · intro q
    exact integral_nonneg fun _ => norm_nonneg _
  · exact fun q => integral_norm_xiShiftedFilteredGammaAtom_le hy M d c q
  · exact hmajor

/-- Complex polynomial-filtered Gamma transmutation for the literal Xi divisor. -/
theorem integral_xiShiftedFilteredGammaKernel_eq_traceHankel
    {y : ℝ} (hy : 0 < y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) :
    (∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernel y M d c t) =
      ((2 * M + 2 * d).factorial : ℂ) *
        xiShiftedReciprocalTraceHankel y
          (X ^ M * Polynomial.ofFn (d + 1) c) := by
  have hFint : ∀ q : XiZeroCopy,
      Integrable (xiShiftedFilteredGammaAtom y M d c q)
        (volume.restrict (Ioi (0 : ℝ))) :=
    fun q => integrableOn_xiShiftedFilteredGammaAtom hy.le M d c q
  have hswap :
      (∫ t in Ioi (0 : ℝ), ∑' q : XiZeroCopy,
        xiShiftedFilteredGammaAtom y M d c q t) =
        ∑' q : XiZeroCopy,
          ∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaAtom y M d c q t :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm hFint
      (summable_integral_norm_xiShiftedFilteredGammaAtom hy M d c)).symm
  calc
    (∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernel y M d c t) =
        ∫ t in Ioi (0 : ℝ), ∑' q : XiZeroCopy,
          xiShiftedFilteredGammaAtom y M d c q t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      exact (tsum_xiShiftedFilteredGammaAtom_eq_kernel y M d c t).symm
    _ = ∑' q : XiZeroCopy,
          ∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaAtom y M d c q t := hswap
    _ = ∑' q : XiZeroCopy,
        ((2 * M + 2 * d).factorial : ℂ) *
          xiShiftedReciprocalTraceHankelTerm y
            (X ^ M * Polynomial.ofFn (d + 1) c) q := by
      apply tsum_congr
      intro q
      exact integral_xiShiftedFilteredGammaAtom hy.le M d c q
    _ = ((2 * M + 2 * d).factorial : ℂ) *
        xiShiftedReciprocalTraceHankel y
          (X ^ M * Polynomial.ofFn (d + 1) c) := by
      rw [xiShiftedReciprocalTraceHankel, tsum_mul_left]

/-- Coefficient-moment form of the complex filtered Gamma transmutation. -/
theorem integral_xiShiftedFilteredGammaKernel_eq_momentSum
    {y : ℝ} (hy : 0 < y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) :
    (∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernel y M d c t) =
      ((2 * M + 2 * d).factorial : ℂ) *
        ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          ((c i * c j : ℝ) : ℂ) *
            xiShiftedReciprocalMoment y
              (2 * M + (i : ℕ) + (j : ℕ)) := by
  rw [integral_xiShiftedFilteredGammaKernel_eq_traceHankel hy M d c,
    xiShiftedReciprocalTraceHankel_X_pow_mul_ofFn hy.le M (d + 1) c]

/-- The complex filtered Gamma kernel is integrable on the positive time axis. -/
theorem integrableOn_xiShiftedFilteredGammaKernel
    {y : ℝ} (hy : 0 < y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) :
    IntegrableOn (xiShiftedFilteredGammaKernel y M d c) (Ioi (0 : ℝ)) := by
  have hsum : Integrable
      (fun t => ∑' q : XiZeroCopy, xiShiftedFilteredGammaAtom y M d c q t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
      (fun q => integrableOn_xiShiftedFilteredGammaAtom hy.le M d c q)
      (summable_integral_norm_xiShiftedFilteredGammaAtom hy M d c)
  refine hsum.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact tsum_xiShiftedFilteredGammaAtom_eq_kernel y M d c t

/-- Real polynomial-filtered Gamma kernel. -/
def xiShiftedFilteredGammaKernelReal
    (y : ℝ) (M d : ℕ) (c : Fin (d + 1) → ℝ) (t : ℝ) : ℝ :=
  t ^ (2 * M + 2 * d) * Real.exp (-(y * t)) *
    xiPolynomialGaussianHeatTraceReal (xiShiftedReversedPolynomial y d c) t

theorem xiShiftedFilteredGammaKernel_re
    (y : ℝ) (M d : ℕ) (c : Fin (d + 1) → ℝ) (t : ℝ) :
    (xiShiftedFilteredGammaKernel y M d c t).re =
      xiShiftedFilteredGammaKernelReal y M d c t := by
  have hpow : (t : ℂ) ^ (2 * M + 2 * d) =
      ((t ^ (2 * M + 2 * d) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hexp : Complex.exp (-((y : ℂ) * t)) =
      ((Real.exp (-(y * t)) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hcast : ((t ^ (2 * M + 2 * d) : ℝ) : ℂ) *
      ((Real.exp (-(y * t)) : ℝ) : ℂ) =
        (((t ^ (2 * M + 2 * d) * Real.exp (-(y * t))) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hcoef :
      (t : ℂ) ^ (2 * M + 2 * d) * Complex.exp (-((y : ℂ) * t)) =
        ((t ^ (2 * M + 2 * d) * Real.exp (-(y * t)) : ℝ) : ℂ) := by
    rw [hpow, hexp, hcast]
  calc
    (xiShiftedFilteredGammaKernel y M d c t).re =
        (((t ^ (2 * M + 2 * d) * Real.exp (-(y * t)) : ℝ) : ℂ) *
          xiPolynomialGaussianHeatTrace
            (xiShiftedReversedPolynomial y d c) t).re := by
      apply congrArg Complex.re
      rw [xiShiftedFilteredGammaKernel, hcoef]
    _ = xiShiftedFilteredGammaKernelReal y M d c t := by
      rw [xiShiftedFilteredGammaKernelReal, xiPolynomialGaussianHeatTraceReal]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero]

theorem integrableOn_xiShiftedFilteredGammaKernelReal
    {y : ℝ} (hy : 0 < y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) :
    IntegrableOn (xiShiftedFilteredGammaKernelReal y M d c) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_xiShiftedFilteredGammaKernel hy M d c).re
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact xiShiftedFilteredGammaKernel_re y M d c t

/-- Real coefficient-moment form of the exact filtered Gamma transmutation. -/
theorem integral_xiShiftedFilteredGammaKernelReal_eq_momentSum
    {y : ℝ} (hy : 0 < y) (M d : ℕ)
    (c : Fin (d + 1) → ℝ) :
    (∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernelReal y M d c t) =
      ((2 * M + 2 * d).factorial : ℝ) *
        ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          c i * c j *
            (xiShiftedReciprocalMoment y
              (2 * M + (i : ℕ) + (j : ℕ))).re := by
  calc
    (∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernelReal y M d c t) =
        ((∫ t in Ioi (0 : ℝ),
          xiShiftedFilteredGammaKernel y M d c t) : ℂ).re := by
      calc
        (∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernelReal y M d c t) =
            ∫ t in Ioi (0 : ℝ),
              (xiShiftedFilteredGammaKernel y M d c t).re := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t _
          exact (xiShiftedFilteredGammaKernel_re y M d c t).symm
        _ = ((∫ t in Ioi (0 : ℝ),
            xiShiftedFilteredGammaKernel y M d c t) : ℂ).re :=
          integral_re (integrableOn_xiShiftedFilteredGammaKernel hy M d c)
    _ = _ := by
      rw [integral_xiShiftedFilteredGammaKernel_eq_momentSum hy M d c]
      simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
      apply congrArg (fun x : ℝ => ((2 * M + 2 * d).factorial : ℝ) * x)
      change Complex.reCLM (∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
        ((c i * c j : ℝ) : ℂ) *
          xiShiftedReciprocalMoment y (2 * M + (i : ℕ) + (j : ℕ))) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      simp [Complex.mul_re]

/-- Literal real Hankel quadratic equals the unnormalized filtered Gamma integral. -/
theorem integral_xiShiftedFilteredGammaKernelReal_eq_hankelQuadratic
    {y : ℝ} (hy : 0 < y) (d : ℕ)
    (c : Fin (d + 1) → ℝ) :
    (∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernelReal y 0 d c t) =
      ((2 * d).factorial : ℝ) *
        xiShiftedReciprocalHankelQuadratic y c := by
  rw [integral_xiShiftedFilteredGammaKernelReal_eq_momentSum hy 0 d c]
  rw [show 2 * 0 + 2 * d = 2 * d by omega]
  congr 1
  rw [xiShiftedReciprocalHankelQuadratic]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 3
  omega

/-- **Normalized Route U transmutation (PDH.4).**  Every shifted-Xi Hankel quadratic is exactly
the positive-factor normalization of its polynomial-filtered Gamma average.  This theorem is
unconditional; positivity of the integral is the remaining analytic problem. -/
theorem xiShiftedReciprocalHankelQuadratic_eq_normalizedFilteredGamma
    {y : ℝ} (hy : 0 < y) (d : ℕ)
    (c : Fin (d + 1) → ℝ) :
    xiShiftedReciprocalHankelQuadratic y c =
      (1 / ((2 * d).factorial : ℝ)) *
        ∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernelReal y 0 d c t := by
  rw [integral_xiShiftedFilteredGammaKernelReal_eq_hankelQuadratic hy d c]
  field_simp [Nat.factorial_ne_zero]

/-- Premise-free unit-shift form of the exact filtered Gamma transmutation.  This is the literal
shift used by the fixed absolute-Euler Route U criterion. -/
theorem xiShiftedReciprocalHankelQuadratic_one_eq_normalizedFilteredGamma
    (d : ℕ) (c : Fin (d + 1) → ℝ) :
    xiShiftedReciprocalHankelQuadratic 1 c =
      (1 / ((2 * d).factorial : ℝ)) *
        ∫ t in Ioi (0 : ℝ), xiShiftedFilteredGammaKernelReal 1 0 d c t := by
  exact xiShiftedReciprocalHankelQuadratic_eq_normalizedFilteredGamma
    (by norm_num) d c

end
end RHTower
