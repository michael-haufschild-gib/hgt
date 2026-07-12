import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Polar prime critical Mellin defect

This file formalizes the unconditional finite-dimensional core of the polar-prime
Mellin calculation and its real positive-parameter infinite Laplace-transform identity.
It does not formalize the full complex Stieltjes-transform continuation.

The main structural result is the signed rank-two decomposition of the polar
kernel.  Its finite complex quadratic form has one positive `cosh` channel and one
negative `sinh` channel.  The file also records the corrected zero-frequency sign
of the polar multiplier and the exact algebraic cancellation used after Abel
summation.
-/

open scoped BigOperators ComplexConjugate ComplexOrder
open Finset MeasureTheory ArithmeticFunction Complex Matrix Set Filter

noncomputable section

namespace RHTower

/-- The physical-space kernel carried by the polar term. -/
def polarKernel (x y : ℝ) : ℝ :=
  2 * Real.cosh ((x - y) / 2)

/-- The polar kernel is the difference of two rank-one kernels. -/
theorem polarKernel_eq_rankTwo (x y : ℝ) :
    polarKernel x y =
      2 * Real.cosh (x / 2) * Real.cosh (y / 2) -
      2 * Real.sinh (x / 2) * Real.sinh (y / 2) := by
  rw [polarKernel]
  rw [show (x - y) / 2 = x / 2 - y / 2 by ring]
  rw [Real.cosh_sub]
  ring

variable {ι : Type*}

/-- The positive rank-one feature of the polar kernel. -/
def polarCoshFeature (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) : ℂ :=
  ∑ i ∈ s, (Real.cosh (x i / 2) : ℂ) * v i

/-- The negative rank-one feature of the polar kernel. -/
def polarSinhFeature (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) : ℂ :=
  ∑ i ∈ s, (Real.sinh (x i / 2) : ℂ) * v i

/-- The finite complex quadratic form associated with `polarKernel`. -/
def polarQuadraticForm (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s,
    (polarKernel (x i) (x j) : ℂ) * v i * conj (v j)

/-- Exact signed rank-two factorization of the finite polar quadratic form. -/
theorem polarQuadraticForm_eq_rankTwo
    (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) :
    polarQuadraticForm s x v =
      2 * (polarCoshFeature s x v * conj (polarCoshFeature s x v) -
        polarSinhFeature s x v * conj (polarSinhFeature s x v)) := by
  unfold polarQuadraticForm polarKernel polarCoshFeature polarSinhFeature
  simp only [map_sum, map_mul, Complex.conj_ofReal]
  simp_rw [show ∀ i j, (x i - x j) / 2 = x i / 2 - x j / 2 by
    intro i j
    ring]
  simp_rw [Real.cosh_sub]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  norm_num
  ring

/-- The real energy of the finite polar quadratic form. -/
def polarEnergy (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) : ℝ :=
  (polarQuadraticForm s x v).re

/-- The polar energy has signature `(+,-)` on its two feature channels. -/
theorem polarEnergy_eq_signature
    (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ) :
    polarEnergy s x v =
      2 * Complex.normSq (polarCoshFeature s x v) -
      2 * Complex.normSq (polarSinhFeature s x v) := by
  rw [polarEnergy, polarQuadraticForm_eq_rankTwo]
  rw [Complex.mul_conj, Complex.mul_conj]
  simp
  ring

/-- Killing the negative channel leaves a nonnegative polar energy. -/
theorem polarEnergy_nonneg_of_sinhFeature_eq_zero
    (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ)
    (h : polarSinhFeature s x v = 0) :
    0 ≤ polarEnergy s x v := by
  rw [polarEnergy_eq_signature, h]
  simp [Complex.normSq_nonneg]

/-- Killing the positive channel leaves a nonpositive polar energy. -/
theorem polarEnergy_nonpos_of_coshFeature_eq_zero
    (s : Finset ι) (x : ι → ℝ) (v : ι → ℂ)
    (h : polarCoshFeature s x v = 0) :
    polarEnergy s x v ≤ 0 := by
  rw [polarEnergy_eq_signature, h]
  simp [Complex.normSq_nonneg]

/-- The corrected Fourier multiplier of the polar distribution. -/
def polarMultiplier (a ξ : ℝ) : ℝ :=
  (2 * Real.sinh a * Real.cos (2 * a * ξ) +
    4 * ξ * Real.cosh a * Real.sin (2 * a * ξ)) /
    (ξ ^ 2 + 1 / 4)

/-- At zero frequency the corrected polar multiplier is positive `8 sinh(a)`. -/
theorem polarMultiplier_zero (a : ℝ) :
    polarMultiplier a 0 = 8 * Real.sinh a := by
  unfold polarMultiplier
  simp
  ring

/-- A positive aperture gives a strictly positive zero-frequency polar term. -/
theorem polarMultiplier_zero_pos {a : ℝ} (ha : 0 < a) :
    0 < polarMultiplier a 0 := by
  rw [polarMultiplier_zero]
  have hs : 0 < Real.sinh a := (Real.sinh_pos_iff).2 ha
  linarith

/-- The zero-frequency polar value in the aperture coordinate `X = exp(2a)`. -/
theorem polarMultiplier_zero_eq_sqrtExp (a : ℝ) :
    polarMultiplier a 0 =
      4 * Real.sqrt (Real.exp (2 * a)) -
        4 / Real.sqrt (Real.exp (2 * a)) := by
  have hsqrt : Real.sqrt (Real.exp (2 * a)) = Real.exp a := by
    rw [show Real.exp (2 * a) = (Real.exp a) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos a)]
  rw [polarMultiplier_zero, hsqrt, Real.sinh_eq, Real.exp_neg]
  ring

/-- Abel summation at the critical square-root weight. -/
theorem abelSqrtWeight_identity (c : ℕ → ℝ) (hc : c 0 = 0) (X : ℝ) :
    ∑ k ∈ Icc 0 ⌊X⌋₊, ((k : ℝ) ^ (-1 / 2 : ℝ)) * c k =
      X ^ (-1 / 2 : ℝ) * (∑ k ∈ Icc 0 ⌊X⌋₊, c k) +
        (1 / 2 : ℝ) * ∫ t in Set.Ioc (1 : ℝ) X,
          t ^ (-3 / 2 : ℝ) * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
  let f : ℝ → ℝ := fun t => t ^ (-1 / 2 : ℝ)
  have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) X, DifferentiableAt ℝ f t := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))).differentiableAt
  have hderiv : deriv f = fun t => (-1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ) := by
    funext t
    rw [show f = fun u : ℝ => u ^ (-1 / 2 : ℝ) by rfl]
    rw [Real.deriv_rpow_const]
    congr 1
    norm_num
  have hcont : ContinuousOn (fun t : ℝ => (-1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ))
      (Set.Icc (1 : ℝ) X) := by
    exact continuousOn_const.mul <|
      continuousOn_id.rpow_const (fun t ht => Or.inl (by
        change t ≠ 0
        linarith [ht.1]))
  have hint : IntegrableOn (deriv f) (Set.Icc (1 : ℝ) X) := by
    rw [hderiv]
    exact hcont.integrableOn_compact isCompact_Icc
  have h := sum_mul_eq_sub_integral_mul₀ c hc X hdiff hint
  rw [show f = fun u : ℝ => u ^ (-1 / 2 : ℝ) by rfl] at h
  rw [hderiv] at h
  have hscale :
      (∫ t in Set.Ioc (1 : ℝ) X,
        ((-1 / 2 : ℝ) * t ^ (-3 / 2 : ℝ)) * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)) =
      (-1 / 2 : ℝ) * ∫ t in Set.Ioc (1 : ℝ) X,
        t ^ (-3 / 2 : ℝ) * (∑ k ∈ Icc 0 ⌊t⌋₊, c k) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    ring
  rw [hscale] at h
  rw [h]
  ring

/-- The elementary critical main integral. -/
theorem integral_invSqrt_Ioc (X : ℝ) (hX : 1 ≤ X) :
    (∫ t in Set.Ioc (1 : ℝ) X, t ^ (-1 / 2 : ℝ)) =
      2 * (Real.sqrt X - 1) := by
  let F : ℝ → ℝ := fun t => t ^ (1 / 2 : ℝ)
  let F' : ℝ → ℝ := fun t => (1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ)
  have hderiv : deriv F = F' := by
    funext t
    rw [show F = fun u : ℝ => u ^ (1 / 2 : ℝ) by rfl]
    rw [Real.deriv_rpow_const]
    rw [show F' t = (1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) by rfl]
    congr 1
    norm_num
  have hdiff : ∀ t ∈ Set.uIcc (1 : ℝ) X, DifferentiableAt ℝ F t := by
    intro t ht
    have ht1 : 1 ≤ t := by
      rw [Set.uIcc_of_le hX] at ht
      exact ht.1
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith))).differentiableAt
  have hcont : ContinuousOn F' (Set.uIcc (1 : ℝ) X) := by
    rw [Set.uIcc_of_le hX]
    exact continuousOn_const.mul <|
      continuousOn_id.rpow_const (fun t ht => Or.inl (by
        change t ≠ 0
        linarith [ht.1]))
  have hfund := intervalIntegral.integral_deriv_eq_sub' F hderiv hdiff hcont
  rw [intervalIntegral.integral_of_le hX] at hfund
  rw [show F' = fun t : ℝ => (1 / 2 : ℝ) * t ^ (-1 / 2 : ℝ) by rfl] at hfund
  rw [MeasureTheory.integral_const_mul] at hfund
  rw [show F X = Real.sqrt X by
    rw [show F X = X ^ (1 / 2 : ℝ) by rfl, ← Real.sqrt_eq_rpow]] at hfund
  norm_num [F] at hfund
  linarith

/-- The linear main term inside the critical Mellin integral. -/
theorem integral_criticalMain_Ioc (X : ℝ) (hX : 1 ≤ X) :
    (∫ t in Set.Ioc (1 : ℝ) X, t ^ (-3 / 2 : ℝ) * t) =
      2 * (Real.sqrt X - 1) := by
  rw [show (∫ t in Set.Ioc (1 : ℝ) X, t ^ (-3 / 2 : ℝ) * t) =
      ∫ t in Set.Ioc (1 : ℝ) X, t ^ (-1 / 2 : ℝ) by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := by linarith [ht.1]
    nth_rewrite 2 [← Real.rpow_one t]
    rw [← Real.rpow_add ht0]
    congr 1
    ring]
  exact integral_invSqrt_Ioc X hX

/-- The cumulative coefficient sum at a real cutoff. -/
def criticalCumulative (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Icc 0 ⌊t⌋₊, c k

/-- The deviation of the cumulative coefficient sum from its linear main term. -/
def criticalMellinError (c : ℕ → ℝ) (t : ℝ) : ℝ :=
  criticalCumulative c t - t

/--
Exact critical Mellin defect identity.  Instantiating `c` with the von Mangoldt
function gives the Chebyshev-error formula used in the CCM polar-prime symbol.
-/
theorem criticalMellinError_identity
    (c : ℕ → ℝ) (hc : c 0 = 0) (X : ℝ) (hX : 1 ≤ X) :
    ∑ k ∈ Icc 0 ⌊X⌋₊, ((k : ℝ) ^ (-1 / 2 : ℝ)) * c k =
      2 * Real.sqrt X - 1 + criticalMellinError c X / Real.sqrt X +
        (1 / 2 : ℝ) * ∫ t in Set.Ioc (1 : ℝ) X,
          criticalMellinError c t * t ^ (-3 / 2 : ℝ) := by
  have hbase := abelSqrtWeight_identity c hc X
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hgcont : ContinuousOn (fun t : ℝ => t ^ (-3 / 2 : ℝ))
      (Set.Icc (1 : ℝ) X) :=
    continuousOn_id.rpow_const (fun t ht => Or.inl (by
      change t ≠ 0
      linarith [ht.1]))
  have hgint : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ))
      (Set.Icc (1 : ℝ) X) := hgcont.integrableOn_compact isCompact_Icc
  have hpsiInt : IntegrableOn
      (fun t : ℝ => t ^ (-3 / 2 : ℝ) * criticalCumulative c t)
      (Set.Icc (1 : ℝ) X) := by
    simpa [criticalCumulative] using
      (integrableOn_mul_sum_Icc c (a := (1 : ℝ)) (b := X) zero_le_one hgint)
  have hmainCont : ContinuousOn (fun t : ℝ => t ^ (-3 / 2 : ℝ) * t)
      (Set.Icc (1 : ℝ) X) := hgcont.mul continuousOn_id
  have hmainInt : IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ) * t)
      (Set.Icc (1 : ℝ) X) := hmainCont.integrableOn_compact isCompact_Icc
  have herrInt : IntegrableOn
      (fun t : ℝ => criticalMellinError c t * t ^ (-3 / 2 : ℝ))
      (Set.Icc (1 : ℝ) X) := by
    have hd := hpsiInt.sub hmainInt
    apply hd.congr_fun _ measurableSet_Icc
    intro t ht
    simp only [Pi.sub_apply, criticalMellinError]
    ring
  have hsplit :
      (∫ t in Set.Ioc (1 : ℝ) X, t ^ (-3 / 2 : ℝ) * criticalCumulative c t) =
      (∫ t in Set.Ioc (1 : ℝ) X, t ^ (-3 / 2 : ℝ) * t) +
      ∫ t in Set.Ioc (1 : ℝ) X, criticalMellinError c t * t ^ (-3 / 2 : ℝ) := by
    rw [← MeasureTheory.integral_add
      (hmainInt.mono_set Set.Ioc_subset_Icc_self)
      (herrInt.mono_set Set.Ioc_subset_Icc_self)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    simp only [criticalMellinError]
    ring
  have hboundary :
      X ^ (-1 / 2 : ℝ) * criticalCumulative c X =
        Real.sqrt X + criticalMellinError c X / Real.sqrt X := by
    have hsqrt0 : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
    have hweight : X ^ (-1 / 2 : ℝ) = 1 / Real.sqrt X := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring]
      rw [Real.rpow_neg hX0.le]
      rw [← Real.sqrt_eq_rpow]
      rw [one_div]
    rw [hweight]
    simp only [criticalMellinError]
    field_simp [hsqrt0.ne']
    nlinarith [Real.sq_sqrt hX0.le]
  rw [show (∑ k ∈ Icc 0 ⌊X⌋₊, c k) = criticalCumulative c X by
    rfl] at hbase
  have hsplit' :
      (∫ t in Set.Ioc (1 : ℝ) X,
        t ^ (-3 / 2 : ℝ) * (∑ k ∈ Icc 0 ⌊t⌋₊, c k)) =
      (∫ t in Set.Ioc (1 : ℝ) X, t ^ (-3 / 2 : ℝ) * t) +
      ∫ t in Set.Ioc (1 : ℝ) X, criticalMellinError c t * t ^ (-3 / 2 : ℝ) := by
    simpa [criticalCumulative] using hsplit
  rw [hsplit', integral_criticalMain_Ioc X hX, hboundary] at hbase
  linarith

/-- The exact critical Mellin error identity for the von Mangoldt coefficients. -/
theorem vonMangoldt_criticalMellinError_identity (X : ℝ) (hX : 1 ≤ X) :
    ∑ k ∈ Icc 0 ⌊X⌋₊, ((k : ℝ) ^ (-1 / 2 : ℝ)) * Λ k =
      2 * Real.sqrt X - 1 +
        criticalMellinError (fun k => Λ k) X / Real.sqrt X +
        (1 / 2 : ℝ) * ∫ t in Set.Ioc (1 : ℝ) X,
          criticalMellinError (fun k => Λ k) t * t ^ (-3 / 2 : ℝ) := by
  exact criticalMellinError_identity (fun k => Λ k) (by simp) X hX

/--
The complete zero-frequency polar--prime cancellation at aperture `a ≥ 0`.
This is the finite critical Mellin defect formula; `m` is the independent
archimedean zero-frequency contribution.
-/
theorem polarPrimeZero_defect_identity (m a : ℝ) (ha : 0 ≤ a) :
    m - 2 * (∑ k ∈ Icc 0 ⌊Real.exp (2 * a)⌋₊,
      ((k : ℝ) ^ (-1 / 2 : ℝ)) * Λ k) + polarMultiplier a 0 =
      m + 2 - 4 / Real.sqrt (Real.exp (2 * a)) -
        2 * criticalMellinError (fun k => Λ k) (Real.exp (2 * a)) /
          Real.sqrt (Real.exp (2 * a)) -
        ∫ t in Set.Ioc (1 : ℝ) (Real.exp (2 * a)),
          criticalMellinError (fun k => Λ k) t * t ^ (-3 / 2 : ℝ) := by
  have hX : 1 ≤ Real.exp (2 * a) := Real.one_le_exp (by linarith)
  rw [vonMangoldt_criticalMellinError_identity (Real.exp (2 * a)) hX]
  rw [polarMultiplier_zero_eq_sqrtExp]
  ring

/--
The exact critical-scale cancellation after inserting an Abel-summation identity
`S = 2r - 1 + E/r + I/2` and the polar value `P = 4r - 4/r`.
-/
theorem criticalMellinDefect_cancellation
    (m S r E I P : ℝ)
    (hS : S = 2 * r - 1 + E / r + I / 2)
    (hP : P = 4 * r - 4 / r) :
    m - 2 * S + P = m + 2 - 4 / r - 2 * E / r - I := by
  rw [hS, hP]
  ring


/-! ## Infinite real Laplace-source colligation -/

/-- The continuous polar half-line channel in the critical Mellin coordinate.  Its density is the
positive source `2 cosh(h/2)`. -/
def continuousPolarLaplaceChannel (s : ℝ) : ℝ :=
  ∫ h : ℝ in Ioi 0,
    Real.exp (-(s + 1 / 2) * h) * (2 * Real.cosh (h / 2))

/-- The resolved von Mangoldt prime-power channel at the matching shifted coordinate. -/
def vonMangoldtPrimeLaplaceChannel (s : ℝ) : ℂ :=
  LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) ((s + 1 : ℝ) : ℂ)

/-- The signed critical Mellin-defect channel: continuous polar source minus the discrete
von Mangoldt atoms.  This is the Laplace transform of
`d(4 sinh(h/2) - sum_(n ≤ exp h) Λ(n)n⁻¹ᐟ²)` on the real convergence ray. -/
def criticalMellinDefectLaplaceChannel (s : ℝ) : ℂ :=
  (continuousPolarLaplaceChannel s : ℂ) - vonMangoldtPrimeLaplaceChannel s

/-- The continuous polar density splits into its two positive Laplace coordinates. -/
theorem continuousPolarLaplaceChannel_eq {s : ℝ} (hs : 0 < s) :
    continuousPolarLaplaceChannel s = 1 / s + 1 / (s + 1) := by
  rw [continuousPolarLaplaceChannel]
  have hs1 : -(s + 1) < 0 := by linarith
  have hs0 : -s < 0 := by linarith
  have hfun : (fun h : ℝ =>
      Real.exp (-(s + 1 / 2) * h) * (2 * Real.cosh (h / 2))) =
      fun h : ℝ => Real.exp (-s * h) + Real.exp (-(s + 1) * h) := by
    funext h
    rw [Real.cosh_eq]
    ring_nf
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1 <;> ring_nf
  rw [hfun, integral_add]
  · rw [integral_exp_mul_Ioi hs0 0, integral_exp_mul_Ioi hs1 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp
  · exact integrableOn_exp_mul_Ioi hs0 0
  · exact integrableOn_exp_mul_Ioi hs1 0

/-- The prime channel is exactly the Euler-region negative logarithmic derivative of zeta. -/
theorem vonMangoldtPrimeLaplaceChannel_eq_logDeriv {s : ℝ} (hs : 0 < s) :
    vonMangoldtPrimeLaplaceChannel s =
      -deriv riemannZeta ((s + 1 : ℝ) : ℂ) / riemannZeta ((s + 1 : ℝ) : ℂ) := by
  rw [vonMangoldtPrimeLaplaceChannel]
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by
    norm_num
    linarith)

private theorem complex_vonMangoldt_nonneg (n : ℕ) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℂ) := by
  apply Complex.nonneg_iff.mpr
  exact ⟨by simp [ArithmeticFunction.vonMangoldt_nonneg], by simp⟩

private theorem complex_vonMangoldt_two_pos :
    0 < (ArithmeticFunction.vonMangoldt 2 : ℂ) := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  change 0 < ((Real.log (2 : ℝ) : ℝ) : ℂ)
  rw [Complex.pos_iff]
  change 0 < Real.log (2 : ℝ) ∧ (0 : ℝ) = 0
  exact ⟨Real.log_pos (by norm_num), rfl⟩

/-- The resolved prime-power channel is strictly positive on the real convergence ray. -/
theorem vonMangoldtPrimeLaplaceChannel_pos {s : ℝ} (hs : 0 < s) :
    0 < vonMangoldtPrimeLaplaceChannel s := by
  rw [vonMangoldtPrimeLaplaceChannel, LSeries]
  have hhalf : 1 < (((s + 1 : ℝ) : ℂ)).re := by
    norm_num
    linarith
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hhalf).tsum_pos
    (fun n => LSeries.term_nonneg (a := fun n =>
      (ArithmeticFunction.vonMangoldt n : ℂ)) (complex_vonMangoldt_nonneg n) (s + 1))
    2 (LSeries.term_pos (a := fun n =>
      (ArithmeticFunction.vonMangoldt n : ℂ)) (by norm_num)
      complex_vonMangoldt_two_pos (s + 1))

/-! ## The resolved Euler channel is an actual finite Gram kernel -/

private abbrev vonMangoldtComplexCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ)

private def vonMangoldtLaplaceWeight (n : ℕ) : ℂ :=
  LSeries.term vonMangoldtComplexCoeff 1 n

private def primePowerLaplaceFeature (x : ℝ) (n : ℕ) : ℂ :=
  ((n : ℂ) ^ (x : ℂ))⁻¹

private theorem vonMangoldtLaplaceWeight_nonneg (n : ℕ) :
    0 ≤ vonMangoldtLaplaceWeight n :=
  LSeries.term_nonneg (complex_vonMangoldt_nonneg n) 1

private theorem primePowerLaplaceFeature_pos {x : ℝ} {n : ℕ} (hn : n ≠ 0) :
    0 < primePowerLaplaceFeature x n := by
  exact Complex.inv_natCast_cpow_ofReal_pos hn x

private theorem primePowerLaplaceFeature_star {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (starRingEnd ℂ) (primePowerLaplaceFeature x n) =
      primePowerLaplaceFeature x n := by
  by_cases hn : n = 0
  · subst n
    simp [primePowerLaplaceFeature,
      Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hx.ne')]
  · have h := (primePowerLaplaceFeature_pos (x := x) hn).le
    rcases Complex.nonneg_iff.mp h with ⟨_, him⟩
    exact RCLike.conj_eq_iff_im.mpr him.symm

private theorem vonMangoldtTerm_eq_weight_mul_features
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    LSeries.term vonMangoldtComplexCoeff (((x + y + 1 : ℝ) : ℂ)) n =
      vonMangoldtLaplaceWeight n * primePowerLaplaceFeature x n *
        primePowerLaplaceFeature y n := by
  by_cases hn : n = 0
  · subst n
    simp [vonMangoldtLaplaceWeight, primePowerLaplaceFeature, LSeries.term,
      Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hx.ne'),
      Complex.zero_cpow (Complex.ofReal_ne_zero.mpr hy.ne')]
  · rw [LSeries.term_of_ne_zero hn]
    simp only [vonMangoldtLaplaceWeight, primePowerLaplaceFeature]
    rw [LSeries.term_of_ne_zero hn]
    simp only [Complex.ofReal_add, Complex.ofReal_one]
    rw [show (x : ℂ) + (y : ℂ) + 1 = (1 : ℂ) + (x : ℂ) + (y : ℂ) by ring]
    rw [Complex.cpow_add ((1 : ℂ) + (x : ℂ)) (y : ℂ) (Nat.cast_ne_zero.mpr hn),
      Complex.cpow_add (1 : ℂ) (x : ℂ) (Nat.cast_ne_zero.mpr hn)]
    simp only [div_eq_mul_inv]
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev]
    ac_rfl

private theorem summable_vonMangoldtWeight_mul_features
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Summable (fun n => vonMangoldtLaplaceWeight n * primePowerLaplaceFeature x n *
      primePowerLaplaceFeature y n) := by
  have hs : 1 < ((((x + y + 1 : ℝ) : ℂ))).re := by
    norm_num
    linarith
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).congr
    (fun n => vonMangoldtTerm_eq_weight_mul_features hx hy n)

/-- The finite resolved von Mangoldt channel on positive Laplace nodes. -/
def vonMangoldtPrimeLaplaceGram {N : ℕ} (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => vonMangoldtPrimeLaplaceChannel (x i + x j)

private def resolvedVonMangoldtPrimeLaplaceGram {N : ℕ} (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => ∑' n, vonMangoldtLaplaceWeight n * primePowerLaplaceFeature (x i) n *
    primePowerLaplaceFeature (x j) n

private theorem resolvedVonMangoldtPrimeLaplaceGram_eq
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    resolvedVonMangoldtPrimeLaplaceGram x = vonMangoldtPrimeLaplaceGram x := by
  ext i j
  rw [resolvedVonMangoldtPrimeLaplaceGram, vonMangoldtPrimeLaplaceGram,
    vonMangoldtPrimeLaplaceChannel, LSeries]
  apply tsum_congr
  intro n
  exact (vonMangoldtTerm_eq_weight_mul_features (hx i) (hx j) n).symm

/-- **Resolved Euler Gram positivity.** Every finite positive-node packet of the actual von
Mangoldt channel is positive semidefinite.  The proof retains the unsquared arithmetic weight:
the quadratic form is the convergent prime-power sum
`sum_n LSeries.term Lambda 1 n * |sum_i c_i n^(-x_i)|^2`. -/
theorem vonMangoldtPrimeLaplaceGram_posSemidef
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    (vonMangoldtPrimeLaplaceGram x).PosSemidef := by
  rw [← resolvedVonMangoldtPrimeLaplaceGram_eq x hx]
  have hherm : (resolvedVonMangoldtPrimeLaplaceGram x).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply]
    rw [resolvedVonMangoldtPrimeLaplaceGram_eq x hx]
    change star (vonMangoldtPrimeLaplaceChannel (x j + x i)) =
      vonMangoldtPrimeLaplaceChannel (x i + x j)
    rw [add_comm (x j) (x i)]
    have hp := vonMangoldtPrimeLaplaceChannel_pos
      (s := x i + x j) (by linarith [hx i, hx j])
    rcases Complex.pos_iff.mp hp with ⟨_, him⟩
    rw [RCLike.star_def]
    exact Complex.conj_eq_iff_im.mpr him.symm
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm (fun c => ?_)
  let P : ℕ → ℂ := fun n => ∑ k, c k * primePowerLaplaceFeature (x k) n
  have hpairs : ∀ i j : Fin N,
      Summable (fun n => star (c i) * (c j *
        (vonMangoldtLaplaceWeight n * primePowerLaplaceFeature (x i) n *
          primePowerLaplaceFeature (x j) n))) := by
    intro i j
    exact (((summable_vonMangoldtWeight_mul_features (hx i) (hx j)).mul_left (c j)).mul_left
      (star (c i))).congr (fun n => by ring)
  have key : star c ⬝ᵥ (resolvedVonMangoldtPrimeLaplaceGram x).mulVec c =
      ∑' n, star (P n) * (vonMangoldtLaplaceWeight n * P n) := by
    simp only [dotProduct, Pi.star_apply]
    have hswap : ∀ i,
        star (c i) * (resolvedVonMangoldtPrimeLaplaceGram x).mulVec c i =
          ∑' n, ∑ j, star (c i) * (c j *
            (vonMangoldtLaplaceWeight n * primePowerLaplaceFeature (x i) n *
              primePowerLaplaceFeature (x j) n)) := by
      intro i
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.mul_sum]
      rw [Summable.tsum_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [resolvedVonMangoldtPrimeLaplaceGram]
        rw [← (summable_vonMangoldtWeight_mul_features (hx i) (hx j)).tsum_mul_right (c j)]
        rw [← ((summable_vonMangoldtWeight_mul_features (hx i) (hx j)).mul_right
          (c j)).tsum_mul_left (star (c i))]
        apply tsum_congr
        intro n
        ring
      · intro j hj
        exact hpairs i j
    calc
      (∑ i, star (c i) * (resolvedVonMangoldtPrimeLaplaceGram x).mulVec c i) =
          ∑ i, ∑' n, ∑ j, star (c i) * (c j *
            (vonMangoldtLaplaceWeight n * primePowerLaplaceFeature (x i) n *
              primePowerLaplaceFeature (x j) n)) :=
        Finset.sum_congr rfl (fun i _ => hswap i)
      _ = ∑' n, star (P n) * (vonMangoldtLaplaceWeight n * P n) := by
        rw [← Summable.tsum_finsetSum]
        · apply tsum_congr
          intro n
          change (∑ i, ∑ j, star (c i) * (c j *
              (vonMangoldtLaplaceWeight n * primePowerLaplaceFeature (x i) n *
                primePowerLaplaceFeature (x j) n))) =
            (starRingEnd ℂ) (∑ k, c k * primePowerLaplaceFeature (x k) n) *
              (vonMangoldtLaplaceWeight n *
                ∑ k, c k * primePowerLaplaceFeature (x k) n)
          rw [map_sum]
          have hstar (k : Fin N) :
              (starRingEnd ℂ) (c k * primePowerLaplaceFeature (x k) n) =
                (starRingEnd ℂ) (c k) * primePowerLaplaceFeature (x k) n := by
            rw [map_mul, primePowerLaplaceFeature_star (hx k)]
          simp_rw [hstar]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          have hcstar : (starRingEnd ℂ) (c i) = star (c i) := rfl
          rw [hcstar]
          ring
        · intro i hi
          exact summable_sum (fun j hj => hpairs i j)
  rw [key]
  apply tsum_nonneg
  intro n
  have hw := vonMangoldtLaplaceWeight_nonneg n
  have hsq : 0 ≤ star (P n) * P n := by
    change 0 ≤ (starRingEnd ℂ) (P n) * P n
    rw [← Complex.normSq_eq_conj_mul_self]
    exact Complex.nonneg_iff.mpr ⟨Complex.normSq_nonneg _, rfl⟩
  have hprod := mul_nonneg hw hsq
  rw [show star (P n) * (vonMangoldtLaplaceWeight n * P n) =
    vonMangoldtLaplaceWeight n * (star (P n) * P n) by ring]
  exact hprod

/-- **Polar--prime critical Mellin colligation.**  On the real convergence ray, the universal
Cauchy coordinate is the resolved von Mangoldt channel minus the shifted polar channel plus the
signed critical Mellin defect.  No Xi divisor or zero-location hypothesis enters this identity. -/
theorem cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
    {s : ℝ} (hs : 0 < s) :
    (1 / s : ℂ) = vonMangoldtPrimeLaplaceChannel s - (1 / (s + 1) : ℂ) +
      criticalMellinDefectLaplaceChannel s := by
  rw [criticalMellinDefectLaplaceChannel, continuousPolarLaplaceChannel_eq hs]
  push_cast
  ring

/-- Real-kernel specialization of the four-channel colligation used by the diagonal Fock
coordinate. -/
theorem cauchyKernel_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (1 / (x + y) : ℂ) =
      vonMangoldtPrimeLaplaceChannel (x + y) - (1 / (x + y + 1) : ℂ) +
        criticalMellinDefectLaplaceChannel (x + y) := by
  simpa only [Complex.ofReal_add, Complex.ofReal_one] using
    (cauchy_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
      (s := x + y) (by linarith))

/-- The universal Cauchy/Laplace transport Gram on a finite positive node packet. -/
def cauchyLaplaceGram {N : ℕ} (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (1 / (x i + x j) : ℂ)

/-- The shifted elementary polar channel in the same finite packet. -/
def shiftedPolarLaplaceGram {N : ℕ} (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (1 / (x i + x j + 1) : ℂ)

/-- The signed critical Mellin-defect channel in the same finite packet. -/
def criticalMellinDefectLaplaceGram {N : ℕ} (x : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => criticalMellinDefectLaplaceChannel (x i + x j)

/-- **Actual finite source incidence.** The Cauchy transport matrix is exactly the resolved
von Mangoldt Gram minus the shifted polar Gram plus the signed critical Mellin-defect matrix.
This discharges the abstract channel-incidence hypothesis for every positive real node packet. -/
theorem cauchyLaplaceGram_eq_prime_sub_shiftedPolar_add_criticalMellinDefect
    {N : ℕ} (x : Fin N → ℝ) (hx : ∀ i, 0 < x i) :
    cauchyLaplaceGram x = vonMangoldtPrimeLaplaceGram x - shiftedPolarLaplaceGram x +
      criticalMellinDefectLaplaceGram x := by
  ext i j
  exact cauchyKernel_eq_prime_sub_shiftedPolar_add_criticalMellinDefect (hx i) (hx j)

end RHTower
