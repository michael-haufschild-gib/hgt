import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

/-!
# Polar prime critical Mellin defect

This file formalizes the unconditional finite-dimensional core of the polar-prime
Mellin calculation.  It does not formalize the von Mangoldt Stieltjes measure, the
zeta logarithmic derivative, or the infinite Laplace-transform identity.

The main structural result is the signed rank-two decomposition of the polar
kernel.  Its finite complex quadratic form has one positive `cosh` channel and one
negative `sinh` channel.  The file also records the corrected zero-frequency sign
of the polar multiplier and the exact algebraic cancellation used after Abel
summation.
-/

open scoped BigOperators ComplexConjugate
open Finset

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

end RHTower
