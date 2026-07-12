import Mathlib

/-!
# The coercive Wigner--Eisenstein archimedean symbol

The theta Wigner current naturally carries the fourth-order dilation polynomial

`((D - 1/2)^2 + b^2) ((D + 1/2)^2 + b^2)`.

On the Fourier frequency `τ` of the logarithmic dilation variable, its symbol is the norm square

`(b^2 + 1/4 - τ^2)^2 + τ^2`.

This file proves its exact sharp positive floor.  It contains no zeta-zero hypothesis and makes no
positivity assertion about the separate arithmetic/radial pairing in the Xi Bezoutian.
-/

open Complex

namespace RHTower

noncomputable section

/-- The scalar Fourier symbol of the Wigner--Eisenstein archimedean fourth-order operator. -/
def thetaWignerEisensteinSymbol (b τ : ℝ) : ℝ :=
  (b ^ 2 + 1 / 4 - τ ^ 2) ^ 2 + τ ^ 2

/-- The exact lower spectral edge of `thetaWignerEisensteinSymbol b`. -/
def thetaWignerEisensteinFloor (b : ℝ) : ℝ :=
  if b ^ 2 ≤ 1 / 4 then (b ^ 2 + 1 / 4) ^ 2 else b ^ 2

/-- The squared modulus of the elementary centered completion polynomial on the radial line
`w = a + i b`. -/
def thetaXiCompletionRadialWeight (b a : ℝ) : ℝ :=
  ((a - 1 / 2) ^ 2 + b ^ 2) * ((a + 1 / 2) ^ 2 + b ^ 2)

/-- The fourth-order symbol is the norm square of either conjugate second-order factor. -/
theorem thetaWignerEisensteinSymbol_eq_normSq (b τ : ℝ) :
    thetaWignerEisensteinSymbol b τ =
      Complex.normSq ((((τ : ℂ) * I - (1 / 2 : ℂ)) ^ 2) + (b : ℂ) ^ 2) := by
  rw [Complex.normSq_apply]
  norm_num [thetaWignerEisensteinSymbol, pow_two]
  ring

/-- Reflection of the dilation frequency preserves the archimedean symbol. -/
theorem thetaWignerEisensteinSymbol_neg (b τ : ℝ) :
    thetaWignerEisensteinSymbol b (-τ) = thetaWignerEisensteinSymbol b τ := by
  simp [thetaWignerEisensteinSymbol]

/-- The exact spectral edge is strictly positive at every real Eisenstein frequency. -/
theorem thetaWignerEisensteinFloor_pos (b : ℝ) :
    0 < thetaWignerEisensteinFloor b := by
  rw [thetaWignerEisensteinFloor]
  split_ifs with h
  · have hb : 0 < b ^ 2 + 1 / 4 := by nlinarith [sq_nonneg b]
    positivity
  · have hb : 1 / 4 < b ^ 2 := lt_of_not_ge h
    positivity

/-- **Sharp coercivity.**  Every dilation frequency lies above the exact positive spectral edge. -/
theorem thetaWignerEisensteinFloor_le_symbol (b τ : ℝ) :
    thetaWignerEisensteinFloor b ≤ thetaWignerEisensteinSymbol b τ := by
  by_cases h : b ^ 2 ≤ 1 / 4
  · rw [thetaWignerEisensteinFloor, if_pos h]
    have hτ : 0 ≤ τ ^ 2 := sq_nonneg τ
    have hsecond : 0 ≤ τ ^ 2 + 1 / 2 - 2 * b ^ 2 := by
      nlinarith
    have hprod : 0 ≤ τ ^ 2 * (τ ^ 2 + 1 / 2 - 2 * b ^ 2) :=
      mul_nonneg hτ hsecond
    unfold thetaWignerEisensteinSymbol
    nlinarith
  · rw [thetaWignerEisensteinFloor, if_neg h]
    have hsquare : 0 ≤ (τ ^ 2 - (b ^ 2 - 1 / 4)) ^ 2 := sq_nonneg _
    unfold thetaWignerEisensteinSymbol
    nlinarith

/-- The archimedean fourth-order symbol has no real-frequency null direction. -/
theorem thetaWignerEisensteinSymbol_pos (b τ : ℝ) :
    0 < thetaWignerEisensteinSymbol b τ :=
  lt_of_lt_of_le (thetaWignerEisensteinFloor_pos b)
    (thetaWignerEisensteinFloor_le_symbol b τ)

/-- The lower edge is attained: at frequency zero below the transition, and at the two displaced
frequencies `±sqrt (b^2 - 1/4)` above it. -/
theorem exists_thetaWignerEisensteinSymbol_eq_floor (b : ℝ) :
    ∃ τ : ℝ,
      thetaWignerEisensteinSymbol b τ = thetaWignerEisensteinFloor b := by
  by_cases h : b ^ 2 ≤ 1 / 4
  · refine ⟨0, ?_⟩
    rw [thetaWignerEisensteinFloor, if_pos h]
    norm_num [thetaWignerEisensteinSymbol]
  · let τ : ℝ := Real.sqrt (b ^ 2 - 1 / 4)
    have hrad : 0 ≤ b ^ 2 - 1 / 4 := by
      have : 1 / 4 < b ^ 2 := lt_of_not_ge h
      linarith
    have hτ : τ ^ 2 = b ^ 2 - 1 / 4 := by
      exact Real.sq_sqrt hrad
    refine ⟨τ, ?_⟩
    rw [thetaWignerEisensteinFloor, if_neg h]
    unfold thetaWignerEisensteinSymbol
    rw [hτ]
    ring

/-- The sharp floor changes formula only at the critical frequency `|b|=1/2`. -/
theorem thetaWignerEisensteinFloor_eq (b : ℝ) :
    thetaWignerEisensteinFloor b =
      if |b| ≤ 1 / 2 then (b ^ 2 + 1 / 4) ^ 2 else b ^ 2 := by
  have hiff : b ^ 2 ≤ 1 / 4 ↔ |b| ≤ 1 / 2 := by
    constructor
    · intro h
      apply (sq_le_sq₀ (abs_nonneg b) (by norm_num)).1
      have h' := h
      norm_num at h' ⊢
      simpa [sq_abs] using h'
    · intro h
      have hsq := (sq_le_sq₀ (abs_nonneg b) (by norm_num)).2 h
      norm_num at hsq ⊢
      simpa [sq_abs] using hsq
  simp only [thetaWignerEisensteinFloor, hiff]

/-- The radial completion weight is exactly `|(a+i b)^2-1/4|^2`. -/
theorem thetaXiCompletionRadialWeight_eq_normSq (b a : ℝ) :
    thetaXiCompletionRadialWeight b a =
      Complex.normSq ((((a : ℂ) + (b : ℂ) * I) ^ 2) - (1 / 4 : ℂ)) := by
  rw [Complex.normSq_apply]
  norm_num [thetaXiCompletionRadialWeight, pow_two]
  ring

/-- Exact radial derivative of the elementary Xi completion weight. -/
theorem hasDerivAt_thetaXiCompletionRadialWeight (b a : ℝ) :
    HasDerivAt (thetaXiCompletionRadialWeight b)
      (4 * a * (a ^ 2 + b ^ 2 - 1 / 4)) a := by
  have hminus : HasDerivAt (fun x : ℝ => (x - 1 / 2) ^ 2 + b ^ 2)
      (2 * (a - 1 / 2)) a := by
    have h := (((hasDerivAt_id a).sub_const (1 / 2)).pow 2).add
      (hasDerivAt_const (x := a) (c := b ^ 2))
    convert h using 1
    all_goals norm_num [id_eq]
  have hplus : HasDerivAt (fun x : ℝ => (x + 1 / 2) ^ 2 + b ^ 2)
      (2 * (a + 1 / 2)) a := by
    have h := (((hasDerivAt_id a).add_const (1 / 2)).pow 2).add
      (hasDerivAt_const (x := a) (c := b ^ 2))
    convert h using 1
    all_goals norm_num [id_eq]
  convert hminus.mul hplus using 1
  all_goals ring

theorem deriv_thetaXiCompletionRadialWeight (b a : ℝ) :
    deriv (thetaXiCompletionRadialWeight b) a =
      4 * a * (a ^ 2 + b ^ 2 - 1 / 4) :=
  (hasDerivAt_thetaXiCompletionRadialWeight b a).deriv

/-- Outside the radius-`1/2` central disk, the elementary completion weight points strictly toward
the Euler half-plane. -/
theorem deriv_thetaXiCompletionRadialWeight_pos {b a : ℝ} (ha : 0 < a)
    (hout : 1 / 4 < a ^ 2 + b ^ 2) :
    0 < deriv (thetaXiCompletionRadialWeight b) a := by
  rw [deriv_thetaXiCompletionRadialWeight]
  positivity

/-- Inside the radius-`1/2` central disk, the elementary completion weight points in the opposite
radial direction. -/
theorem deriv_thetaXiCompletionRadialWeight_neg {b a : ℝ} (ha : 0 < a)
    (hin : a ^ 2 + b ^ 2 < 1 / 4) :
    deriv (thetaXiCompletionRadialWeight b) a < 0 := by
  rw [deriv_thetaXiCompletionRadialWeight]
  have hfactor : a ^ 2 + b ^ 2 - 1 / 4 < 0 := by linarith
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) ha) hfactor

/-- Exact ordered-pair polynomial collapse in the theta Wigner transform.  After recentering an
ordered theta-index pair, every dependence on the ratio of the indices leaves the Gaussian
polynomial and survives only in the separate Fourier phase. -/
theorem thetaWignerAtomPair_polynomial (c v : ℝ) :
    (c ^ 2 * Real.exp (4 * v) - 3 * c * Real.exp (2 * v)) *
        (c ^ 2 * Real.exp (-4 * v) - 3 * c * Real.exp (-2 * v)) =
      c ^ 4 - 6 * c ^ 3 * Real.cosh (2 * v) + 9 * c ^ 2 := by
  rw [Real.cosh_eq]
  have h44 : Real.exp (4 * v) * Real.exp (-4 * v) = 1 := by
    rw [← Real.exp_add]
    simp
  have h22 : Real.exp (2 * v) * Real.exp (-2 * v) = 1 := by
    rw [← Real.exp_add]
    simp
  have h42 : Real.exp (4 * v) * Real.exp (-2 * v) = Real.exp (2 * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h24 : Real.exp (2 * v) * Real.exp (-4 * v) = Real.exp (-(2 * v)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = c ^ 4 * (Real.exp (4 * v) * Real.exp (-4 * v))
        - 3 * c ^ 3 * (Real.exp (4 * v) * Real.exp (-2 * v))
        - 3 * c ^ 3 * (Real.exp (2 * v) * Real.exp (-4 * v))
        + 9 * c ^ 2 * (Real.exp (2 * v) * Real.exp (-2 * v)) := by ring
    _ = _ := by rw [h44, h22, h42, h24]; ring

end

end RHTower
