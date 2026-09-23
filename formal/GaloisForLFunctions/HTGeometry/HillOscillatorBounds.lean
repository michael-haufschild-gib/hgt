import GaloisForLFunctions.HTGeometry.HillEquationSolution

/-!
# Pointwise bounds on a Hill oscillator

The energy bound is what a synthesis over frequencies consumes, but only after it is turned into
bounds on the oscillator and on its velocity separately. Both follow from the definition of the
energy, and the frequency enters exactly once:

`|u'| ≤ √E`,  `ω|u| ≤ √E`.

For the datum `(u, u') = (1, 0)` the initial energy is `ω(a)²`, so the oscillator is bounded by
`ω(a)/ω(t)` times the Grönwall factor — and for a family `ω = c·s` that ratio is `c(a)/c(t)`, the
same for every frequency. For the datum `(0, 1)` the initial energy is `1`, and the oscillator decays
like `1/ω`: one power of the frequency, which the initial datum has to supply.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

/-! ## Splitting the energy -/

section Split

variable {ω u du : ℝ → ℝ}

theorem abs_deriv_le_sqrt_hillEnergy (t : ℝ) :
    |du t| ≤ Real.sqrt (hillEnergy ω u du t) := by
  have hle : du t ^ (2 : ℕ) ≤ hillEnergy ω u du t := by
    have : (0 : ℝ) ≤ ω t ^ (2 : ℕ) * u t ^ (2 : ℕ) := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [hillEnergy]
    linarith
  have habs : |du t| ^ (2 : ℕ) ≤ hillEnergy ω u du t := by
    rwa [sq_abs]
  calc |du t| = Real.sqrt (|du t| ^ (2 : ℕ)) := by
        rw [Real.sqrt_sq (abs_nonneg _)]
    _ ≤ Real.sqrt (hillEnergy ω u du t) := Real.sqrt_le_sqrt habs

theorem mul_abs_le_sqrt_hillEnergy (hω : ∀ t, 0 < ω t) (t : ℝ) :
    ω t * |u t| ≤ Real.sqrt (hillEnergy ω u du t) := by
  have hle : (ω t * |u t|) ^ (2 : ℕ) ≤ hillEnergy ω u du t := by
    have hdu : (0 : ℝ) ≤ du t ^ (2 : ℕ) := sq_nonneg _
    have hexp : (ω t * |u t|) ^ (2 : ℕ) = ω t ^ (2 : ℕ) * u t ^ (2 : ℕ) := by
      rw [mul_pow, sq_abs]
    rw [hexp, hillEnergy]
    linarith
  have hnn : 0 ≤ ω t * |u t| := mul_nonneg (le_of_lt (hω t)) (abs_nonneg _)
  calc ω t * |u t| = Real.sqrt ((ω t * |u t|) ^ (2 : ℕ)) := by rw [Real.sqrt_sq hnn]
    _ ≤ Real.sqrt (hillEnergy ω u du t) := Real.sqrt_le_sqrt hle

end Split

/-! ## The bounds carried by the Grönwall factor -/

section Bounds

variable {ω dω : ℝ → ℝ} {M K a b : ℝ}

theorem sqrt_hillEnergy_le (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (hωd : ∀ t, HasDerivAt ω (dω t) t) (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t)
    (y₀ : ℝ × ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    Real.sqrt (hillEnergy ω (hillSolution ω y₀) (hillSolutionDeriv ω y₀) t) ≤
      Real.sqrt (hillEnergy ω (hillSolution ω y₀) (hillSolutionDeriv ω y₀) a) *
        Real.exp (K * (t - a)) := by
  have hgron := hillEnergy_hillSolution_le hω hM1 hM hωd hωpos hK y₀ ht
  have hfactor : Real.exp (2 * K * (t - a)) = Real.exp (K * (t - a)) ^ (2 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hfactor] at hgron
  have hsqrt := Real.sqrt_le_sqrt hgron
  refine hsqrt.trans_eq ?_
  rw [Real.sqrt_mul (hillEnergy_nonneg ω _ _ a), Real.sqrt_sq (Real.exp_nonneg _)]

/-- **The oscillator and its velocity, separately.** -/
theorem abs_hillSolutionDeriv_le (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (hωd : ∀ t, HasDerivAt ω (dω t) t) (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t)
    (y₀ : ℝ × ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    |hillSolutionDeriv ω y₀ t| ≤
      Real.sqrt (hillEnergy ω (hillSolution ω y₀) (hillSolutionDeriv ω y₀) a) *
        Real.exp (K * (t - a)) :=
  (abs_deriv_le_sqrt_hillEnergy t).trans
    (sqrt_hillEnergy_le hω hM1 hM hωd hωpos hK y₀ ht)

theorem mul_abs_hillSolution_le (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (hωd : ∀ t, HasDerivAt ω (dω t) t) (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t)
    (y₀ : ℝ × ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    ω t * |hillSolution ω y₀ t| ≤
      Real.sqrt (hillEnergy ω (hillSolution ω y₀) (hillSolutionDeriv ω y₀) a) *
        Real.exp (K * (t - a)) :=
  (mul_abs_le_sqrt_hillEnergy hωpos t).trans
    (sqrt_hillEnergy_le hω hM1 hM hωd hωpos hK y₀ ht)

end Bounds

/-! ## The two canonical data -/

section Data

variable {ω dω : ℝ → ℝ} {M K a b : ℝ}

/-- The initial energy of the datum `(u, u') = (1, 0)` at time `0` is `ω(0)²`. -/
theorem hillEnergy_cos_zero (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) :
    hillEnergy ω (hillSolution ω (1, 0)) (hillSolutionDeriv ω (1, 0)) 0 = ω 0 ^ (2 : ℕ) := by
  rw [hillEnergy, hillSolution_zero hω hM1 hM, hillSolutionDeriv_zero hω hM1 hM]
  norm_num

/-- The initial energy of the datum `(u, u') = (0, 1)` at time `0` is `1`. -/
theorem hillEnergy_sin_zero (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M) :
    hillEnergy ω (hillSolution ω (0, 1)) (hillSolutionDeriv ω (0, 1)) 0 = 1 := by
  rw [hillEnergy, hillSolution_zero hω hM1 hM, hillSolutionDeriv_zero hω hM1 hM]
  norm_num

/-- **The oscillator of the datum `(1,0)` is bounded by the frequency ratio.** For a family
`ω = c·s` the ratio `ω(0)/ω(t)` is `c(0)/c(t)`: the bound does not see the frequency. -/
theorem mul_abs_hillSolution_cos_le (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (hωd : ∀ t, HasDerivAt ω (dω t) t) (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    ω t * |hillSolution ω (1, 0) t| ≤ ω 0 * Real.exp (K * t) := by
  have h := mul_abs_hillSolution_le hω hM1 hM hωd hωpos hK (1, 0) ht
  rw [hillEnergy_cos_zero hω hM1 hM, Real.sqrt_sq (le_of_lt (hωpos 0)), sub_zero] at h
  exact h

/-- **The oscillator of the datum `(0,1)` decays like one power of the frequency.** -/
theorem mul_abs_hillSolution_sin_le (hω : Continuous ω) (hM1 : 1 ≤ M) (hM : ∀ s, ω s ^ (2 : ℕ) ≤ M)
    (hωd : ∀ t, HasDerivAt ω (dω t) t) (hωpos : ∀ t, 0 < ω t) (hK : ∀ t, |dω t| ≤ K * ω t)
    {t : ℝ} (ht : t ∈ Icc 0 b) :
    ω t * |hillSolution ω (0, 1) t| ≤ Real.exp (K * t) := by
  have h := mul_abs_hillSolution_le hω hM1 hM hωd hωpos hK (0, 1) ht
  rw [hillEnergy_sin_zero hω hM1 hM, Real.sqrt_one, one_mul, sub_zero] at h
  exact h

end Data

end GaloisForLFunctions.HTGeometry
