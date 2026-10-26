import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The depth kernel of the conjugate-diagonal Hecke defect

The symmetric translation defect at depth `d` is `k(L,d) = 2 cosh(2dL) − 2`.
It is nonnegative, controls the quadratic depth moment, and doubles by
`k(2L,d) = 4k(L,d) + k(L,d)²`. Thus two translation scales read both the
first and second moments of one nonnegative depth observable.
-/

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-- The contribution of unit collided mass at depth `d` to the symmetric Hecke defect. -/
def depthKernel (L d : ℝ) : ℝ := 2 * Real.cosh (2 * d * L) - 2

theorem depthKernel_nonneg (L d : ℝ) : 0 ≤ depthKernel L d := by
  have h := Real.one_le_cosh (2 * d * L)
  dsimp [depthKernel]
  linarith only [h]

theorem depthKernel_eq_four_sinh_sq (L d : ℝ) :
    depthKernel L d = 4 * Real.sinh (d * L) ^ 2 := by
  rw [depthKernel, show 2 * d * L = 2 * (d * L) by ring, Real.cosh_two_mul]
  nlinarith only [Real.cosh_sq (d * L)]

/-- The quadratic term is a global lower bound, including arbitrarily shallow depths. -/
theorem quadratic_le_depthKernel (L d : ℝ) : 4 * L ^ 2 * d ^ 2 ≤ depthKernel L d := by
  have hs : (d * L) ^ 2 ≤ Real.sinh (d * L) ^ 2 := by
    rw [sq_le_sq, Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  rw [depthKernel_eq_four_sinh_sq]
  nlinarith only [hs]

@[simp] theorem depthKernel_zero_scale (d : ℝ) : depthKernel 0 d = 0 := by
  simp [depthKernel]

@[simp] theorem depthKernel_zero_depth (L : ℝ) : depthKernel L 0 = 0 := by
  simp [depthKernel]

/-- Vanishing detects precisely the critical depth or the trivial translation. -/
theorem depthKernel_eq_zero_iff (L d : ℝ) : depthKernel L d = 0 ↔ d = 0 ∨ L = 0 := by
  rw [depthKernel_eq_four_sinh_sq]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or, pow_eq_zero_iff (by norm_num : 2 ≠ 0),
    Real.sinh_eq_zero, mul_eq_zero]

/-- Exact scale doubling, before any spectral summation. -/
theorem depthKernel_double (L d : ℝ) :
    depthKernel (2 * L) d = 4 * depthKernel L d + depthKernel L d ^ 2 := by
  unfold depthKernel
  rw [show 2 * d * (2 * L) = 2 * (2 * d * L) by ring, Real.cosh_two_mul, Real.sinh_sq]
  ring

theorem depthKernel_le_iff (L d e : ℝ) :
    depthKernel L d ≤ depthKernel L e ↔ |d * L| ≤ |e * L| := by
  unfold depthKernel
  have hcos : 2 * Real.cosh (2 * d * L) - 2 ≤ 2 * Real.cosh (2 * e * L) - 2 ↔
      Real.cosh (2 * d * L) ≤ Real.cosh (2 * e * L) := by
    constructor <;> intro h <;> linarith only [h]
  rw [hcos, Real.cosh_le_cosh]
  rw [show 2 * d * L = 2 * (d * L) by ring,
    show 2 * e * L = 2 * (e * L) by ring]
  simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  constructor <;> intro h <;> linarith only [h]

theorem depthKernel_mono_depth (L : ℝ) {d e : ℝ} (h : |d| ≤ |e|) :
    depthKernel L d ≤ depthKernel L e := by
  apply (depthKernel_le_iff L d e).2
  simpa only [abs_mul] using mul_le_mul_of_nonneg_right h (abs_nonneg L)

/-- Equal readings at a nonzero scale mean equal absolute depths. -/
theorem depthKernel_eq_iff (L d e : ℝ) :
    depthKernel L d = depthKernel L e ↔ |d * L| = |e * L| := by
  rw [le_antisymm_iff, depthKernel_le_iff, depthKernel_le_iff, ← le_antisymm_iff]

end GaloisForLFunctions.ConjugateDiagonalGeometry
