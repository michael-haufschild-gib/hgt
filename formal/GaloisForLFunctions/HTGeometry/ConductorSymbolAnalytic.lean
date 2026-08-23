import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The conductor symbol is an analytic symbol up to a bounded error

Stirling's formula gives the real-place conductor symbol as `log(2 + |ξ|)` up to a bounded error.
That symbol is not itself a boundary value of a function analytic in a half plane, but it differs
from one by a bounded function:

`log(2 + |ξ|) − Re Log(2 + iξ) ∈ [0, ½ log 2]`,

because `(2+|ξ|)²/(4+ξ²) = 1 + 4|ξ|/(4+ξ²) ∈ [1,2]`.  Since `2 + iξ` has positive real part, the
principal branch never meets the cut, and `2 + iz` is nonvanishing on `Im z > −2`, so `Log(2+iz)`
is analytic on a half plane containing the real axis.

A bounded symbol has a bounded commutator with any projection, so only the analytic part carries
the commutator, and its Hankel kernel is the one bounded in `ConductorHankelBound`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The real-place conductor symbol, in its Stirling normal form. -/
def conductorSymbol (ξ : ℝ) : ℝ := Real.log (2 + |ξ|)

/-- The analytic symbol whose real part carries the conductor singularity. -/
def conductorAnalytic (ξ : ℝ) : ℂ := Complex.log (2 + Complex.I * ξ)

theorem conductorAnalytic_ne_zero (ξ : ℝ) : (2 : ℂ) + Complex.I * ξ ≠ 0 := by
  intro h
  have hre : ((2 : ℂ) + Complex.I * ξ).re = 0 := by rw [h]; simp
  simp at hre

theorem norm_two_add_I_mul (ξ : ℝ) : ‖(2 : ℂ) + Complex.I * ξ‖ = Real.sqrt (4 + ξ ^ 2) := by
  have hre : ((2 : ℂ) + Complex.I * ξ).re = 2 := by simp
  have him : ((2 : ℂ) + Complex.I * ξ).im = ξ := by simp
  rw [Complex.norm_def, Complex.normSq_apply, hre, him]
  congr 1
  ring

theorem conductorAnalytic_re (ξ : ℝ) :
    (conductorAnalytic ξ).re = Real.log (Real.sqrt (4 + ξ ^ 2)) := by
  rw [conductorAnalytic, Complex.log_re, norm_two_add_I_mul]

/-! ## The bounded difference -/

theorem sq_bounds (ξ : ℝ) :
    4 + ξ ^ 2 ≤ (2 + |ξ|) ^ 2 ∧ (2 + |ξ|) ^ 2 ≤ 2 * (4 + ξ ^ 2) := by
  have habs : |ξ| ^ 2 = ξ ^ 2 := sq_abs ξ
  have hnn : 0 ≤ |ξ| := abs_nonneg ξ
  constructor
  · nlinarith [habs, hnn]
  · nlinarith [habs, hnn, sq_nonneg (|ξ| - 2)]

theorem conductorSymbol_sub_analytic_nonneg (ξ : ℝ) :
    0 ≤ conductorSymbol ξ - (conductorAnalytic ξ).re := by
  have hpos : (0 : ℝ) < 4 + ξ ^ 2 := by positivity
  have hsq := (sq_bounds ξ).1
  have hs : Real.sqrt (4 + ξ ^ 2) ≤ 2 + |ξ| := by
    rw [show (2 : ℝ) + |ξ| = Real.sqrt ((2 + |ξ|) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hsq
  have hspos : (0 : ℝ) < Real.sqrt (4 + ξ ^ 2) := Real.sqrt_pos.mpr hpos
  rw [conductorSymbol, conductorAnalytic_re, sub_nonneg]
  exact Real.log_le_log hspos hs

theorem conductorSymbol_sub_analytic_le (ξ : ℝ) :
    conductorSymbol ξ - (conductorAnalytic ξ).re ≤ Real.log 2 / 2 := by
  have hpos : (0 : ℝ) < 4 + ξ ^ 2 := by positivity
  have hsq := (sq_bounds ξ).2
  have hspos : (0 : ℝ) < Real.sqrt (4 + ξ ^ 2) := Real.sqrt_pos.mpr hpos
  have hs : (2 : ℝ) + |ξ| ≤ Real.sqrt 2 * Real.sqrt (4 + ξ ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num) (4 + ξ ^ 2),
      show (2 : ℝ) + |ξ| = Real.sqrt ((2 + |ξ|) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt hsq
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlog : Real.log (2 + |ξ|) ≤ Real.log (Real.sqrt 2) + Real.log (Real.sqrt (4 + ξ ^ 2)) := by
    have h1 : Real.log (2 + |ξ|) ≤ Real.log (Real.sqrt 2 * Real.sqrt (4 + ξ ^ 2)) :=
      Real.log_le_log (by positivity) hs
    rwa [Real.log_mul (ne_of_gt hsqrt2) (ne_of_gt hspos)] at h1
  have hval : Real.log (Real.sqrt 2) = Real.log 2 / 2 := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    have hlog := Real.log_mul (ne_of_gt hsqrt2) (ne_of_gt hsqrt2)
    rw [h2] at hlog
    linarith
  rw [conductorSymbol, conductorAnalytic_re]
  rw [hval] at hlog
  linarith

/-- **The conductor symbol is analytic up to a bounded error.** -/
theorem abs_conductorSymbol_sub_analytic_le (ξ : ℝ) :
    |conductorSymbol ξ - (conductorAnalytic ξ).re| ≤ Real.log 2 / 2 := by
  rw [abs_le]
  have h1 := conductorSymbol_sub_analytic_nonneg ξ
  have h2 := conductorSymbol_sub_analytic_le ξ
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  constructor <;> linarith

end

end GaloisForLFunctions.HTGeometry
