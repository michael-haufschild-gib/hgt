import GaloisForLFunctions.SquareRootThreshold.DepthProfileFourierModeLaw
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Smooth depth profiles hide up to a logarithmic aperture

A run with a sharp edge is visible at aperture `O(1/δ)` (`OffLineRunEdgeVisibilityLaw`), while a
uniform depth hides up to the Nyquist ceiling `L/2` (`DepthProfileNyquistCeiling`). This module
quantifies the regime in between: **smooth** depth modulations.

Let `d` be a depth profile of period `P` with values in `[0, δ]` whose cyclic first and second
differences are at most `κ₁` and `κ₂`. Two periodic summations by parts
(`one_sub_mul_sum_pow`) give, for `1 ≤ m ≤ P/2` and `v = mL/P`,

`|D(m)| ≤ P³ (2vκ₂ sinh(vδ) + 4v²κ₁² cosh(vδ)) / (16 m²)`  (`norm_depthSymbol_le_of_smooth`),

because the second difference of `cosh(v·d)` is controlled by the mean value theorem
(`abs_second_diff_cosh_le`) and `|1 − e^{2πim/P}| ≥ 4m/P`. Summing the modes against the
Gershgorin criterion of `DepthProfileFourierModeLaw` gives (`profileConfig_weil_nonneg_of_smooth`):
the profile is invisible at every aperture `a ≤ L/4` with

`P L κ₂ sinh(2δa)(1 + log n)/8 + n L² κ₁² cosh(2δa)/4 ≤ 1`,  `n = ⌈2aP/L⌉`.

For a smooth profile of amplitude `δ` and period `P` (in lattice units) one has `κ₁ ≍ δ/P` and
`κ₂ ≍ δ/P²`, so the condition reads `e^{2δa} ≲ P/(δL log P)`: the profile hides up to aperture
`≈ (1/2δ) log(P/(δL))`, i.e. logarithmically in the modulation length `Λ = 2πP/L` measured in units
of the depth. Edges (`Λ → 0`) are seen at `O(1/δ)`, smooth modulations at `(1/2δ) log(Λ/δ)`, and the
uniform lattice (`Λ = ∞`) only at the ceiling `L/2`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Periodic summation by parts -/

/-- Along the cyclic rotation, a `(n+1)`-th root of unity picks up one factor `ω`. -/
theorem pow_finRotate {n : ℕ} {ω : ℂ} (hω : ω ^ (n + 1) = 1) (r : Fin (n + 1)) :
    ω ^ ((finRotate (n + 1) r : Fin (n + 1)) : ℕ) = ω * ω ^ (r : ℕ) := by
  by_cases h : r = Fin.last n
  · subst h
    rw [finRotate_last, Fin.val_zero, pow_zero, Fin.val_last, ← pow_succ', hω]
  · rw [coe_finRotate_of_ne_last h, pow_succ']

/-- The cyclic backward difference `∇g(r) = g(r) − g(r − 1)`. -/
def backDiff {n : ℕ} (g : Fin (n + 1) → ℂ) (r : Fin (n + 1)) : ℂ :=
  g r - g ((finRotate (n + 1)).symm r)

/-- **Periodic summation by parts.** `(1 − ω) Σ_r g(r) ω^r = Σ_r ∇g(r) ω^r` for `ω^{n+1} = 1`. -/
theorem one_sub_mul_sum_pow {n : ℕ} {ω : ℂ} (hω : ω ^ (n + 1) = 1) (g : Fin (n + 1) → ℂ) :
    (1 - ω) * ∑ r, g r * ω ^ (r : ℕ) = ∑ r, backDiff g r * ω ^ (r : ℕ) := by
  have hshift : ∑ r, g ((finRotate (n + 1)).symm r) * ω ^ (r : ℕ) =
      ω * ∑ r, g r * ω ^ (r : ℕ) := by
    rw [← Equiv.sum_comp (finRotate (n + 1)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Equiv.symm_apply_apply, pow_finRotate hω]
    ring
  simp only [backDiff, sub_mul, Finset.sum_sub_distrib, hshift]
  ring

/-- Two summations by parts: `|Σ_r g(r) ω^r| ≤ Σ_r |∇²g(r)| / |1 − ω|²`. -/
theorem norm_sum_pow_le {n : ℕ} {ω : ℂ} (hω : ω ^ (n + 1) = 1) (hω1 : ω ≠ 1) (hωn : ‖ω‖ = 1)
    (g : Fin (n + 1) → ℂ) :
    ‖∑ r, g r * ω ^ (r : ℕ)‖ ≤ (∑ r, ‖backDiff (backDiff g) r‖) / ‖1 - ω‖ ^ 2 := by
  have h1 : (1 - ω) ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
  have h2 : (1 - ω) ^ 2 * ∑ r, g r * ω ^ (r : ℕ) = ∑ r, backDiff (backDiff g) r * ω ^ (r : ℕ) := by
    rw [sq, mul_assoc, one_sub_mul_sum_pow hω, one_sub_mul_sum_pow hω]
  have hpos : 0 < ‖1 - ω‖ ^ 2 := by positivity
  rw [le_div_iff₀ hpos, ← norm_pow, ← norm_mul, mul_comm, h2]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [norm_mul, norm_pow, hωn, one_pow, mul_one]

/-! ### The second difference of `cosh(v·d)` -/

/-- `|sinh x − sinh y| ≤ cosh M · |x − y|` for `|x|, |y| ≤ M`. -/
theorem abs_sinh_sub_sinh_le {x y M : ℝ} (hx : |x| ≤ M) (hy : |y| ≤ M) :
    |Real.sinh x - Real.sinh y| ≤ Real.cosh M * |x - y| := by
  rcases lt_trichotomy x y with h | h | h
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh h
      Real.continuous_sinh.continuousOn fun z _ => Real.hasDerivAt_sinh z
    rw [eq_div_iff (by linarith)] at hcd
    rw [abs_sub_comm, ← hcd, abs_mul, abs_sub_comm y x, abs_of_pos (Real.cosh_pos c)]
    gcongr
    rw [Real.cosh_le_cosh]
    exact (abs_le.mpr ⟨by linarith [(abs_le.mp hx).1, hc.1], by linarith [(abs_le.mp hy).2, hc.2]⟩).trans
      (le_abs_self M)
  · subst h; simp
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope Real.sinh Real.cosh h
      Real.continuous_sinh.continuousOn fun z _ => Real.hasDerivAt_sinh z
    rw [eq_div_iff (by linarith)] at hcd
    rw [← hcd, abs_mul, abs_of_pos (Real.cosh_pos c)]
    gcongr
    rw [Real.cosh_le_cosh]
    exact (abs_le.mpr ⟨by linarith [(abs_le.mp hy).1, hc.1], by linarith [(abs_le.mp hx).2, hc.2]⟩).trans
      (le_abs_self M)

end GaloisForLFunctions.SquareRootThreshold
