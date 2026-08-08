import Mathlib

/-!
# The Schur weight of the Carleman kernel

The Carleman (Hilbert) kernel `1/(s + t)` is homogeneous of degree `−1`, and `t^{-1/2}` is its
Schur weight:

`∫_0^∞ dt / ((s + t) √t) = π / √s`.

The constant `π` on the right is the source of the sharp bound `‖S‖ ≤ π` for the Carleman transform.
The primitive is `(2/√s) arctan(√t/√s)`, and because the integrand is nonnegative the improper
integral needs no separate integrability argument.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The primitive of the Carleman Schur integrand. -/
noncomputable def carlemanSchurPrimitive (s t : ℝ) : ℝ :=
  2 / Real.sqrt s * Real.arctan (Real.sqrt t / Real.sqrt s)

theorem continuous_carlemanSchurPrimitive (s : ℝ) : Continuous (carlemanSchurPrimitive s) := by
  unfold carlemanSchurPrimitive
  fun_prop

theorem hasDerivAt_carlemanSchurPrimitive {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (carlemanSchurPrimitive s) (1 / ((s + t) * Real.sqrt t)) t := by
  have hst : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have htt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have ht2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have h1 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t := Real.hasDerivAt_sqrt ht.ne'
  have h2 : HasDerivAt (fun u : ℝ => Real.sqrt u / Real.sqrt s)
      (1 / (2 * Real.sqrt t) / Real.sqrt s) t := h1.div_const _
  have h3 : HasDerivAt (fun u : ℝ => Real.arctan (Real.sqrt u / Real.sqrt s))
      (1 / (1 + (Real.sqrt t / Real.sqrt s) ^ 2) * (1 / (2 * Real.sqrt t) / Real.sqrt s)) t :=
    (Real.hasDerivAt_arctan _).comp t h2
  have h4 := h3.const_mul (2 / Real.sqrt s)
  refine h4.congr_deriv ?_
  have hden : (1 : ℝ) + (Real.sqrt t / Real.sqrt s) ^ 2 = (s + t) / s := by
    rw [div_pow, ht2, hs2]
    field_simp
  rw [hden]
  field_simp
  exact hs2.symm

theorem tendsto_carlemanSchurPrimitive {s : ℝ} (hs : 0 < s) :
    Tendsto (carlemanSchurPrimitive s) atTop (𝓝 (2 / Real.sqrt s * (Real.pi / 2))) := by
  have hst : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h1 : Tendsto (fun t : ℝ => Real.sqrt t / Real.sqrt s) atTop atTop := by
    have := Real.tendsto_sqrt_atTop
    exact Filter.Tendsto.atTop_div_const hst this
  have h2 : Tendsto (fun t : ℝ => Real.arctan (Real.sqrt t / Real.sqrt s)) atTop
      (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
  exact h2.const_mul _

/-- **The Schur weight identity.**  `∫_0^∞ dt/((s+t)√t) = π/√s`. -/
theorem integral_carlemanSchurWeight {s : ℝ} (hs : 0 < s) :
    (∫ t in Ioi (0 : ℝ), 1 / ((s + t) * Real.sqrt t)) = Real.pi / Real.sqrt s := by
  have hst : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hcont : ContinuousWithinAt (carlemanSchurPrimitive s) (Ici (0 : ℝ)) 0 :=
    (continuous_carlemanSchurPrimitive s).continuousWithinAt
  have hderiv : ∀ t ∈ Ioi (0 : ℝ),
      HasDerivAt (carlemanSchurPrimitive s) (1 / ((s + t) * Real.sqrt t)) t :=
    fun t ht => hasDerivAt_carlemanSchurPrimitive hs ht
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ 1 / ((s + t) * Real.sqrt t) := by
    intro t ht
    have htt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    have : 0 < s + t := by linarith [mem_Ioi.mp ht]
    positivity
  have h := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos
    (tendsto_carlemanSchurPrimitive hs)
  rw [h, carlemanSchurPrimitive, Real.sqrt_zero, zero_div, Real.arctan_zero, mul_zero, sub_zero]
  field_simp

end GaloisForLFunctions.HTGeometry
