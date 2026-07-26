import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FunProp
import GaloisForLFunctions.RHTower.FuchsProlateScale

/-!
# Self-adjointness of the prolate operator on the band

The prolate Sturm–Liouville action `P_c ψ = ((1−y²)ψ')' − c²y²ψ = (1−y²)ψ'' − 2yψ' − c²y²ψ` is
symmetric on the band `[−1,1]` with **no boundary conditions**: the Sturm–Liouville flux
`(1−y²)·ψ'` vanishes identically at both endpoints because the leading coefficient `1−y²`
vanishes there.  For twice differentiable `f, g` with continuous second derivatives,

`∫_{−1}^{1} g·(P_c f) = ∫_{−1}^{1} f·(P_c g)`  (`prolateSLAction_band_symmetric`).

Integration by parts moves the flux derivative onto `g`, the boundary terms are killed by the
`1−y²` factor, and the remaining first-order form `∫ (1−y²)·f'·g'` together with the potential
term `∫ c²y²·f·g` is manifestly symmetric.  Combined with the off-diagonal kernel identity
`P_x K_c = P_y K_c`, this symmetry is what forces the time–band integral operator to commute
with the prolate differential operator on the band.
-/

open MeasureTheory intervalIntegral

namespace RHTower

/-- Derivative of the Sturm–Liouville flux `(1−y²)·f'`. -/
theorem hasDerivAt_bandFlux {f : ℝ → ℝ} {t : ℝ} (hf2 : DifferentiableAt ℝ (deriv f) t) :
    HasDerivAt (fun y => (1 - y ^ 2) * deriv f y)
      (-(2 * t) * deriv f t + (1 - t ^ 2) * deriv (deriv f) t) t := by
  have hpoly : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * t)) t := by
    have h0 := (hasDerivAt_pow 2 t).const_sub 1
    simpa using h0
  exact hpoly.mul hf2.hasDerivAt

/-- Integration by parts on the band: the flux part of the prolate action integrated against a
differentiable weight loses its boundary terms, since the flux `(1−y²)·f'` vanishes at `±1`. -/
theorem band_flux_integral_by_parts {f g : ℝ → ℝ}
    (hf2 : Differentiable ℝ (deriv f)) (hf2c : Continuous (deriv (deriv f)))
    (hg1 : Differentiable ℝ g) (hg'c : Continuous (deriv g)) :
    ∫ y in (-1 : ℝ)..1, g y * (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y)
      = -∫ y in (-1 : ℝ)..1, deriv g y * ((1 - y ^ 2) * deriv f y) := by
  have hu : ∀ y ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (deriv g y) y :=
    fun y _ => (hg1 y).hasDerivAt
  have hv : ∀ y ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt (fun t => (1 - t ^ 2) * deriv f t)
      (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y) y :=
    fun y _ => hasDerivAt_bandFlux (hf2 y)
  have hu' : IntervalIntegrable (deriv g) volume (-1) 1 := hg'c.intervalIntegrable _ _
  have hv' : IntervalIntegrable
      (fun y => -(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y) volume (-1) 1 := by
    have hf'c : Continuous (deriv f) := hf2.continuous
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simp only [] at h
  rw [h]
  norm_num

/-- **Self-adjointness of the prolate operator on the band.**  The prolate Sturm–Liouville
action is symmetric over `[−1,1]` with no boundary conditions: the vanishing of `1−y²` at the
endpoints replaces them. -/
theorem prolateSLAction_band_symmetric {f g : ℝ → ℝ}
    (hf1 : Differentiable ℝ f) (hf2 : Differentiable ℝ (deriv f))
    (hf2c : Continuous (deriv (deriv f)))
    (hg1 : Differentiable ℝ g) (hg2 : Differentiable ℝ (deriv g))
    (hg2c : Continuous (deriv (deriv g))) (c : ℝ) :
    ∫ y in (-1 : ℝ)..1, g y * prolateSLAction c f y
      = ∫ y in (-1 : ℝ)..1, f y * prolateSLAction c g y := by
  have hfc : Continuous f := hf1.continuous
  have hgc : Continuous g := hg1.continuous
  have hf'c : Continuous (deriv f) := hf2.continuous
  have hg'c : Continuous (deriv g) := hg2.continuous
  have hAf : IntervalIntegrable
      (fun y => g y * (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hBf : IntervalIntegrable (fun y => g y * (c ^ 2 * y ^ 2 * f y)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hAg : IntervalIntegrable
      (fun y => f y * (-(2 * y) * deriv g y + (1 - y ^ 2) * deriv (deriv g) y))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hBg : IntervalIntegrable (fun y => f y * (c ^ 2 * y ^ 2 * g y)) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsplitf : ∫ y in (-1 : ℝ)..1, g y * prolateSLAction c f y
      = (∫ y in (-1 : ℝ)..1, g y * (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y))
        - ∫ y in (-1 : ℝ)..1, g y * (c ^ 2 * y ^ 2 * f y) := by
    rw [← intervalIntegral.integral_sub hAf hBf]
    exact intervalIntegral.integral_congr fun y _ => by
      simp only [prolateSLAction]; ring
  have hsplitg : ∫ y in (-1 : ℝ)..1, f y * prolateSLAction c g y
      = (∫ y in (-1 : ℝ)..1, f y * (-(2 * y) * deriv g y + (1 - y ^ 2) * deriv (deriv g) y))
        - ∫ y in (-1 : ℝ)..1, f y * (c ^ 2 * y ^ 2 * g y) := by
    rw [← intervalIntegral.integral_sub hAg hBg]
    exact intervalIntegral.integral_congr fun y _ => by
      simp only [prolateSLAction]; ring
  have hibpf := band_flux_integral_by_parts hf2 hf2c hg1 hg'c
  have hibpg := band_flux_integral_by_parts hg2 hg2c hf1 hf'c
  have hcross : ∫ y in (-1 : ℝ)..1, deriv g y * ((1 - y ^ 2) * deriv f y)
      = ∫ y in (-1 : ℝ)..1, deriv f y * ((1 - y ^ 2) * deriv g y) :=
    intervalIntegral.integral_congr fun y _ => by ring
  have hmul : ∫ y in (-1 : ℝ)..1, g y * (c ^ 2 * y ^ 2 * f y)
      = ∫ y in (-1 : ℝ)..1, f y * (c ^ 2 * y ^ 2 * g y) :=
    intervalIntegral.integral_congr fun y _ => by ring
  rw [hsplitf, hibpf, hcross, hmul, ← hibpg, ← hsplitg]

/-- Local form of the band integration by parts: differentiability is required only on a set
containing the band.  This is the form usable with kernels that are singular away from the
band. -/
theorem band_flux_integral_by_parts_on {f g : ℝ → ℝ} {U : Set ℝ}
    (hUI : Set.uIcc (-1 : ℝ) 1 ⊆ U)
    (hf2 : ∀ y ∈ U, DifferentiableAt ℝ (deriv f) y)
    (hf2c : ContinuousOn (deriv (deriv f)) U)
    (hg1 : ∀ y ∈ U, DifferentiableAt ℝ g y)
    (hg2 : ∀ y ∈ U, DifferentiableAt ℝ (deriv g) y) :
    ∫ y in (-1 : ℝ)..1, g y * (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y)
      = -∫ y in (-1 : ℝ)..1, deriv g y * ((1 - y ^ 2) * deriv f y) := by
  have hu : ∀ y ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt g (deriv g y) y :=
    fun y hy => (hg1 y (hUI hy)).hasDerivAt
  have hv : ∀ y ∈ Set.uIcc (-1 : ℝ) 1, HasDerivAt (fun t => (1 - t ^ 2) * deriv f t)
      (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y) y :=
    fun y hy => hasDerivAt_bandFlux (hf2 y (hUI hy))
  have hg'on : ContinuousOn (deriv g) (Set.uIcc (-1 : ℝ) 1) :=
    fun y hy => ((hg2 y (hUI hy)).continuousAt).continuousWithinAt
  have hf'on : ContinuousOn (deriv f) (Set.uIcc (-1 : ℝ) 1) :=
    fun y hy => ((hf2 y (hUI hy)).continuousAt).continuousWithinAt
  have hu' : IntervalIntegrable (deriv g) volume (-1) 1 := hg'on.intervalIntegrable
  have hv' : IntervalIntegrable
      (fun y => -(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    exact (((continuous_const.mul continuous_id).neg.continuousOn).mul hf'on).add
      (((continuous_const.sub (continuous_pow 2)).continuousOn).mul (hf2c.mono hUI))
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simp only [] at h
  rw [h]
  norm_num

/-- Local form of the band self-adjointness of the prolate operator: hypotheses only on a set
containing the band. -/
theorem prolateSLAction_band_symmetric_on {f g : ℝ → ℝ} {U : Set ℝ}
    (hUI : Set.uIcc (-1 : ℝ) 1 ⊆ U)
    (hf1 : ∀ y ∈ U, DifferentiableAt ℝ f y)
    (hf2 : ∀ y ∈ U, DifferentiableAt ℝ (deriv f) y)
    (hf2c : ContinuousOn (deriv (deriv f)) U)
    (hg1 : ∀ y ∈ U, DifferentiableAt ℝ g y)
    (hg2 : ∀ y ∈ U, DifferentiableAt ℝ (deriv g) y)
    (hg2c : ContinuousOn (deriv (deriv g)) U) (c : ℝ) :
    ∫ y in (-1 : ℝ)..1, g y * prolateSLAction c f y
      = ∫ y in (-1 : ℝ)..1, f y * prolateSLAction c g y := by
  have hfon : ContinuousOn f (Set.uIcc (-1 : ℝ) 1) :=
    fun y hy => ((hf1 y (hUI hy)).continuousAt).continuousWithinAt
  have hgon : ContinuousOn g (Set.uIcc (-1 : ℝ) 1) :=
    fun y hy => ((hg1 y (hUI hy)).continuousAt).continuousWithinAt
  have hf'on : ContinuousOn (deriv f) (Set.uIcc (-1 : ℝ) 1) :=
    fun y hy => ((hf2 y (hUI hy)).continuousAt).continuousWithinAt
  have hg'on : ContinuousOn (deriv g) (Set.uIcc (-1 : ℝ) 1) :=
    fun y hy => ((hg2 y (hUI hy)).continuousAt).continuousWithinAt
  have hAf : IntervalIntegrable
      (fun y => g y * (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y))
      volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    exact hgon.mul ((((continuous_const.mul continuous_id).neg.continuousOn).mul hf'on).add
      (((continuous_const.sub (continuous_pow 2)).continuousOn).mul (hf2c.mono hUI)))
  have hBf : IntervalIntegrable (fun y => g y * (c ^ 2 * y ^ 2 * f y)) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    exact hgon.mul (((continuous_const.mul (continuous_pow 2)).continuousOn).mul hfon)
  have hAg : IntervalIntegrable
      (fun y => f y * (-(2 * y) * deriv g y + (1 - y ^ 2) * deriv (deriv g) y))
      volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    exact hfon.mul ((((continuous_const.mul continuous_id).neg.continuousOn).mul hg'on).add
      (((continuous_const.sub (continuous_pow 2)).continuousOn).mul (hg2c.mono hUI)))
  have hBg : IntervalIntegrable (fun y => f y * (c ^ 2 * y ^ 2 * g y)) volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable
    exact hfon.mul (((continuous_const.mul (continuous_pow 2)).continuousOn).mul hgon)
  have hsplitf : ∫ y in (-1 : ℝ)..1, g y * prolateSLAction c f y
      = (∫ y in (-1 : ℝ)..1, g y * (-(2 * y) * deriv f y + (1 - y ^ 2) * deriv (deriv f) y))
        - ∫ y in (-1 : ℝ)..1, g y * (c ^ 2 * y ^ 2 * f y) := by
    rw [← intervalIntegral.integral_sub hAf hBf]
    exact intervalIntegral.integral_congr fun y _ => by
      simp only [prolateSLAction]; ring
  have hsplitg : ∫ y in (-1 : ℝ)..1, f y * prolateSLAction c g y
      = (∫ y in (-1 : ℝ)..1, f y * (-(2 * y) * deriv g y + (1 - y ^ 2) * deriv (deriv g) y))
        - ∫ y in (-1 : ℝ)..1, f y * (c ^ 2 * y ^ 2 * g y) := by
    rw [← intervalIntegral.integral_sub hAg hBg]
    exact intervalIntegral.integral_congr fun y _ => by
      simp only [prolateSLAction]; ring
  have hibpf := band_flux_integral_by_parts_on hUI hf2 hf2c hg1 hg2
  have hibpg := band_flux_integral_by_parts_on hUI hg2 hg2c hf1 hf2
  have hcross : ∫ y in (-1 : ℝ)..1, deriv g y * ((1 - y ^ 2) * deriv f y)
      = ∫ y in (-1 : ℝ)..1, deriv f y * ((1 - y ^ 2) * deriv g y) :=
    intervalIntegral.integral_congr fun y _ => by ring
  have hmul : ∫ y in (-1 : ℝ)..1, g y * (c ^ 2 * y ^ 2 * f y)
      = ∫ y in (-1 : ℝ)..1, f y * (c ^ 2 * y ^ 2 * g y) :=
    intervalIntegral.integral_congr fun y _ => by ring
  rw [hsplitf, hibpf, hcross, hmul, ← hibpg, ← hsplitg]

end RHTower
