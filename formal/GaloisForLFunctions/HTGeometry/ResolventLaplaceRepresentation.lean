import GaloisForLFunctions.HTGeometry.AccretiveSemigroupDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The shifted resolvent is the Laplace transform of the semigroup

With a numerical floor `μ` on `B` and a shift `L` with `μ + L > 0`, the orbit
`s ↦ e^{-Ls} e^{-sB} u` decays like `e^{-(μ+L)s}`, so it is integrable on the ray, and it solves

`v'(s) = −(B + L)v(s)`,   `v(0) = u`,   `v(s) → 0`.

Integrating the equation over the ray and moving the bounded operator through the Bochner integral
gives

`(B + L)⁻¹u = ∫₀^∞ e^{-Ls} e^{-sB} u ds`.

The representation is what turns a resolvent bound into a *rate*: the `s`-integrand factors the
shift `e^{-Ls}` away from the operator, so a shift that grows with a parameter contributes an
exponential gain rather than a mere reciprocal.
-/

open MeasureTheory Set Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The Laplace orbit whose integral represents the shifted resolvent. -/
def resolventOrbit (B : X →L[ℂ] X) (L : ℝ) (u : X) (s : ℝ) : X :=
  Real.exp (-(L * s)) • accretiveSemigroup B s u

omit [CompleteSpace X] in
theorem resolventOrbit_zero (B : X →L[ℂ] X) (L : ℝ) (u : X) :
    resolventOrbit B L u 0 = u := by
  rw [resolventOrbit, accretiveSemigroup_zero]
  simp

theorem norm_resolventOrbit_le {B : X →L[ℂ] X} {μ : ℝ}
    (hB : ∀ u : X, μ * ‖u‖ ^ 2 ≤ (inner ℂ (B u) u).re) (L : ℝ) (u : X) {s : ℝ} (hs : 0 ≤ s) :
    ‖resolventOrbit B L u s‖ ≤ Real.exp (-((μ + L) * s)) * ‖u‖ := by
  have hbase := norm_accretiveSemigroup_apply_le hB u hs
  rw [resolventOrbit, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-(L * s)) * ‖accretiveSemigroup B s u‖
      ≤ Real.exp (-(L * s)) * (Real.exp (-(μ * s)) * ‖u‖) :=
        mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = Real.exp (-((μ + L) * s)) * ‖u‖ := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring

/-- **The orbit solves the shifted equation.** -/
theorem hasDerivAt_resolventOrbit (B : X →L[ℂ] X) (L : ℝ) (u : X) (s : ℝ) :
    HasDerivAt (resolventOrbit B L u)
      (-((B + (L : ℂ) • ContinuousLinearMap.id ℂ X) (resolventOrbit B L u s))) s := by
  have hexp : HasDerivAt (fun r : ℝ => Real.exp (-(L * r))) (Real.exp (-(L * s)) * (-L)) s := by
    have h1 : HasDerivAt (fun r : ℝ => -(L * r)) (-L) s := by
      have h0 : HasDerivAt (fun r : ℝ => (-L) * r) ((-L) * 1) s := (hasDerivAt_id s).const_mul (-L)
      simpa [neg_mul] using h0
    simpa [mul_comm] using h1.exp
  have hsg : HasDerivAt (fun t : ℝ => accretiveSemigroup B t u)
      (-(B (accretiveSemigroup B s u))) s := hasDerivAt_accretiveSemigroup_apply B u s
  have hprod := hexp.smul hsg
  refine hprod.congr_deriv ?_
  have hexpand : (B + (L : ℂ) • ContinuousLinearMap.id ℂ X) (resolventOrbit B L u s)
      = B (resolventOrbit B L u s) + L • resolventOrbit B L u s := by
    simp [Complex.coe_smul]
  rw [hexpand, resolventOrbit]
  rw [ContinuousLinearMap.map_smul_of_tower]
  module

theorem continuous_resolventOrbit (B : X →L[ℂ] X) (L : ℝ) (u : X) :
    Continuous (resolventOrbit B L u) :=
  continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_resolventOrbit B L u s).continuousAt

/-- **The orbit is integrable on the ray.** -/
theorem integrableOn_resolventOrbit {B : X →L[ℂ] X} {μ L : ℝ}
    (hB : ∀ u : X, μ * ‖u‖ ^ 2 ≤ (inner ℂ (B u) u).re) (hgap : 0 < μ + L) (u : X) :
    IntegrableOn (resolventOrbit B L u) (Ioi (0 : ℝ)) volume := by
  have hmaj : IntegrableOn (fun s : ℝ => Real.exp (-(μ + L) * s) * ‖u‖)
      (Ioi (0 : ℝ)) volume :=
    (exp_neg_integrableOn_Ioi 0 hgap).mul_const ‖u‖
  refine Integrable.mono' hmaj
    ((continuous_resolventOrbit B L u).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hbase := norm_resolventOrbit_le hB L u (le_of_lt hs)
  calc ‖resolventOrbit B L u s‖ ≤ Real.exp (-((μ + L) * s)) * ‖u‖ := hbase
    _ = Real.exp (-(μ + L) * s) * ‖u‖ := by
        congr 2
        ring

/-- **The orbit vanishes at infinity.** -/
theorem tendsto_resolventOrbit {B : X →L[ℂ] X} {μ L : ℝ}
    (hB : ∀ u : X, μ * ‖u‖ ^ 2 ≤ (inner ℂ (B u) u).re) (hgap : 0 < μ + L) (u : X) :
    Filter.Tendsto (resolventOrbit B L u) Filter.atTop (nhds 0) := by
  have hzero : Filter.Tendsto (fun s : ℝ => Real.exp (-((μ + L) * s)) * ‖u‖)
      Filter.atTop (nhds 0) := by
    have hinner : Filter.Tendsto (fun s : ℝ => -((μ + L) * s)) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp
        (Filter.Tendsto.const_mul_atTop hgap Filter.tendsto_id)
    have := Real.tendsto_exp_atBot.comp hinner
    simpa using this.mul_const ‖u‖
  refine squeeze_zero_norm' ?_ hzero
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with s hs
  exact norm_resolventOrbit_le hB L u hs

/-- **The shifted resolvent is the Laplace transform of the semigroup.** -/
theorem resolvent_integral_apply {B : X →L[ℂ] X} {μ L : ℝ}
    (hB : ∀ u : X, μ * ‖u‖ ^ 2 ≤ (inner ℂ (B u) u).re) (hgap : 0 < μ + L) (u : X) :
    (B + (L : ℂ) • ContinuousLinearMap.id ℂ X)
        (∫ s in Ioi (0 : ℝ), resolventOrbit B L u s) = u := by
  set A : X →L[ℂ] X := B + (L : ℂ) • ContinuousLinearMap.id ℂ X with hA
  set AR : X →L[ℝ] X := A.restrictScalars ℝ with hAR
  have hint : IntegrableOn (resolventOrbit B L u) (Ioi (0 : ℝ)) volume :=
    integrableOn_resolventOrbit hB hgap u
  have hAeq : ∀ x : X, AR x = A x := fun _ => rfl
  have hint' : IntegrableOn (fun s : ℝ => -(A (resolventOrbit B L u s)))
      (Ioi (0 : ℝ)) volume := by
    have h1 : IntegrableOn (fun s : ℝ => AR (resolventOrbit B L u s)) (Ioi (0 : ℝ)) volume :=
      AR.integrable_comp hint
    exact h1.neg
  have hderiv : ∀ s ∈ Ioi (0 : ℝ),
      HasDerivAt (resolventOrbit B L u) (-(A (resolventOrbit B L u s))) s :=
    fun s _ => hasDerivAt_resolventOrbit B L u s
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    ((continuous_resolventOrbit B L u).continuousWithinAt) hderiv hint'
    (tendsto_resolventOrbit hB hgap u)
  rw [resolventOrbit_zero] at hFTC
  have hcomm : (∫ s in Ioi (0 : ℝ), A (resolventOrbit B L u s))
      = A (∫ s in Ioi (0 : ℝ), resolventOrbit B L u s) := by
    have := ContinuousLinearMap.integral_comp_comm AR hint
    simpa [hAeq] using this
  have hneg : (∫ s in Ioi (0 : ℝ), -(A (resolventOrbit B L u s)))
      = -(∫ s in Ioi (0 : ℝ), A (resolventOrbit B L u s)) := integral_neg _
  rw [hneg, hcomm] at hFTC
  have : -A (∫ s in Ioi (0 : ℝ), resolventOrbit B L u s) = 0 - u := hFTC
  linear_combination (norm := module) -this

end GaloisForLFunctions.HTGeometry
