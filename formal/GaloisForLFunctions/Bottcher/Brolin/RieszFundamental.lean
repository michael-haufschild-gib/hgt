/-
# Böttcher tower — Brolin GAP-A: the Riesz / fundamental-solution core

GAP-A of the Brolin program asks for the global identification
`μ_c = (2π)⁻¹ Δ G_c` (the equilibrium/Brolin measure is the distributional
Laplacian of the dynamical Green function).  Mathlib has no Riesz / subharmonic
/ Laplacian-as-measure theory, so this file builds it from the fundamental
solution of the planar Laplacian.

## Interface correction (verified defect in `IsRieszMeasureOf`)

`Brolin.Basic.IsRieszMeasureOf μ u` tests the identity
`∫ φ dμ = (2π)⁻¹ ∫ u · Δφ` against **every** `φ : C_c(ℂ,ℝ)` — merely continuous.
But Mathlib's `Δ` is `iteratedFDeriv ℝ 2`-based, so `Δφ = 0` wherever `φ` fails
to be `C²`.  For a non-`C²` test function (e.g. a continuous tent) the right-hand
side collapses to `0` while `∫ φ dμ > 0`, so the identity is **false**.  Taking
`μ = δ₀`, `u = log‖·‖`, `φ` a tent already refutes `IsRieszMeasureOf δ₀ log‖·‖`.
Hence `IsRieszMeasureOf` (and `IsBrolinMeasure`, `BrolinMeasure`) is too strong to
be inhabited by the genuine Brolin measure: it can never be discharged as written.

The dischargeable statement restricts the test class to `C²` compactly supported
functions.  That is `IsRieszMeasureOfSmooth` below, and it is exactly what the
support theorem needs (a smooth `φ` supported in a `μ`-null ball forces
`∫ G · Δφ = 0`, i.e. `ΔG = 0` there weakly, i.e. `G` harmonic — Weyl).

## Route to GAP-A (constraint, not flow)

* `FundamentalSolutionProp` — the atomic identity
  `∫ log‖z-ρ‖ · Δφ(z) dz = 2π · φ(ρ)` for `C²` compact-support `φ`.  This is the
  2D Newtonian potential / Green's identity.  The polar reduction step toward it
  is `integral_log_norm_mul_eq_polar` (banked here).
* From it, `isRieszMeasureOfSmooth_dirac` gives the atomic Riesz identity
  `δ_ρ = (2π)⁻¹ Δ log‖·-ρ‖`.
* Level-`n` pullback measures are finite averages of such Diracs, with potential
  `greenApprox_n = -logPotential μ_n`; linearity gives the level-`n` Riesz
  identity.
* `greenApprox_n → G_c` (locally uniformly) passes the identity to the limit
  `μ_c = (2π)⁻¹ Δ G_c`, i.e. `IsRieszMeasureOfSmooth μ_c G_c`.
-/
import GaloisForLFunctions.Bottcher.Brolin.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.MeasureTheory.Group.Integral

open Filter Topology MeasureTheory CompactlySupported Laplacian InnerProductSpace
open scoped Laplacian

namespace Bottcher

noncomputable section

local instance rieszFundamentalLocalInst1 : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- **Corrected distributional Riesz condition.** `IsRieszMeasureOfSmooth μ u`
means `μ = (2π)⁻¹ Δu` tested against `C²` compactly supported functions — the
honestly dischargeable relaxation of `Brolin.Basic.IsRieszMeasureOf`, whose
continuous test class makes it false for the genuine Brolin measure (see the
module docstring). -/
def IsRieszMeasureOfSmooth (μ : Measure ℂ) (u : ℂ → ℝ) : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
    ∫ z, φ z ∂μ = (2 * Real.pi)⁻¹ * ∫ z, u z * (Δ φ) z

/-- **The planar fundamental-solution identity.** `∫ log‖z-ρ‖ · Δφ(z) dz = 2π·φ(ρ)`
for every `C²` compactly supported `φ`.  This is the atomic content of GAP-A:
`(2π)⁻¹ Δ log‖·-ρ‖ = δ_ρ` distributionally. -/
def FundamentalSolutionProp : Prop :=
  ∀ (ρ : ℂ) (φ : ℂ → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
    ∫ z, Real.log ‖z - ρ‖ * (Δ φ) z = 2 * Real.pi * φ ρ

/-- Smoothness is preserved by right translation. -/
theorem contDiff_comp_add_right (φ : ℂ → ℝ) (ρ : ℂ) {n : ℕ∞}
    (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (fun x => φ (x + ρ)) :=
  hφ.comp (contDiff_id.add contDiff_const)

/-- Compact support is preserved by right translation. -/
theorem hasCompactSupport_comp_add_right (φ : ℂ → ℝ) (ρ : ℂ)
    (hφc : HasCompactSupport φ) : HasCompactSupport (fun x => φ (x + ρ)) := by
  have : HasCompactSupport (φ ∘ (fun x => x + ρ)) :=
    hφc.comp_homeomorph (Homeomorph.addRight ρ)
  rw [show (fun x => φ (x + ρ)) = φ ∘ fun x => x + ρ by rfl]
  exact this

/-- **Polar reduction of the log-weighted integral** (the first analytic step
toward `FundamentalSolutionProp`, banked and verified).  The planar integral of
`log‖z‖ · g(z)` becomes the `(r,θ)` integral of `r · log r · g` over
`polarCoord.target = Ioi 0 ×ˢ Ioo (-π) π`, where `log r = log|p.1|`. -/
theorem integral_log_norm_mul_eq_polar (g : ℂ → ℝ) :
    (∫ z, Real.log ‖z‖ * g z) =
      ∫ p in polarCoord.target,
        p.1 * (Real.log |p.1| * g (Complex.polarCoord.symm p)) := by
  rw [← Complex.integral_comp_polarCoord_symm (fun z => Real.log ‖z‖ * g z)]
  refine setIntegral_congr_fun polarCoord.open_target.measurableSet ?_
  intro p hp
  simp only [smul_eq_mul, Complex.norm_polarCoord_symm]

/-- **Atomic Riesz identity.** Under the fundamental-solution identity, the Dirac
mass at `ρ` is `(2π)⁻¹ Δ` of the log kernel `log‖·-ρ‖`. -/
theorem isRieszMeasureOfSmooth_dirac (hfund : FundamentalSolutionProp) (ρ : ℂ) :
    IsRieszMeasureOfSmooth (Measure.dirac ρ) (fun z => Real.log ‖z - ρ‖) := by
  intro φ hφ hφc
  rw [integral_dirac φ ρ, hfund ρ φ hφ hφc]
  have h2π : (2 * Real.pi) ≠ 0 := ne_of_gt Real.two_pi_pos
  field_simp

/-- **The Laplacian commutes with translation.** `Δ (φ(·+ρ)) = (Δφ)(·+ρ)`. -/
theorem laplacian_comp_add_right (φ : ℂ → ℝ) (ρ : ℂ) :
    Δ (fun x => φ (x + ρ)) = fun x => (Δ φ) (x + ρ) := by
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_comp_add_right']

/-- **Reduction to the centered fundamental solution.** The full identity
`FundamentalSolutionProp` follows from its `ρ = 0` case
`∫ log‖z‖ · Δφ = 2π·φ(0)`, by translation invariance of Lebesgue measure and of
the Laplacian.  This collapses GAP-A's atomic content to a single centered
statement. -/
theorem fundamentalSolutionProp_of_center
    (h0 : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      ∫ z, Real.log ‖z‖ * (Δ φ) z = 2 * Real.pi * φ 0) :
    FundamentalSolutionProp := by
  intro ρ φ hφ hφc
  have hψ : ContDiff ℝ 2 (fun x => φ (x + ρ)) := contDiff_comp_add_right φ ρ hφ
  have hψc : HasCompactSupport (fun x => φ (x + ρ)) := hasCompactSupport_comp_add_right φ ρ hφc
  have key := h0 (fun x => φ (x + ρ)) hψ hψc
  rw [laplacian_comp_add_right] at key
  simp only [zero_add] at key
  rw [← key]
  have hsub := (integral_add_right_eq_self (μ := volume)
    (fun z => Real.log ‖z - ρ‖ * (Δ φ) z) ρ).symm
  rw [hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro z
  simp only [add_sub_cancel_right]

end

end Bottcher
