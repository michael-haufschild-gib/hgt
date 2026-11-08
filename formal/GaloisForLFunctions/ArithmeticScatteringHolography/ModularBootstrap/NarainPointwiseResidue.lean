import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainPrincipalPart
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorEndpointResidues

/-!
# Inverse-Mellin residue of the pointwise Narain source

The shifted main-pole numerator is analytic at one. Its value and
derivative determine the exact logarithmic and constant heat terms.
-/

open Complex RHTower Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private theorem shifted_source_analytic (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    AnalyticAt ℂ (fun s : ℂ => narainMainPoleNumerator ρ σ (s - 1 / 2)) 1 := by
  have hA := analyticAt_narainMainPoleNumerator ρ σ (u := 1 / 2)
    (by norm_num [xi_two_ne_zero])
  have hshift : AnalyticAt ℂ (fun s : ℂ => s - 1 / 2) 1 := by fun_prop
  exact AnalyticAt.comp (g := narainMainPoleNumerator ρ σ)
    (f := fun s : ℂ => s - 1 / 2) (x := 1)
    (by rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]; exact hA) hshift

private theorem shifted_source_deriv (ρ σ : D4BMUpperHalfPlaneCoordinate) :
    deriv (fun s : ℂ => narainMainPoleNumerator ρ σ (s - 1 / 2)) 1 =
      narainScalarConstant ρ σ := by
  have hA := analyticAt_narainMainPoleNumerator ρ σ (u := 1 / 2)
    (by norm_num [xi_two_ne_zero])
  have hd : HasDerivAt (narainMainPoleNumerator ρ σ) (narainScalarConstant ρ σ)
      (1 - 1 / 2 : ℂ) := by
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]
    exact hA.differentiableAt.hasDerivAt
  have hb := hd.comp 1 ((hasDerivAt_id (1 : ℂ)).sub_const (1 / 2))
  convert! hb.deriv using 1
  simp only [mul_one]

private theorem source_eq_shifted_quotient (ρ σ : D4BMUpperHalfPlaneCoordinate) {s : ℂ} (hs : s ≠ 1) :
    narainMellinContinuation ρ σ (s - 1 / 2) =
      narainMainPoleNumerator ρ σ (s - 1 / 2) / (s - 1) ^ 2 := by
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have htwo : 2 * (s - 1 / 2) - 1 ≠ 0 := by
    intro h
    apply hs
    linear_combination h / 2
  apply (eq_div_iff (pow_ne_zero 2 hs0)).mpr
  rw [narainMainPoleNumerator_eq ρ σ htwo]
  ring

/-- The double pole contributes exactly the logarithmic and constant heat main terms. -/
theorem narainMellinContinuation_weighted_residue (ρ σ : D4BMUpperHalfPlaneCoordinate) {y : ℝ} (hy : 0 < y) :
    laurentCoeff (fun s : ℂ => (y : ℂ) ^ (-s) * narainMellinContinuation ρ σ (s - 1 / 2)) 1 (-1) =
      (y : ℂ) ^ (-1 : ℂ) *
        (narainScalarConstant ρ σ - (3 / (Real.pi : ℂ)) * (Real.log y : ℂ)) := by
  have hw : AnalyticAt ℂ (fun s : ℂ => (y : ℂ) ^ (-s)) 1 := by
    have hd : Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ (-s)) :=
      (by fun_prop : Differentiable ℂ (fun s : ℂ => -s)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
    exact hd.analyticAt 1
  have hd : AnalyticAt ℂ (fun s : ℂ => (s - 1) ^ 2) 1 := by fun_prop
  have hm : MeromorphicAt (fun s : ℂ => (y : ℂ) ^ (-s) *
      (narainMainPoleNumerator ρ σ (s - 1 / 2) / (s - 1) ^ 2)) 1 :=
    hw.meromorphicAt.mul ((shifted_source_analytic ρ σ).meromorphicAt.div hd.meromorphicAt)
  have heq : (fun s : ℂ => (y : ℂ) ^ (-s) * narainMellinContinuation ρ σ (s - 1 / 2))
      =ᶠ[𝓝[≠] (1 : ℂ)] (fun s : ℂ => (y : ℂ) ^ (-s) *
        (narainMainPoleNumerator ρ σ (s - 1 / 2) / (s - 1) ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [source_eq_shifted_quotient ρ σ hs]
  calc
    _ = laurentCoeff (fun s : ℂ => (y : ℂ) ^ (-s) *
        (narainMainPoleNumerator ρ σ (s - 1 / 2) / (s - 1) ^ 2)) 1 (-1) :=
      (laurentCoeff_congr hm heq.symm (-1)).symm
    _ = _ := by
      rw [WeilHigherDenominator.laurentCoeff_mellin_doublePole (shifted_source_analytic ρ σ) hy,
        shifted_source_deriv, show (1 : ℂ) - 1 / 2 = 1 / 2 by ring,
        narainMainPoleNumerator_half]

#print axioms narainMellinContinuation_weighted_residue
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
