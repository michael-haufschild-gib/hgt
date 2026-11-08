import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorEndpointResidues

/-!
# Inverse-Mellin residue of the averaged Narain source

The shifted main-pole numerator is analytic at one. Its value and
derivative determine the exact logarithmic and constant heat terms.
-/

open Complex RHTower Set Filter Topology
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

private theorem shifted_mean_analytic (Y Z : Height) :
    AnalyticAt ℂ (fun s : ℂ => narainMeanMainPoleNumerator Y Z (s - 1 / 2)) 1 := by
  have hA := analyticAt_narainMeanMainPoleNumerator Y Z (u := 1 / 2)
    (by norm_num [xi_two_ne_zero])
  have hshift : AnalyticAt ℂ (fun s : ℂ => s - 1 / 2) 1 := by fun_prop
  exact AnalyticAt.comp (g := narainMeanMainPoleNumerator Y Z)
    (f := fun s : ℂ => s - 1 / 2) (x := 1)
    (by rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]; exact hA) hshift

private theorem shifted_mean_deriv (Y Z : Height) :
    deriv (fun s : ℂ => narainMeanMainPoleNumerator Y Z (s - 1 / 2)) 1 =
      narainAverageConstant Y Z := by
  have hA := analyticAt_narainMeanMainPoleNumerator Y Z (u := 1 / 2)
    (by norm_num [xi_two_ne_zero])
  have hd : HasDerivAt (narainMeanMainPoleNumerator Y Z) (narainAverageConstant Y Z)
      (1 - 1 / 2 : ℂ) := by
    rw [show (1 : ℂ) - 1 / 2 = 1 / 2 by ring]
    exact hA.differentiableAt.hasDerivAt
  have hb := hd.comp 1 ((hasDerivAt_id (1 : ℂ)).sub_const (1 / 2))
  convert! hb.deriv using 1
  simp only [mul_one]

private theorem mean_eq_shifted_quotient (Y Z : Height) {s : ℂ} (hs : s ≠ 1) :
    narainMellinMean Y Z (s - 1 / 2) =
      narainMeanMainPoleNumerator Y Z (s - 1 / 2) / (s - 1) ^ 2 := by
  have hs0 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have htwo : 2 * (s - 1 / 2) - 1 ≠ 0 := by
    intro h
    apply hs
    linear_combination h / 2
  apply (eq_div_iff (pow_ne_zero 2 hs0)).mpr
  rw [narainMeanMainPoleNumerator_eq Y Z htwo]
  ring

/-- The double pole contributes exactly the logarithmic and constant heat main terms. -/
theorem narainMellinMean_weighted_residue (Y Z : Height) {y : ℝ} (hy : 0 < y) :
    laurentCoeff (fun s : ℂ => (y : ℂ) ^ (-s) * narainMellinMean Y Z (s - 1 / 2)) 1 (-1) =
      (y : ℂ) ^ (-1 : ℂ) *
        (narainAverageConstant Y Z - (3 / (Real.pi : ℂ)) * (Real.log y : ℂ)) := by
  have hw : AnalyticAt ℂ (fun s : ℂ => (y : ℂ) ^ (-s)) 1 := by
    have hd : Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ (-s)) :=
      (by fun_prop : Differentiable ℂ (fun s : ℂ => -s)).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))
    exact hd.analyticAt 1
  have hd : AnalyticAt ℂ (fun s : ℂ => (s - 1) ^ 2) 1 := by fun_prop
  have hm : MeromorphicAt (fun s : ℂ => (y : ℂ) ^ (-s) *
      (narainMeanMainPoleNumerator Y Z (s - 1 / 2) / (s - 1) ^ 2)) 1 :=
    hw.meromorphicAt.mul ((shifted_mean_analytic Y Z).meromorphicAt.div hd.meromorphicAt)
  have heq : (fun s : ℂ => (y : ℂ) ^ (-s) * narainMellinMean Y Z (s - 1 / 2))
      =ᶠ[𝓝[≠] (1 : ℂ)] (fun s : ℂ => (y : ℂ) ^ (-s) *
        (narainMeanMainPoleNumerator Y Z (s - 1 / 2) / (s - 1) ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [mean_eq_shifted_quotient Y Z hs]
  calc
    _ = laurentCoeff (fun s : ℂ => (y : ℂ) ^ (-s) *
        (narainMeanMainPoleNumerator Y Z (s - 1 / 2) / (s - 1) ^ 2)) 1 (-1) :=
      (laurentCoeff_congr hm heq.symm (-1)).symm
    _ = _ := by
      rw [WeilHigherDenominator.laurentCoeff_mellin_doublePole (shifted_mean_analytic Y Z) hy,
        shifted_mean_deriv, show (1 : ℂ) - 1 / 2 = 1 / 2 by ring,
        narainMeanMainPoleNumerator_half]

#print axioms narainMellinMean_weighted_residue
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
