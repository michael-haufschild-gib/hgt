import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiGaussianSingularPoissonLift
import GaloisForLFunctions.RHTower.MFreeLadder

/-!
# Deninger--Meyer Möbius--Gaussian Neumann source

This module constructs the singular Poisson--Gaussian lift from literal arithmetic source data on
its absolute-convergence chamber.  The arithmetic factor is the `m = 1` Möbius `L`-series, not an
abstract reciprocal-zeta symbol.  The archimedean factor is the convergent Neumann series of the
Gaussian Mellin character.  If

`‖χ_c(s) χ_c(ρ)⁻¹‖ < 1` and `1 < re s`,

their product sums exactly to

`(ζ(s) (χ_c(ρ) - χ_c(s)))⁻¹`.

Thus a concrete source object exists before continuation to the critical strip.  The unresolved
Route-L theorem is now a precise continuation problem: extend this coefficient-faithful source
series in the singular Meyer/Gamma graph topology to Xi-zero fibres while retaining the simple
completed Green residue proved in `DeningerMeyerXiGaussianSingularPoissonLift`.
-/

open Complex Filter Topology Set Metric
open ArithmeticFunction LSeries
open scoped Real LSeries.notation Moebius ArithmeticFunction.zeta

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- Gaussian Neumann ratio between observation point `s` and resolvent base `rho`. -/
def mobiusGaussianNeumannRatio (c rho s : ℂ) : ℂ :=
  gaussianMellinCharacter c s * (gaussianMellinCharacter c rho)⁻¹

/--
Literal Möbius--Gaussian source series.  Its arithmetic coefficient is the `m = 1` power-supported
Möbius `L`-series; each Neumann level is a Gaussian convolution depth.
-/
def mobiusGaussianNeumannSource (c rho s : ℂ) : ℂ :=
  ∑' k : ℕ,
    (L ↗(mPart 1 (μ : ArithmeticFunction ℤ)) s) *
      (gaussianMellinCharacter c rho)⁻¹ *
        mobiusGaussianNeumannRatio c rho s ^ k

theorem summable_mobiusGaussianNeumannSource
    {c rho s : ℂ} (hratio : ‖mobiusGaussianNeumannRatio c rho s‖ < 1) :
    Summable (fun k : ℕ =>
      (L ↗(mPart 1 (μ : ArithmeticFunction ℤ)) s) *
        (gaussianMellinCharacter c rho)⁻¹ *
          mobiusGaussianNeumannRatio c rho s ^ k) := by
  exact (summable_geometric_of_norm_lt_one hratio).mul_left _

/-- On the safe chamber, the literal Möbius--Gaussian series is the singular Poisson lift. -/
theorem mobiusGaussianNeumannSource_eq_poissonGaussianSingularLift
    {c rho s : ℂ} (hs : 1 < s.re)
    (hratio : ‖mobiusGaussianNeumannRatio c rho s‖ < 1) :
    mobiusGaussianNeumannSource c rho s = poissonGaussianSingularLift c rho s := by
  have hmobius :
      L ↗(mPart 1 (μ : ArithmeticFunction ℤ)) s = (riemannZeta s)⁻¹ := by
    simpa using LSeries_mPart_moebius (m := 1) (by norm_num) (by simpa using hs)
  rw [mobiusGaussianNeumannSource, tsum_mul_left, tsum_geometric_of_norm_lt_one hratio,
    hmobius]
  rw [poissonGaussianSingularLift, gaussianResolventDenominator,
    mobiusGaussianNeumannRatio]
  have hchar : gaussianMellinCharacter c rho ≠ 0 := Complex.exp_ne_zero _
  have hzeta : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hratioNe :
      1 - gaussianMellinCharacter c s * (gaussianMellinCharacter c rho)⁻¹ ≠ 0 := by
    intro h
    have hone : (1 : ℂ) =
        gaussianMellinCharacter c s * (gaussianMellinCharacter c rho)⁻¹ :=
      sub_eq_zero.mp h
    have heq : gaussianMellinCharacter c s * (gaussianMellinCharacter c rho)⁻¹ = 1 :=
      hone.symm
    rw [mobiusGaussianNeumannRatio, heq, norm_one] at hratio
    exact (lt_irrefl 1 hratio)
  field_simp [hzeta, hchar, hratioNe]

/-- Exact summation law, retaining every Gaussian convolution depth. -/
theorem hasSum_mobiusGaussianNeumannSource
    {c rho s : ℂ} (hs : 1 < s.re)
    (hratio : ‖mobiusGaussianNeumannRatio c rho s‖ < 1) :
    HasSum (fun k : ℕ =>
      (L ↗(mPart 1 (μ : ArithmeticFunction ℤ)) s) *
        (gaussianMellinCharacter c rho)⁻¹ *
          mobiusGaussianNeumannRatio c rho s ^ k)
      (poissonGaussianSingularLift c rho s) := by
  rw [← mobiusGaussianNeumannSource_eq_poissonGaussianSingularLift hs hratio]
  exact (summable_mobiusGaussianNeumannSource hratio).hasSum

end
end DeningerMeyerGaussianGreen
end RHTower
