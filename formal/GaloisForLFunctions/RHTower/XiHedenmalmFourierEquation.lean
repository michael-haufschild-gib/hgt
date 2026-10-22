import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspSchwartzFourierXi
import GaloisForLFunctions.RHTower.XiWeilPolarization

/-!
# The exact Fourier equation behind the Hedenmalm theta eigenfunction

The normalized theta-cusp Schwartz source has Fourier transform `XiC` on the real axis. For every
centered Xi zero `alpha`, the removable entire quotient `xiThetaEigenFourier alpha` solves

`(alpha - z) U(z) = -I * XiC z`.

It is the unique continuous solution of that equation on the whole complex plane. Thus the
vectors used in the Hedenmalm eigenbasis and completion files are the unique regular Fourier-side
solutions of the concrete theta-source equation, rather than an abstract family of divided
differences.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- The removable Hedenmalm quotient is continuous on the whole complex plane. -/
theorem continuous_xiThetaEigenFourier (alpha : ℂ) :
    Continuous (xiThetaEigenFourier alpha) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact (xiThetaEigenFourier_analytic alpha z (Set.mem_univ z)).continuousAt

/-- The removable quotient as a continuous complex function. -/
def xiThetaEigenFourierContinuous (alpha : ℂ) : C(ℂ, ℂ) :=
  ⟨xiThetaEigenFourier alpha, continuous_xiThetaEigenFourier alpha⟩

/-- Continuous solutions of the transformed theta-source equation at spectral parameter
`alpha`. -/
def xiThetaFourierSolutionSet (alpha : ℂ) : Set C(ℂ, ℂ) :=
  {U | ∀ z : ℂ, (alpha - z) * U z = -I * XiC z}

/-- The removable quotient satisfies the transformed equation at every complex frequency,
including the removed point. -/
theorem xiThetaEigenFourier_equation
    {alpha : ℂ} (halpha : XiC alpha = 0) (z : ℂ) :
    (alpha - z) * xiThetaEigenFourier alpha z = -I * XiC z := by
  rw [xiThetaEigenFourier]
  have hfactor := sub_smul_dslope XiC alpha z
  rw [halpha, sub_zero, smul_eq_mul] at hfactor
  calc
    (alpha - z) * (I * dslope XiC alpha z) =
        -I * ((z - alpha) * dslope XiC alpha z) := by ring
    _ = -I * XiC z := by rw [hfactor]

/-- Exact regular-solution law: at a centered Xi zero, the continuous solution set of the
transformed Hedenmalm equation is the singleton containing the removable quotient. -/
theorem xiThetaFourierSolutionSet_eq_singleton
    {alpha : ℂ} (halpha : XiC alpha = 0) :
    xiThetaFourierSolutionSet alpha = {xiThetaEigenFourierContinuous alpha} := by
  ext U
  constructor
  · intro hU
    simp only [Set.mem_singleton_iff]
    apply ContinuousMap.ext
    have hfun : (U : ℂ → ℂ) = xiThetaEigenFourier alpha := by
      apply Continuous.ext_on (dense_compl_singleton alpha)
        U.continuous (continuous_xiThetaEigenFourier alpha)
      intro z hz
      have hne : z ≠ alpha := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
      have hcoef : alpha - z ≠ 0 := sub_ne_zero.mpr hne.symm
      apply mul_left_cancel₀ hcoef
      exact (hU z).trans (xiThetaEigenFourier_equation halpha z).symm
    exact congrFun hfun
  · intro hU
    simp only [Set.mem_singleton_iff] at hU
    subst U
    exact xiThetaEigenFourier_equation halpha

/-- On the real frequency axis the equation is driven by the Fourier transform of the concrete
theta-cusp Schwartz source. -/
theorem xiThetaEigenFourier_real_source_equation
    {alpha : ℂ} (halpha : XiC alpha = 0) (t : ℝ) :
    (alpha - (t : ℂ)) * xiThetaEigenFourier alpha (t : ℂ) =
      -I * (𝓕 xiThetaSchwartzSource) t := by
  rw [fourier_xiThetaSchwartzSource]
  exact xiThetaEigenFourier_equation halpha (t : ℂ)

end RHTower
