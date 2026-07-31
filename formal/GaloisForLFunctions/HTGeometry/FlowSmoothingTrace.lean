import GaloisForLFunctions.HTGeometry.UnitaryFlowSmoothing
import GaloisForLFunctions.HTGeometry.EigenbasisTrace

/-!
# The trace of a smoothed unitary flow

Combining the two halves already proved: a flow eigenvector is an eigenvector of every smoothing,
with eigenvalue the integral of the weight against the flow character, and the operator trace is
the sum of the eigenvalues over a diagonalizing basis.  Hence, whenever the canonical Hilbert
basis consists of flow eigenvectors,

`Tr K_φ = ∑ᵢ ∫ φ(t) χᵢ(t) dt`,

and for `χᵢ(t) = exp (i λᵢ t)` the summands are the values of the weight's Fourier transform at
the spectral points, each spectral point occurring once per basis vector carrying it.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory ContinuousLinearMap

section General

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [NormedSpace ℝ H] [CompleteSpace H] [SMulCommClass ℝ 𝕜 H] [IsScalarTower ℝ 𝕜 H]

/-- **Trace of a smoothing in a flow eigenbasis.**  Each basis vector contributes the integral of
the weight against its flow character. -/
theorem opTrace_flowSmoothing_eq_tsum_characterIntegral
    (U : UnitaryFlow 𝕜 H) (phi : ℝ → ℝ)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi)
    {chi : _ → ℝ → 𝕜}
    (hchar : ∀ i t, U.op t (hsBasis 𝕜 H i) = chi i t • hsBasis 𝕜 H i) :
    opTrace (flowSmoothingCLM U phi hphi hsupp) = ∑' i, ∫ t, phi t • chi i t := by
  refine opTrace_eq_tsum_eigenvalues ?_
  intro i
  rw [flowSmoothingCLM_apply]
  exact flowSmoothing_eigenvector U phi (hchar i)

end General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [NormedSpace ℝ H] [CompleteSpace H] [SMulCommClass ℝ ℂ H] [IsScalarTower ℝ ℂ H]

/-- **Trace formula for a smoothed flow.**  With the spectral points read off the flow characters,
the trace of the smoothing is the sum of the weight's transform over the spectrum, counted with
the multiplicity supplied by the basis. -/
theorem opTrace_flowSmoothing_eq_tsum_fourier
    (U : UnitaryFlow ℂ H) (phi : ℝ → ℝ)
    (hphi : Continuous phi) (hsupp : HasCompactSupport phi)
    {lam : _ → ℝ}
    (hchar : ∀ i t, U.op t (hsBasis ℂ H i)
      = Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) • hsBasis ℂ H i) :
    opTrace (flowSmoothingCLM U phi hphi hsupp)
      = ∑' i, ∫ t, phi t • Complex.exp (Complex.I * ((lam i : ℂ) * (t : ℂ))) :=
  opTrace_flowSmoothing_eq_tsum_characterIntegral U phi hphi hsupp hchar

end GaloisForLFunctions.HTGeometry
