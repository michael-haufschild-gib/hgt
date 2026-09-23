import GaloisForLFunctions.HTGeometry.DiscreteTimeCrystalSpinChain
import GaloisForLFunctions.HTGeometry.DoubledParityClock

/-!
# Discrete-time-crystal identities in existing corpus clocks

The doubled-parity clock already present in the corpus has an odd observable sector.  This module
identifies that sector with the exact period-doubled signal and finite DTC indicator used by
Formicola--Di Bello--de Candia--De Filippis--Perroni, arXiv:2609.04037.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Identity parity on the base space gives an unconditional exact alternating doubled-clock
orbit. -/
theorem identityDoubledParityClock_iterate_oddObservable
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (ψ : E) (n : ℕ) :
    ((HTGeometry.doubledParityClock (1 : E →L[𝕜] E)) ^ n)
        (HTGeometry.doubledOddObservable (1 : E →L[𝕜] E)
          (HTGeometry.doubledParitySource (1 : E →L[𝕜] E) ψ)) =
      ((-1 : 𝕜) ^ n) •
        HTGeometry.doubledOddObservable (1 : E →L[𝕜] E)
          (HTGeometry.doubledParitySource (1 : E →L[𝕜] E) ψ) := by
  have hJsq : (1 : E →L[𝕜] E) ^ (2 : ℕ) = 1 := by simp
  have hcomm : (1 : E →L[𝕜] E) * 1 = 1 * 1 := rfl
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp,
        HTGeometry.doubledParityClock_odd_source
          (1 : E →L[𝕜] E) (1 : E →L[𝕜] E) hJsq hcomm,
        map_neg, ih]
      rw [pow_succ]
      module

/-- Scalar response seen by a real linear observer along the doubled-clock orbit. -/
def identityDoubledParityClockResponse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (observer : WithLp 2 (E × E) →L[ℝ] ℝ)
    (ψ : E) (n : ℕ) : ℝ :=
  observer (((HTGeometry.doubledParityClock (1 : E →L[ℝ] E)) ^ n)
    (HTGeometry.doubledOddObservable (1 : E →L[ℝ] E)
      (HTGeometry.doubledParitySource (1 : E →L[ℝ] E) ψ)))

/-- Every real observer sees the paper's exact `(-1)^n` period-doubled signal. -/
theorem identityDoubledParityClockResponse_eq_periodDoubledSignal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (observer : WithLp 2 (E × E) →L[ℝ] ℝ)
    (ψ : E) (n : ℕ) :
    identityDoubledParityClockResponse observer ψ n =
      periodDoubledSignal
        (observer (HTGeometry.doubledOddObservable (1 : E →L[ℝ] E)
          (HTGeometry.doubledParitySource (1 : E →L[ℝ] E) ψ))) n := by
  unfold identityDoubledParityClockResponse periodDoubledSignal
  rw [identityDoubledParityClock_iterate_oddObservable ψ n,
    map_smul]
  rfl

/-- The paper's finite DTC demodulator exactly extracts every doubled-clock observer amplitude. -/
theorem finiteDTCIndicator_identityDoubledParityClockResponse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (observer : WithLp 2 (E × E) →L[ℝ] ℝ)
    (ψ : E) (N : ℕ) :
    finiteDTCIndicator N (identityDoubledParityClockResponse observer ψ) =
      observer (HTGeometry.doubledOddObservable (1 : E →L[ℝ] E)
        (HTGeometry.doubledParitySource (1 : E →L[ℝ] E) ψ)) := by
  have hsignal : identityDoubledParityClockResponse observer ψ =
      periodDoubledSignal
        (observer (HTGeometry.doubledOddObservable (1 : E →L[ℝ] E)
          (HTGeometry.doubledParitySource (1 : E →L[ℝ] E) ψ))) := by
    funext n
    exact identityDoubledParityClockResponse_eq_periodDoubledSignal observer ψ n
  rw [hsignal, finiteDTCIndicator_periodDoubledSignal]

end

end GaloisForLFunctions.HTGeometry
