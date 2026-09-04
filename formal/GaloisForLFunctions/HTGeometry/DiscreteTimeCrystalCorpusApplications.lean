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

/-- A doubled-clock odd observable has an exact alternating orbit. -/
theorem doubledParityClock_iterate_oddObservable
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (J A : E →L[𝕜] E) (hJsq : J ^ 2 = 1)
    (hcomm : J * A = A * J) (ψ : E) (n : ℕ) :
    ((HTGeometry.doubledParityClock J) ^ n)
        (HTGeometry.doubledOddObservable A (HTGeometry.doubledParitySource J ψ)) =
      ((-1 : 𝕜) ^ n) •
        HTGeometry.doubledOddObservable A (HTGeometry.doubledParitySource J ψ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, mul_apply_eq_comp,
        HTGeometry.doubledParityClock_odd_source J A hJsq hcomm,
        map_neg, ih]
      rw [pow_succ]
      module

/-- Scalar response seen by a real linear observer along the doubled-clock orbit. -/
def doubledParityClockResponse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J A : E →L[ℝ] E)
    (observer : WithLp 2 (E × E) →L[ℝ] ℝ)
    (ψ : E) (n : ℕ) : ℝ :=
  observer (((HTGeometry.doubledParityClock J) ^ n)
    (HTGeometry.doubledOddObservable A (HTGeometry.doubledParitySource J ψ)))

/-- Every real observer sees the paper's exact `(-1)^n` period-doubled signal. -/
theorem doubledParityClockResponse_eq_periodDoubledSignal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J A : E →L[ℝ] E) (hJsq : J ^ 2 = 1)
    (hcomm : J * A = A * J)
    (observer : WithLp 2 (E × E) →L[ℝ] ℝ)
    (ψ : E) (n : ℕ) :
    doubledParityClockResponse J A observer ψ n =
      periodDoubledSignal
        (observer (HTGeometry.doubledOddObservable A
          (HTGeometry.doubledParitySource J ψ))) n := by
  unfold doubledParityClockResponse periodDoubledSignal
  rw [doubledParityClock_iterate_oddObservable J A hJsq hcomm ψ n,
    map_smul]
  rfl

/-- The paper's finite DTC demodulator exactly extracts every doubled-clock observer amplitude. -/
theorem finiteDTCIndicator_doubledParityClockResponse
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (J A : E →L[ℝ] E) (hJsq : J ^ 2 = 1)
    (hcomm : J * A = A * J)
    (observer : WithLp 2 (E × E) →L[ℝ] ℝ)
    (ψ : E) (N : ℕ) :
    finiteDTCIndicator N (doubledParityClockResponse J A observer ψ) =
      observer (HTGeometry.doubledOddObservable A
        (HTGeometry.doubledParitySource J ψ)) := by
  have hsignal : doubledParityClockResponse J A observer ψ =
      periodDoubledSignal
        (observer (HTGeometry.doubledOddObservable A
          (HTGeometry.doubledParitySource J ψ))) := by
    funext n
    exact doubledParityClockResponse_eq_periodDoubledSignal
      J A hJsq hcomm observer ψ n
  rw [hsignal, finiteDTCIndicator_periodDoubledSignal]

end

end GaloisForLFunctions.HTGeometry
