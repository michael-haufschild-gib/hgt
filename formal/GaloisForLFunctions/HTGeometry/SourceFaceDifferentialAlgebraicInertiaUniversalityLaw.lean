import GaloisForLFunctions.HTGeometry.SourceRigidificationFaceInertia
import GaloisForLFunctions.HTGeometry.ExponentialSumDA

/-!
# Differential-algebraic classification of source-face gauge inertia

Deleting a nonreal source translation creates arbitrarily large packets of unit-periodic Gamma
gauges.  Every vector in those packets is nevertheless a finite exponential sum.  Thus the entire
new reconstruction inertia is differentially algebraic: face specialization can create gauges of
unbounded finite rank without creating a hypertranscendental direction.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Every positive period-one Gamma Fourier packet is differentially algebraic. -/
theorem differentiallyAlgebraic_gammaPositivePeriodicFourierPacket
    {k : ℕ} (a : Fin k → ℂ) :
    DifferentiallyAlgebraic (gammaPositivePeriodicFourierPacket a) := by
  simpa [gammaPositivePeriodicFourierPacket, gammaPeriodicMode] using!
    (differentiallyAlgebraic_finset_expSum_general
      (Finset.univ : Finset (Fin k)) a
      (fun m : Fin k => gammaPeriodicFrequency ((m : ℕ) + 1)))

/-- **Source-face DA-inertia universality law.**  At every finite rank, the positive Fourier basis
is independent, and every packet it spans is DA and fixed by the surviving unit translation; a
packet is also fixed by the deleted nonreal translation only when its coefficient vector is zero. -/
theorem nonreal_sourceFace_arbitraryDifferentialAlgebraicGaugeBirth
    (tau : ℂ) (htau : tau.im ≠ 0) (k : ℕ) :
    LinearIndependent ℂ (fun m : Fin k => gammaPeriodicMode ((m : ℕ) + 1)) ∧
      ∀ a : Fin k → ℂ,
        DifferentiallyAlgebraic (gammaPositivePeriodicFourierPacket a) ∧
        Function.Periodic (gammaPositivePeriodicFourierPacket a) 1 ∧
        (a ≠ 0 → ¬ Function.Periodic (gammaPositivePeriodicFourierPacket a) tau) := by
  refine ⟨gammaPositivePeriodicModes_linearIndependent k, ?_⟩
  intro a
  exact ⟨differentiallyAlgebraic_gammaPositivePeriodicFourierPacket a,
    gammaPositivePeriodicFourierPacket_periodic a,
    fun ha => gammaPositivePeriodicFourierPacket_not_periodic_of_im_ne_zero
      a ha tau htau⟩

end

end GaloisForLFunctions.HTGeometry
