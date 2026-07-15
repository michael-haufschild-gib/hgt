import GaloisForLFunctions.HTGeometry.FiniteConstraintGroupAverage

/-!
# Fixed points of a finite-clock observable twirl

For every nonempty finite-period clock, an observable survives cyclic coarse-graining exactly
when it commutes with one clock step.  The forward implication was already formalized; the
converse follows because the twirl itself lies in the clock commutant.

This is the finite-period observer-algebra criterion underlying clock dephasing.  It assumes no
self-adjointness, positivity, isometry, state, or temporal evolution.
-/

namespace HTGeometry

noncomputable section

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Finite-clock observable fixed-point theorem.**  For a nonempty periodic clock, the fixed
algebra of cyclic observable averaging is exactly the commutant of one clock step. -/
theorem finiteCyclicObservableTwirl_eq_self_iff_commutes
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1) :
    finiteCyclicObservableTwirl U X N = X ↔ U * X = X * U := by
  constructor
  · intro hfixed
    calc
      U * X = U * finiteCyclicObservableTwirl U X N :=
        congrArg (fun Y => U * Y) hfixed.symm
      _ = finiteCyclicObservableTwirl U X N * U :=
        finiteCyclicObservableTwirl_commutes U X N hperiod
      _ = X * U := congrArg (fun Y => Y * U) hfixed
  · exact finiteCyclicObservableTwirl_eq_self_of_commutes
      U X N hN hperiod

/-- Disturbance form of the same theorem: the clock erases nothing exactly on its commutant. -/
theorem sub_finiteCyclicObservableTwirl_eq_zero_iff_commutes
    (U X : E →L[𝕜] E) (N : ℕ) (hN : N ≠ 0) (hperiod : U ^ N = 1) :
    X - finiteCyclicObservableTwirl U X N = 0 ↔ U * X = X * U := by
  rw [sub_eq_zero]
  constructor
  · intro hfixed
    exact (finiteCyclicObservableTwirl_eq_self_iff_commutes
      U X N hN hperiod).mp hfixed.symm
  · intro hcomm
    exact (finiteCyclicObservableTwirl_eq_self_iff_commutes
      U X N hN hperiod).mpr hcomm |>.symm

end

end HTGeometry
