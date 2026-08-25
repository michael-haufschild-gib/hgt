import GaloisForLFunctions.HTGeometry.CausalCollisionRecurrenceLaw
import GaloisForLFunctions.RHTower.XiResolvedStokesWardCharacter

/-!
# Resolved Xi recurrence localizes charge without erasing conductor

The Xi defect has two independent coordinates: exact divisor multiplicity in the primary Stokes
conductor, and horizontal displacement in the secondary relative Ward character.  Put both in one
resolved collision carrier, but let dissipative recurrence report only the Ward coordinate.

Finite-action cofinal replay then forces the collision into the reporter kernel.  The result is not
the zero collision: its conductor coordinate remains `8m ≠ 0`.  Thus recurrence selects the
critical line by killing transverse response while preserving the multiplicity-bearing defect.

This is a conditional localization theorem, not an RH proof.  Its falsifier is exact: an off-line
Xi divisor cannot admit such a finite-action recurrent replay.  The arithmetic producer would have
to construct the replay history from the prime--Gamma source without indexing it by the divisor.
-/

open Complex Filter MeasureTheory Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Two resolved coordinates of one Xi defect: primary conductor and secondary Ward mode. -/
abbrev XiResolvedRecurrenceCarrier :=
  ℝ × Lp ℂ 2 unitIntervalMeasure

/-- Dissipative recurrence reports only the secondary Ward coordinate. -/
def xiResolvedRecurrenceTransverseReporter :
    XiResolvedRecurrenceCarrier →+ Lp ℂ 2 unitIntervalMeasure where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' := fun _ _ => rfl

/-- Marked resolved Xi collision: exact multiplicity conductor plus relative Ward character. -/
def xiResolvedStokesWardCollision
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    XiResolvedRecurrenceCarrier × XiResolvedRecurrenceCarrier :=
  (((xiSupportMultiplicity rho : ℝ) * 8,
      thetaXiIntegralWardRelativeCharacter rho p), 0)

/-- **Resolved recurrence localization.**  Finite-action cofinal replay sends the resolved Xi
collision into the transverse reporter kernel, but not to zero.  Its surviving primary coordinate
is exact conductor multiplicity, and vanishing of the secondary Ward coordinate places the divisor
on the critical line. -/
theorem xiResolvedStokesWardCollision_localizes_to_nonzero_conductorKernel
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (history : ℕ → XiResolvedRecurrenceCarrier × XiResolvedRecurrenceCarrier)
    (hsummable : Summable (fun n => collisionTransverseAction
      xiResolvedRecurrenceTransverseReporter (history n)))
    (hrecurrent : IsCofinalCollisionChargeRecurrent
      xiResolvedRecurrenceTransverseReporter history
      (xiResolvedStokesWardCollision rho p)) :
    let defect := (xiResolvedStokesWardCollision rho p).1 -
      (xiResolvedStokesWardCollision rho p).2
    defect ∈ xiResolvedRecurrenceTransverseReporter.ker ∧
      defect ≠ 0 ∧
      (rho : ℂ).re = 1 / 2 := by
  dsimp only
  have htransverse : collisionTransverseCharge
      xiResolvedRecurrenceTransverseReporter
      (xiResolvedStokesWardCollision rho p) = 0 :=
    collisionTransverseCharge_eq_zero_of_summableAction_of_cofinallyRecurrent
      xiResolvedRecurrenceTransverseReporter history
      (xiResolvedStokesWardCollision rho p) hsummable hrecurrent
  have hward : thetaXiIntegralWardRelativeCharacter rho p = 0 := by
    simpa [collisionTransverseCharge, xiResolvedStokesWardCollision,
      xiResolvedRecurrenceTransverseReporter] using htransverse
  have hconductor : (xiSupportMultiplicity rho : ℝ) * 8 ≠ 0 := by
    have hm : (0 : ℝ) < (xiSupportMultiplicity rho : ℝ) := by
      exact_mod_cast xiSupportMultiplicity_pos rho
    positivity
  have hline : (rho : ℂ).re = 1 / 2 :=
    (xiStokesPrimaryCharge_ne_zero_and_secondaryNeutral_iff rho p).mp
      ⟨hconductor, hward⟩
  refine ⟨?_, ?_, hline⟩
  · exact htransverse
  · intro hzero
    have hfirst := congrArg Prod.fst hzero
    exact hconductor (by
      simpa [xiResolvedStokesWardCollision] using hfirst)

/-- **Exact falsifier.**  An off-line Xi divisor cannot be replayed cofinally with finite total
transverse action in the resolved recurrence carrier. -/
theorem no_xiResolvedStokesWardCollision_finiteActionReplay_of_offLine
    (rho : XiDivisorSupport) (p : Nat.Primes)
    (hoff : (rho : ℂ).re ≠ 1 / 2)
    (history : ℕ → XiResolvedRecurrenceCarrier × XiResolvedRecurrenceCarrier) :
    ¬ (Summable (fun n => collisionTransverseAction
          xiResolvedRecurrenceTransverseReporter (history n)) ∧
        IsCofinalCollisionChargeRecurrent
          xiResolvedRecurrenceTransverseReporter history
          (xiResolvedStokesWardCollision rho p)) := by
  rintro ⟨hsummable, hrecurrent⟩
  exact hoff
    (xiResolvedStokesWardCollision_localizes_to_nonzero_conductorKernel
      rho p history hsummable hrecurrent).2.2

end

end RHTower
