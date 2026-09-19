import GaloisForLFunctions.HilbertMetric.LamzouriSimpleOrSelectedMultiplicity
import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging

/-!
# Finite Xi counts for zeros that are simple or on the critical line

This instantiates the simple-or-selected multiplicity bookkeeping on the
literal positive Xi-zero census.  The selected predicate is `re z = 1/2`, so
the resulting mass is precisely the finite simple-or-critical-line event.
-/

open Finset
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Collision mass of analytic Xi multiplicities in the positive census. -/
def xiPositiveCensusCollisionMass (T : ℝ) : ℝ :=
  finiteMultiplicityCollisionMass (stripFinsetPos T)
    (fun z => (analyticOrderAt xi z).toNat)

/-- All simple Xi zeros in the positive census, whether on or off the
critical line. -/
def xiPositiveSimpleZeroSupport (T : ℝ) : Finset ℂ :=
  finiteSimpleMultiplicitySupport (stripFinsetPos T)
    (fun z => (analyticOrderAt xi z).toNat)

/-- Multiplicity mass of Xi zeros that are simple or lie on the critical
line.  A repeated critical-line zero contributes its full multiplicity. -/
def xiSimpleOrCriticalZeroMass (T : ℝ) : ℝ :=
  finiteSimpleOrSelectedMultiplicityMass (stripFinsetPos T)
    (fun z => (analyticOrderAt xi z).toNat) (fun z => z.re = 1 / 2)

/-- Critical-line multiplicity carried by non-simple Xi zeros. -/
def xiCriticalNonsimpleZeroMass (T : ℝ) : ℝ :=
  finiteSelectedNonsimpleMultiplicityMass (stripFinsetPos T)
    (fun z => (analyticOrderAt xi z).toNat) (fun z => z.re = 1 / 2)

/-- The generic finite multiplicity mass is exactly the existing positive Xi
zero census. -/
theorem xiPositiveCensusMultiplicityMass_eq (T : ℝ) :
    finiteMultiplicityMass (stripFinsetPos T)
        (fun z => (analyticOrderAt xi z).toNat) =
      (xiPosZeroCount T : ℝ) := by
  simp [finiteMultiplicityMass, xiPosZeroCount]

/-- Exact disjoint description: simple-or-critical mass consists of all
simple support plus repeated critical-line multiplicity. -/
theorem xiSimpleOrCriticalZeroMass_eq (T : ℝ) :
    xiSimpleOrCriticalZeroMass T =
      ((xiPositiveSimpleZeroSupport T).card : ℝ) +
        xiCriticalNonsimpleZeroMass T := by
  exact finiteSimpleOrSelectedMultiplicityMass_eq
    (stripFinsetPos T) (fun z => (analyticOrderAt xi z).toNat)
      (fun z => z.re = 1 / 2)

/-- Unconditional finite simple-or-critical-line inequality on the literal
Xi census.  The extra term records every non-simple critical-line copy. -/
theorem xiSimpleOrCriticalZeroMass_lower (T : ℝ) :
    2 * (xiPosZeroCount T : ℝ) - xiPositiveCensusCollisionMass T +
        xiCriticalNonsimpleZeroMass T ≤
      xiSimpleOrCriticalZeroMass T := by
  rw [← xiPositiveCensusMultiplicityMass_eq]
  exact finiteSimpleOrSelectedMultiplicityMass_lower
    (stripFinsetPos T) (fun z => (analyticOrderAt xi z).toNat)
      (fun z => z.re = 1 / 2)

/-- The simple-or-critical event is a genuine submass of the total Xi
counting mass. -/
theorem xiSimpleOrCriticalZeroMass_le_total (T : ℝ) :
    xiSimpleOrCriticalZeroMass T ≤ (xiPosZeroCount T : ℝ) := by
  rw [← xiPositiveCensusMultiplicityMass_eq]
  unfold xiSimpleOrCriticalZeroMass
    finiteSimpleOrSelectedMultiplicityMass finiteMultiplicityMass
  refine Finset.sum_le_sum fun z _hz => ?_
  split_ifs
  · exact le_rfl
  · positivity

end

end RHTower
