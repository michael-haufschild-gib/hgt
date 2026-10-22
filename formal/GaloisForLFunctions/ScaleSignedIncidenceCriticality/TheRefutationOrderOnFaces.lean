import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheRefutationCalculusIsCompleteOnBothFaces

/-!
# The refutation order on faces

The faces of the field are usually compared by their floors, and all the floors are `½`, so the
comparison is empty. In the refutation direction they are not equal at all, and this module orders
them.

* A bounded-aperture certificate **cannot refute** (`not_refutes_aperturePositivity`): the on-line
  lattice shares every such certificate, so no shadow of it consists entirely of off-line data. With
  the two-sided vacuity of `TheResolutionIntervalIsTheWholeRange` — interval equal to the whole
  range of the width — the aperture face is useless in *both* directions.
* A truncated divisor **can refute**, and completely: it refutes exactly when an off-line zero lies
  below its height (`refutes_heightReading`), and RH is the statement that no height does
  (`riemannHypothesis_iff_no_heightReading_refutes`).
* A radius certificate **can refute**, and completely as well
  (`riemannHypothesis_iff_no_radiusReading_refutes`).

`theRefutationOrder` states the three facts together. The ordering they induce is strict: the height
and radius faces dominate the aperture face, which is maximally blind. This is the first comparison
of faces the programme can make, and it is a comparison the floors cannot see, because it lives in
the lower theory.

The practical reading is a division of labour. A mechanism aiming to refute should be built on a
divisor or a prime window, where bounded data suffice and the calculus is complete; a mechanism
aiming to confirm cannot use a bounded aperture certificate for any part of its argument, since that
reading is vacuous in both directions.
-/

open Set
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

open Zeta23 _root_.RHTower

set_option autoImplicit false

/-! ### 1. The aperture face cannot refute -/

/-- **A bounded-aperture certificate never refutes the critical line.** The on-line lattice shares
every such certificate and lies on the line. -/
theorem not_refutes_aperturePositivity {a : ℝ} {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) :
    ¬ Refutes (aperturePositivity a) (fun W => width W = 0) Z := fun href =>
  href _ (onLineLattice_mem_shadow_aperturePositivity hZ)
    (width_onLineLattice (by norm_num : (0 : ℝ) < 1))

/-- Nor does any family of them. -/
theorem not_refutes_familyPositivity {ι : Type*} {a : ι → ℝ} {Z : TemperedZeroConfig}
    (hZ : familyPositivity a Z) :
    ¬ Refutes (familyPositivity a) (fun W => width W = 0) Z := fun href =>
  href _ (propext (iff_of_true
      (fun i => aperturePositivity_onLineLattice (by norm_num : (0 : ℝ) < 1) (a i)) hZ))
    (width_onLineLattice (by norm_num : (0 : ℝ) < 1))

/-! ### 2. The order -/

/-- **The refutation order.** The aperture face refutes nothing, while the height and radius faces
refute completely: RH is equivalent to the absence of a refuting reading on each of them. -/
theorem theRefutationOrder {a : ℝ} {Z : TemperedZeroConfig} (hZ : aperturePositivity a Z) :
    ¬ Refutes (aperturePositivity a) (fun W => width W = 0) Z ∧
      (RiemannHypothesis ↔
        ¬ ∃ T : ℝ, Refutes (heightReading T) (fun W => width W = 0) zetaConfig) ∧
      (RiemannHypothesis ↔
        ¬ ∃ R : ℝ, Refutes (radiusReading R)
          WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))) :=
  ⟨not_refutes_aperturePositivity hZ, riemannHypothesis_iff_no_heightReading_refutes,
    riemannHypothesis_iff_no_radiusReading_refutes⟩

/-- **The aperture face is vacuous in both directions.** Its interval is the whole range of the
width and it refutes nothing: no part of an argument can rest on it. -/
theorem theApertureFaceIsTwoSidedlyVacuous {a : ℝ} (ha : 0 < a) {Z : TemperedZeroConfig}
    (hZ : aperturePositivity a Z) :
    resolutionInterval width (aperturePositivity a) Z = range width ∧
      ¬ Refutes (aperturePositivity a) (fun W => width W = 0) Z :=
  ⟨resolutionInterval_width_aperturePositivity ha hZ, not_refutes_aperturePositivity hZ⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
