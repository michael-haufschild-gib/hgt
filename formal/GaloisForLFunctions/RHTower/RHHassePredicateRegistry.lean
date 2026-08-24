import GaloisForLFunctions.HTGeometry.HassePredicate
import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.LadderLattice
import GaloisForLFunctions.RHTower.SquareLadder
import GaloisForLFunctions.RHTower.CliffordMultiplicity
import GaloisForLFunctions.RHTower.WindowLadder
import GaloisForLFunctions.RHTower.XiWardIntegerWindowMassCriterion
import GaloisForLFunctions.RHTower.XiWardEdgeSymmetryHalfCriterion

/-!
# Route-neutral Hasse-predicate registry for RH endpoints

Closed RH equivalences from distinct research routes are exposed through one local--global
interface.  This records exact finite or pointwise obstruction systems; it makes no assertion that
any local condition has been proved independently.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- Multiplicity-parity ladder levels as local places. -/
def riemannHypothesisLadderHassePredicate : HassePredicate Unit ℕ :=
  HassePredicate.fixed rh_iff_forall_ladder

/-- Divisor-order lattice levels as local places. -/
def riemannHypothesisOrderLadderHassePredicate : HassePredicate Unit ℕ :=
  HassePredicate.fixed rh_iff_forall_orderLadder

/-- Iterated square-root descent on the slit plane as a Hasse predicate. -/
def riemannHypothesisSlitPlaneRootHassePredicate : HassePredicate Unit ℕ :=
  HassePredicate.fixed rh_iff_forall_root_slitPlane

/-- Clifford multiplicity models at each level as a Hasse predicate. -/
def riemannHypothesisCliffordModelHassePredicate : HassePredicate Unit ℕ :=
  HassePredicate.fixed rh_iff_forall_cliffordModel

/-- The full level-height window system, flattened into product-indexed local places. -/
def riemannHypothesisWindowCertificateHassePredicate : HassePredicate Unit (ℕ × ℝ) :=
  HassePredicate.fixed (by
    constructor
    · intro h p
      exact rh_iff_forall_windowCertificate.mp h p.1 p.2
    · intro h
      exact rh_iff_forall_windowCertificate.mpr (fun k T => h (k, T)))

/-- One fixed ladder rung, detected by its natural-height windows. -/
def rhLadderNaturalWindowHassePredicate (k : ℕ) : HassePredicate Unit ℕ :=
  HassePredicate.fixed (rhLadder_iff_forall_nat_windowCertificate k)

/-- Two-stage Hasse composition: RH is first localized to ladder levels, then each level is
localized to natural-height finite windows. -/
def riemannHypothesisNaturalWindowHassePredicate :
    HassePredicate Unit (Σ _ : ℕ, ℕ) :=
  riemannHypothesisLadderHassePredicate.refinePlaces
    (fun k n _ => WindowCertificate k n)
    (fun _ k => rhLadder_iff_forall_nat_windowCertificate k)

/-- Zero-freeness of every bounded box as a Hasse predicate. -/
def riemannHypothesisBoxZeroFreeHassePredicate : HassePredicate Unit ℝ :=
  HassePredicate.fixed rh_iff_forall_boxZeros_empty

/-- Integer-window Ward mass vanishing as a Hasse predicate. -/
def riemannHypothesisWardIntegerWindowHassePredicate : HassePredicate Unit ℤ :=
  HassePredicate.fixed riemannHypothesis_iff_forall_xiWardIntegerWindowMass_eq_zero

/-- The symmetry-reduced nonpositive Ward windows as local places. -/
def riemannHypothesisWardNonpositiveWindowHassePredicate : HassePredicate Unit ℤ :=
  HassePredicate.fixed riemannHypothesis_iff_forall_nonpos_xiWardIntegerWindowMass_eq_zero

end RHTower
