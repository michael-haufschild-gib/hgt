import GaloisForLFunctions.HTGeometry.ReversibleSnapshotIndependence
import GaloisForLFunctions.HTGeometry.UniformPermutationPairOrder

/-!
# Pair-order fairness conditioned on a reversible snapshot

Combining reversible snapshot fibers with uniform pair-order counting shows that, inside every
fixed-snapshot fiber, exactly half of all order/sample pairs place one chosen element before the
other. This is the cardinal form of the conditional `1/2` step in the matroid analysis.
-/

namespace GaloisForLFunctions.HTGeometry

variable {α State : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]

/-- Restricting the snapshot-fiber/order equivalence to the pair-order event. -/
def snapshotBeforeFiberEquiv
    (trajectory : Equiv.Perm α → State ≃ State) (snapshot : State) (e f : α) :
    {x : {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} //
        ArrivesBefore e f x.1.1} ≃
      {σ : Equiv.Perm α // ArrivesBefore e f σ} :=
  Equiv.subtypeEquiv (snapshotFiberOrderEquiv trajectory snapshot) (fun _ => Iff.rfl)

/-- **Conditional pair fairness.** In any family of reversible trajectories indexed by ambient
permutations, precisely half of a fixed snapshot fiber has `e` before a distinct `f`. -/
theorem two_mul_natCard_snapshot_arrivesBefore
    (trajectory : Equiv.Perm α → State ≃ State) (snapshot : State)
    {e f : α} (hef : e ≠ f) :
    2 * Nat.card
        {x : {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} //
          ArrivesBefore e f x.1.1} =
      Nat.card {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} := by
  rw [Nat.card_congr (snapshotBeforeFiberEquiv trajectory snapshot e f),
    Nat.card_congr (snapshotFiberOrderEquiv trajectory snapshot)]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using
    two_mul_card_arrivesBefore hef

/-- Rational-mass form of conditional pair fairness inside a reversible snapshot fiber. -/
theorem snapshot_arrivesBefore_mass
    (trajectory : Equiv.Perm α → State ≃ State) (snapshot : State)
    {e f : α} (hef : e ≠ f) :
    (Nat.card
        {x : {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} //
          ArrivesBefore e f x.1.1} : ℚ) /
      (Nat.card {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} : ℚ) = 1 / 2 := by
  have hhalf := two_mul_natCard_snapshot_arrivesBefore trajectory snapshot hef
  have hfiber :
      Nat.card {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} =
        (Fintype.card α).factorial := by
    rw [Nat.card_congr (snapshotFiberOrderEquiv trajectory snapshot),
      Nat.card_eq_fintype_card, Fintype.card_perm]
  have hneNat :
      Nat.card {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} ≠ 0 := by
    rw [hfiber]
    exact Nat.factorial_ne_zero _
  have hneRat :
      (Nat.card {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} : ℚ) ≠ 0 := by
    exact_mod_cast hneNat
  field_simp [hneRat]
  have hhalf' :
      Nat.card
          {x : {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} //
            ArrivesBefore e f x.1.1} * 2 =
        Nat.card {x : Equiv.Perm α × State // trajectory x.1 x.2 = snapshot} := by
    simpa [mul_comm] using hhalf
  exact_mod_cast hhalf'

end GaloisForLFunctions.HTGeometry
