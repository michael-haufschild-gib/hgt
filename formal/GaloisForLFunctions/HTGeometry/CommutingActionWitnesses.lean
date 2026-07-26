import GaloisForLFunctions.HTGeometry.RankOneCohomology
import GaloisForLFunctions.HTGeometry.KoszulCohomology

/-!
# Realizations of the commuting difference-action interface

Both cohomology towers assume that the difference actions commute pairwise.  The identity family, a
constant family, and the integer power families realize this: in a commutative group the integer
power maps commute because integer multiplication does.  The power families are indexed by an
arbitrary integer weight, so the interface is realized in every direction count.

Substituting a power family removes the commutation premise from the rank-one coboundary and Koszul
cocycle laws.
-/

namespace GaloisForLFunctions

noncomputable section

/-! ## Multiplicative realizations -/

/-- The integer power endomorphism of a commutative group. -/
def zpowAction {G : Type*} [CommGroup G] (n : ℤ) : G →* G where
  toFun x := x ^ n
  map_one' := one_zpow n
  map_mul' x y := mul_zpow x y n

theorem commutingActions_id {ι G : Type*} [CommGroup G] :
    commutingActions (fun _ : ι => MonoidHom.id G) := fun _ _ _ => rfl

theorem commutingActions_const {ι G : Type*} [CommGroup G] (f : G →* G) :
    commutingActions (fun _ : ι => f) := fun _ _ _ => rfl

/-- **Integer power actions commute.**  In a commutative group `x ↦ x ^ n` commutes with
`x ↦ x ^ m`, because `n * m = m * n`. -/
theorem commutingActions_zpow {ι G : Type*} [CommGroup G] (n : ι → ℤ) :
    commutingActions (ι := ι) (G := G) (fun p => zpowAction (n p)) := by
  intro p q x
  simp [zpowAction, ← zpow_mul, mul_comm]

/-! ## Additive realizations -/

/-- The integer scaling endomorphism of a commutative group. -/
def zsmulAction {M : Type*} [AddCommGroup M] (n : ℤ) : M →+ M where
  toFun x := n • x
  map_zero' := smul_zero n
  map_add' x y := smul_add n x y

theorem commutingAdditiveActions_id {ι M : Type*} [AddCommGroup M] :
    commutingAdditiveActions (fun _ : ι => AddMonoidHom.id M) := fun _ _ _ => rfl

theorem commutingAdditiveActions_const {ι M : Type*} [AddCommGroup M] (f : M →+ M) :
    commutingAdditiveActions (fun _ : ι => f) := fun _ _ _ => rfl

/-- **Integer scaling actions commute.** -/
theorem commutingAdditiveActions_zsmul {ι M : Type*} [AddCommGroup M] (n : ι → ℤ) :
    commutingAdditiveActions (ι := ι) (M := M) (fun p => zsmulAction (n p)) := by
  intro p q x
  simp [zsmulAction, smul_smul, mul_comm]

/-! ## The premise disappears from the coboundary laws -/

/-- Rank-one coboundaries of a power action family are cocycles, with no commutation premise. -/
theorem rankOneCoboundary_cocycle_zpow {ι G : Type*} [CommGroup G] (n : ι → ℤ) (h : G) :
    scalarCocycle (ι := ι) (G := G) (fun p => zpowAction (n p))
      (rankOneCoboundary (fun p : ι => zpowAction (n p)) h) :=
  rankOneCoboundary_cocycle (commutingActions_zpow n) h

/-- Koszul coboundaries of a scaling action family are additive cocycles, with no commutation
premise. -/
theorem koszulCoboundary_cocycle_zsmul {ι M : Type*} [AddCommGroup M] (n : ι → ℤ) (h : M) :
    additiveCocycle (ι := ι) (M := M) (fun p => zsmulAction (n p))
      (koszulCoboundary (fun p : ι => zsmulAction (n p)) h) :=
  koszulCoboundary_cocycle (commutingAdditiveActions_zsmul n) h

end

end GaloisForLFunctions
