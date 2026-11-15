import GaloisForLFunctions.HTGeometry.MilnorKTheory.FrobeniusWeights
import GaloisForLFunctions.HTGeometry.MilnorKTwoDiagonalExtension

/-!
# Power and Frobenius actions on the Milnor diagonal extension

The diagonal extension is built from a sum of degree-one cup symbols. Simultaneous
powering therefore scales its cocycle quadratically. The operation on the extension
has weight one on diagonal units and weight two on the central Milnor group.
In characteristic `p`, these are precisely the maps induced by Frobenius.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F : Type*} [Field F] {n : ℕ}

/-- A degree-two symbol is quadratic under simultaneous powering of its entries. -/
theorem milnorSym2_pow_both (d : ℕ) (a b : Fˣ) :
    milnorSym2 F (a ^ d) (b ^ d) = d ^ 2 • milnorSym2 F a b :=
  milnorClassDeg_map_pow d 2 ⟨[a, b], rfl⟩

/-- The cup cocycle of the determinant-one diagonal group has weight two. -/
theorem milnorDiagonalCocycle_pow_both (d : ℕ) (u v : detOneDiagonalUnits F n) :
    milnorDiagonalCocycle (u ^ d) (v ^ d) = d ^ 2 • milnorDiagonalCocycle u v := by
  classical
  simp only [milnorDiagonalCocycle, Subgroup.coe_pow, Pi.pow_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs with h
  · exact milnorSym2_pow_both d _ _
  · exact (smul_zero _).symm

namespace MilnorDiagonalExtension

/-- The power operation lifted through the cup cocycle, with quadratic central weight. -/
def powerLift (d : ℕ) : MilnorDiagonalExtension F n →* MilnorDiagonalExtension F n where
  toFun x := ⟨x.diag ^ d, d ^ 2 • x.central⟩
  map_one' := by
    apply MilnorDiagonalExtension.ext
    · exact one_pow d
    · exact smul_zero _
  map_mul' x y := by
    apply MilnorDiagonalExtension.ext
    · exact mul_pow x.diag y.diag d
    · change d ^ 2 • (x.central + y.central + milnorDiagonalCocycle x.diag y.diag) =
        d ^ 2 • x.central + d ^ 2 • y.central + milnorDiagonalCocycle (x.diag ^ d) (y.diag ^ d)
      rw [milnorDiagonalCocycle_pow_both, smul_add, smul_add]

/-- Diagonal coordinates have weight one. -/
theorem powerLift_diag (d : ℕ) (x : MilnorDiagonalExtension F n) :
    (powerLift d x).diag = x.diag ^ d := rfl

/-- Central Milnor coordinates have weight two. -/
theorem powerLift_central (d : ℕ) (x : MilnorDiagonalExtension F n) :
    (powerLift d x).central = d ^ 2 • x.central := rfl

/-- Power lifts compose multiplicatively in their exponents. -/
theorem powerLift_mul (d e : ℕ) (x : MilnorDiagonalExtension F n) :
    powerLift (d * e) x = powerLift e (powerLift d x) := by
  apply MilnorDiagonalExtension.ext
  · exact pow_mul x.diag d e
  · change (d * e) ^ 2 • x.central = e ^ 2 • (d ^ 2 • x.central)
    rw [mul_pow, smul_smul, Nat.mul_comm (e ^ 2)]

/-- Frobenius on the centre is induced from the field itself. -/
theorem powerLift_frobenius_central (p : ℕ) [Fact p.Prime] [CharP F p]
    (x : MilnorDiagonalExtension F n) :
    (powerLift p x).central = milnorKDegMap (frobenius F p) 2 x.central :=
  (milnorKDegMap_frobenius p 2 x.central).symm

/-- Every diagonal entry is acted on by the same field Frobenius. -/
theorem powerLift_frobenius_diag (p : ℕ) [Fact p.Prime] [CharP F p]
    (x : MilnorDiagonalExtension F n) (i : Fin n) :
    (((powerLift p x).diag.1 i : Fˣ) : F) = frobenius F p (x.diag.1 i : F) := rfl

open scoped commutatorElement

/-- The commutator pairing scales quadratically under the power lift. -/
theorem powerLift_commutator_central (d : ℕ) (x y : MilnorDiagonalExtension F n) :
    (⁅powerLift d x, powerLift d y⁆).central = d ^ 2 • (⁅x, y⁆).central := by
  rw [← map_commutatorElement (powerLift d)]
  rfl

end MilnorDiagonalExtension

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.MilnorDiagonalExtension.powerLift
#print axioms GaloisForLFunctions.HTGeometry.MilnorDiagonalExtension.powerLift_commutator_central
