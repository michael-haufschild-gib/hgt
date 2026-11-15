import GaloisForLFunctions.HTGeometry.MilnorKTheory.FrobeniusWeights
import GaloisForLFunctions.HTGeometry.MilnorKDegTwoSymbol
import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagH2

/-!
# The central extension defined by the Milnor cup symbol

The degree-one cup-product formula with trivial coefficients sends `(a,b)` to `{a,b}`.
Bilinearity makes this a normalized cocycle. Its central extension has commutator
pairing `2{a,b}`; hence commuting lifts are characterized exactly by the two-torsion
of the symbol. Simultaneous powering lifts to an endomorphism with weights one on
the unit group and two on the central Milnor group.
-/

namespace GaloisForLFunctions.HTGeometry

open RHTower

variable (F : Type) [Field F]

/-- The cup of the two universal degree-one Milnor classes. -/
def milnorSymbolCocycle : DeningerNormalizedCocycle Fˣ (MilnorKDeg F 2) where
  f ab := milnorSym2 F ab.1 ab.2
  cocycle a b c := by
    simp only [milnorSym2_mul_left, milnorSym2_mul_right]
    abel
  one_fst := milnorSym2_one_left
  one_snd := milnorSym2_one_right

/-- The unit group centrally extended by its universal degree-two symbol. -/
abbrev MilnorSymbolExtension := DeningerCocycleExt (milnorSymbolCocycle F)

/-- The canonical set-theoretic lift of a unit. -/
def milnorUnitLift (a : Fˣ) : MilnorSymbolExtension F := DeningerCocycleExt.mk 0 a

/-- The central copy of the second Milnor group. -/
def milnorCentralLift (z : MilnorKDeg F 2) : MilnorSymbolExtension F :=
  DeningerCocycleExt.mk z 1

/-- The commutation defect of two lifts is exactly twice their Milnor symbol. -/
theorem milnorSymbolExtension_commutation (x y : MilnorSymbolExtension F) :
    x * y = milnorCentralLift F (2 • milnorSym2 F x.snd y.snd) * (y * x) := by
  apply DeningerCocycleExt.ext_iff
  · simp only [DeningerCocycleExt.mul_fst, milnorCentralLift,
      DeningerCocycleExt.fst_mk, DeningerCocycleExt.snd_mk,
      milnorSymbolCocycle, milnorSym2_one_left, add_zero]
    rw [milnorSym2_antisymm y.snd x.snd, two_nsmul]
    abel
  · simp only [DeningerCocycleExt.mul_snd, milnorCentralLift,
      DeningerCocycleExt.snd_mk, one_mul, mul_comm]

/-- The extension detects precisely the quotient of symbols by two-torsion. -/
theorem milnorSymbolExtension_commute_iff (x y : MilnorSymbolExtension F) :
    Commute x y ↔ (2 : ℕ) • milnorSym2 F x.snd y.snd = 0 := by
  constructor
  · intro h
    have hfirst := congrArg DeningerCocycleExt.fst h.eq
    simp only [DeningerCocycleExt.mul_fst, milnorSymbolCocycle] at hfirst
    have hsym : milnorSym2 F x.snd y.snd = milnorSym2 F y.snd x.snd := by
      apply add_left_cancel (a := x.fst + y.fst)
      simpa only [add_comm y.fst x.fst] using hfirst
    rw [milnorSym2_antisymm y.snd x.snd] at hsym
    rw [two_nsmul]
    nth_rw 1 [hsym]
    exact neg_add_cancel _
  · intro h
    show x * y = y * x
    rw [milnorSymbolExtension_commutation, h]
    exact one_mul (y * x)

/-- Applying a power to both symbol entries gives its quadratic weight. -/
theorem milnorSym2_pow_both (d : ℕ) (a b : Fˣ) :
    milnorSym2 F (a ^ d) (b ^ d) = d ^ 2 • milnorSym2 F a b := by
  exact milnorClassDeg_map_pow d 2 ⟨[a, b], rfl⟩

/-- Powering units lifts to a group endomorphism with quadratic central weight. -/
def milnorSymbolExtensionPower (d : ℕ) : MilnorSymbolExtension F →* MilnorSymbolExtension F where
  toFun x := DeningerCocycleExt.mk (d ^ 2 • x.fst) (x.snd ^ d)
  map_one' := by
    apply DeningerCocycleExt.ext_iff
    · exact smul_zero _
    · exact one_pow d
  map_mul' x y := by
    apply DeningerCocycleExt.ext_iff
    · change d ^ 2 • (x.fst + y.fst + milnorSym2 F x.snd y.snd) =
        d ^ 2 • x.fst + d ^ 2 • y.fst + milnorSym2 F (x.snd ^ d) (y.snd ^ d)
      rw [milnorSym2_pow_both, smul_add, smul_add]
    · exact mul_pow x.snd y.snd d

/-- On the central fibre, the lifted power operation acts by its square. -/
theorem milnorSymbolExtensionPower_central (d : ℕ) (z : MilnorKDeg F 2) :
    milnorSymbolExtensionPower F d (milnorCentralLift F z) =
      milnorCentralLift F (d ^ 2 • z) := by
  apply DeningerCocycleExt.ext_iff
  · rfl
  · exact one_pow d

/-- In positive characteristic the central action is the actual Frobenius-induced map. -/
theorem milnorSymbolExtensionPower_frobenius (p : ℕ) [Fact p.Prime] [CharP F p]
    (x : MilnorSymbolExtension F) :
    (milnorSymbolExtensionPower F p x).fst = milnorKDegMap (frobenius F p) 2 x.fst :=
  (milnorKDegMap_frobenius p 2 x.fst).symm

end GaloisForLFunctions.HTGeometry
