import GaloisForLFunctions.WindowedLandauTheory.TameInertiaTowers.StatementGroup



-- Powers in `ℤˣ` (also inside products) are monoid powers here, as the proofs assume.
attribute [-instance] Int.instUnitsPow

namespace WindowedLandauTheory.TwoAdicCyclotomicDecomposition

def InvLength : Prop :=
  ∀ (N : ℕ) (u : ℤ), u ≠ 1 →
    Nat.card {x : ZMod (2 ^ N) // ((u - 1 : ℤ) : ZMod (2 ^ N)) * x = 0} =
      2 ^ min N (padicValInt 2 (u - 1))

end WindowedLandauTheory.TwoAdicCyclotomicDecomposition

