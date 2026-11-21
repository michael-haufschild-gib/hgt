import GaloisForLFunctions.WindowedLandauTheory.FrobeniusOrbits.HostOrbitsPlaces



-- Powers in `ℤˣ` (also inside products) are monoid powers here, as the proofs assume.
attribute [-instance] Int.instUnitsPow

noncomputable section

namespace WindowedLandauTheory.FrobeniusOrbits

def HostOrbitCountSg : Prop :=
  ∀ e : ℕ, ∀ φ : GG e, φ.1 = ((1 : ℤˣ), (-1 : ℤˣ)) → ∀ τ ∈ Psi e,
    orderOf φ = Nat.lcm 2 (orderOf φ.2) ∧
    (Set.range fun i : ℕ => placeOf (φ ^ i * τ)).ncard = orderOf φ

end WindowedLandauTheory.FrobeniusOrbits

