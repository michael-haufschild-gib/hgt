import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularSourceXi
import GaloisForLFunctions.RHTower.XiAffineCollisionControl

/-!
# Collision control for the evaluated angular source

The strict-right angular source vanishes exactly at the three affine Xi collisions
`xi (5ρ/2 - 1) = 0`, `xi (ρ/2) = 0`, `xi (3ρ/2) = 0`.  The zero-free half-plane removes the
third factor for `Re ρ ≥ 2/3` and the first for `Re ρ ≥ 4/5`, and the half-descent shows that
every Xi zero copy leads to a strict-right zero whose half-value is nonzero.  Only the
`5ρ/2 - 1` factor below `Re ρ = 4/5` remains uncontrolled.
-/

open Complex Set Filter Topology
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMModularCore
noncomputable section
set_option autoImplicit false

/-- For `Re ρ ≥ 2/3` the angular source vanishes only through the first two affine values. -/
theorem physicalSelfSourceCoefficient_zero_iff_of_two_thirds_le (q : XiZeroCopy)
    (hq : 2 / 3 ≤ (q.1 : ℂ).re) :
    physicalSelfSourceCoefficient q = 0 ↔
      xi (5 * (q.1 : ℂ) / 2 - 1) = 0 ∨ xi ((q.1 : ℂ) / 2) = 0 := by
  have h5 : 1 / 2 < (q.1 : ℂ).re := by linarith
  rw [physicalSelfSourceCoefficient_zero_iff_xi q h5]
  have hc := xi_three_half_ne_zero_of_re hq
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hc
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

/-- For `Re ρ ≥ 4/5` the angular source vanishes only through the half-value collision. -/
theorem physicalSelfSourceCoefficient_zero_iff_half_of_four_fifths_le (q : XiZeroCopy)
    (hq : 4 / 5 ≤ (q.1 : ℂ).re) :
    physicalSelfSourceCoefficient q = 0 ↔ xi ((q.1 : ℂ) / 2) = 0 := by
  rw [physicalSelfSourceCoefficient_zero_iff_of_two_thirds_le q (by linarith)]
  have ha := xi_five_half_sub_one_ne_zero_of_re hq
  constructor
  · rintro (h | h)
    · exact absurd h ha
    · exact h
  · exact fun h => Or.inr h

/-- For `Re ρ ≥ 4/5`, no half-collision means a nonzero angular source. -/
theorem physicalSelfSourceCoefficient_ne_zero_of_four_fifths_le (q : XiZeroCopy)
    (hq : 4 / 5 ≤ (q.1 : ℂ).re) (hh : xi ((q.1 : ℂ) / 2) ≠ 0) :
    physicalSelfSourceCoefficient q ≠ 0 := by
  rw [Ne, physicalSelfSourceCoefficient_zero_iff_half_of_four_fifths_le q hq]
  exact hh

/-- Every off-line Xi zero copy leads, by reflection and half-descent, to a strict-right nonreal
zero whose half-value is nonzero. -/
theorem exists_strict_right_zero_half_ne_zero_of_copy (q : XiZeroCopy)
    (hre : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ ρ' : ℂ, xi ρ' = 0 ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ ρ'.im ≠ 0 ∧ xi (ρ' / 2) ≠ 0 := by
  have hz := xi_eq_zero_of_mem_divisor_support q.1
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hi := xi_divisor_support_im_ne_zero q.1
  obtain ⟨ρ₀, h0, h1, h2, h3⟩ := exists_strict_right_representative hz hstrip.1 hstrip.2 hre hi
  exact exists_xi_zero_half_ne_zero h0 h1 h2 h3

end
end RHTower.D4BMJointSource
