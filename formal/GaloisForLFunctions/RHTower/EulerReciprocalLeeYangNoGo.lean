import GaloisForLFunctions.RHTower.LeeYangQuadraticBlock

/-!
# Reciprocal pairing of a local Euler weight lies on the wrong Lee--Yang side

The most direct attempt to turn a positive local Euler weight `a` into a reciprocal quadratic is

`1 + (a + a⁻¹) z + z²`.

Its normalized Lee--Yang coefficient is `(a + a⁻¹)/2`, which is at least one for `a > 0` and is
equal to one only at `a = 1`.  Hence a genuine contracting Euler weight `0 < a < 1` produces an
off-circle reciprocal pair, not a ferromagnetic Lee--Yang block.

The positive conclusion is that an Ising detour must convert arithmetic data into interaction
couplings with coefficient `exp(-2J) ≤ 1`; reciprocal symmetrization of local fugacities is closed.
-/

namespace GaloisForLFunctions.RHTower

noncomputable def reciprocalEulerPairCoefficient (a : ℝ) : ℝ :=
  (a + a⁻¹) / 2

/-- Positive reciprocal pairing lands at or beyond the Lee--Yang chamber boundary. -/
theorem one_le_reciprocalEulerPairCoefficient {a : ℝ} (ha : 0 < a) :
    1 ≤ reciprocalEulerPairCoefficient a := by
  have hid : a + a⁻¹ - 2 = (a - 1) ^ (2 : ℕ) / a := by
    field_simp [ha.ne']
    ring
  have hnonneg : 0 ≤ a + a⁻¹ - 2 := by
    rw [hid]
    positivity
  dsimp [reciprocalEulerPairCoefficient]
  linarith

/-- Exact boundary classification: the reciprocal Euler pair is Lee--Yang only at unit weight. -/
theorem leeYangPairCircle_reciprocalEulerPair_iff {a : ℝ} (ha : 0 < a) :
    leeYangPairCircle (reciprocalEulerPairCoefficient a) ↔ a = 1 := by
  constructor
  · intro hcircle
    have hle : reciprocalEulerPairCoefficient a ^ (2 : ℕ) ≤ 1 :=
      (leeYangPairCircle_iff _).mp hcircle
    have hge := one_le_reciprocalEulerPairCoefficient ha
    have hc : reciprocalEulerPairCoefficient a = 1 := by nlinarith
    dsimp [reciprocalEulerPairCoefficient] at hc
    have ha0 : a ≠ 0 := ha.ne'
    field_simp [ha0] at hc
    nlinarith [sq_nonneg (a - 1)]
  · intro ha1
    subst a
    norm_num [reciprocalEulerPairCoefficient, leeYangPairCircle_iff]

/-- Contracting positive Euler weights give reciprocal zeros off the unit circle. -/
theorem not_leeYangPairCircle_reciprocalEulerPair_of_lt_one {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) :
    ¬ leeYangPairCircle (reciprocalEulerPairCoefficient a) := by
  rw [leeYangPairCircle_reciprocalEulerPair_iff ha]
  exact ne_of_lt ha1

end GaloisForLFunctions.RHTower
