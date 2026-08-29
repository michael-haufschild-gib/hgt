import GaloisForLFunctions.RHTower.ThetaCuspFixedActionC5LikelihoodLiftReduction

/-!
# Adverse saturated second channel in the fixed-action C5 tangent

At the exact first-atom endpoint, the likelihood tangent is linear in seven likelihood jets.
The existing pairwise bounds allow a distinguished saturated direction: second displacement loss
equals first mixed-centre gain, while every other likelihood channel vanishes.  This module proves
that this direction is strictly adverse throughout the physical first-atom tail.

Consequently separate jet signs and the existing pairwise likelihood cone cannot prove the C5
atom-tangent reserve.  Any surviving proof must retain quantitative non-saturation or the coupled
third-displacement/second-centre rescue.
-/

namespace RHTower

noncomputable section

/-- Exact first-atom C5 Bose compensation weight. -/
def c5SingleAtomCompensationWeight (u t : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let q := thetaCuspSingleAtomReflectedAction A t
  let v := t * thetaCuspSingleAtomReflectedActionJetOne A z (2 * Real.sinh (2 * t))
  14 + 10 * v + 8 * v / (Real.exp q - 1)

/-- Coefficient of the saturated likelihood tangent direction
`db = -y`, `dm = y`, with all other likelihood variations zero. -/
def c5SingleAtomTangentSaturatedSecondChannel (u t : ℝ) : ℝ :=
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let a := thetaCuspSingleAtomReflectedActionJetOne A z (2 * Real.sinh (2 * t))
  let s := c5SingleAtomScaleActionJetOne A z
  let W := c5SingleAtomCompensationWeight u t
  t * (a * (5 - W) - s * (W - 15))

/-- **The saturated second likelihood channel is strictly adverse everywhere in the physical
first-atom tail.** This is a closed source theorem: its only implications specify the physical
domain, and it imports no numeric computation or route premise. -/
theorem c5SingleAtomTangentSaturatedSecondChannel_neg :
    ∀ u t : ℝ,
      0 < t → t ≤ u → 6 ≤ thetaCuspSingleAtomReflectionScale 1 u →
        c5SingleAtomTangentSaturatedSecondChannel u t < 0 := by
  intro u t ht htu hscale
  let A := thetaCuspSingleAtomReflectionScale 1 u
  let z := thetaCuspSingleAtomReflectionDefect t
  let q := thetaCuspSingleAtomReflectedAction A t
  let v := t * thetaCuspSingleAtomReflectedActionJetOne A z (2 * Real.sinh (2 * t))
  let a := thetaCuspSingleAtomReflectedActionJetOne A z (2 * Real.sinh (2 * t))
  let s := c5SingleAtomScaleActionJetOne A z
  let W := 14 + 10 * v + 8 * v / (Real.exp q - 1)
  have hq : 0 < q := by
    simpa only [q, A] using
      thetaCuspSingleAtomReflectedAction_pos_of_sameHalfLine (n := 1) (by norm_num) ht htu
  have hA : 3 < A := by linarith
  have hr := thetaCuspSingleAtomReflectionFactor_pos_of_sameHalfLine
    (n := 1) (by norm_num) ht.le htu
  have hv : 2 * q < v := by
    simpa only [q, v, A, z] using
      two_mul_thetaCuspSingleAtomReflectedAction_lt_velocity hA ht hr
  have hW : 30 + 12 * q < W := by
    simpa only [W] using
      thirty_add_twelve_mul_lt_c5BoseWeight_of_superquadratic hq hv
  have ha : 0 < a := by
    simpa only [a, A, z] using
      thetaCuspSingleAtomReflectedActionJetOne_pos_of_sameHalfLine ht htu
  have hz : 0 < z := by
    dsimp only [z, thetaCuspSingleAtomReflectionDefect]
    exact sub_pos.mpr (Real.one_lt_cosh.mpr (by linarith))
  have hslope := c5SingleAtomScaleActionSlope_pos_of_sameHalfLine ht.le htu hscale
  have hsEq : s = z *
      (4 * A + c5SingleAtomScaleLambdaJetOne A /
        thetaCuspSingleAtomReflectionFactor A z) := by
    unfold s c5SingleAtomScaleActionJetOne
    ring
  have hs : 0 < s := by
    rw [hsEq]
    exact mul_pos hz (by simpa only [A, z] using hslope)
  have hfirst : a * (5 - W) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
  have hsecond : s * (W - 15) > 0 := mul_pos hs (by linarith)
  unfold c5SingleAtomTangentSaturatedSecondChannel c5SingleAtomCompensationWeight
  dsimp only [A, z, q, v, a, s, W] at hfirst hsecond ⊢
  exact mul_neg_of_pos_of_neg ht (by linarith)

end

end RHTower
