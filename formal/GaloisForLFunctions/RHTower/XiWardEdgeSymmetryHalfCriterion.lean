import GaloisForLFunctions.RHTower.XiWardIntegerWindowMassCriterion

/-!
# Edge symmetry and the nonpositive half-window criterion

Each strict-right Schwarz pair contributes an even edge profile: its two
Lorentzians sit at reflected heights with a common half-width.  The full edge
density of the continued Ward response is therefore an even function of the
height, and every criterion of the family is symmetric under height reversal.

Independently, the detection window of an upper pair is centered at the
integer nearest `-Im λ < 0`, which is nonpositive.  The integer-window mass
criterion therefore needs only the nonpositive half of `ℤ`.
-/

open Complex Filter MeasureTheory Real

namespace RHTower

noncomputable section

/-- Each Schwarz pair has an even Euler-edge profile. -/
theorem re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_even
    (q : XiRightUpperZeroCopy) (t : ℝ) :
    (xiAntiCausalWardSchwarzPairResponse q
      ((1 / 2 : ℂ) + I * ((-t : ℝ) : ℂ))).re =
      (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  rw [re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq q (-t),
    re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq q t]
  have h1 : (-t + (xiRightCenteredZero q.1).im) ^ 2 =
      (t + -(xiRightCenteredZero q.1).im) ^ 2 := by ring
  have h2 : (-t + -(xiRightCenteredZero q.1).im) ^ 2 =
      (t + (xiRightCenteredZero q.1).im) ^ 2 := by ring
  rw [h1, h2]
  ring

/-- **Edge evenness law**: the Euler-edge density of the continued Ward
response is an even function of the height. -/
theorem re_continuedXiAntiCausalWardResponse_eulerEdge_even (t : ℝ) :
    (continuedXiAntiCausalWardResponse
      ((1 / 2 : ℂ) + I * ((-t : ℝ) : ℂ))).re =
      (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
  have hwn : 0 < ((1 / 2 : ℂ) + I * ((-t : ℝ) : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hwp : 0 < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hsn := summable_xiAntiCausalWardSchwarzPairResponse hwn
  have hsp := summable_xiAntiCausalWardSchwarzPairResponse hwp
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hwn,
    continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hwp,
    Complex.re_tsum hsn, Complex.re_tsum hsp]
  exact tsum_congr fun q =>
    re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_even q t

/-- The detection window of an upper pair sits at a nonpositive integer. -/
theorem round_neg_im_nonpos (q : XiRightUpperZeroCopy) :
    round (-(xiRightCenteredZero q.1).im) ≤ 0 := by
  have hb : 0 < (xiRightCenteredZero q.1).im := q.2
  rw [round_eq]
  calc ⌊-(xiRightCenteredZero q.1).im + 1 / 2⌋ ≤ ⌊(1 / 2 : ℝ)⌋ :=
      Int.floor_le_floor (by linarith)
    _ = 0 := by norm_num

/-- **Nonpositive half-window criterion.**  RH is already equivalent to the
vanishing of the integer-window masses over the nonpositive integers alone. -/
theorem riemannHypothesis_iff_forall_nonpos_xiWardIntegerWindowMass_eq_zero :
    RiemannHypothesis ↔
      ∀ k : ℤ, k ≤ 0 → xiWardIntegerWindowMass k = 0 := by
  constructor
  · intro hRH k _
    exact
      (riemannHypothesis_iff_forall_xiWardIntegerWindowMass_eq_zero.mp hRH) k
  · intro h0
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
    have hlow := le_xiWardIntegerWindowMass_round q
    rw [h0 (round (-(xiRightCenteredZero q.1).im))
      (round_neg_im_nonpos q), le_zero_iff, ENNReal.ofReal_eq_zero] at hlow
    have harctan : 0 < Real.arctan (1 / 2) :=
      Real.arctan_pos.mpr (by norm_num)
    nlinarith

end

end RHTower
