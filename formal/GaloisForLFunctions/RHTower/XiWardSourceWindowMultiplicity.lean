import GaloisForLFunctions.RHTower.XiWardInteriorReflectionAbsorption

/-!
# Source-only Ward multiplicity bound in a height window

Every strict-right upper Xi zero copy whose height lies in a fixed window contributes a uniform
positive amount to the Ward response at one interior probe.  The amount remains positive as the
horizontal displacement tends to zero, while critical-line copies do not occur in the
strict-right index type.  Positivity of all other Schwarz-pair terms promotes the atomic estimate
to any finite multiplicity-exact packet.

Functional-equation absorption then bounds that packet by an explicit source quantity containing
only pole, Gamma, and absolutely convergent von Mangoldt terms at real part greater than one.  This
is an unconditional, source-faithful submicroscopic separator.  It does not supply the centered
quadratic estimate needed for a positive-proportion theorem.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every finite packet of strict-right upper zero copies is bounded by the full Ward response at
an interior probe. -/
theorem finite_sum_re_xiAntiCausalWardSchwarzPairResponse_le_continued
    (S : Finset XiRightUpperZeroCopy) {w : ℂ} (hw : 0 < w.re) :
    (∑ q ∈ S, (xiAntiCausalWardSchwarzPairResponse q w).re) ≤
      (continuedXiAntiCausalWardResponse w).re := by
  have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
  have hreal : Summable (fun q : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse q w).re) := by
    simpa only [Complex.reCLM_apply] using hsum.mapL Complex.reCLM
  have hfinite := hreal.sum_le_tsum S
    (fun q _ => (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le)
  rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
    Complex.re_tsum hsum]
  exact hfinite

/-- **Multiplicity-exact Euler--Gamma window estimate.** Every finite packet of strict-right
upper zero copies in the height window `|gamma-c| <= delta` costs a uniform positive Ward quantum.
The source-only bound on the right uses only pole, Gamma, and absolutely convergent von Mangoldt
data at `s = h + 1/2 + i*c`, with `Re s > 1`. -/
theorem finite_strictRight_window_card_mul_quantum_le_sourceArithmetic
    (S : Finset XiRightUpperZeroCopy) {h c δ : ℝ} (hh : 1 / 2 < h)
    (hwin : ∀ q ∈ S,
      ((xiRightCenteredZero q.1).im - c) ^ 2 ≤ δ ^ 2) :
    (S.card : ℝ) * (2 * h / ((h + 1 / 2) ^ 2 + δ ^ 2)) ≤
      xiWardInteriorSourceArithmeticBound
        ((h : ℂ) + Complex.I * (c : ℂ)) := by
  let w : ℂ := (h : ℂ) + Complex.I * (c : ℂ)
  let quantum : ℝ := 2 * h / ((h + 1 / 2) ^ 2 + δ ^ 2)
  have hw : 0 < w.re := by
    simp [w, Complex.mul_re]
    linarith
  have hsource := re_continuedXiAntiCausalWardResponse_le_sourceArithmetic
    (w := w) (by simpa [w, Complex.mul_re] using hh)
  have hfinite :=
    finite_sum_re_xiAntiCausalWardSchwarzPairResponse_le_continued S hw
  have hquantum : (S.card : ℝ) * quantum ≤
      ∑ q ∈ S, (xiAntiCausalWardSchwarzPairResponse q w).re := by
    calc
      (S.card : ℝ) * quantum = ∑ q ∈ S, quantum := by simp
      _ ≤ ∑ q ∈ S, (xiAntiCausalWardSchwarzPairResponse q w).re := by
        apply Finset.sum_le_sum
        intro q hq
        exact interior_pair_quantum (by linarith : 0 < h) q (hwin q hq)
  change (S.card : ℝ) * quantum ≤ xiWardInteriorSourceArithmeticBound w
  exact hquantum.trans (hfinite.trans hsource)

end

end RHTower
