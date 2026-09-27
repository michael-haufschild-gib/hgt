import GaloisForLFunctions.RHTower.CCMRestrictedWeilOddPrimeBudget
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPoleBoundaryBounds
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The odd continuous arithmetic has a negative exponential tail

The literal Gamma and pole energy is eventually bounded above by a negative
exponential square. The proof uses the established boundary integral bounds
and symbolic exponential domination. No prime estimate or numerical test is
used. This concerns the continuous part, not the full Weil quadratic.
-/

noncomputable section
open Filter

namespace RHTower

theorem exists_ccmOddPoleGammaPolarBalance_negative_tail :
    ∃ A : ℝ, 0 < A ∧ ∀ a : SuzukiPositiveAperture, A ≤ a.1 →
      ccmOddPoleGammaPolarBalance a ≤ -(Real.exp a.1) ^ 2 / 4 := by
  let c := -Real.eulerMascheroniConstant - Real.log (2 * Real.pi)
  let C := 2 * Real.log 2 + Real.pi + 1
  let K := |c| + C + 2
  have h₁ : Tendsto (fun x : ℝ => (2 * x + 1) * Real.exp (-x)) atTop (nhds 0) := by
    convert ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul 2).add
      Real.tendsto_exp_neg_atTop_nhds_zero using 1 <;> simp [pow_one, add_mul, mul_assoc]
  have h₂ : Tendsto (fun x : ℝ => 2 * x ^ 2 * Real.exp (-x)) atTop (nhds 0) := by
    convert (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul 2 using 1 <;>
      simp [mul_assoc]
  have hev : ∀ᶠ x : ℝ in atTop,
      (2 * x + 1) * Real.exp (-x) ≤ 1 / 2 ∧
      2 * x ^ 2 * Real.exp (-x) ≤ 1 ∧ 8 * K ≤ Real.exp x :=
    (h₁.eventually_le_const (by norm_num)).and
      ((h₂.eventually_le_const (by norm_num)).and
        (Real.tendsto_exp_atTop.eventually_ge_atTop (8 * K)))
  obtain ⟨A, hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 1, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro a ha
  obtain ⟨h₁a, h₂a, hKa⟩ := hA a.1 ((le_max_left _ _).trans ha)
  let E := Real.exp a.1
  let b := 2 * Real.sinh a.1 - 2 * a.1
  have hE : 0 < E := Real.exp_pos _
  have hem : Real.exp (-a.1) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [a.2])
  have hcancel : Real.exp (-a.1) * E = 1 := by
    dsimp [E]
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hlinear : 2 * a.1 + 1 ≤ E / 2 := by
    have h := mul_le_mul_of_nonneg_right h₁a hE.le
    rw [mul_assoc, hcancel, mul_one] at h
    linarith only [h]
  have hquadratic : 2 * a.1 ^ 2 ≤ E := by
    have h := mul_le_mul_of_nonneg_right h₂a hE.le
    rw [mul_assoc, hcancel, mul_one, one_mul] at h
    exact h
  have hb : b = E - Real.exp (-a.1) - 2 * a.1 := by
    dsimp [b, E]
    rw [Real.sinh_eq]
    ring
  have hblower : E / 2 ≤ b := by rw [hb]; linarith only [hlinear, hem]
  have hbpos : 0 ≤ b := (by positivity : 0 ≤ E / 2).trans hblower
  have hbupper : b ≤ E := by
    rw [hb]
    linarith [Real.exp_pos (-a.1), a.2]
  have hbsq : E ^ 2 / 4 ≤ b ^ 2 := by
    nlinarith only [mul_le_mul hblower hblower (by positivity : 0 ≤ E / 2) hbpos]
  have hcb : c * b ≤ |c| * E :=
    mul_le_mul (le_abs_self c) hbupper hbpos (abs_nonneg c)
  have hsmall : (2 * a.1 + 1) * Real.exp (-a.1) ≤ E / 2 := by
    calc
      _ ≤ (2 * a.1 + 1) * 1 :=
        mul_le_mul_of_nonneg_left hem (by linarith [a.2])
      _ ≤ E / 2 := by simpa only [mul_one] using hlinear
  have hboundary := ccmGammaPoleSelfBoundaryMass_le a
  have hcross := (ccmGammaPoleBoundaryMass_nonneg a).1
  have hKE : 8 * K * E ≤ E ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hKa hE.le
  change 2 * (c * b - E + (2 * a.1 + 1) * Real.exp (-a.1) + 2 * a.1 ^ 2 +
    ccmGammaPoleSelfBoundaryMass a - ccmGammaPoleCrossBoundaryMass a - b ^ 2) ≤ -E ^ 2 / 4
  change ccmGammaPoleSelfBoundaryMass a ≤ C * E at hboundary
  dsimp only [K] at hKE
  nlinarith only [hcb, hsmall, hquadratic, hboundary, hcross, hbsq, hKE, hE]

/-- Actual odd pole sources have continuous energy below any prescribed real level. -/
theorem ccmOddPoleGammaPolarBalance_unbounded_below (R : ℝ) :
    ∃ a : SuzukiPositiveAperture, ccmOddPoleGammaPolarBalance a < R := by
  obtain ⟨A, hA, htail⟩ := exists_ccmOddPoleGammaPolarBalance_negative_tail
  obtain ⟨x, hxA, hxE⟩ := ((eventually_ge_atTop A).and
    (Real.tendsto_exp_atTop.eventually_ge_atTop (4 * (|R| + 1)))).exists
  let a : SuzukiPositiveAperture := ⟨x, hA.trans_le hxA⟩
  have h := htail a hxA
  have hE := Real.exp_pos x
  have hR := le_abs_self (-R)
  rw [abs_neg] at hR
  have hsq := sq_nonneg (Real.exp x - 2)
  refine ⟨a, ?_⟩
  change ccmOddPoleGammaPolarBalance a ≤ -(Real.exp x) ^ 2 / 4 at h
  nlinarith only [h, hE, hxE, hR, hsq]

end RHTower
