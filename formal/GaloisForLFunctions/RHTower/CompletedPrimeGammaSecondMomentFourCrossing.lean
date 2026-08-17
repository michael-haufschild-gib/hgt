import GaloisForLFunctions.RHTower.CompletedPrimeGammaSecondMomentCenterPositive
import GaloisForLFunctions.RHTower.CompletedPrimeGammaMomentFarRightAsymptotic
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# Four real sign changes of the second completed odd moment

The completed Xi function has no real zero, so the second normalized odd logarithmic-derivative
moment is real analytic, hence continuous, on the whole real axis, and the functional equation
makes it invariant under `x ↦ 1 - x`.  Its value is strictly positive at the centre `1/2`,
strictly negative at `10`, and positive far to the right because its exact asymptotic is
`x^(-5)/10`.  Two applications of the intermediate value theorem therefore produce sign-changing
zeros in `(1/2, 10)` and in `(10, X)`, and reflection produces two more to the left of the centre.
-/

namespace RHTower

open Filter Topology Set

noncomputable section

/-- The second normalized odd completed logarithmic-derivative moment, read on the real axis. -/
noncomputable def secondOddMomentReal (x : ℝ) : ℝ :=
  (completedOddLogDerivMoment (x : ℂ) 2).re

theorem continuous_secondOddMomentReal : Continuous secondOddMomentReal := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hxi : xi (x : ℂ) ≠ 0 := xi_ne_zero_of_real x
  have hana := analyticAt_completedOddLogDerivMoment 2 hxi
  have hc : ContinuousAt (fun s : ℂ => completedOddLogDerivMoment s 2) ((x : ℝ) : ℂ) :=
    hana.continuousAt
  have hofReal : ContinuousAt (fun t : ℝ => ((t : ℝ) : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt
  exact Complex.continuous_re.continuousAt.comp (hc.comp hofReal)

/-- The functional equation fixes the second odd moment under `x ↦ 1 - x`. -/
theorem secondOddMomentReal_one_sub (x : ℝ) :
    secondOddMomentReal (1 - x) = secondOddMomentReal x := by
  simp only [secondOddMomentReal]
  rw [show ((1 - x : ℝ) : ℂ) = 1 - (x : ℂ) by push_cast; ring,
    completedOddLogDerivMoment_one_sub]

theorem secondOddMomentReal_one_half_pos : 0 < secondOddMomentReal (1 / 2) := by
  have h := completedOddLogDerivMoment_two_one_half_re_pos
  simpa [secondOddMomentReal] using h

theorem secondOddMomentReal_ten_neg : secondOddMomentReal 10 < 0 := by
  have h := completedOddLogDerivMoment_two_ten_re_neg
  simpa [secondOddMomentReal] using h

/-- Far to the right the second odd moment is positive: its exact `x^{-5}` asymptotic has
positive leading constant. -/
theorem exists_far_right_secondOddMomentReal_pos :
    ∃ X : ℝ, 10 < X ∧ 0 < secondOddMomentReal X := by
  have h := completedOddLogDerivMomentFarRightAsymptotic 2
  have hlim : (0 : ℝ) < (-1 : ℝ) ^ 2 / (2 * (2 * 2 + 1)) := by norm_num
  have hev : ∀ᶠ x : ℝ in atTop, 0 < x ^ (2 * 2 + 1) * secondOddMomentReal x :=
    h.eventually (eventually_gt_nhds hlim)
  obtain ⟨X, hXpos, hX10⟩ := (hev.and (eventually_gt_atTop (10 : ℝ))).exists
  refine ⟨X, hX10, ?_⟩
  have hXp : (0 : ℝ) < X ^ (2 * 2 + 1) := by positivity
  nlinarith [hXpos]

/-- **The four-crossing law.**  The second normalized odd completed logarithmic-derivative moment
has at least four real sign-changing zeros: two to the right of the functional-equation centre,
bracketed by the strict signs at `1/2`, `10` and far to the right, and their two reflections. -/
theorem exists_four_real_sign_changing_zeros :
    ∃ α β X : ℝ,
      0 < secondOddMomentReal (1 / 2) ∧ secondOddMomentReal 10 < 0 ∧
        0 < secondOddMomentReal X ∧
      1 / 2 < α ∧ α < 10 ∧ 10 < β ∧ β < X ∧
      secondOddMomentReal α = 0 ∧ secondOddMomentReal β = 0 ∧
      secondOddMomentReal (1 - α) = 0 ∧ secondOddMomentReal (1 - β) = 0 ∧
      1 - β < 1 - α ∧ 1 - α < 1 / 2 ∧ 1 / 2 < α ∧ α < β := by
  obtain ⟨X, hX10, hXpos⟩ := exists_far_right_secondOddMomentReal_pos
  have hcont := continuous_secondOddMomentReal
  have hhalf := secondOddMomentReal_one_half_pos
  have hten := secondOddMomentReal_ten_neg
  have hleft : (0 : ℝ) ∈ Ioo (secondOddMomentReal 10) (secondOddMomentReal (1 / 2)) :=
    ⟨hten, hhalf⟩
  obtain ⟨α, hαmem, hα⟩ :=
    intermediate_value_Ioo' (by norm_num : (1 / 2 : ℝ) ≤ 10) hcont.continuousOn hleft
  have hright : (0 : ℝ) ∈ Ioo (secondOddMomentReal 10) (secondOddMomentReal X) :=
    ⟨hten, hXpos⟩
  obtain ⟨β, hβmem, hβ⟩ :=
    intermediate_value_Ioo (le_of_lt hX10) hcont.continuousOn hright
  refine ⟨α, β, X, hhalf, hten, hXpos, hαmem.1, hαmem.2, hβmem.1, hβmem.2, hα, hβ, ?_, ?_, ?_, ?_,
    hαmem.1, lt_trans hαmem.2 hβmem.1⟩
  · rw [secondOddMomentReal_one_sub]; exact hα
  · rw [secondOddMomentReal_one_sub]; exact hβ
  · have := hαmem.2
    have := hβmem.1
    linarith
  · have := hαmem.1
    linarith

end

end RHTower
