import GaloisForLFunctions.RHTower.LevinsonWindowBound
import GaloisForLFunctions.RHTower.LevinsonWindowUnconditional

/-!
# Every edge estimated, and nothing assumed on the critical edge

Combining the three edge estimates of `LevinsonWindowBound` with the window inequality that no
longer needs the detector to be zero-free on the critical segment leaves exactly one undetermined
quantity: the number of zeros of the entire detector inside `[½,4]×[T₁,T₂]`.

The two surviving hypotheses are that the horizontal edges avoid the zeros of `G`; heights with that
property are dense, so they cost nothing.
-/

open Complex Set MeasureTheory

noncomputable section

namespace RHTower

/-- **The Levinson window with every edge estimated and no hypothesis on the critical edge.**
The only quantities left are the number of zeros of the entire detector inside `[½,4]×[T₁,T₂]` and
the requirement that the two horizontal edges avoid its zeros. -/
theorem exists_levinson_window_edge_bound_unconditional :
    ∃ c : ℝ, 0 < c ∧ ∀ lam : ℝ, lam < 0 → |lam| ≤ 1 → ∀ T₁ T₂ : ℝ, 20 ≤ T₁ → T₁ < T₂ →
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) 4, levinsonG (lam : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) →
      (∀ x ∈ Set.Icc (1 / 2 : ℝ) 4, levinsonG (lam : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) →
      ∀ n : ℕ,
        (∀ Z : Finset ℂ,
          (∀ z : ℂ, z ∈ Z ↔ z ∈ (Set.uIcc (1 / 2 : ℝ) 4 ×ℂ Set.uIcc T₁ T₂) ∧
            levinsonGEntire (lam : ℂ) z = 0) →
          ((n : ℝ) + 2) * Real.pi + Real.pi + (T₂ - T₁) * (6 / T₁ ^ 2)
              + c * Real.log T₁ + c * Real.log T₂
              + 2 * Real.pi *
                (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire (lam : ℂ)) w).toNat : ℝ))
            ≤ gammaHardyTheta T₂ - gammaHardyTheta T₁) →
        n ≤ xiOddFiberCount T₂ := by
  obtain ⟨c, hc, hhoriz⟩ := exists_horizontal_levinsonGEntire_bound
  refine ⟨c, hc, ?_⟩
  intro lam hlam0 hlam T₁ T₂ h20 hT hbotG htopG n hn
  have hlamC : ‖(lam : ℂ)‖ ≤ 1 := by rwa [Complex.norm_real, Real.norm_eq_abs]
  have huIcc : Set.uIcc (1 / 2 : ℝ) 4 = Set.Icc (1 / 2 : ℝ) 4 := uIcc_of_le (by norm_num)
  have hne1 : ∀ (x T : ℝ), 20 ≤ T → ((x : ℂ) + (T : ℂ) * I) ≠ 1 := by
    intro x T hT' h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, Complex.one_im] at him
    linarith
  have hbot : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 4,
      levinsonGEntire (lam : ℂ) ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [huIcc] at hx
    rw [Ne, levinsonGEntire_eq_zero_iff (lam : ℂ) (hne1 x T₁ h20)]
    exact hbotG x hx
  have htop : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 4,
      levinsonGEntire (lam : ℂ) ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    rw [huIcc] at hx
    rw [Ne, levinsonGEntire_eq_zero_iff (lam : ℂ) (hne1 x T₂ (by linarith))]
    exact htopG x hx
  refine le_xiOddFiberCount_of_levinson_window_unconditional hlam0
    (by norm_num : (1 / 2 : ℝ) < 4) h20 hT hbot htop ?_ ?_
  · intro t _
    refine levinsonGEntire_ne_zero_of_four_le hlamC ?_
    simp
  · intro Z hZ
    have hR := abs_integral_re_logDeriv_levinsonGEntire_right_le hlamC h20 hT.le
    have hB := hhoriz lam hlam T₁ h20 hbotG
    have hTp := hhoriz lam hlam T₂ (by linarith) htopG
    have hgoal := hn Z hZ
    rw [abs_le] at hR hB hTp
    simp only [Complex.ofReal_ofNat]
    linarith [hR.1, hR.2, hB.1, hB.2, hTp.1, hTp.2, hgoal]

end RHTower

end
