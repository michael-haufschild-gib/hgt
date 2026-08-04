import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegStrip
import GaloisForLFunctions.RHTower.Sieve.InvZetaLowBox
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegShift

/-!
# The regular part near the real axis

The strip estimate needs height at least `9`; below it the bound comes from compactness.  The
regular part is holomorphic on a zero-free box straddling the abscissa — the pole costing nothing,
since `zetaLogDerivReg 1 = -γ` — so it is bounded there.

The constant carries no rate and needs none: it does not depend on the truncation height.
-/

namespace RHTower.Sieve

open Complex RHTower

/-- **The regular part is bounded on a box straddling the abscissa near the real axis.** -/
theorem exists_bound_zetaLogDerivReg_low_box (d : ℝ) (hd : 1 ≤ d) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ d → |s.im| ≤ 9 → ‖zetaLogDerivReg s‖ ≤ M := by
  obtain ⟨δ, hδ, hzf⟩ := exists_zero_free_rect (T := (9 : ℝ)) (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  set c : ℝ := 1 - δ with hcdef
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  have hcd : c ≤ d := le_trans hc1 hd
  have hrect : Set.uIcc c d ×ℂ Set.uIcc (-9 : ℝ) 9 = Set.Icc c d ×ℂ Set.Icc (-9 : ℝ) 9 := by
    rw [Set.uIcc_of_le hcd, Set.uIcc_of_le (by norm_num : (-9 : ℝ) ≤ 9)]
  have hdiff : DifferentiableOn ℂ zetaLogDerivReg (Set.Icc c d ×ℂ Set.Icc (-9 : ℝ) 9) := by
    rw [← hrect]
    exact differentiableOn_zetaLogDerivReg_rect (hzf c d (by rw [hcdef]) hc1 hd)
  have hK : IsCompact (Set.Icc c d ×ℂ Set.Icc (-9 : ℝ) 9) := isCompact_reProdIm_Icc _ _ _ _
  have hne : (Set.Icc c d ×ℂ Set.Icc (-9 : ℝ) 9).Nonempty := by
    refine ⟨1, ?_, ?_⟩
    · exact ⟨by simpa using hc1, by simpa using hd⟩
    · constructor <;> simp
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne (hdiff.continuousOn.norm)
  refine ⟨‖zetaLogDerivReg z‖, norm_nonneg _, fun s hlo hhi him => ?_⟩
  exact hmax (show s ∈ Set.Icc c d ×ℂ Set.Icc (-9 : ℝ) 9 from
    ⟨⟨hlo, hhi⟩, (abs_le.1 him).1, (abs_le.1 him).2⟩)

/-- The low-box bound in line form. -/
theorem exists_bound_zetaLogDerivReg_line_low (d : ℝ) (hd : 1 ≤ d) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℝ, 1 - δ ≤ c → c ≤ d →
      ∀ y : ℝ, |y| ≤ 9 → ‖zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M := by
  obtain ⟨δ, hδ, M, hM, hbd⟩ := exists_bound_zetaLogDerivReg_low_box d hd
  refine ⟨δ, hδ, M, hM, fun c hc hcd y hy => ?_⟩
  have hre : ((c : ℂ) + (y : ℝ) * Complex.I).re = c := by simp
  have him : ((c : ℂ) + (y : ℝ) * Complex.I).im = y := by simp
  exact hbd _ (by rw [hre]; exact hc) (by rw [hre]; exact hcd) (by rw [him]; exact hy)

end RHTower.Sieve
