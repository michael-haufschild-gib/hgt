import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRectangle

/-!
# A bound for the regular reciprocal near the real axis

The quantitative bound for `‖1/ζ‖` left of the abscissa (`norm_inv_riemannZeta_left_le`) needs the
segment joining `β + iγ` to `σ + iγ` to avoid the pole, so it says nothing at height `γ = 0` — the
segment there runs along the real axis straight through `s = 1`.  The left edge of the truncated
rectangle passes through that height.

Near the real axis the bound comes from the same source as the zero-freeness did: the box is
compact, `invZeta` is continuous on it (the pole costing nothing, since `invZeta 1 = 0`), and a
continuous function on a compact set is bounded.  The constant is not explicit and does not need to
be — it does not depend on the truncation height.
-/

namespace RHTower.Sieve

open Complex RHTower

/-- A closed complex box is compact. -/
theorem isCompact_reProdIm_Icc (a b c d : ℝ) :
    IsCompact (Set.Icc a b ×ℂ Set.Icc c d) := by
  have himg : Set.Icc a b ×ℂ Set.Icc c d =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℝ) * Complex.I) '' (Set.Icc a b ×ˢ Set.Icc c d) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z.re, z.im), ⟨hz.1, hz.2⟩, ?_⟩
      apply Complex.ext <;> simp
    · rintro ⟨p, hp, rfl⟩
      exact ⟨by simpa using hp.1, by simpa using hp.2⟩
  rw [himg]
  exact (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)

/-- **`invZeta` is bounded on a box straddling the abscissa near the real axis.**  Compactness plus
continuity; the constant carries no rate but is independent of the truncation height. -/
theorem exists_bound_invZeta_low_box (d : ℝ) (hd : 1 ≤ d) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧
      ∀ s : ℂ, 1 - δ ≤ s.re → s.re ≤ d → |s.im| ≤ 1 → ‖invZeta s‖ ≤ M := by
  obtain ⟨δ, hδ, hzf⟩ := exists_zero_free_rect (T := (1 : ℝ)) (by norm_num)
  refine ⟨δ, hδ, ?_⟩
  set c : ℝ := 1 - δ with hcdef
  have hc1 : c ≤ 1 := by rw [hcdef]; linarith
  have hcd : c ≤ d := le_trans hc1 hd
  have hrect : Set.uIcc c d ×ℂ Set.uIcc (-1 : ℝ) 1 = Set.Icc c d ×ℂ Set.Icc (-1 : ℝ) 1 := by
    rw [Set.uIcc_of_le hcd, Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  have hdiff : DifferentiableOn ℂ invZeta (Set.Icc c d ×ℂ Set.Icc (-1 : ℝ) 1) := by
    rw [← hrect]
    exact differentiableOn_invZeta_rect (hzf c d (by rw [hcdef]) hc1 hd)
  have hK : IsCompact (Set.Icc c d ×ℂ Set.Icc (-1 : ℝ) 1) := isCompact_reProdIm_Icc _ _ _ _
  have hne : (Set.Icc c d ×ℂ Set.Icc (-1 : ℝ) 1).Nonempty := by
    refine ⟨1, ?_, ?_⟩
    · exact ⟨by simpa using hc1, by simpa using hd⟩
    · constructor <;> simp
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn hne (hdiff.continuousOn.norm)
  refine ⟨‖invZeta z‖, norm_nonneg _, fun s hlo hhi him => ?_⟩
  exact hmax (show s ∈ Set.Icc c d ×ℂ Set.Icc (-1 : ℝ) 1 from
    ⟨⟨hlo, hhi⟩, (abs_le.1 him).1, (abs_le.1 him).2⟩)

/-- The bound in the form the edge estimates consume: a uniform bound for `‖invZeta‖` along the
part of a vertical line lying near the real axis. -/
theorem exists_bound_invZeta_line_low (d : ℝ) (hd : 1 ≤ d) :
    ∃ δ > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ c : ℝ, 1 - δ ≤ c → c ≤ d →
      ∀ y : ℝ, |y| ≤ 1 → ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M := by
  obtain ⟨δ, hδ, M, hM, hbd⟩ := exists_bound_invZeta_low_box d hd
  refine ⟨δ, hδ, M, hM, fun c hc hcd y hy => ?_⟩
  have hre : ((c : ℂ) + (y : ℝ) * Complex.I).re = c := by simp
  have him : ((c : ℂ) + (y : ℝ) * Complex.I).im = y := by simp
  exact hbd _ (by rw [hre]; exact hc) (by rw [hre]; exact hcd) (by rw [him]; exact hy)

end RHTower.Sieve
