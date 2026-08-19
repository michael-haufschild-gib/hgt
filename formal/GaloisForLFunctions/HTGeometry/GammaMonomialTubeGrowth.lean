import GaloisForLFunctions.HTGeometry.GammaSingleBlockDatum

/-!
# A balanced monomial is a unit for negligibility

A balanced gamma monomial is bounded on every vertical tube and bounded away from zero there, so
multiplying by it preserves negligibility in both directions.  A block of terms sharing a Gamma
degree and first moment may therefore always be normalised so that its reference monomial is `1`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {r : ℕ}

/-- **A balanced gamma monomial is bounded on every tube.** -/
theorem hasTubePolyGrowth_gammaMonomial (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, ((g i : ℤ) : ℝ) * lam i = 0) :
    HasTubePolyGrowth (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g) := by
  intro M hM
  obtain ⟨T, hT⟩ := tubeLimit_gammaMonomial lam hlam g hdeg hmom hM 1 one_pos
  refine ⟨0, 2, max T 2, by norm_num, le_max_right _ _, fun σ t hσ hσM ht => ?_⟩
  have h := hT σ t hσ hσM (le_trans (le_max_left _ _) ht)
  dsimp only at h
  have hrev := norm_sub_norm_le
    (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g ((σ : ℂ) + (t : ℂ) * Complex.I)) (1 : ℂ)
  rw [norm_one] at hrev
  rw [pow_zero, mul_one]
  linarith

/-- Multiplying by a balanced monomial preserves negligibility. -/
theorem IsVerticallyNegligible.mul_gammaMonomial {f : ℂ → ℂ} (hf : IsVerticallyNegligible f)
    (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i) (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0)
    (hmom : ∑ i, ((g i : ℤ) : ℝ) * lam i = 0) :
    IsVerticallyNegligible (fun z => f z * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z) := by
  have hfun : (fun z => f z * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z)
      = fun z => gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z * f z := by
    funext z; ring
  rw [hfun]
  exact hf.mul_polyGrowth (hasTubePolyGrowth_gammaMonomial lam hlam g hdeg hmom)

/-- **A balanced monomial is a unit for negligibility.** -/
theorem isVerticallyNegligible_mul_gammaMonomial_iff {f : ℂ → ℂ}
    (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i) (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0)
    (hmom : ∑ i, ((g i : ℤ) : ℝ) * lam i = 0) :
    IsVerticallyNegligible (fun z => f z * gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g z)
      ↔ IsVerticallyNegligible f := by
  constructor
  · intro hneg
    by_contra hf
    exact not_isVerticallyNegligible_mul_gammaMonomial hf lam hlam g hdeg hmom hneg
  · intro hf
    exact hf.mul_gammaMonomial lam hlam g hdeg hmom

end

end GaloisForLFunctions.HTGeometry
