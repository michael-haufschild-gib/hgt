import GaloisForLFunctions.ArithmeticIndexDescent.TheSectionProjectionHasACanonicalLimit

/-!
# The completed residual index is reached at a finite source stage

Source refinement decreases residual quadratic forms. Consequently each finite
residual index is at most the completed index. Entrywise convergence supplies
the reverse inequality eventually. Thus every fixed probe family has exactly
its completed negative index at all sufficiently large finite source refinements.
-/

open Matrix Filter RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics HTGeometry

/-- Decreasing every quadratic reading cannot decrease the number of negative squares. -/
theorem negIndex_antitone_of_hermQuad_le {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι ℂ} (h : ∀ x, hermQuad A x ≤ hermQuad B x) :
    hermNegIndex B ≤ hermNegIndex A := by
  obtain ⟨V, hdim, hV⟩ := exists_isPosDefOn_finrank_eq_posIndex (-B)
  have hA : IsPosDefOn (-A) V := by
    intro x hx hx0
    have hb := hV x hx hx0
    rw [hermQuad_neg] at hb ⊢
    exact lt_of_lt_of_le hb (neg_le_neg (h x))
  exact hdim.symm.trans_le (finrank_le_posIndex hA)

private def complexRealFormGram {ι : Type*} (B : LinearMap.BilinForm ℝ realTests)
    (g : ι → realTests) : Matrix ι ι ℂ := fun i j => (B (g i) (g j) : ℂ)

private theorem hermQuad_realFormGram_ofReal {ι : Type*} [Fintype ι]
    (B : LinearMap.BilinForm ℝ realTests) (g : ι → realTests) (x : ι → ℝ) :
    hermQuad (complexRealFormGram B g) (fun i => (x i : ℂ)) =
      B (realTestSynthesis g x) (realTestSynthesis g x) := by
  simp only [hermQuad, dotProduct, Matrix.mulVec, complexRealFormGram,
    Pi.star_apply, Complex.star_def, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum, Complex.im_sum,
    zero_mul, sub_zero, mul_zero, realTestSynthesis, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem hermQuad_realFormGram {m : ℕ}
    (B : LinearMap.BilinForm ℝ realTests) (g : Fin m → realTests) (x : Fin m → ℂ) :
    hermQuad (complexRealFormGram B g) x =
      B (realTestSynthesis g (fun i => (x i).re)) (realTestSynthesis g (fun i => (x i).re)) +
      B (realTestSynthesis g (fun i => (x i).im)) (realTestSynthesis g (fun i => (x i).im)) := by
  have h := hermQuad_map_ofReal_eq_add (fun i j => B (g i) (g j)) x
  change hermQuad (complexRealFormGram B g) x =
    hermQuad (complexRealFormGram B g) (fun i => ((x i).re : ℂ)) +
    hermQuad (complexRealFormGram B g) (fun i => ((x i).im : ℂ)) at h
  rw [h, hermQuad_realFormGram_ofReal, hermQuad_realFormGram_ofReal]

variable {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
  (hw : w ≤ fullSectionRatio * atomSpacing N)

/-- The source completion lies below every finite residual in quadratic form. -/
theorem completedSectionResidualForm_self_le_finite
    (S : Finset (arithmeticSectionTests N w)) (g : realTests) :
    completedSectionResidualForm hN hw0 hw g g ≤
      realWeilForm (g - finiteSectionProjection hN hw0 hw S g)
        (g - finiteSectionProjection hN hw0 hw S g) := by
  rw [show realWeilForm (g - finiteSectionProjection hN hw0 hw S g)
      (g - finiteSectionProjection hN hw0 hw S g) =
      realWeilForm g g - finiteSectionEnergy hN hw0 hw S g from
    arithmeticSectionProjection_residual_pair hN hw0 hw (fun p : S => p.1) g g]
  change realWeilForm g g - sectionCompletionPair hN hw0 hw g g ≤ _
  rw [sectionCompletionPair_self]
  exact sub_le_sub_left (finiteSectionEnergy_le_completion hN hw0 hw S g) _

private theorem synthesis_finiteSectionResidual {ι : Type*} [Fintype ι]
    (S : Finset (arithmeticSectionTests N w)) (g : ι → realTests) (x : ι → ℝ) :
    realTestSynthesis (fun i => g i - finiteSectionProjection hN hw0 hw S (g i)) x =
      realTestSynthesis g x - finiteSectionProjection hN hw0 hw S (realTestSynthesis g x) := by
  have hp : (∑ i, x i • finiteSectionProjection hN hw0 hw S (g i)) =
      finiteSectionProjection hN hw0 hw S (realTestSynthesis g x) := by
    change (∑ i, x i • (arithmeticSectionProjectionMap hN hw0 hw (fun p : S => p.1)) (g i)) =
      (arithmeticSectionProjectionMap hN hw0 hw (fun p : S => p.1)) (∑ i, x i • g i)
    simp only [map_sum, map_smul]
  simpa only [realTestSynthesis, smul_sub, Finset.sum_sub_distrib] using
    congrArg (fun p => realTestSynthesis g x - p) hp

/-- Complex quadratic readings retain the source order through completion. -/
theorem hermQuad_completedSectionResidual_le_finite {m : ℕ}
    (S : Finset (arithmeticSectionTests N w)) (g : Fin m → realTests) (x : Fin m → ℂ) :
    hermQuad (completedSectionResidualGram hN hw0 hw g) x ≤
      hermQuad (complexWeilMixed
        (fun i => g i - finiteSectionProjection hN hw0 hw S (g i))
        (fun i => g i - finiteSectionProjection hN hw0 hw S (g i))) x := by
  change hermQuad (complexRealFormGram (completedSectionResidualForm hN hw0 hw) g) x ≤
    hermQuad (complexRealFormGram realWeilForm
      (fun i => g i - finiteSectionProjection hN hw0 hw S (g i))) x
  rw [hermQuad_realFormGram, hermQuad_realFormGram,
    synthesis_finiteSectionResidual, synthesis_finiteSectionResidual]
  exact add_le_add
    (completedSectionResidualForm_self_le_finite hN hw0 hw S _)
    (completedSectionResidualForm_self_le_finite hN hw0 hw S _)

/-- No finite residual has more negative squares than the completed source residual. -/
theorem negIndex_finiteSectionResidual_le_completed {m : ℕ}
    (S : Finset (arithmeticSectionTests N w)) (g : Fin m → realTests) :
    hermNegIndex (complexWeilMixed
      (fun i => g i - finiteSectionProjection hN hw0 hw S (g i))
      (fun i => g i - finiteSectionProjection hN hw0 hw S (g i))) ≤
      hermNegIndex (completedSectionResidualGram hN hw0 hw g) :=
  negIndex_antitone_of_hermQuad_le (hermQuad_completedSectionResidual_le_finite hN hw0 hw S g)

/-- Every fixed completed index is attained at all sufficiently large finite source stages. -/
theorem eventually_negIndex_completedSectionResidual_eq {m : ℕ} (g : Fin m → realTests) :
    ∀ᶠ S : Finset (arithmeticSectionTests N w) in atTop,
      hermNegIndex (completedSectionResidualGram hN hw0 hw g) =
        hermNegIndex (complexWeilMixed
          (fun i => g i - finiteSectionProjection hN hw0 hw S (g i))
          (fun i => g i - finiteSectionProjection hN hw0 hw S (g i))) := by
  filter_upwards [eventually_negIndex_completedSectionResidual_le hN hw0 hw g] with S hS
  exact le_antisymm hS (negIndex_finiteSectionResidual_le_completed hN hw0 hw S g)

/-- Completion's finite index is exactly the index of an actual smooth Weil Gram. -/
theorem exists_actual_weilGram_with_completion_index {m : ℕ} (g : Fin m → realTests) :
    ∃ q : Fin m → realTests,
      hermNegIndex (completedSectionResidualGram hN hw0 hw g) =
        hermNegIndex (weilGram
          (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (fun j => cx (q j).1)) := by
  obtain ⟨S, hS⟩ := (eventually_negIndex_completedSectionResidual_eq hN hw0 hw g).exists
  refine ⟨fun j => g j - finiteSectionProjection hN hw0 hw S (g j), ?_⟩
  simpa only [complexWeilMixed_eq_weilGram] using hS

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.negIndex_finiteSectionResidual_le_completed
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.eventually_negIndex_completedSectionResidual_eq
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_actual_weilGram_with_completion_index
