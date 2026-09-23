/-
# Chen--Gupta--Li Proposition 5.1 `S₁` reassembly

The source `S₁` carrier is exactly the disjoint union of its three axial
punctured-frequency rays.  This module proves that decomposition, transports
absolute convergence, and combines the three closed ray estimates into the
literal `S₁` power saving.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiProposition51CyclicAxes

open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

/-- The source `S₁` frequency carrier is the disjoint sum of its three
punctured coordinate rays. -/
def cglProposition51S1FrequencyEquiv :
    {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m} ≃
      (CGLProposition51PuncturedFrequency ⊕ CGLProposition51PuncturedFrequency ⊕
        CGLProposition51PuncturedFrequency) where
  toFun x := by
    classical
    exact if h₁ : x.1.1.1 ≠ 0 then
      Sum.inl ⟨x.1.1.1, h₁⟩
    else if h₂ : x.1.1.2 ≠ 0 then
      Sum.inr (Sum.inl ⟨x.1.1.2, h₂⟩)
    else
      Sum.inr (Sum.inr ⟨x.1.2, by
        intro h₃
        rcases x.2 with h | h | h
        · exact h₁ h.1
        · exact h₂ h.2.1
        · exact h.2.2 h₃⟩)
  invFun
    | Sum.inl m => ⟨cglProposition51FirstAxialFrequencyVector m.1,
        Or.inl ⟨m.2, rfl, rfl⟩⟩
    | Sum.inr (Sum.inl m) => ⟨cglProposition51SecondAxialFrequencyVector m.1,
        Or.inr (Or.inl ⟨rfl, m.2, rfl⟩)⟩
    | Sum.inr (Sum.inr m) => ⟨cglProposition51AxialFrequencyVector m.1,
        Or.inr (Or.inr ⟨rfl, rfl, m.2⟩)⟩
  left_inv x := by
    rcases x with ⟨⟨⟨m₁, m₂⟩, m₃⟩, h⟩
    rcases h with h | h | h
    · apply Subtype.ext
      change m₁ ≠ 0 ∧ m₂ = 0 ∧ m₃ = 0 at h
      simp only [dif_pos h.1]
      change ((m₁, 0), 0) = ((m₁, m₂), m₃)
      simp [h.2.1, h.2.2]
    · apply Subtype.ext
      change m₁ = 0 ∧ m₂ ≠ 0 ∧ m₃ = 0 at h
      have hm₁ : ¬ m₁ ≠ 0 := by simp [h.1]
      simp only [dif_neg hm₁, dif_pos h.2.1]
      change ((0, m₂), 0) = ((m₁, m₂), m₃)
      simp [h.1, h.2.2]
    · apply Subtype.ext
      change m₁ = 0 ∧ m₂ = 0 ∧ m₃ ≠ 0 at h
      have hm₁ : ¬ m₁ ≠ 0 := by simp [h.1]
      have hm₂ : ¬ m₂ ≠ 0 := by simp [h.2.1]
      simp only [dif_neg hm₁, dif_neg hm₂]
      change ((0, 0), m₃) = ((m₁, m₂), m₃)
      simp [h.1, h.2.1]
  right_inv x := by
    rcases x with m | m | m
    · simp [cglProposition51FirstAxialFrequencyVector, m.2,
        cglProposition51SecondAxialFrequencyVector, cglProposition51AxialFrequencyVector]
    · simp [cglProposition51FirstAxialFrequencyVector,
        cglProposition51SecondAxialFrequencyVector, m.2, cglProposition51AxialFrequencyVector]
    · simp [cglProposition51FirstAxialFrequencyVector,
        cglProposition51SecondAxialFrequencyVector, cglProposition51AxialFrequencyVector, m.2]

/-- Absolute convergence of the first `S₁` ray, transported from the closed
third-ray reduction. -/
theorem cglProposition51_firstAxis_norm_summable
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    Summable fun m : CGLProposition51PuncturedFrequency =>
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51FirstAxialFrequencyVector m.val)‖ := by
  refine Summable.congr (cglProposition51_axialFrequencyTerm_norm_summable P w N n) fun m => ?_
  exact (congrArg norm (cglProposition51_firstAxis_term_eq_thirdAxis w m.val)).symm

/-- Absolute convergence of the second `S₁` ray, transported from the closed
third-ray reduction. -/
theorem cglProposition51_secondAxis_norm_summable
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    Summable fun m : CGLProposition51PuncturedFrequency =>
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) (cglProposition51SecondAxialFrequencyVector m.val)‖ := by
  refine Summable.congr (cglProposition51_axialFrequencyTerm_norm_summable P w N n) fun m => ?_
  exact (congrArg norm (cglProposition51_secondAxis_term_eq_thirdAxis w m.val)).symm

/-- Absolute convergence of the literal source `S₁` coefficient series. -/
theorem cglProposition51S1_norm_summable
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    Summable fun m : {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m} =>
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) m.val‖ := by
  let F : (ℤ × ℤ) × ℤ → ℝ := fun m =>
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) m‖
  let e := cglProposition51S1FrequencyEquiv
  let f : (CGLProposition51PuncturedFrequency ⊕ CGLProposition51PuncturedFrequency ⊕
      CGLProposition51PuncturedFrequency) → ℝ := fun x =>
    match x with
    | Sum.inl m => F (cglProposition51FirstAxialFrequencyVector m.val)
    | Sum.inr (Sum.inl m) => F (cglProposition51SecondAxialFrequencyVector m.val)
    | Sum.inr (Sum.inr m) => F (cglProposition51AxialFrequencyVector m.val)
  have hfirst : Summable fun m : CGLProposition51PuncturedFrequency =>
      F (cglProposition51FirstAxialFrequencyVector m.val) := by
    simpa only [F] using cglProposition51_firstAxis_norm_summable P w N n
  have hsecond : Summable fun m : CGLProposition51PuncturedFrequency =>
      F (cglProposition51SecondAxialFrequencyVector m.val) := by
    simpa only [F] using cglProposition51_secondAxis_norm_summable P w N n
  have hthird : Summable fun m : CGLProposition51PuncturedFrequency =>
      F (cglProposition51AxialFrequencyVector m.val) := by
    simpa only [F] using cglProposition51_axialFrequencyTerm_norm_summable P w N n
  have hsecond' : Summable fun m : CGLProposition51PuncturedFrequency =>
      f (Sum.inr (Sum.inl m)) := by
    simpa only [f] using hsecond
  have hthird' : Summable fun m : CGLProposition51PuncturedFrequency =>
      f (Sum.inr (Sum.inr m)) := by
    simpa only [f] using hthird
  have hrest : Summable (fun x : CGLProposition51PuncturedFrequency ⊕
      CGLProposition51PuncturedFrequency => f (Sum.inr x)) := by
    refine Summable.sum (fun x : CGLProposition51PuncturedFrequency ⊕
      CGLProposition51PuncturedFrequency => f (Sum.inr x)) ?_ ?_
    · exact hsecond'
    · exact hthird'
  have hsum : Summable f := by
    refine Summable.sum f ?_ hrest
    simpa only [f, Function.comp_def] using hfirst
  apply e.symm.summable_iff.mp
  refine Summable.congr hsum fun x => ?_
  rcases x with m | m | m
  · simp [e, f, F, cglProposition51S1FrequencyEquiv, m.2,
      cglProposition51FirstAxialFrequencyVector,
      cglProposition51SecondAxialFrequencyVector, cglProposition51AxialFrequencyVector]
  · simp [e, f, F, cglProposition51S1FrequencyEquiv,
      cglProposition51FirstAxialFrequencyVector, cglProposition51SecondAxialFrequencyVector, m.2,
      cglProposition51AxialFrequencyVector]
  · simp [e, f, F, cglProposition51S1FrequencyEquiv,
      cglProposition51FirstAxialFrequencyVector,
      cglProposition51SecondAxialFrequencyVector, cglProposition51AxialFrequencyVector, m.2]

/-- Exact decomposition of the absolute `S₁` coefficient mass into its three
disjoint coordinate-ray masses. -/
theorem cglProposition51S1_norm_tsum_eq_rays
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (w : CGLRealSmoothBump) (N : CGLPositiveLength) (n : ℕ) :
    ∑' m : {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m},
      ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
        (cglLemma45FibreRows P) m.val‖ =
      (∑' m : CGLProposition51PuncturedFrequency,
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51FirstAxialFrequencyVector m.val)‖) +
        ((∑' m : CGLProposition51PuncturedFrequency,
          ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
            (cglLemma45FibreRows P) (cglProposition51SecondAxialFrequencyVector m.val)‖) +
          ∑' m : CGLProposition51PuncturedFrequency,
            ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
              (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖) := by
  let F : (ℤ × ℤ) × ℤ → ℝ := fun m =>
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) m‖
  let e := cglProposition51S1FrequencyEquiv
  let f : (CGLProposition51PuncturedFrequency ⊕ CGLProposition51PuncturedFrequency ⊕
      CGLProposition51PuncturedFrequency) → ℝ := fun x =>
    match x with
    | Sum.inl m => F (cglProposition51FirstAxialFrequencyVector m.val)
    | Sum.inr (Sum.inl m) => F (cglProposition51SecondAxialFrequencyVector m.val)
    | Sum.inr (Sum.inr m) => F (cglProposition51AxialFrequencyVector m.val)
  have hfirst : Summable fun m : CGLProposition51PuncturedFrequency =>
      F (cglProposition51FirstAxialFrequencyVector m.val) := by
    simpa only [F] using cglProposition51_firstAxis_norm_summable P w N n
  have hsecond : Summable fun m : CGLProposition51PuncturedFrequency =>
      F (cglProposition51SecondAxialFrequencyVector m.val) := by
    simpa only [F] using cglProposition51_secondAxis_norm_summable P w N n
  have hthird : Summable fun m : CGLProposition51PuncturedFrequency =>
      F (cglProposition51AxialFrequencyVector m.val) := by
    simpa only [F] using cglProposition51_axialFrequencyTerm_norm_summable P w N n
  have hsecond' : Summable fun m : CGLProposition51PuncturedFrequency =>
      f (Sum.inr (Sum.inl m)) := by
    simpa only [f] using hsecond
  have hthird' : Summable fun m : CGLProposition51PuncturedFrequency =>
      f (Sum.inr (Sum.inr m)) := by
    simpa only [f] using hthird
  have hrest : Summable (fun x : CGLProposition51PuncturedFrequency ⊕
      CGLProposition51PuncturedFrequency => f (Sum.inr x)) := by
    refine Summable.sum (fun x : CGLProposition51PuncturedFrequency ⊕
      CGLProposition51PuncturedFrequency => f (Sum.inr x)) ?_ ?_
    · exact hsecond'
    · exact hthird'
  have hfirst' : Summable (f ∘ Sum.inl) := by
    simpa only [f, Function.comp_def] using hfirst
  let g : CGLProposition51PuncturedFrequency ⊕
      CGLProposition51PuncturedFrequency → ℝ := fun x =>
    match x with
    | Sum.inl m => F (cglProposition51SecondAxialFrequencyVector m.val)
    | Sum.inr m => F (cglProposition51AxialFrequencyVector m.val)
  have hsecondg : Summable (g ∘ Sum.inl) := by
    simpa only [g, Function.comp_def] using hsecond
  have hthirdg : Summable (g ∘ Sum.inr) := by
    simpa only [g, Function.comp_def] using hthird
  have hfg (x : CGLProposition51PuncturedFrequency ⊕
      CGLProposition51PuncturedFrequency) : f (Sum.inr x) = g x := by
    rcases x with m | m <;> rfl
  calc
    ∑' m : {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m}, F m.val =
      ∑' x, F (e.symm x).val := (e.symm.tsum_eq (fun m => F m.val)).symm
    _ = ∑' x, f x := by
        apply tsum_congr
        intro x
        rcases x with m | m | m
        · simp [e, f, F, cglProposition51S1FrequencyEquiv, m.2,
            cglProposition51FirstAxialFrequencyVector,
            cglProposition51SecondAxialFrequencyVector, cglProposition51AxialFrequencyVector]
        · simp [e, f, F, cglProposition51S1FrequencyEquiv,
            cglProposition51FirstAxialFrequencyVector, cglProposition51SecondAxialFrequencyVector, m.2,
            cglProposition51AxialFrequencyVector]
        · simp [e, f, F, cglProposition51S1FrequencyEquiv,
            cglProposition51FirstAxialFrequencyVector,
            cglProposition51SecondAxialFrequencyVector, cglProposition51AxialFrequencyVector, m.2]
    _ = (∑' m : CGLProposition51PuncturedFrequency,
        F (cglProposition51FirstAxialFrequencyVector m.val)) +
        ∑' x : CGLProposition51PuncturedFrequency ⊕ CGLProposition51PuncturedFrequency,
          f (Sum.inr x) := hfirst'.tsum_sum hrest
    _ = (∑' m : CGLProposition51PuncturedFrequency,
        F (cglProposition51FirstAxialFrequencyVector m.val)) +
        ∑' x : CGLProposition51PuncturedFrequency ⊕ CGLProposition51PuncturedFrequency,
          g x := by
      congr 1
      exact tsum_congr hfg
    _ = (∑' m : CGLProposition51PuncturedFrequency,
        F (cglProposition51FirstAxialFrequencyVector m.val)) +
        ((∑' m : CGLProposition51PuncturedFrequency,
          F (cglProposition51SecondAxialFrequencyVector m.val)) +
          ∑' m : CGLProposition51PuncturedFrequency,
            F (cglProposition51AxialFrequencyVector m.val)) := by
      rw [hsecondg.tsum_sum hthirdg]
    _ = _ := by rfl

/-- CGL Proposition 5.1, literal `S₁` component: the complete exactly-one-
nonzero-coordinate frequency contribution has the source's closed `X⁻¹⁰`
saving.  All regularity, separation, cutoff, and epsilon data are certified
inside `S`; no raw analytic premise is exposed to callers. -/
theorem cglProposition51S1_norm_le_literalEpsilonSourcePower
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N)
    (w : CGLRealSmoothBump) :
    ‖cglProposition51S1 w N (cglLemma45FibreModulus q) R (cglLemma45FibreRows P)‖ ≤
      3 *
        ((9 *
          (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
            (S.epsilonDenominator * 25) *
            cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
            (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ)) *
            cglProposition51PuncturedInverseSquareMass)) /
          S.base ^ (10 : ℕ)) := by
  unfold cglProposition51S1
  calc
    ‖∑' m : {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m},
        cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) m.val‖ ≤
      ∑' m : {m : (ℤ × ℤ) × ℤ // cglProposition51S1Frequency m},
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) m.val‖ :=
        norm_tsum_le_tsum_norm (cglProposition51S1_norm_summable P w N 0)
    _ =
      (∑' m : CGLProposition51PuncturedFrequency,
        ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
          (cglLemma45FibreRows P) (cglProposition51FirstAxialFrequencyVector m.val)‖) +
        ((∑' m : CGLProposition51PuncturedFrequency,
          ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
            (cglLemma45FibreRows P) (cglProposition51SecondAxialFrequencyVector m.val)‖) +
          ∑' m : CGLProposition51PuncturedFrequency,
            ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
              (cglLemma45FibreRows P) (cglProposition51AxialFrequencyVector m.val)‖) :=
      cglProposition51S1_norm_tsum_eq_rays P w N 0
    _ ≤
      ((9 *
        (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
          (S.epsilonDenominator * 25) *
          cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
          (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ)) *
          cglProposition51PuncturedInverseSquareMass)) /
        S.base ^ (10 : ℕ)) +
        (((9 *
          (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
            (S.epsilonDenominator * 25) *
            cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
            (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ)) *
            cglProposition51PuncturedInverseSquareMass)) /
          S.base ^ (10 : ℕ)) +
          ((9 *
            (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
              (S.epsilonDenominator * 25) *
              cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
              (cglSmoothBumpHtAllOrderBudget w.toCGLSmoothBump 2 / (2 * Real.pi) ^ (2 : ℕ)) *
              cglProposition51PuncturedInverseSquareMass)) /
            S.base ^ (10 : ℕ))) := by
        gcongr
        · exact cglProposition51_firstAxis_norm_tsum_le_literalEpsilonSourcePower S w
        · exact cglProposition51_secondAxis_norm_tsum_le_literalEpsilonSourcePower S w
        · exact cglProposition51_axialFrequencyTerm_norm_tsum_le_literalEpsilonSourcePower S w
    _ = _ := by ring

end RHTower
