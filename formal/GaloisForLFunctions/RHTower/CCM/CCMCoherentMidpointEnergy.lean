import GaloisForLFunctions.RHTower.CCM.CCMCoherentReflectedCancellation

/-!
# Midpoint reflection splits the actual coherent energy

Real linear combinations of translates have the same norm as their
midpoint-reflected combinations. Hence the actual prime-plus-terminal
field splits into a visible half-difference and an invisible half-sum.
The signed current is preserved and the energy removed is an exact square.
No symmetry or reality assumption on the physical source is required.
-/

noncomputable section
open Complex MeasureTheory
open scoped InnerProduct BigOperators

namespace RHTower

private theorem reflected_translation_pair (r s t : ℝ) (f : SoninL2) :
    (inner ℂ (logTranslationCLM (r+s) f) (logTranslationCLM (r+t) f)).re =
      (inner ℂ (logTranslationCLM (-s) f) (logTranslationCLM (-t) f)).re := by
  have he : inner ℂ (logTranslationCLM (r+s) f) (logTranslationCLM (r+t) f) =
      inner ℂ (logTranslationCLM (-t) f) (logTranslationCLM (-s) f) := by
    rw [inner_logTranslationCLM (r+s), inner_logTranslationCLM (-t),
      logTranslationCLM_add_apply, logTranslationCLM_add_apply]
    rw [show -(r+s)+(r+t) = -(-t)+(-s) by ring]
  rw [he]
  exact inner_re_symm (𝕜 := ℂ) (logTranslationCLM (-t) f) (logTranslationCLM (-s) f)

/-- Every finite real translation packet preserves energy under midpoint reflection. -/
theorem norm_sq_real_translation_packet_reflection {ι : Type*} (I : Finset ι)
    (c s : ι → ℝ) (r : ℝ) (f : SoninL2) :
    ‖∑ i ∈ I, (c i : ℂ) • logTranslationCLM (r+s i) f‖ ^ 2 =
      ‖∑ i ∈ I, (c i : ℂ) • logTranslationCLM (-s i) f‖ ^ 2 := by
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ _ _).re = (inner ℂ _ _).re
  simp only [sum_inner, inner_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    reflected_translation_pair]

/-- Reflection preserves the full field energy, including the oriented terminal term. -/
theorem norm_sq_ccmActualHeadReflectedCoherentField (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadReflectedCoherentField T N f r‖ ^ 2 =
      ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2 := by
  have h := norm_sq_real_translation_packet_reflection (Finset.range N).insertNone
    (fun o : Option ℕ => o.elim (ccmActualHeadQuantileTerminalDisplacementDensity T N r)
      (fun n => ccmOutgoingQuantileDisplacementCellDensity n r))
    (fun o : Option ℕ => o.elim T (fun n => Real.log n)) r f
  simpa only [Finset.sum_insertNone, Option.elim,
    ccmActualHeadReflectedCoherentField, ccmActualHeadQuantileCompletedCoherentField,
    ccmActualHeadQuantileBulkCoherentField, ccmActualHeadQuantileCellCoherentField,
    ccmActualHeadQuantileTerminalCoherentField, add_comm] using h

def ccmActualHeadMidpointOddField (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  ((1 / 2 : ℝ) : ℂ) • (ccmActualHeadQuantileCompletedCoherentField T N f r -
    ccmActualHeadReflectedCoherentField T N f r)

def ccmActualHeadMidpointEvenField (T : ℝ) (N : ℕ) (f : SoninL2) (r : ℝ) : SoninL2 :=
  ((1 / 2 : ℝ) : ℂ) • (ccmActualHeadQuantileCompletedCoherentField T N f r +
    ccmActualHeadReflectedCoherentField T N f r)

private theorem norm_sq_half (v : SoninL2) :
    ‖((1 / 2 : ℝ) : ℂ) • v‖ ^ 2 = ‖v‖ ^ 2 / 4 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Both pieces are literal components of the complete arithmetic field. -/
theorem ccmActualHeadCoherentField_eq_midpoint_parts (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    ccmActualHeadQuantileCompletedCoherentField T N f r =
      ccmActualHeadMidpointOddField T N f r + ccmActualHeadMidpointEvenField T N f r := by
  unfold ccmActualHeadMidpointOddField ccmActualHeadMidpointEvenField
  rw [← smul_add]
  have he : ∀ v w : SoninL2, (v-w)+(v+w) = (2 : ℂ) • v := by
    intro v w
    rw [two_smul]
    abel
  rw [he, smul_smul]
  norm_num

/-- The half-sum is invisible to the exact signed current. -/
theorem re_inner_increment_midpointEven_zero (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    (inner ℂ (logTranslationCLM r f - f) (ccmActualHeadMidpointEvenField T N f r)).re = 0 := by
  rw [ccmActualHeadMidpointEvenField, inner_smul_right, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    re_inner_increment_completed_add_reflected_zero, mul_zero]

/-- The half-difference retains the complete prime and terminal current. -/
theorem re_inner_increment_midpointOdd (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    (inner ℂ (logTranslationCLM r f - f) (ccmActualHeadMidpointOddField T N f r)).re =
      (inner ℂ (logTranslationCLM r f - f)
        (ccmActualHeadQuantileCompletedCoherentField T N f r)).re := by
  conv_rhs => rw [ccmActualHeadCoherentField_eq_midpoint_parts T N f r]
  rw [inner_add_right, Complex.add_re, re_inner_increment_midpointEven_zero, add_zero]

/-- Exact energy conservation under decomposition into midpoint parity components. -/
theorem norm_sq_ccmActualHeadCoherentField_midpoint_split (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2 =
      ‖ccmActualHeadMidpointOddField T N f r‖ ^ 2 +
        ‖ccmActualHeadMidpointEvenField T N f r‖ ^ 2 := by
  rw [ccmActualHeadMidpointOddField, ccmActualHeadMidpointEvenField,
    norm_sq_half, norm_sq_half, norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ),
    norm_sq_ccmActualHeadReflectedCoherentField]
  ring

theorem norm_sq_ccmActualHeadMidpointOddField_le (T : ℝ) (N : ℕ)
    (f : SoninL2) (r : ℝ) :
    ‖ccmActualHeadMidpointOddField T N f r‖ ^ 2 ≤
      ‖ccmActualHeadQuantileCompletedCoherentField T N f r‖ ^ 2 := by
  rw [norm_sq_ccmActualHeadCoherentField_midpoint_split]
  exact le_add_of_nonneg_right (sq_nonneg _)

end RHTower
