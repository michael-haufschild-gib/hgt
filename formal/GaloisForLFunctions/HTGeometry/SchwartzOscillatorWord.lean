import GaloisForLFunctions.HTGeometry.SchwartzShiftedIterates

/-!
# Words in the oscillator operators are bounded by a power of the shift

Since `4π > 1`, the quadratic bounds of the oscillator operators simplify to `‖Ag‖₂ ≤ ‖Kg‖₂` and
`‖Bg‖₂ ≤ ‖Kg‖₂`.  Combined with the iterated commutation rules, an induction on the length of a
word in the two operators bounds it by a single power of the shifted number operator: for every
word `W`,

`‖W g‖₂ ≤ C · ‖K^{|W|} g‖₂`.

Every operator built from multiplication by the coordinate and differentiation is a combination of
such words, so this is the estimate the reverse seminorm comparison needs.

* `norm_creationCLM_le_shifted`, `norm_annihilationCLM_le_shifted` : the operators are contractions
  relative to the shift.
* `oscWord` : a word in the two operators.
* `oscWord_shift_bound` : **a power of the shift applied after a word is bounded by the
  corresponding power of the shift.**
* `oscWord_bound` : **`‖W g‖₂ ≤ C ‖K^{|W|} g‖₂`.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The operators are contractions relative to the shift -/

theorem one_le_four_pi : (1 : ℝ) ≤ 4 * π := by
  nlinarith [Real.two_le_pi]

theorem one_le_two_pi : (1 : ℝ) ≤ 2 * π := by
  nlinarith [Real.two_le_pi]

theorem norm_creationCLM_le_shifted (g : 𝓢(ℝ, ℂ)) :
    ‖(creationCLM g).toLp 2 (volume : Measure ℝ)‖
      ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := by
  have h := norm_creationCLM_sq_le_shifted g
  have hsq : ‖(creationCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
      ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg ‖(creationCLM g).toLp 2 (volume : Measure ℝ)‖, one_le_four_pi]
  have hroot := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hroot

theorem norm_annihilationCLM_le_shifted (g : 𝓢(ℝ, ℂ)) :
    ‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖
      ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := by
  have h := norm_annihilationCLM_sq_le_shifted g
  have hsq : ‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
      ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg ‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖, one_le_two_pi]
  have hroot := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hroot

/-! ## Words in the two operators -/

/-- A word in the creation and annihilation operators, applied to a Schwartz function: `true`
stands for the creation operator, `false` for the annihilation operator. -/
def oscWord : List Bool → 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)
  | [], g => g
  | (true :: w), g => creationCLM (oscWord w g)
  | (false :: w), g => annihilationCLM (oscWord w g)

@[simp] theorem oscWord_nil (g : 𝓢(ℝ, ℂ)) : oscWord [] g = g := rfl

@[simp] theorem oscWord_cons_true (w : List Bool) (g : 𝓢(ℝ, ℂ)) :
    oscWord (true :: w) g = creationCLM (oscWord w g) := rfl

@[simp] theorem oscWord_cons_false (w : List Bool) (g : 𝓢(ℝ, ℂ)) :
    oscWord (false :: w) g = annihilationCLM (oscWord w g) := rfl

/-- **A power of the shift applied after a word is bounded by the corresponding power of the
shift.**  The induction peels the word from the left: the commutation rules move the power of the
shift across the leading operator, at the cost of a factor `2ʲ` and a change of neighbour. -/
theorem oscWord_shift_bound (w : List Bool) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝓢(ℝ, ℂ),
      ‖((shiftedNumberCLM^[j]) (oscWord w g)).toLp 2 (volume : Measure ℝ)‖
        ≤ C * ‖((shiftedNumberCLM^[j + w.length]) g).toLp 2 (volume : Measure ℝ)‖ := by
  induction w generalizing j with
  | nil => exact ⟨1, zero_le_one, fun g => by simp⟩
  | cons b w ih =>
    obtain ⟨C, hC, hbound⟩ := ih (j + 1)
    refine ⟨2 ^ j * C, by positivity, fun g => ?_⟩
    have hlen : j + (b :: w).length = j + 1 + w.length := by
      simp only [List.length_cons]
      omega
    cases b with
    | true =>
      calc ‖((shiftedNumberCLM^[j]) (oscWord (true :: w) g)).toLp 2 (volume : Measure ℝ)‖
          = ‖(creationCLM ((shiftedPlusCLM^[j]) (oscWord w g))).toLp
              2 (volume : Measure ℝ)‖ := by
            rw [oscWord_cons_true, shiftedNumberCLM_iterate_creationCLM]
        _ ≤ ‖(shiftedNumberCLM ((shiftedPlusCLM^[j]) (oscWord w g))).toLp
              2 (volume : Measure ℝ)‖ := norm_creationCLM_le_shifted _
        _ = ‖((shiftedPlusCLM^[j]) (shiftedNumberCLM (oscWord w g))).toLp
              2 (volume : Measure ℝ)‖ := by
            rw [shiftedPlusCLM_iterate_shiftedNumberCLM]
        _ ≤ 2 ^ j * ‖((shiftedNumberCLM^[j]) (shiftedNumberCLM (oscWord w g))).toLp
              2 (volume : Measure ℝ)‖ := norm_shiftedPlusCLM_iterate_le _ _
        _ = 2 ^ j * ‖((shiftedNumberCLM^[j + 1]) (oscWord w g)).toLp
              2 (volume : Measure ℝ)‖ := by
            rw [Function.iterate_succ_apply]
        _ ≤ 2 ^ j * (C * ‖((shiftedNumberCLM^[j + 1 + w.length]) g).toLp
              2 (volume : Measure ℝ)‖) := by
            refine mul_le_mul_of_nonneg_left (hbound g) (by positivity)
        _ = 2 ^ j * C * ‖((shiftedNumberCLM^[j + (true :: w).length]) g).toLp
              2 (volume : Measure ℝ)‖ := by
            rw [hlen]
            ring
    | false =>
      calc ‖((shiftedNumberCLM^[j]) (oscWord (false :: w) g)).toLp 2 (volume : Measure ℝ)‖
          = ‖(annihilationCLM ((numberCLM^[j]) (oscWord w g))).toLp
              2 (volume : Measure ℝ)‖ := by
            rw [oscWord_cons_false, shiftedNumberCLM_iterate_annihilationCLM]
        _ ≤ ‖(shiftedNumberCLM ((numberCLM^[j]) (oscWord w g))).toLp
              2 (volume : Measure ℝ)‖ := norm_annihilationCLM_le_shifted _
        _ = ‖((numberCLM^[j]) (shiftedNumberCLM (oscWord w g))).toLp
              2 (volume : Measure ℝ)‖ := by
            rw [numberCLM_iterate_shiftedNumberCLM]
        _ ≤ 2 ^ j * ‖((shiftedNumberCLM^[j]) (shiftedNumberCLM (oscWord w g))).toLp
              2 (volume : Measure ℝ)‖ := norm_numberCLM_iterate_le _ _
        _ = 2 ^ j * ‖((shiftedNumberCLM^[j + 1]) (oscWord w g)).toLp
              2 (volume : Measure ℝ)‖ := by
            rw [Function.iterate_succ_apply]
        _ ≤ 2 ^ j * (C * ‖((shiftedNumberCLM^[j + 1 + w.length]) g).toLp
              2 (volume : Measure ℝ)‖) := by
            refine mul_le_mul_of_nonneg_left (hbound g) (by positivity)
        _ = 2 ^ j * C * ‖((shiftedNumberCLM^[j + (false :: w).length]) g).toLp
              2 (volume : Measure ℝ)‖ := by
            rw [hlen]
            ring

/-- **A word in the oscillator operators is bounded by the corresponding power of the shift.** -/
theorem oscWord_bound (w : List Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : 𝓢(ℝ, ℂ),
      ‖(oscWord w g).toLp 2 (volume : Measure ℝ)‖
        ≤ C * ‖((shiftedNumberCLM^[w.length]) g).toLp 2 (volume : Measure ℝ)‖ := by
  obtain ⟨C, hC, hbound⟩ := oscWord_shift_bound w 0
  refine ⟨C, hC, fun g => ?_⟩
  have h := hbound g
  simpa using h

end GaloisForLFunctions

end
