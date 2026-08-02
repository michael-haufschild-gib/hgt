import GaloisForLFunctions.HTGeometry.SchwartzShiftedNumberBounds

/-!
# Iterating the shift past the oscillator operators

Commuting the shifted number operator past a creation operator replaces it by the shift raised by
`4π`, and past an annihilation operator by the number operator itself.  Iterating, a power of the
shift moves across an oscillator operator at the cost of replacing it by the corresponding power
of a neighbouring operator: `Kʲ A = A (K+4π)ʲ` and `Kʲ B = B Nʲ`.

Both neighbours are dominated by the shift with a factor two — `‖Ng‖₂ ≤ 2‖Kg‖₂` and
`‖(K+4π)g‖₂ ≤ 2‖Kg‖₂` — and they commute with it, so their powers are dominated by the same power
of the shift with a factor `2ʲ`.  No binomial expansion is needed.

* `shiftedPlusCLM` : the raised shift `K + 4π`.
* `norm_numberCLM_le_two`, `norm_shiftedPlusCLM_le_two` : the two neighbours are dominated.
* `norm_numberCLM_iterate_le`, `norm_shiftedPlusCLM_iterate_le` : **their powers are dominated by
  the same power of the shift.**
* `shiftedNumberCLM_iterate_creationCLM`, `shiftedNumberCLM_iterate_annihilationCLM` : **the
  iterated commutation rules.**
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The raised shift -/

/-- The raised shift `K + 4π = N + 8π`. -/
def shiftedPlusCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  shiftedNumberCLM + (4 * (π : ℂ)) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)

theorem shiftedPlusCLM_apply (g : 𝓢(ℝ, ℂ)) :
    shiftedPlusCLM g = shiftedNumberCLM g + (4 * (π : ℂ)) • g := rfl

theorem norm_toLp_smul_four_pi (g : 𝓢(ℝ, ℂ)) :
    ‖((4 * (π : ℂ)) • g).toLp 2 (volume : Measure ℝ)‖
      = 4 * π * ‖g.toLp 2 (volume : Measure ℝ)‖ := by
  rw [toLp_smul, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num

theorem toLp_add (u v : 𝓢(ℝ, ℂ)) :
    (u + v).toLp 2 (volume : Measure ℝ)
      = u.toLp 2 (volume : Measure ℝ) + v.toLp 2 (volume : Measure ℝ) := by
  have h := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_add u v
  rw [SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply] at h
  exact h

/-! ## The two neighbours are dominated by the shift -/

theorem norm_numberCLM_le_two (g : 𝓢(ℝ, ℂ)) :
    ‖(numberCLM g).toLp 2 (volume : Measure ℝ)‖
      ≤ 2 * ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := by
  have hsub : numberCLM g = shiftedNumberCLM g - (4 * (π : ℂ)) • g := by
    rw [shiftedNumberCLM_apply]
    abel
  rw [hsub, toLp_sub]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_toLp_smul_four_pi]
  have h := norm_le_shiftedNumberCLM g
  linarith

theorem norm_shiftedPlusCLM_le_two (g : 𝓢(ℝ, ℂ)) :
    ‖(shiftedPlusCLM g).toLp 2 (volume : Measure ℝ)‖
      ≤ 2 * ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := by
  rw [shiftedPlusCLM_apply, toLp_add]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_toLp_smul_four_pi]
  have h := norm_le_shiftedNumberCLM g
  linarith

/-! ## Commuting the shift with its neighbours -/

theorem shiftedNumberCLM_numberCLM (g : 𝓢(ℝ, ℂ)) :
    shiftedNumberCLM (numberCLM g) = numberCLM (shiftedNumberCLM g) := by
  rw [shiftedNumberCLM_apply, shiftedNumberCLM_apply, map_add, map_smul]

theorem shiftedNumberCLM_shiftedPlusCLM (g : 𝓢(ℝ, ℂ)) :
    shiftedNumberCLM (shiftedPlusCLM g) = shiftedPlusCLM (shiftedNumberCLM g) := by
  rw [shiftedPlusCLM_apply, shiftedPlusCLM_apply, map_add, map_smul]

theorem numberCLM_iterate_shiftedNumberCLM (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    (numberCLM^[k]) (shiftedNumberCLM g) = shiftedNumberCLM ((numberCLM^[k]) g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ← shiftedNumberCLM_numberCLM, ih]

theorem shiftedPlusCLM_iterate_shiftedNumberCLM (k : ℕ) (g : 𝓢(ℝ, ℂ)) :
    (shiftedPlusCLM^[k]) (shiftedNumberCLM g) = shiftedNumberCLM ((shiftedPlusCLM^[k]) g) := by
  induction k generalizing g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      ← shiftedNumberCLM_shiftedPlusCLM, ih]

/-! ## The powers of the neighbours -/

theorem norm_numberCLM_iterate_le (j : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ‖((numberCLM^[j]) g).toLp 2 (volume : Measure ℝ)‖
      ≤ 2 ^ j * ‖((shiftedNumberCLM^[j]) g).toLp 2 (volume : Measure ℝ)‖ := by
  induction j generalizing g with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply]
    calc ‖(numberCLM ((numberCLM^[j]) g)).toLp 2 (volume : Measure ℝ)‖
        ≤ 2 * ‖(shiftedNumberCLM ((numberCLM^[j]) g)).toLp 2 (volume : Measure ℝ)‖ :=
          norm_numberCLM_le_two _
      _ = 2 * ‖((numberCLM^[j]) (shiftedNumberCLM g)).toLp 2 (volume : Measure ℝ)‖ := by
          rw [numberCLM_iterate_shiftedNumberCLM]
      _ ≤ 2 * (2 ^ j * ‖((shiftedNumberCLM^[j]) (shiftedNumberCLM g)).toLp
            2 (volume : Measure ℝ)‖) := by
          refine mul_le_mul_of_nonneg_left (ih (shiftedNumberCLM g)) (by norm_num)
      _ = 2 ^ (j + 1) * ‖((shiftedNumberCLM^[j]) (shiftedNumberCLM g)).toLp
            2 (volume : Measure ℝ)‖ := by
          rw [pow_succ]
          ring

theorem norm_shiftedPlusCLM_iterate_le (j : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ‖((shiftedPlusCLM^[j]) g).toLp 2 (volume : Measure ℝ)‖
      ≤ 2 ^ j * ‖((shiftedNumberCLM^[j]) g).toLp 2 (volume : Measure ℝ)‖ := by
  induction j generalizing g with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply]
    calc ‖(shiftedPlusCLM ((shiftedPlusCLM^[j]) g)).toLp 2 (volume : Measure ℝ)‖
        ≤ 2 * ‖(shiftedNumberCLM ((shiftedPlusCLM^[j]) g)).toLp 2 (volume : Measure ℝ)‖ :=
          norm_shiftedPlusCLM_le_two _
      _ = 2 * ‖((shiftedPlusCLM^[j]) (shiftedNumberCLM g)).toLp 2 (volume : Measure ℝ)‖ := by
          rw [shiftedPlusCLM_iterate_shiftedNumberCLM]
      _ ≤ 2 * (2 ^ j * ‖((shiftedNumberCLM^[j]) (shiftedNumberCLM g)).toLp
            2 (volume : Measure ℝ)‖) := by
          refine mul_le_mul_of_nonneg_left (ih (shiftedNumberCLM g)) (by norm_num)
      _ = 2 ^ (j + 1) * ‖((shiftedNumberCLM^[j]) (shiftedNumberCLM g)).toLp
            2 (volume : Measure ℝ)‖ := by
          rw [pow_succ]
          ring

/-! ## The iterated commutation rules -/

/-- **`Kʲ A = A (K+4π)ʲ`.** -/
theorem shiftedNumberCLM_iterate_creationCLM (j : ℕ) (g : 𝓢(ℝ, ℂ)) :
    (shiftedNumberCLM^[j]) (creationCLM g) = creationCLM ((shiftedPlusCLM^[j]) g) := by
  induction j generalizing g with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, shiftedNumberCLM_creationCLM, ih,
      Function.iterate_succ_apply]
    rfl

/-- **`Kʲ B = B Nʲ`.** -/
theorem shiftedNumberCLM_iterate_annihilationCLM (j : ℕ) (g : 𝓢(ℝ, ℂ)) :
    (shiftedNumberCLM^[j]) (annihilationCLM g) = annihilationCLM ((numberCLM^[j]) g) := by
  induction j generalizing g with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, shiftedNumberCLM_annihilationCLM, ih,
      Function.iterate_succ_apply]

end GaloisForLFunctions

end
