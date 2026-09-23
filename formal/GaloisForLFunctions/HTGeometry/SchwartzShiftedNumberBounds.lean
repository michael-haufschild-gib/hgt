import GaloisForLFunctions.HTGeometry.SchwartzOscillatorAlgebra

/-!
# The shifted number operator dominates the oscillator operators

The number operator is nonnegative for the `L²` inner product, because its pairing against a
function is the squared norm of the annihilation operator applied to it.  So the shifted operator
`K = N + 4π` satisfies `4π‖g‖₂ ≤ ‖Kg‖₂`, and the quadratic bounds of the oscillator operators
become bounds by `K` alone:

`4π‖Ag‖₂² ≤ ‖Kg‖₂²` and `2π‖Bg‖₂² ≤ ‖Kg‖₂²`.

Commuting `K` past the two operators only shifts it — `K A = A (K + 4π)` and `K B = B N` — so a
word in the oscillator operators is bounded by a single power of `K`, with no accumulation of
lower-order terms.

* `schwartzPair_conj_self` : the pairing of a conjugate against itself is the squared `L²` norm.
* `schwartzPair_conj_numberCLM` : **the number operator is nonnegative.**
* `norm_le_shiftedNumberCLM` : **`4π‖g‖₂ ≤ ‖Kg‖₂`.**
* `norm_creationCLM_sq_le_shifted`, `norm_annihilationCLM_sq_le_shifted` : **the oscillator
  operators are dominated by `K`.**
* `shiftedNumberCLM_creationCLM`, `shiftedNumberCLM_annihilationCLM` : the commutation rules.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-! ## The pairing of a conjugate against itself -/

theorem schwartzPair_conj_self (u : 𝓢(ℝ, ℂ)) :
    schwartzPair (SchwartzMap.conjSLM u) u
      = ((‖u.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [schwartzPair_eq_inner, conjSLM_conjSLM, inner_self_eq_norm_sq_to_K]
  norm_cast

theorem toLp_sub (u v : 𝓢(ℝ, ℂ)) :
    (u - v).toLp 2 (volume : Measure ℝ)
      = u.toLp 2 (volume : Measure ℝ) - v.toLp 2 (volume : Measure ℝ) := by
  have h := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_sub u v
  simpa using h

theorem toLp_smul (c : ℂ) (u : 𝓢(ℝ, ℂ)) :
    (c • u).toLp 2 (volume : Measure ℝ) = c • u.toLp 2 (volume : Measure ℝ) := by
  have h := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_smul c u
  rw [SchwartzMap.toLpCLM_apply, SchwartzMap.toLpCLM_apply] at h
  exact h

/-! ## The shifted number operator -/

/-- The shifted number operator `K = N + 4π`. -/
def shiftedNumberCLM : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  numberCLM + (4 * (π : ℂ)) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)

theorem shiftedNumberCLM_apply (g : 𝓢(ℝ, ℂ)) :
    shiftedNumberCLM g = numberCLM g + (4 * (π : ℂ)) • g := rfl

/-- **The number operator is nonnegative**: its pairing against a function is the squared `L²`
norm of the annihilation operator applied to it. -/
theorem schwartzPair_conj_numberCLM (g : 𝓢(ℝ, ℂ)) :
    schwartzPair (SchwartzMap.conjSLM g) (numberCLM g)
      = ((‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hadj : schwartzPair (SchwartzMap.conjSLM g) (creationCLM (annihilationCLM g))
      = schwartzPair (annihilationCLM (SchwartzMap.conjSLM g)) (annihilationCLM g) := by
    have h := schwartzPair_creationCLM (annihilationCLM g) (SchwartzMap.conjSLM g)
    rw [schwartzPair_comm (SchwartzMap.conjSLM g) (creationCLM (annihilationCLM g)),
      schwartzPair_comm (annihilationCLM (SchwartzMap.conjSLM g)) (annihilationCLM g)]
    exact h
  rw [numberCLM_apply, hadj, ← conjSLM_annihilationCLM, schwartzPair_conj_self]

/-- **The shifted number operator dominates the identity**: `4π‖g‖₂ ≤ ‖Kg‖₂`. -/
theorem norm_le_shiftedNumberCLM (g : 𝓢(ℝ, ℂ)) :
    4 * π * ‖g.toLp 2 (volume : Measure ℝ)‖
      ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := by
  have hpair : schwartzPair (SchwartzMap.conjSLM g) (shiftedNumberCLM g)
      = ((‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
        + 4 * π * ‖g.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [shiftedNumberCLM_apply, schwartzPair_add_right, schwartzPair_conj_numberCLM,
      schwartzPair_smul_right, schwartzPair_conj_self]
    push_cast
    ring
  have hnorm : ‖schwartzPair (SchwartzMap.conjSLM g) (shiftedNumberCLM g)‖
      ≤ ‖g.toLp 2 (volume : Measure ℝ)‖
        * ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := by
    have h := norm_schwartzPair_le (SchwartzMap.conjSLM g) (shiftedNumberCLM g)
    rwa [norm_toLp_conjSLM] at h
  rw [hpair, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hnorm
  rcases eq_or_lt_of_le (norm_nonneg (g.toLp 2 (volume : Measure ℝ))) with hzero | hpos
  · rw [← hzero]
    simp
  · have hge : 4 * π * ‖g.toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
        ≤ ‖g.toLp 2 (volume : Measure ℝ)‖
          * ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := by
      refine le_trans ?_ hnorm
      nlinarith [sq_nonneg ‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖]
    have h' : 4 * π * ‖g.toLp 2 (volume : Measure ℝ)‖ * ‖g.toLp 2 (volume : Measure ℝ)‖
        ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖
          * ‖g.toLp 2 (volume : Measure ℝ)‖ := by
      nlinarith [hge]
    exact le_of_mul_le_mul_right h' hpos

/-! ## The oscillator operators are dominated by the shift -/

theorem norm_creationCLM_sq_le_shifted (g : 𝓢(ℝ, ℂ)) :
    4 * π * ‖(creationCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
      ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
  have h1 := norm_toLp_creationCLM_sq_le g
  have h2 := norm_le_shiftedNumberCLM g
  have hshift : (numberCLM g + (4 * (π : ℂ)) • g) = shiftedNumberCLM g := rfl
  rw [hshift] at h1
  calc 4 * π * ‖(creationCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
      ≤ 4 * π * (‖g.toLp 2 (volume : Measure ℝ)‖
        * ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖) := by
        have hpi : (0 : ℝ) ≤ 4 * π := by positivity
        exact mul_le_mul_of_nonneg_left h1 hpi
    _ = (4 * π * ‖g.toLp 2 (volume : Measure ℝ)‖)
        * ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := by ring
    _ ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖
        * ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by ring

theorem norm_annihilationCLM_sq_le_shifted (g : 𝓢(ℝ, ℂ)) :
    2 * π * ‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
      ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
  have h1 := norm_toLp_annihilationCLM_sq_le g
  have h2 := norm_le_shiftedNumberCLM g
  have hsub : numberCLM g = shiftedNumberCLM g - (4 * (π : ℂ)) • g := by
    rw [shiftedNumberCLM_apply]
    abel
  have hsmul : ‖((4 * (π : ℂ)) • (g.toLp 2 (volume : Measure ℝ)))‖
      = 4 * π * ‖g.toLp 2 (volume : Measure ℝ)‖ := by
    rw [norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  have hN : ‖(numberCLM g).toLp 2 (volume : Measure ℝ)‖
      ≤ 2 * ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := by
    rw [hsub, toLp_sub, toLp_smul]
    refine le_trans (norm_sub_le _ _) ?_
    rw [hsmul]
    linarith [h2]
  have hg : 4 * π * ‖g.toLp 2 (volume : Measure ℝ)‖
      ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ := h2
  calc 2 * π * ‖(annihilationCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ)
      ≤ 2 * π * (‖g.toLp 2 (volume : Measure ℝ)‖
        * ‖(numberCLM g).toLp 2 (volume : Measure ℝ)‖) := by
        have hpi : (0 : ℝ) ≤ 2 * π := by positivity
        exact mul_le_mul_of_nonneg_left h1 hpi
    _ ≤ ‖(shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)‖ ^ (2 : ℕ) := by
        nlinarith [norm_nonneg (g.toLp 2 (volume : Measure ℝ)),
          norm_nonneg ((shiftedNumberCLM g).toLp 2 (volume : Measure ℝ)),
          norm_nonneg ((numberCLM g).toLp 2 (volume : Measure ℝ)), Real.pi_pos, hN, hg]

/-! ## Commuting the shift past the oscillator operators -/

/-- **`K A = A (K + 4π)`.** -/
theorem shiftedNumberCLM_creationCLM (g : 𝓢(ℝ, ℂ)) :
    shiftedNumberCLM (creationCLM g)
      = creationCLM (shiftedNumberCLM g + (4 * (π : ℂ)) • g) := by
  simp only [shiftedNumberCLM_apply, numberCLM_creationCLM, map_add, map_smul]

/-- **`K B = B N`.** -/
theorem shiftedNumberCLM_annihilationCLM (g : 𝓢(ℝ, ℂ)) :
    shiftedNumberCLM (annihilationCLM g) = annihilationCLM (numberCLM g) := by
  rw [shiftedNumberCLM_apply, numberCLM_annihilationCLM]

end GaloisForLFunctions

end
