import Mathlib

/-!
# Spectral parameters below the Selberg bound

An eigenvalue `λ` of the hyperbolic Laplacian contributes the two spectral parameters
`1/2 ± √(1/4 - λ)`.  For `0 < λ < 1/4` both parameters are real, lie strictly inside the unit
interval, are distinct from `1/2`, and are exchanged by the reflection `s ↦ 1 - s`.

This is the exact quantitative content of the small-eigenvalue witness: an eigenvalue strictly
below the Selberg bound produces two real off-critical parameters symmetric about the critical
line.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The two spectral parameters attached to an eigenvalue. -/
def selbergSpectralParameter (lam : ℝ) (upper : Bool) : ℝ :=
  if upper then 1 / 2 + Real.sqrt (1 / 4 - lam) else 1 / 2 - Real.sqrt (1 / 4 - lam)

theorem sqrt_quarter_sub_pos {lam : ℝ} (h1 : lam < 1 / 4) :
    0 < Real.sqrt (1 / 4 - lam) :=
  Real.sqrt_pos.mpr (by linarith)

theorem sqrt_quarter_sub_lt_half {lam : ℝ} (h0 : 0 < lam) :
    Real.sqrt (1 / 4 - lam) < 1 / 2 := by
  have hlt : 1 / 4 - lam < (1 / 2 : ℝ) ^ (2 : ℕ) := by norm_num; linarith
  calc Real.sqrt (1 / 4 - lam) < Real.sqrt ((1 / 2 : ℝ) ^ (2 : ℕ)) := by
        rcases le_or_gt (1 / 4 - lam) 0 with hneg | hpos
        · rw [Real.sqrt_eq_zero_of_nonpos hneg, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)]
          norm_num
        · exact Real.sqrt_lt_sqrt hpos.le hlt
    _ = 1 / 2 := by
        rw [Real.sqrt_sq (by norm_num)]

/-- **Off-critical location.**  An eigenvalue strictly between `0` and the Selberg bound places
both spectral parameters strictly inside the unit interval. -/
theorem selbergSpectralParameter_mem_Ioo {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 4)
    (upper : Bool) : selbergSpectralParameter lam upper ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpos := sqrt_quarter_sub_pos h1
  have hlt := sqrt_quarter_sub_lt_half h0
  cases upper <;> · rw [selbergSpectralParameter]; constructor <;> simp <;> linarith

/-- **Off-critical strictness.**  Neither parameter is the critical value. -/
theorem selbergSpectralParameter_ne_half {lam : ℝ} (h1 : lam < 1 / 4) (upper : Bool) :
    selbergSpectralParameter lam upper ≠ 1 / 2 := by
  have hpos := sqrt_quarter_sub_pos h1
  cases upper <;> · rw [selbergSpectralParameter]; simp; linarith

/-- **Reflection symmetry.**  The two parameters are exchanged by `s ↦ 1 - s`. -/
theorem selbergSpectralParameter_add (lam : ℝ) :
    selbergSpectralParameter lam true + selbergSpectralParameter lam false = 1 := by
  rw [selbergSpectralParameter, selbergSpectralParameter]
  simp
  ring

/-- The parameters coincide with the critical value exactly at the Selberg bound. -/
theorem selbergSpectralParameter_eq_half_iff {lam : ℝ} (hle : lam ≤ 1 / 4) (upper : Bool) :
    selbergSpectralParameter lam upper = 1 / 2 ↔ lam = 1 / 4 := by
  constructor
  · intro heq
    by_contra hne
    exact selbergSpectralParameter_ne_half (lt_of_le_of_ne hle hne) upper heq
  · intro hlam
    subst hlam
    cases upper <;> · rw [selbergSpectralParameter]; simp

/-- **Small-eigenvalue witness.**  Every eigenvalue strictly below the Selberg bound produces two
distinct real parameters inside the unit interval, symmetric about the critical value and neither
equal to it. -/
theorem selbergSmallEigenvalue_offCritical {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1 / 4) :
    selbergSpectralParameter lam true ∈ Set.Ioo (0 : ℝ) 1 ∧
      selbergSpectralParameter lam false ∈ Set.Ioo (0 : ℝ) 1 ∧
      selbergSpectralParameter lam true ≠ 1 / 2 ∧
      selbergSpectralParameter lam false ≠ 1 / 2 ∧
      selbergSpectralParameter lam true ≠ selbergSpectralParameter lam false ∧
      selbergSpectralParameter lam true + selbergSpectralParameter lam false = 1 := by
  have hpos := sqrt_quarter_sub_pos h1
  refine ⟨selbergSpectralParameter_mem_Ioo h0 h1 true,
    selbergSpectralParameter_mem_Ioo h0 h1 false,
    selbergSpectralParameter_ne_half h1 true,
    selbergSpectralParameter_ne_half h1 false, ?_,
    selbergSpectralParameter_add lam⟩
  rw [selbergSpectralParameter, selbergSpectralParameter]
  simp
  linarith

end

end GaloisForLFunctions.HTGeometry
