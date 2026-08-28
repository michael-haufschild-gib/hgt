import GaloisForLFunctions.RHTower.FZZCigarParityDelaySourceContinuation

/-!
# The FZZ parity Fermi–Hankel kernel is not positive

After diagonal graded KMS data proved temperature-universal, the first genuinely off-diagonal
candidate is the symmetric multiplicative Hankel kernel

`K(x,y) = fzzCigarParityDelay (x*y)`.

This file proves that its principal minor on the literal scales `1` and `2` is strictly negative.
More strongly, every nonzero real diagonal reweighting preserves that negative determinant. Thus
the source-exact Fermi kernel cannot define a positive Hilbert kernel, even after arbitrary local
positive changes of density.

The positive survivor is an exact two-scale Lorentzian signature: every such reweighted block has
one positive and one negative direction. A surviving FZZ orientation mechanism must therefore use
an indefinite/Krein interaction or a genuinely nonlocal correction, not positivity of the bare
multiplicative Fermi–Hankel kernel.
-/

namespace RHTower

noncomputable section

/-- Determinant of the literal multiplicative FZZ parity kernel on scales `1` and `2`. -/
def fzzCigarParityTwoScaleHankelMinor : ℝ :=
  fzzCigarParityDelay 1 * fzzCigarParityDelay 4 -
    fzzCigarParityDelay 2 ^ 2

/-- The first nontrivial principal minor of the source-exact Fermi–Hankel kernel is strictly
negative. -/
theorem fzzCigarParityTwoScaleHankelMinor_neg :
    fzzCigarParityTwoScaleHankelMinor < 0 := by
  rw [fzzCigarParityTwoScaleHankelMinor,
    fzzCigarParityDelay_eq_fermi (by norm_num : (0 : ℝ) < 1),
    fzzCigarParityDelay_eq_fermi (by norm_num : (0 : ℝ) < 4),
    fzzCigarParityDelay_eq_fermi (by norm_num : (0 : ℝ) < 2)]
  let a : ℝ := Real.exp 1
  have ha : 1 < a := by
    change 1 < Real.exp 1
    exact Real.one_lt_exp_iff.mpr zero_lt_one
  have he2 : Real.exp 2 = a ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    change a * a = a ^ 2
    ring
  have he4 : Real.exp 4 = a ^ 4 := by
    rw [show (4 : ℝ) = 2 + 2 by norm_num, Real.exp_add, he2]
    ring
  rw [show Real.exp 1 = a by rfl, he2, he4]
  have hB : 0 < (a ^ 2 + 1) ^ 2 := sq_pos_of_pos (by positivity)
  have hBA : (a ^ 2 + 1) ^ 2 < (a + 1) * (a ^ 4 + 1) := by
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    have ha2 : 1 < a ^ 2 := one_lt_pow₀ ha (by norm_num)
    have ha4 : a ^ 2 < a ^ 4 := by nlinarith [ha2]
    nlinarith [ha0]
  have hinv : ((a + 1) * (a ^ 4 + 1))⁻¹ < ((a ^ 2 + 1) ^ 2)⁻¹ := by
    simpa [one_div] using one_div_lt_one_div_of_lt hB hBA
  exact sub_neg.mpr (by simpa [mul_inv, inv_pow, mul_comm] using hinv)

/-- Determinant after an arbitrary real diagonal congruence by weights `w₁,w₂`. -/
def fzzCigarParityTwoScaleReweightedMinor (w₁ w₂ : ℝ) : ℝ :=
  (w₁ ^ 2 * fzzCigarParityDelay 1) *
      (w₂ ^ 2 * fzzCigarParityDelay 4) -
    (w₁ * w₂ * fzzCigarParityDelay 2) ^ 2

/-- Diagonal reweighting scales the minor by the positive-square congruence character. -/
theorem fzzCigarParityTwoScaleReweightedMinor_eq (w₁ w₂ : ℝ) :
    fzzCigarParityTwoScaleReweightedMinor w₁ w₂ =
      (w₁ * w₂) ^ 2 * fzzCigarParityTwoScaleHankelMinor := by
  rw [fzzCigarParityTwoScaleReweightedMinor, fzzCigarParityTwoScaleHankelMinor]
  ring

/-- Every nondegenerate diagonal reweighting retains a strictly negative determinant. -/
theorem fzzCigarParityTwoScaleReweightedMinor_neg
    {w₁ w₂ : ℝ} (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) :
    fzzCigarParityTwoScaleReweightedMinor w₁ w₂ < 0 := by
  rw [fzzCigarParityTwoScaleReweightedMinor_eq]
  exact mul_neg_of_pos_of_neg (sq_pos_of_ne_zero (mul_ne_zero hw₁ hw₂))
    fzzCigarParityTwoScaleHankelMinor_neg

/-- Candidate positive-kernel repair by local positive weights on the first two scales. -/
def FZZCigarParityPositiveDiagonalHankelPSD : Prop :=
  ∃ w₁ w₂ : ℝ, 0 < w₁ ∧ 0 < w₂ ∧
    0 ≤ fzzCigarParityTwoScaleReweightedMinor w₁ w₂

/-- **Positive Fermi–Hankel no-go.** No positive diagonal density can make even the first
two-scale source block positive semidefinite. -/
theorem not_fzzCigarParityPositiveDiagonalHankelPSD :
    ¬ FZZCigarParityPositiveDiagonalHankelPSD := by
  rintro ⟨w₁, w₂, hw₁, hw₂, hminor⟩
  exact (not_lt_of_ge hminor)
    (fzzCigarParityTwoScaleReweightedMinor_neg hw₁.ne' hw₂.ne')

/-- Quadratic form of the bare two-scale source block. -/
def fzzCigarParityTwoScaleQuadratic (u v : ℝ) : ℝ :=
  u ^ 2 * fzzCigarParityDelay 1 +
    2 * u * v * fzzCigarParityDelay 2 +
    v ^ 2 * fzzCigarParityDelay 4

/-- The first coordinate is a strict positive direction. -/
theorem fzzCigarParityTwoScaleQuadratic_pos :
    0 < fzzCigarParityTwoScaleQuadratic 1 0 := by
  rw [fzzCigarParityTwoScaleQuadratic]
  simp only [one_pow, one_mul, mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero]
  rw [fzzCigarParityDelay_eq_fermi (by norm_num : (0 : ℝ) < 1)]
  positivity

/-- The determinant-adapted coordinate is a strict negative direction. Together with the previous
theorem this is the exact two-scale Lorentzian survivor. -/
theorem fzzCigarParityTwoScaleQuadratic_neg :
    fzzCigarParityTwoScaleQuadratic
      (fzzCigarParityDelay 2) (-fzzCigarParityDelay 1) < 0 := by
  rw [fzzCigarParityTwoScaleQuadratic]
  have hP1 : 0 < fzzCigarParityDelay 1 := by
    rw [fzzCigarParityDelay_eq_fermi (by norm_num : (0 : ℝ) < 1)]
    positivity
  have hminor := fzzCigarParityTwoScaleHankelMinor_neg
  rw [fzzCigarParityTwoScaleHankelMinor] at hminor
  have heq :
      fzzCigarParityDelay 2 ^ 2 * fzzCigarParityDelay 1 +
          2 * fzzCigarParityDelay 2 * (-fzzCigarParityDelay 1) *
            fzzCigarParityDelay 2 +
          (-fzzCigarParityDelay 1) ^ 2 * fzzCigarParityDelay 4 =
        fzzCigarParityDelay 1 *
          (fzzCigarParityDelay 1 * fzzCigarParityDelay 4 -
            fzzCigarParityDelay 2 ^ 2) := by ring
  rw [heq]
  exact mul_neg_of_pos_of_neg hP1 hminor

end

end RHTower
