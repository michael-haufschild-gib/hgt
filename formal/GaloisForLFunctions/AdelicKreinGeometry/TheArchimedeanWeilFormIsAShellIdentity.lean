import GaloisForLFunctions.AdelicKreinGeometry.TheArchimedeanGluingFormula
import GaloisForLFunctions.AdelicKreinGeometry.TheShellDecompositionOfAPoleSuccessorForm

/-!
# The archimedean Weil form is a shell identity

The Gram form of a glued state `Φ = K(|a|) − c|a|^{−1/2}|b|` at a family `g_i = (x ↦ a_i x + b_i)` with
weights `w` splits exactly into the form of the dilation data at the slopes and the shell form of the
successor at the shifts (`hermQuad_gram_archGlue_shell`):

  `Q_Φ(w) = Q_K(w; |a_i|) + 2c ∫_L^R |Σ_{b_i < t} β_i|² dt − 2c Re(ℓ̄ Σ_i β_i(R − b_i))`,

with the boost weights `β_i = w_i |a_i|^{−1/2}` and their mass `ℓ = Σ β_i`.

* **On the boost hyperplane** (`hermQuad_gram_archGlue_shell_of_boostMass`): the counterterm drops and
  `Q_Φ = Q_K + 2c ∫ |tail sums|²`, an exact sum of squares indexed by the half-line agreement shells
  `(−∞, t)` of the shifts.
* **Weil's archimedean state** (`hermQuad_gram_weilArchState_shell`): on `ℓ = 0` its form is Weil's
  dilation form plus the shell squares; the shifts contribute only squares, and all indefiniteness of
  the archimedean Weil form on the boost hyperplane is that of Weil's correlation.
-/

open Complex Finset MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- **The shell identity of a glued state.** -/
theorem hermQuad_gram_archGlue_shell (K : posUnits → ℂ) (c : ℝ) {n : ℕ}
    (g : Fin n → AffineGroupQ) (w : Fin n → ℂ) {L R : ℝ}
    (hL : ∀ a, L ≤ ((shiftOf (g a) : ℚ) : ℝ)) (hR : ∀ a, ((shiftOf (g a) : ℚ) : ℝ) ≤ R) :
    hermQuad (gram (archGlue K c) g) w =
      hermQuad (gram K fun a => slopeAbs (g a)) w +
        c * (2 * (∫ t in Set.Icc L R, normSq (tailSum (fun a => ((shiftOf (g a) : ℚ) : ℝ))
          (boostWeights Rat.AbsoluteValue.real 1 g w) t)) -
        2 * (conj (∑ a, boostWeights Rat.AbsoluteValue.real 1 g w a) *
          ∑ a, boostWeights Rat.AbsoluteValue.real 1 g w a *
            ((R - ((shiftOf (g a) : ℚ) : ℝ) : ℝ) : ℂ)).re) := by
  rw [hermQuad_gram_archGlue]
  have e : gram (fun m => (c : ℂ) * negAbsRat m) (shifts g) = (c : ℂ) • gram negAbsRat (shifts g) := by
    ext a b; simp [gram]
  rw [e, hermQuad_smul, hermQuad_gram_negAbsRat_eq (shifts g) _ hL hR]
  rfl

/-- **On the boost hyperplane the successor contributes only shell squares.** -/
theorem hermQuad_gram_archGlue_shell_of_boostMass (K : posUnits → ℂ) (c : ℝ) {n : ℕ}
    (g : Fin n → AffineGroupQ) {w : Fin n → ℂ}
    (hw : boostMassU (fun a => slopeAbs (g a)) w = 0) {L R : ℝ}
    (hL : ∀ a, L ≤ ((shiftOf (g a) : ℚ) : ℝ)) (hR : ∀ a, ((shiftOf (g a) : ℚ) : ℝ) ≤ R) :
    hermQuad (gram (archGlue K c) g) w =
      hermQuad (gram K fun a => slopeAbs (g a)) w +
        2 * c * ∫ t in Set.Icc L R, normSq (tailSum (fun a => ((shiftOf (g a) : ℚ) : ℝ))
          (boostWeights Rat.AbsoluteValue.real 1 g w) t) := by
  rw [hermQuad_gram_archGlue_shell K c g w hL hR, sum_boostWeights_eq, hw]
  simp only [map_zero, zero_mul, Complex.zero_re, mul_zero, sub_zero]
  ring

/-- **The archimedean Weil form on the boost hyperplane**: Weil's dilation form plus the squares of the
half-line shells of the shifts. -/
theorem hermQuad_gram_weilArchState_shell (c : ℝ) {n : ℕ} (g : Fin n → AffineGroupQ)
    {w : Fin n → ℂ} (hw : boostMassU (fun a => slopeAbs (g a)) w = 0) {L R : ℝ}
    (hL : ∀ a, L ≤ ((shiftOf (g a) : ℚ) : ℝ)) (hR : ∀ a, ((shiftOf (g a) : ℚ) : ℝ) ≤ R) :
    hermQuad (gram (weilArchState c) g) w =
      hermQuad (gram ratCorr fun a => slopeAbs (g a)) w +
        2 * c * ∫ t in Set.Icc L R, normSq (tailSum (fun a => ((shiftOf (g a) : ℚ) : ℝ))
          (boostWeights Rat.AbsoluteValue.real 1 g w) t) := by
  rw [weilArchState_eq_archGlue]
  exact hermQuad_gram_archGlue_shell_of_boostMass ratCorr c g hw hL hR

end GaloisForLFunctions.AdelicKreinGeometry
