import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Strict Hankel matrices from positive discrete moments

This is the atomic bridge into `MomentHankelStrict`: summable nonnegative weights at nodes that
escape every finite set define an infinitely supported representing measure. Consequently every
finite moment Hankel matrix is positive definite and has positive determinant.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace HTGeometry

noncomputable section

/-- The positive atomic measure with weight `w i` at node `x i`. -/
def discreteMomentMeasure {ι : Type*} [Countable ι]
    (w x : ι → ℝ) : Measure ℝ :=
  Measure.sum fun i ↦ ENNReal.ofReal (w i) • Measure.dirac (x i)

/-- A summable positive atomic family with nodes outside every finite set represents an
infinite-support moment sequence. -/
theorem discreteMomentHankel_posDef
    {ι : Type*} [Countable ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hsumm : ∀ k : ℕ, Summable (fun i ↦ w i * |x i| ^ k))
    (hinf : ∀ F : Finset ℝ, ∃ i, x i ∉ F ∧ 0 < w i)
    (n : ℕ) :
    (momentHankelMatrix (fun k ↦ ∑' i, w i * x i ^ k) n).PosDef := by
  let μ : Measure ℝ := discreteMomentMeasure w x
  have hint : ∀ k, Integrable (fun y : ℝ ↦ y ^ k) μ := by
    intro k
    apply integrable_sum_dirac (fun i ↦ by simp [ENNReal.ofReal_ne_top])
    convert hsumm k using 1
    funext i
    simp [ENNReal.toReal_ofReal (hw i), norm_pow, Real.norm_eq_abs]
  have hmom : ∀ k, (∑' i, w i * x i ^ k) = ∫ y, y ^ k ∂μ := by
    intro k
    rw [show μ = Measure.sum (fun i ↦ ENNReal.ofReal (w i) • Measure.dirac (x i)) by rfl]
    rw [integral_sum_dirac (fun i ↦ by simp [ENNReal.ofReal_ne_top])]
    congr 1
    funext i
    simp [ENNReal.toReal_ofReal (hw i), smul_eq_mul]
  have hμinf : ∀ F : Finset ℝ, 0 < μ {y : ℝ | y ∉ F} := by
    intro F
    obtain ⟨i, hxi, hwi⟩ := hinf F
    have hmass :
        0 < (ENNReal.ofReal (w i) • Measure.dirac (x i)) {y : ℝ | y ∉ F} := by
      simp [hxi, ENNReal.ofReal_pos.mpr hwi]
    exact hmass.trans_le ((Measure.le_sum (fun j ↦
      ENNReal.ofReal (w j) • Measure.dirac (x j)) i) {y : ℝ | y ∉ F})
  exact momentHankelMatrix_posDef_of_infiniteSupport
    (fun k ↦ ∑' i, w i * x i ^ k) hmom hint hμinf n

/-- Determinant form of `discreteMomentHankel_posDef`. -/
theorem det_discreteMomentHankel_pos
    {ι : Type*} [Countable ι] (w x : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hsumm : ∀ k : ℕ, Summable (fun i ↦ w i * |x i| ^ k))
    (hinf : ∀ F : Finset ℝ, ∃ i, x i ∉ F ∧ 0 < w i)
    (n : ℕ) :
    0 < (momentHankelMatrix (fun k ↦ ∑' i, w i * x i ^ k) n).det :=
  (discreteMomentHankel_posDef w x hw hsumm hinf n).det_pos

end
end HTGeometry
