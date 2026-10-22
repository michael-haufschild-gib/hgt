import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualEigenEquation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinModularGeneratorInvariance
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Positive real Eisenstein source and its actual coordinate derivatives

The literal primitive-pair series at s=2 is a positive real sum. Its two
identity rows give E(z) >= y². Exact modular-generator reindexing and the
original differentiated series provide its invariance and Laplacian law.
-/

open Set Filter Topology
namespace GaloisForLFunctions.RHTower.SelbergPositiveEisenstein
open _root_.RHTower
noncomputable section

/-- The real weight-two point of the actual absolute-convergence chamber. -/
def parameter : D4BMEisensteinAbsoluteConvergenceParameter := ⟨2, by norm_num⟩

/-- The positive real summand of the literal primitive-pair series at s=2. -/
def seed (z : D4BMUpperHalfPlaneCoordinate) (p : D4BMPrimitiveIntegerPair) : ℝ :=
  (z.y / d4BMPoincareQuadratic z p.pair) ^ (2 : ℕ)

/-- Every complex summand is the inclusion of its positive real value. -/
theorem seed_complex (z : D4BMUpperHalfPlaneCoordinate) (p : D4BMPrimitiveIntegerPair) :
    d4BMPoincareSeed z parameter.s p = (seed z p : ℂ) := by
  simp [d4BMPoincareSeed, parameter, seed]

/-- The original absolute convergence gives genuine real summability. -/
theorem seed_summable (z : D4BMUpperHalfPlaneCoordinate) : Summable (seed z) := by
  have h := Complex.hasSum_re (summable_d4BMPoincareSeed z parameter).hasSum
  simpa only [seed_complex, Complex.ofReal_re] using h.summable

/-- The actual real nonholomorphic Eisenstein function at s=2. -/
def E (z : D4BMUpperHalfPlaneCoordinate) : ℝ :=
  (d4BMRawEisensteinPoincareSeries z parameter).re

/-- Exact positive-series normalization of the original Eisenstein function. -/
theorem E_eq (z : D4BMUpperHalfPlaneCoordinate) : E z = (1 / 2 : ℝ) * ∑' p, seed z p := by
  unfold E d4BMRawEisensteinPoincareSeries
  rw [Complex.mul_re, Complex.re_tsum (summable_d4BMPoincareSeed z parameter)]
  simp only [seed_complex, Complex.ofReal_re]
  norm_num

/-- The two primitive identity rows give the full y² lower bound. -/
theorem height_sq_le (z : D4BMUpperHalfPlaneCoordinate) : z.y ^ (2 : ℕ) ≤ E z := by
  classical
  let p := (d4BMPrimitiveFirstRowPairOfBool true).1
  let m := (d4BMPrimitiveFirstRowPairOfBool false).1
  have hne : p ≠ m := by
    intro h
    have he := congrArg (fun q : D4BMPrimitiveIntegerPair => q.pair.2) h
    norm_num [p, m, d4BMPrimitiveFirstRowPairOfBool] at he
  have h := (seed_summable z).sum_le_tsum {p, m} (fun q _ => sq_nonneg _)
  have hp : seed z p = z.y ^ (2 : ℕ) := by simp [seed, p, d4BMPrimitiveFirstRowPairOfBool, d4BMPoincareQuadratic]
  have hm : seed z m = z.y ^ (2 : ℕ) := by simp [seed, m, d4BMPrimitiveFirstRowPairOfBool, d4BMPoincareQuadratic]
  rw [Finset.sum_pair hne] at h
  change seed z p + seed z m ≤ ∑' q, seed z q at h
  rw [hp, hm] at h
  rw [E_eq]
  linarith

/-- The literal Eisenstein function is strictly positive everywhere. -/
theorem E_pos (z : D4BMUpperHalfPlaneCoordinate) : 0 < E z :=
  (sq_pos_of_pos z.y_pos).trans_le (height_sq_le z)

/-- Translation invariance is inherited from the actual primitive-pair reindexing. -/
theorem E_translate (z : D4BMUpperHalfPlaneCoordinate) : E (d4BMEisensteinTranslateCoordinate z) = E z :=
  congrArg Complex.re (d4BM_rawEisensteinPoincareSeries_translate z parameter)

/-- Inversion invariance is inherited from the actual primitive-pair reindexing. -/
theorem E_invert (z : D4BMUpperHalfPlaneCoordinate) : E (d4BMEisensteinInvertCoordinate z) = E z :=
  congrArg Complex.re (d4BM_rawEisensteinPoincareSeries_invert z parameter)

/-- Original horizontal first derivative, followed by real projection. -/
def Ex (z : D4BMUpperHalfPlaneCoordinate) : ℝ := (d4BMRawPoincareHorizontalFirstJet z parameter).re
/-- Original vertical first derivative, followed by real projection. -/
def Ey (z : D4BMUpperHalfPlaneCoordinate) : ℝ := (d4BMRawPoincareVerticalFirstJet z parameter).re
/-- Original horizontal second derivative, followed by real projection. -/
def Exx (z : D4BMUpperHalfPlaneCoordinate) : ℝ := (d4BMRawPoincareHorizontalSecondJet z parameter).re
/-- Original vertical second derivative, followed by real projection. -/
def Eyy (z : D4BMUpperHalfPlaneCoordinate) : ℝ := (d4BMRawPoincareVerticalSecondJet z parameter).re

/-- The first horizontal jet differentiates the actual function. -/
theorem horizontal_derivative (z : D4BMUpperHalfPlaneCoordinate) :
    HasDerivAt (fun x => E (d4BMHorizontalCoordinate z x)) (Ex z) z.x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt z.x (hasDerivAt_d4BMRawEisensteinPoincareSeries_horizontal z parameter)

/-- The second horizontal jet differentiates the actual first jet. -/
theorem horizontal_second_derivative (z : D4BMUpperHalfPlaneCoordinate) :
    HasDerivAt (fun x => Ex (d4BMHorizontalCoordinate z x)) (Exx z) z.x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt z.x (hasDerivAt_d4BMRawPoincareHorizontalFirstJet_horizontal z parameter)

/-- The first vertical jet differentiates the literal vertical source slice. -/
theorem vertical_derivative (z : D4BMUpperHalfPlaneCoordinate) :
    HasDerivAt (fun y => (d4BMRawPoincareVerticalSlice z parameter y).re) (Ey z) z.y := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt z.y (hasDerivAt_d4BMRawPoincareVerticalSlice z parameter)

/-- The second vertical jet differentiates the literal first-jet slice. -/
theorem vertical_second_derivative (z : D4BMUpperHalfPlaneCoordinate) :
    HasDerivAt (fun y => (d4BMRawPoincareVerticalFirstJetSlice z parameter y).re) (Eyy z) z.y := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt z.y (hasDerivAt_d4BMRawPoincareVerticalFirstJetSlice z parameter)

/-- The positive-sign hyperbolic Laplacian is twice the original positive function. -/
theorem eigen_equation (z : D4BMUpperHalfPlaneCoordinate) :
    z.y ^ (2 : ℕ) * (Exx z + Eyy z) = 2 * E z := by
  have h := congrArg Complex.re (d4BM_rawEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z parameter)
  norm_num [parameter, pow_two, Complex.mul_re, Complex.mul_im, Exx, Eyy, E] at h ⊢
  exact h

end
end GaloisForLFunctions.RHTower.SelbergPositiveEisenstein
