import GaloisForLFunctions.CompletedArithmeticForms.HermiteJetCongruence
import GaloisForLFunctions.CompletedArithmeticForms.HermiteRadiusPayment
import GaloisForLFunctions.CompletedArithmeticForms.WeightedInverseStability

/-!
# Polynomial rank payment for the physical first-atom form

Adaptive contours pay the complete Hermite error in its exact Gaussian norm.
The entry cost is cubic in the degree cutoff; summing the full mixed form costs
one further dimension factor. All constants come from the literal physical source.
-/

noncomputable section

open Finset Matrix
open scoped ContDiff

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower

/-- Cubic numerator for every normalized Hermite entry through degree `N`. -/
def hermiteSourceErrorNumerator (N : ℕ) : ℝ :=
  gaussianRelativeErrorConstant * Real.exp 2 * ((N : ℝ) + 1) * ((N : ℝ) + 2) ^ 2

theorem hermiteSourceErrorNumerator_pos (N : ℕ) : 0 < hermiteSourceErrorNumerator N := by
  have hD := gaussianRelativeErrorConstant_pos
  unfold hermiteSourceErrorNumerator
  positivity

/-- The complete mixed source jet has a polynomial error in its Hermite diagonal norm. -/
theorem firstAtomWickError_normalized_jet_le {x : ℝ} {i j N : ℕ}
    (hi : i ≤ N) (hj : j ≤ N)
    (hq : 4 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x) :
    ‖mixedKernelJet (firstAtomWickError x) i j‖ ≤
      (hermiteSourceErrorNumerator N / thetaCuspSingleAtomReflectionScale 1 x) *
        Real.sqrt (hermiteGaussianNormSq i) * Real.sqrt (hermiteGaussianNormSq j) := by
  let R := Real.sqrt ((N : ℝ) + 2)
  let q := thetaCuspSingleAtomReflectionScale 1 x
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hR2 : R ^ 2 = (N : ℝ) + 2 := Real.sq_sqrt (by positivity)
  have hR4 : R ^ 4 = ((N : ℝ) + 2) ^ 2 := by
    calc
      _ = (R ^ 2) ^ 2 := by ring
      _ = _ := by rw [hR2]
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR : 1 ≤ R := by nlinarith only [hR2, hR0, hN]
  have hq3 : 3 ≤ q := by dsimp [q]; nlinarith only [hq, hN, sq_nonneg (N : ℝ)]
  have hqp : 0 < q := by linarith only [hq3]
  have hRq : 4 * R ^ 2 ≤ q := by
    rw [hR2]
    change 4 * ((N : ℝ) + 2) ^ 2 ≤ q at hq
    nlinarith only [hq, hN, sq_nonneg (N : ℝ)]
  have hR4q : R ^ 4 ≤ q := by
    rw [hR4]
    change 4 * ((N : ℝ) + 2) ^ 2 ≤ q at hq
    nlinarith only [hq, sq_nonneg ((N : ℝ) + 2)]
  have hb := firstAtomWickError_mixed_jet_le
    (hermiteContourRadius_pos i) (hermiteContourRadius_pos j) hR
    (hermiteContourRadius_add_le hi hj) hq3 hRq hR4q i j
  have hC : 0 ≤ gaussianRelativeErrorConstant * R ^ 4 / q := by
    have hD := gaussianRelativeErrorConstant_pos
    positivity
  have hp := mul_le_mul_of_nonneg_left (hermiteContourPairWeight_le hi hj) hC
  have hp' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg (hermiteGaussianNormSq i)))
    (Real.sqrt_nonneg (hermiteGaussianNormSq j))
  calc
    _ ≤ (i.factorial : ℝ) * (j.factorial : ℝ) *
        (gaussianRelativeErrorConstant * R ^ 4 / q *
          Real.exp (8 * hermiteContourRadius i * hermiteContourRadius j)) /
        (hermiteContourRadius i ^ i * hermiteContourRadius j ^ j) := hb
    _ = (gaussianRelativeErrorConstant * R ^ 4 / q) * hermiteContourPairWeight i j *
        Real.sqrt (hermiteGaussianNormSq i) * Real.sqrt (hermiteGaussianNormSq j) := by
      calc
        _ = (gaussianRelativeErrorConstant * R ^ 4 / q) *
            ((i.factorial : ℝ) / hermiteContourRadius i ^ i) *
            ((j.factorial : ℝ) / hermiteContourRadius j ^ j) *
            Real.exp (8 * hermiteContourRadius i * hermiteContourRadius j) := by ring
        _ = _ := by
          rw [hermiteContour_factorial_identity, hermiteContour_factorial_identity]
          unfold hermiteContourPairWeight
          ring
    _ ≤ (gaussianRelativeErrorConstant * R ^ 4 / q) *
        (Real.exp 2 * ((N : ℝ) + 1)) *
        Real.sqrt (hermiteGaussianNormSq i) * Real.sqrt (hermiteGaussianNormSq j) := hp'
    _ = _ := by rw [hR4]; unfold hermiteSourceErrorNumerator; ring

/-- Exact Hermite comparison head, with every Gaussian norm retained. -/
def hermiteGaussianHead (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => hermiteGaussianNormSq i.val)

/-- Mixed Hermite error of the literal first-atom source. -/
def firstAtomHermiteError (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => (mixedKernelJet (firstAtomWickError x) i.val j.val).re

/-- The analytic error is exactly the difference of the two complete Hermite heads. -/
theorem firstAtomHermiteError_eq (N : ℕ) (x : ℝ) :
    firstAtomHermiteError N x =
      realWickJetMatrix (firstAtomNormalizedRotatedPair x) N - hermiteGaussianHead N := by
  let G : ℂ → ℂ := fun z => Complex.exp (4 * z ^ 2)
  have hG : Differentiable ℂ G := by dsimp [G]; fun_prop
  have he : firstAtomWickError x = fun p =>
      wickSourceKernel (firstAtomNormalizedRotatedPair x) p - wickSourceKernel G p := by
    funext p
    rw [wickSourceKernel_firstAtom]
    exact congrArg (fun a => firstAtomWickKernel x p.1 p.2 - a)
      (wickSourceKernel_gaussian p).symm
  have hdiag : hermiteGaussianHead N = realWickJetMatrix G N := by
    simpa only [G, hermiteGaussianHead, hermiteGaussianNormSq] using
      (realWickJetMatrix_gaussian N).symm
  rw [hdiag]
  ext i j
  change (mixedKernelJet (firstAtomWickError x) i.val j.val).re = _
  rw [he, mixedKernelJet_sub
    (contDiff_wickSourceKernel (firstAtomNormalizedRotatedPair_entire x))
    (contDiff_wickSourceKernel hG), Complex.sub_re]
  rfl

/-- The first-atom complete Hermite form has a quartic rank payment. -/
theorem firstAtomHermiteHead_relative_error_le {x : ℝ} (N : ℕ)
    (hq : 4 * ((N : ℝ) + 2) ^ 2 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (v : Fin N → ℝ) :
    |v ⬝ᵥ (realWickJetMatrix (firstAtomNormalizedRotatedPair x) N -
      hermiteGaussianHead N) *ᵥ v| ≤
      ((N : ℝ) * hermiteSourceErrorNumerator N /
        thetaCuspSingleAtomReflectionScale 1 x) * (v ⬝ᵥ hermiteGaussianHead N *ᵥ v) := by
  have hqp : 0 < thetaCuspSingleAtomReflectionScale 1 x := by
    unfold thetaCuspSingleAtomReflectionScale
    positivity
  have he := weighted_entry_error_le (firstAtomHermiteError N x)
    (fun i => Real.sqrt (hermiteGaussianNormSq i.val))
    (fun i => Real.sqrt_pos.mpr (hermiteGaussianNormSq_pos i.val))
    (div_nonneg (hermiteSourceErrorNumerator_pos N).le hqp.le)
    (fun i j => (Complex.abs_re_le_norm _).trans
      (firstAtomWickError_normalized_jet_le (Nat.le_of_lt i.isLt) (Nat.le_of_lt j.isLt) hq)) v
  rw [firstAtomHermiteError_eq] at he
  simp only [Real.sq_sqrt (hermiteGaussianNormSq_pos _).le] at he
  have hg : v ⬝ᵥ hermiteGaussianHead N *ᵥ v =
      ∑ i, hermiteGaussianNormSq i.val * v i ^ 2 := by
    simp only [hermiteGaussianHead, dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hg]
  convert he using 1
  ring

#print axioms firstAtomWickError_normalized_jet_le
#print axioms firstAtomHermiteError_eq
#print axioms firstAtomHermiteHead_relative_error_le

end GaloisForLFunctions.CompletedArithmeticForms
