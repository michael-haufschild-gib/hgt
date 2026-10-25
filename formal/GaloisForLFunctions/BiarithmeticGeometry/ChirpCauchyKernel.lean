import GaloisForLFunctions.RHTower.BaezDuarteDetectorIndependence
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strict positivity of logarithmic-chirp kernel packets

The explicit chirp kernel is a diagonal congruence of a right-half-plane
Cauchy kernel. Distinct positive cofactors give distinct logarithmic nodes,
and every amplitude is nonzero. Thus every finite Gram matrix is strictly
positive, even before restricting phases to the logarithmic orbit closure.
-/

noncomputable section
open Matrix Finset
open scoped ComplexOrder
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The right-half-plane node for a logarithmic cofactor frequency. -/
def chirpCauchyNode (α : ℝ) (j : ℕ+) : ℂ :=
  ((α / 2 : ℝ) : ℂ) - ((2 * Real.log (j : ℝ) : ℝ) : ℂ) * Complex.I

theorem chirpCauchyNode_re (α : ℝ) (j : ℕ+) :
    (chirpCauchyNode α j).re = α / 2 := by
  simp only [chirpCauchyNode, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero]

/-- Positive cofactors have distinct logarithmic Cauchy nodes. -/
theorem chirpCauchyNode_injective (α : ℝ) : Function.Injective (chirpCauchyNode α) := by
  intro j k h
  have hi := congrArg Complex.im h
  simp only [chirpCauchyNode, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero] at hi
  have hl : Real.log (j : ℝ) = Real.log (k : ℝ) := by linarith only [hi]
  have he := congrArg Real.exp hl
  rw [Real.exp_log (by exact_mod_cast j.property),
    Real.exp_log (by exact_mod_cast k.property)] at he
  exact_mod_cast he

/-- The power amplitude and quadratic logarithmic phase of a cofactor. -/
def chirpCauchyAmplitude (β : ℝ) (z : ℕ+ → Circle) (j : ℕ+) : ℂ :=
  (((j : ℝ) ^ (-β) : ℝ) : ℂ) * (z j : ℂ) *
    Complex.exp ((((Real.log (j : ℝ)) ^ 2 : ℝ) : ℂ) * Complex.I)

theorem chirpCauchyAmplitude_ne_zero (β : ℝ) (z : ℕ+ → Circle) (j : ℕ+) :
    chirpCauchyAmplitude β z j ≠ 0 := by
  have hj : (0 : ℝ) < j := by exact_mod_cast j.property
  have hp : (((j : ℝ) ^ (-β) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hj _).ne'
  have hz : (z j : ℂ) ≠ 0 := Circle.coe_ne_zero (z j)
  exact mul_ne_zero (mul_ne_zero hp hz) (Complex.exp_ne_zero _)

/-- The Hermitian chirp kernel with its explicit Cauchy denominator. -/
def chirpCauchyKernel (α β : ℝ) (z : ℕ+ → Circle) (j k : ℕ+) : ℂ :=
  (α : ℂ) * chirpCauchyAmplitude β z j *
    (1 / (chirpCauchyNode α j + star (chirpCauchyNode α k))) *
      star (chirpCauchyAmplitude β z k)

/-- Its real part is the covariance kernel of real cofactor packets. -/
def chirpRealKernel (α β : ℝ) (z : ℕ+ → Circle) (j k : ℕ+) : ℝ :=
  (chirpCauchyKernel α β z j k).re

/-- The Cauchy denominator is exactly the difference-frequency Laplace denominator. -/
theorem chirpCauchyNode_add_star (α : ℝ) (j k : ℕ+) :
    chirpCauchyNode α j + star (chirpCauchyNode α k) =
      (α : ℂ) - ((2 * (Real.log (j : ℝ) - Real.log (k : ℝ)) : ℝ) : ℂ) *
        Complex.I := by
  simp only [chirpCauchyNode, star_sub, star_mul, RCLike.star_def,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The phase factors do not change a cofactor's power amplitude. -/
theorem norm_chirpCauchyAmplitude (β : ℝ) (z : ℕ+ → Circle) (j : ℕ+) :
    ‖chirpCauchyAmplitude β z j‖ = (j : ℝ) ^ (-β) := by
  have hj : (0 : ℝ) < j := by exact_mod_cast j.property
  rw [chirpCauchyAmplitude, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hj _), Circle.norm_coe, mul_one, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, Real.exp_zero, mul_one]

/-- Every diagonal entry is the same power of its cofactor for every unit phase. -/
theorem chirpCauchyKernel_diagonal (α β : ℝ) (hα : α ≠ 0)
    (z : ℕ+ → Circle) (j : ℕ+) :
    chirpCauchyKernel α β z j j = (((j : ℝ) ^ (-2 * β) : ℝ) : ℂ) := by
  have hαC : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  have hj : (0 : ℝ) < j := by exact_mod_cast j.property
  have hnorm : chirpCauchyAmplitude β z j * star (chirpCauchyAmplitude β z j) =
      (((j : ℝ) ^ (-2 * β) : ℝ) : ℂ) := by
    rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      norm_chirpCauchyAmplitude, pow_two, ← Real.rpow_add hj]
    congr 2
    ring
  rw [chirpCauchyKernel, chirpCauchyNode_add_star]
  simp only [sub_self, mul_zero, Complex.ofReal_zero, zero_mul, sub_zero]
  calc
    _ = chirpCauchyAmplitude β z j * star (chirpCauchyAmplitude β z j) := by
      field_simp [hαC]
    _ = _ := hnorm

/-- The real covariance has its exact phase-independent diagonal. -/
theorem chirpRealKernel_diagonal (α β : ℝ) (hα : α ≠ 0)
    (z : ℕ+ → Circle) (j : ℕ+) : chirpRealKernel α β z j j = (j : ℝ) ^ (-2 * β) := by
  rw [chirpRealKernel, chirpCauchyKernel_diagonal α β hα, Complex.ofReal_re]

/-- Every kernel entry depends continuously on the entire phase parameter. -/
theorem continuous_chirpRealKernel (α β : ℝ) (j k : ℕ+) :
    Continuous (fun z : ℕ+ → Circle => chirpRealKernel α β z j k) := by
  unfold chirpRealKernel chirpCauchyKernel chirpCauchyAmplitude
  fun_prop

private theorem chirpCauchyKernel_matrix {N : ℕ} (α β : ℝ)
    (z : ℕ+ → Circle) (j : Fin N → ℕ+) :
    (fun r s => chirpCauchyKernel α β z (j r) (j s)) =
      α • (diagonal (fun r => chirpCauchyAmplitude β z (j r)) *
        RHTower.rightHalfPlaneHardyCauchyGram (fun r => chirpCauchyNode α (j r)) *
          (diagonal (fun r => chirpCauchyAmplitude β z (j r)))ᴴ) := by
  ext r s
  simp only [chirpCauchyKernel, Matrix.smul_apply, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul, Matrix.mul_diagonal, RHTower.rightHalfPlaneHardyCauchyGram,
    Pi.star_apply, Complex.real_smul, mul_assoc]

/-- Every finite packet at distinct cofactors has a strictly positive complex Gram matrix. -/
theorem chirpCauchyKernel_posDef {N : ℕ} (α β : ℝ) (hα : 0 < α)
    (z : ℕ+ → Circle) (j : Fin N → ℕ+) (hj : Function.Injective j) :
    Matrix.PosDef (fun r s => chirpCauchyKernel α β z (j r) (j s)) := by
  have hnodes : ∀ r, 0 < (chirpCauchyNode α (j r)).re := by
    intro r
    rw [chirpCauchyNode_re]
    exact half_pos hα
  have hC := RHTower.rightHalfPlaneHardyCauchyGram_posDef
    (fun r => chirpCauchyNode α (j r)) hnodes ((chirpCauchyNode_injective α).comp hj)
  have hD : IsUnit (diagonal (fun r => chirpCauchyAmplitude β z (j r))) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    exact isUnit_iff_ne_zero.mpr
      (prod_ne_zero_iff.mpr fun r _ => chirpCauchyAmplitude_ne_zero β z (j r))
  rw [chirpCauchyKernel_matrix]
  exact (hC.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.mpr hD)).smul hα

/-- The real covariance quadratic form is strictly positive on every nonzero finite packet. -/
theorem chirpRealKernel_packet_pos {N : ℕ} (α β : ℝ) (hα : 0 < α)
    (z : ℕ+ → Circle) (j : Fin N → ℕ+) (hj : Function.Injective j)
    (c : Fin N → ℝ) (hc : c ≠ 0) :
    0 < ∑ r, ∑ s, c r * c s * chirpRealKernel α β z (j r) (j s) := by
  have hcC : (fun r => (c r : ℂ)) ≠ 0 := by
    intro h
    apply hc
    funext r
    have hr := congrFun h r
    exact Complex.ofReal_injective hr
  have hp := (chirpCauchyKernel_posDef α β hα z j hj).dotProduct_mulVec_pos hcC
  have hr := (Complex.pos_iff.mp hp).1
  simp only [dotProduct, mulVec, Pi.star_apply, RCLike.star_def, Complex.conj_ofReal,
    Finset.mul_sum, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero] at hr
  convert hr using 1
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  unfold chirpRealKernel
  ring

end GaloisForLFunctions.BiarithmeticGeometry

