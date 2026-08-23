import GaloisForLFunctions.RHTower.XiWardKreinTransverseMassShell
import GaloisForLFunctions.HTGeometry.KreinLangerInertia
import GaloisForLFunctions.HTGeometry.TensorPolarizationAmplification

/-!
# Canonical transverse Pick block for an off-line Xi pair

The inward and outward witnesses of the transverse Ward--Krein mass shell do more than expose
opposite diagonal signs.  Their mixed Pick entry vanishes exactly.  Hence they canonically
diagonalize the conjugate-pair Pick block, with eigenvalues
`-8 / (3 * delta^2)` and `2 / (3 * delta^2)`.

Consequences:

* transverse fourth-power renormalization gives the fixed determinant quantum `-16/9`;
* the block has exactly one positive and one negative channel;
* every further tensor formation has exactly half of its channels negative.

Thus a single off-line Xi atom cannot be hidden by small transverse displacement after this
canonical two-channel normalization.  No arithmetic tensor-source upper bound is asserted here.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-- Two-point Pick kernel of the conjugate-pair carrier. -/
def conjugatePairPickCross (t z w : ℂ) : ℂ :=
  (conjugatePairCarrierValue t z - star (conjugatePairCarrierValue t w)) /
    (z - star w)

/-- Canonical inward and outward witnesses are Pick-orthogonal. -/
theorem conjugatePairPickCross_inward_outward
    (t : ℂ) (ht : t.im ≠ 0) :
    conjugatePairPickCross t (conjugatePairInwardWitness t)
      (conjugatePairOutwardWitness t) = 0 := by
  have hsc : t - star t = ((2 * t.im : ℝ) : ℂ) * I := by
    rw [show star t = (starRingEnd ℂ) t from rfl, Complex.sub_conj]
  have hst : star t - t = -(((2 * t.im : ℝ) : ℂ) * I) := by
    rw [← hsc]
    ring
  simp only [conjugatePairInwardWitness, conjugatePairOutwardWitness]
  have e1 : t - (t - I * ((t.im / 2 : ℝ) : ℂ)) =
      I * ((t.im / 2 : ℝ) : ℂ) := by ring
  have e2 : star t - (t - I * ((t.im / 2 : ℝ) : ℂ)) =
      I * (((-3 * t.im / 2 : ℝ)) : ℂ) := by
    rw [show star t - (t - I * ((t.im / 2 : ℝ) : ℂ)) =
      (star t - t) + I * ((t.im / 2 : ℝ) : ℂ) from by ring, hst]
    push_cast
    ring
  have e3 : star t - star (t + I * ((t.im : ℝ) : ℂ)) =
      I * ((t.im : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im]
  have e4 : t - star (t + I * ((t.im : ℝ) : ℂ)) =
      I * (((3 * t.im : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp [Complex.mul_re, Complex.mul_im]
    · simp [Complex.mul_re, Complex.mul_im]
      ring
  have h1 : t - conjugatePairInwardWitness t ≠ 0 := by
    rw [conjugatePairInwardWitness, e1]
    exact mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr (div_ne_zero ht (by norm_num)))
  have h2 : star t - conjugatePairInwardWitness t ≠ 0 := by
    rw [conjugatePairInwardWitness, e2]
    exact mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr (by
      intro h
      apply ht
      linarith))
  have h3 : t - star (conjugatePairOutwardWitness t) ≠ 0 := by
    rw [conjugatePairOutwardWitness, e4]
    exact mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) ht))
  have h4 : star t - star (conjugatePairOutwardWitness t) ≠ 0 := by
    rw [conjugatePairOutwardWitness, e3]
    exact mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr ht)
  have hD : conjugatePairInwardWitness t - star (conjugatePairOutwardWitness t) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [conjugatePairInwardWitness, conjugatePairOutwardWitness,
      Complex.mul_im] at him
    apply ht
    linarith
  have hpe := conjPair_pe t (star t)
    (conjugatePairInwardWitness t) (star (conjugatePairOutwardWitness t))
    h1 h2 h3 h4 hD
  have hstar :
      star ((t - conjugatePairOutwardWitness t)⁻¹ +
          (star t - conjugatePairOutwardWitness t)⁻¹) =
        (star t - star (conjugatePairOutwardWitness t))⁻¹ +
          (t - star (conjugatePairOutwardWitness t))⁻¹ := by
    simp
  change
    (((t - conjugatePairInwardWitness t)⁻¹ +
          (star t - conjugatePairInwardWitness t)⁻¹) -
        star ((t - conjugatePairOutwardWitness t)⁻¹ +
          (star t - conjugatePairOutwardWitness t)⁻¹)) /
      (conjugatePairInwardWitness t - star (conjugatePairOutwardWitness t)) = 0
  rw [hstar, hpe,
    conjugatePairInwardWitness, conjugatePairOutwardWitness,
    e1, e2, e3, e4]
  field_simp [ht]
  push_cast
  ring

theorem conjugatePairPickCross_swap (t z w : ℂ) :
    conjugatePairPickCross t w z = star (conjugatePairPickCross t z w) := by
  rw [conjugatePairPickCross, conjugatePairPickCross]
  change (conjugatePairCarrierValue t w - star (conjugatePairCarrierValue t z)) /
      (w - star z) =
    (starRingEnd ℂ) ((conjugatePairCarrierValue t z -
      star (conjugatePairCarrierValue t w)) / (z - star w))
  rw [map_div₀, map_sub, map_sub]
  simp only [starRingEnd_apply, star_star]
  rw [show star z - w = -(w - star z) by ring, div_neg]
  ring

theorem conjugatePairPickCross_outward_inward
    (t : ℂ) (ht : t.im ≠ 0) :
    conjugatePairPickCross t (conjugatePairOutwardWitness t)
      (conjugatePairInwardWitness t) = 0 := by
  rw [conjugatePairPickCross_swap,
    conjugatePairPickCross_inward_outward t ht, star_zero]

theorem conjugatePairPickCross_inward_inward
    (t : ℂ) (ht : t.im ≠ 0) :
    conjugatePairPickCross t (conjugatePairInwardWitness t)
      (conjugatePairInwardWitness t) =
        (((-8 / (3 * t.im ^ 2) : ℝ)) : ℂ) := by
  have hz : (conjugatePairInwardWitness t).im = t.im / 2 := by
    simp [conjugatePairInwardWitness, Complex.sub_im, Complex.mul_im]
    ring
  have hzim : (conjugatePairInwardWitness t).im ≠ 0 := by
    rw [hz]
    exact div_ne_zero ht (by norm_num)
  rw [conjugatePairPickCross, pickDiag_eq _ _ hzim]
  norm_cast
  rw [conjugatePairCarrierValue_inward_im t ht]
  rw [hz]
  field_simp [ht]
  all_goals norm_num

theorem conjugatePairPickCross_outward_outward
    (t : ℂ) (ht : t.im ≠ 0) :
    conjugatePairPickCross t (conjugatePairOutwardWitness t)
      (conjugatePairOutwardWitness t) =
        (((2 / (3 * t.im ^ 2) : ℝ)) : ℂ) := by
  have hz : (conjugatePairOutwardWitness t).im = 2 * t.im := by
    simp [conjugatePairOutwardWitness, Complex.add_im, Complex.mul_im]
    ring
  have hzim : (conjugatePairOutwardWitness t).im ≠ 0 := by
    rw [hz]
    exact mul_ne_zero (by norm_num) ht
  rw [conjugatePairPickCross, pickDiag_eq _ _ hzim]
  norm_cast
  rw [conjugatePairCarrierValue_outward_im t ht]
  rw [hz]
  field_simp [ht]
  all_goals norm_num

/-- Ordered inward/outward transverse nodes. -/
def conjugatePairTransversePickNodes (t : ℂ) : Fin 2 → ℂ :=
  ![conjugatePairInwardWitness t, conjugatePairOutwardWitness t]

/-- Two-node transverse Pick compression. -/
def conjugatePairTransversePickBlock (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    conjugatePairPickCross t (conjugatePairTransversePickNodes t i)
      (conjugatePairTransversePickNodes t j)

/-- The canonical transverse nodes diagonalize the Pick block exactly. -/
theorem conjugatePairTransversePickBlock_eq_diagonal
    (t : ℂ) (ht : t.im ≠ 0) :
    conjugatePairTransversePickBlock t = Matrix.diagonal
      ![(((-8 / (3 * t.im ^ 2) : ℝ)) : ℂ),
        (((2 / (3 * t.im ^ 2) : ℝ)) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [conjugatePairTransversePickBlock, conjugatePairTransversePickNodes,
      conjugatePairPickCross_inward_inward t ht,
      conjugatePairPickCross_inward_outward t ht,
      conjugatePairPickCross_outward_inward t ht,
      conjugatePairPickCross_outward_outward t ht]

/-- Exact determinant before transverse renormalization. -/
theorem conjugatePairTransversePickBlock_det
    (t : ℂ) (ht : t.im ≠ 0) :
    (conjugatePairTransversePickBlock t).det =
      (((-16 / (9 * t.im ^ 4) : ℝ)) : ℂ) := by
  rw [conjugatePairTransversePickBlock_eq_diagonal t ht, Matrix.det_fin_two]
  simp
  field_simp [ht]
  ring

/-- Fourth-power renormalization produces a displacement-independent determinant quantum. -/
theorem conjugatePairTransversePickBlock_renormalized_det
    (t : ℂ) (ht : t.im ≠ 0) :
    t.im ^ 4 * (conjugatePairTransversePickBlock t).det.re = -16 / 9 := by
  have hdet := congrArg Complex.re (conjugatePairTransversePickBlock_det t ht)
  simp only [Complex.ofReal_re] at hdet
  rw [hdet]
  field_simp [ht]

theorem conjugatePairTransversePickBlock_det_re_neg
    (t : ℂ) (ht : t.im ≠ 0) :
    (conjugatePairTransversePickBlock t).det.re < 0 := by
  have hdet := congrArg Complex.re (conjugatePairTransversePickBlock_det t ht)
  simp only [Complex.ofReal_re] at hdet
  rw [hdet]
  have hb4 : 0 < t.im ^ 4 := by
    calc
      0 < (t.im ^ 2) ^ 2 := sq_pos_of_ne_zero (pow_ne_zero 2 ht)
      _ = t.im ^ 4 := by ring
  exact div_neg_of_neg_of_pos (by norm_num)
    (mul_pos (by norm_num) hb4)

/-- The transverse Pick block has exactly one negative channel. -/
theorem conjugatePairTransversePickBlock_negIndex
    (t : ℂ) (ht : t.im ≠ 0) :
    GaloisForLFunctions.HTGeometry.hermNegIndex
      (conjugatePairTransversePickBlock t) = 1 := by
  classical
  have hb2 : 0 < t.im ^ 2 := sq_pos_of_ne_zero ht
  have hneg : -8 / (3 * t.im ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (mul_pos (by norm_num) hb2)
  have hpos : 0 < 2 / (3 * t.im ^ 2) :=
    div_pos (by norm_num) (mul_pos (by norm_num) hb2)
  rw [conjugatePairTransversePickBlock_eq_diagonal t ht]
  have hvec :
      ![(((-8 / (3 * t.im ^ 2) : ℝ)) : ℂ),
        (((2 / (3 * t.im ^ 2) : ℝ)) : ℂ)] =
      fun i => ((![(-8 / (3 * t.im ^ 2) : ℝ),
        (2 / (3 * t.im ^ 2) : ℝ)] i : ℝ) : ℂ) := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, GaloisForLFunctions.HTGeometry.negIndex_diagonal]
  have hpneg : ¬ 2 / (3 * t.im ^ 2) < 0 := not_lt_of_ge hpos.le
  have hset :
      ({i | ![(-8 / (3 * t.im ^ 2) : ℝ),
        (2 / (3 * t.im ^ 2) : ℝ)] i < 0} : Finset (Fin 2)) = {0} := by
    ext i
    fin_cases i <;> simp [hneg, hpneg]
  rw [hset]
  simp

/-- The transverse Pick block has exactly one positive channel. -/
theorem conjugatePairTransversePickBlock_posIndex
    (t : ℂ) (ht : t.im ≠ 0) :
    GaloisForLFunctions.HTGeometry.hermPosIndex
      (conjugatePairTransversePickBlock t) = 1 := by
  classical
  have hb2 : 0 < t.im ^ 2 := sq_pos_of_ne_zero ht
  have hneg : -8 / (3 * t.im ^ 2) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (mul_pos (by norm_num) hb2)
  have hpos : 0 < 2 / (3 * t.im ^ 2) :=
    div_pos (by norm_num) (mul_pos (by norm_num) hb2)
  rw [conjugatePairTransversePickBlock_eq_diagonal t ht]
  have hvec :
      ![(((-8 / (3 * t.im ^ 2) : ℝ)) : ℂ),
        (((2 / (3 * t.im ^ 2) : ℝ)) : ℂ)] =
      fun i => ((![(-8 / (3 * t.im ^ 2) : ℝ),
        (2 / (3 * t.im ^ 2) : ℝ)] i : ℝ) : ℂ) := by
    funext i
    fin_cases i <;> rfl
  rw [hvec, GaloisForLFunctions.HTGeometry.posIndex_diagonal]
  have hnpos : ¬ 0 < -8 / (3 * t.im ^ 2) := not_lt_of_ge hneg.le
  have hset :
      ({i | 0 < ![(-8 / (3 * t.im ^ 2) : ℝ),
        (2 / (3 * t.im ^ 2) : ℝ)] i} : Finset (Fin 2)) = {1} := by
    ext i
    fin_cases i <;> simp [hnpos, hpos]
  rw [hset]
  simp

end

end GaloisForLFunctions

namespace RHTower

open Complex GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Actual transverse Pick block selected by a strict-right upper Xi zero. -/
def xiWardKreinTransversePickBlock
    (q : XiRightUpperZeroCopy) : Matrix (Fin 2) (Fin 2) ℂ :=
  conjugatePairTransversePickBlock (xiWardKreinUpperSpectralPole q)

/-- Exact canonical eigenchannels of the Xi-selected transverse Pick block. -/
theorem xiWardKreinTransversePickBlock_eq_diagonal
    (q : XiRightUpperZeroCopy) :
    xiWardKreinTransversePickBlock q = Matrix.diagonal
      ![(((-8 / (3 * (xiRightCenteredZero q.1).re ^ 2) : ℝ)) : ℂ),
        (((2 / (3 * (xiRightCenteredZero q.1).re ^ 2) : ℝ)) : ℂ)] := by
  rw [xiWardKreinTransversePickBlock,
    conjugatePairTransversePickBlock_eq_diagonal _
      (xiWardKreinUpperSpectralPole_im_pos q).ne']
  rw [xiWardKreinUpperSpectralPole_im_eq_transverse]

/-- Every off-line Xi atom carries the exact normalized determinant quantum `-16/9`. -/
theorem xiWardKreinTransversePickBlock_renormalized_det
    (q : XiRightUpperZeroCopy) :
    (xiRightCenteredZero q.1).re ^ 4 *
        (xiWardKreinTransversePickBlock q).det.re = -16 / 9 := by
  simpa [xiWardKreinTransversePickBlock,
    xiWardKreinUpperSpectralPole_im_eq_transverse q] using
    conjugatePairTransversePickBlock_renormalized_det
      (xiWardKreinUpperSpectralPole q)
      (xiWardKreinUpperSpectralPole_im_pos q).ne'

theorem xiWardKreinTransversePickBlock_det_re_neg
    (q : XiRightUpperZeroCopy) :
    (xiWardKreinTransversePickBlock q).det.re < 0 := by
  exact conjugatePairTransversePickBlock_det_re_neg
    (xiWardKreinUpperSpectralPole q)
    (xiWardKreinUpperSpectralPole_im_pos q).ne'

theorem xiWardKreinTransversePickBlock_negIndex
    (q : XiRightUpperZeroCopy) :
    hermNegIndex (xiWardKreinTransversePickBlock q) = 1 := by
  exact conjugatePairTransversePickBlock_negIndex
    (xiWardKreinUpperSpectralPole q)
    (xiWardKreinUpperSpectralPole_im_pos q).ne'

theorem xiWardKreinTransversePickBlock_posIndex
    (q : XiRightUpperZeroCopy) :
    hermPosIndex (xiWardKreinTransversePickBlock q) = 1 := by
  exact conjugatePairTransversePickBlock_posIndex
    (xiWardKreinUpperSpectralPole q)
    (xiWardKreinUpperSpectralPole_im_pos q).ne'

theorem tensorPolarNeg_one_one_succ (d : ℕ) :
    tensorPolarNeg 1 1 (d + 1) = 2 ^ d := by
  simp only [tensorPolarNeg, one_mul]
  simpa using tensorPolar_total 1 1 d

/-- A single off-line Xi atom generates an exact half-rank negative tensor sector at every depth. -/
theorem xiWardKreinTransversePickBlock_tensorNegativeHalf
    (q : XiRightUpperZeroCopy) (d : ℕ) :
    tensorPolarNeg
        (hermPosIndex (xiWardKreinTransversePickBlock q))
        (hermNegIndex (xiWardKreinTransversePickBlock q)) (d + 1) = 2 ^ d := by
  rw [xiWardKreinTransversePickBlock_posIndex,
    xiWardKreinTransversePickBlock_negIndex]
  exact tensorPolarNeg_one_one_succ d

end

end RHTower
