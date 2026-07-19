import GaloisForLFunctions.RHTower.XiSquaredEulerRayFullResponse

/-!
# Exterior-cubic masking and amplification for the Xi Euler response

The complete Xi kernel can mask the negative three-node determinant of one off-line orbit at its
physical weight.  This file identifies that obstruction exactly.  The determinant of a background
plus a scalar multiple of one orbit is a cubic polynomial: its leading coefficient is the orbit's
strictly negative self-determinant, while the lower three coefficients are the full background and
the two mixed discriminants.

Therefore cross-orbit masking is finite-amplitude only.  For any fixed three positive nodes and any
fixed background, sufficiently strong positive amplification of an off-line orbit forces the
complete determinant to become negative.  Applied to the actual full Xi response, this says that
the remaining RH mechanism is not another sign estimate: it is the construction of a source-pure
unbounded transverse amplifier.  The theorem does not assert that the existing prime or true-
aperture source supplies such an amplifier.
-/

open Set

namespace RHTower

noncomputable section

/-! ## Exact mixed-discriminant expansion -/

/-- The coefficient containing one copy of `A` and two copies of `B` in the symmetric
three-point determinant.  It is the row-polarized mixed discriminant with all three placements of
the `A` row collected. -/
def symmetricThreePointMixedDetOne
    (A B : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  A x x * B y y * B z z + B x x * A y y * B z z + B x x * B y y * A z z +
  2 * (A x y * B x z * B y z + B x y * A x z * B y z +
    B x y * B x z * A y z) -
  (A x x * B y z ^ 2 + 2 * B x x * B y z * A y z) -
  (A y y * B x z ^ 2 + 2 * B y y * B x z * A x z) -
  (A z z * B x y ^ 2 + 2 * B z z * B x y * A x y)

/-- Exact cubic expansion of the three-node determinant under amplification of one kernel. -/
theorem symmetricThreePointDet_add_smul
    (A B : ℝ → ℝ → ℝ) (lambda x y z : ℝ) :
    symmetricThreePointDet (fun u v => B u v + lambda * A u v) x y z =
      symmetricThreePointDet B x y z +
        lambda * symmetricThreePointMixedDetOne A B x y z +
        lambda ^ 2 * symmetricThreePointMixedDetOne B A x y z +
        lambda ^ 3 * symmetricThreePointDet A x y z := by
  unfold symmetricThreePointDet symmetricThreePointMixedDetOne
  ring

/-- Absolute lower-degree budget which can mask the self-cubic of `A`. -/
def symmetricThreePointMaskingBudget
    (A B : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  |symmetricThreePointDet B x y z| +
    |symmetricThreePointMixedDetOne A B x y z| +
    |symmetricThreePointMixedDetOne B A x y z|

/-- Once the amplified negative self-cubic exceeds the entire lower-degree masking budget, the
three-node determinant is strictly negative. -/
theorem symmetricThreePointDet_add_smul_neg_of_maskingBudget_lt
    (A B : ℝ → ℝ → ℝ) {lambda x y z : ℝ}
    (hlambda : 1 ≤ lambda)
    (hmask : symmetricThreePointMaskingBudget A B x y z <
      -symmetricThreePointDet A x y z * lambda) :
    symmetricThreePointDet (fun u v => B u v + lambda * A u v) x y z < 0 := by
  let dA := symmetricThreePointDet A x y z
  let dB := symmetricThreePointDet B x y z
  let m1 := symmetricThreePointMixedDetOne A B x y z
  let m2 := symmetricThreePointMixedDetOne B A x y z
  have hlambda0 : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hlambdaSq : 1 ≤ lambda ^ 2 := by nlinarith
  have hdB : dB ≤ |dB| := le_abs_self dB
  have hm1 : lambda * m1 ≤ lambda * |m1| :=
    mul_le_mul_of_nonneg_left (le_abs_self m1) hlambda0.le
  have hm2 : lambda ^ 2 * m2 ≤ lambda ^ 2 * |m2| :=
    mul_le_mul_of_nonneg_left (le_abs_self m2) (sq_nonneg lambda)
  have hdBscale : |dB| ≤ lambda ^ 2 * |dB| := by
    nlinarith [abs_nonneg dB]
  have hm1scale : lambda * |m1| ≤ lambda ^ 2 * |m1| := by
    have hprod : 0 ≤ (lambda - 1) * (lambda * |m1|) :=
      mul_nonneg (sub_nonneg.mpr hlambda)
        (mul_nonneg hlambda0.le (abs_nonneg m1))
    nlinarith
  have hupper :
      dB + lambda * m1 + lambda ^ 2 * m2 + lambda ^ 3 * dA ≤
        lambda ^ 2 *
          (symmetricThreePointMaskingBudget A B x y z + lambda * dA) := by
    dsimp only [symmetricThreePointMaskingBudget, dA, dB, m1, m2] at *
    nlinarith
  have hbracket :
      symmetricThreePointMaskingBudget A B x y z + lambda * dA < 0 := by
    dsimp only [dA] at hmask ⊢
    nlinarith
  have hneg : lambda ^ 2 *
      (symmetricThreePointMaskingBudget A B x y z + lambda * dA) < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos hlambda0) hbracket
  rw [symmetricThreePointDet_add_smul]
  exact hupper.trans_lt hneg

/-- A negative atomic cubic dominates every fixed background after a finite positive amplification
threshold. -/
theorem exists_symmetricThreePointDet_add_smul_neg
    (A B : ℝ → ℝ → ℝ) {x y z : ℝ}
    (hA : symmetricThreePointDet A x y z < 0) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lambda : ℝ, L < lambda →
      symmetricThreePointDet (fun u v => B u v + lambda * A u v) x y z < 0 := by
  let a : ℝ := -symmetricThreePointDet A x y z
  let C : ℝ := symmetricThreePointMaskingBudget A B x y z
  let L : ℝ := max 1 (C / a)
  have ha : 0 < a := by dsimp only [a]; linarith
  refine ⟨L, le_max_left _ _, ?_⟩
  intro lambda hlambda
  have hLfrac : C / a ≤ L := le_max_right _ _
  have hfrac : C / a < lambda := hLfrac.trans_lt hlambda
  have hmask : C < a * lambda := by
    simpa only [mul_comm] using (div_lt_iff₀ ha).mp hfrac
  apply symmetricThreePointDet_add_smul_neg_of_maskingBudget_lt A B
    (le_trans (le_max_left 1 (C / a)) hlambda.le)
  dsimp only [C, a] at hmask ⊢
  simpa only [neg_mul] using hmask

/-! ## Specialization to the complete Xi response -/

/-- Reweight one actual Xi orbit inside the complete response.  `lambda=1` is the physical full
kernel; larger `lambda` amplifies only the selected orbit while retaining every cross-orbit term. -/
def xiSquaredEulerReweightedFullKernel
    (q : XiZeroCopy) (lambda x y : ℝ) : ℝ :=
  xiSquaredEulerFullKernel x y +
    (lambda - 1) * xiSquaredEulerOrbitKernel q x y

/-- **Finite-amplitude masking law.**  At any fixed ordered positive triple, the rest of the
complete Xi divisor can mask an off-line orbit only below a finite amplification threshold. -/
theorem exists_xiSquaredEulerReweightedFullKernel_threePointDet_neg
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ lambda : ℝ, L < lambda →
      symmetricThreePointDet
        (xiSquaredEulerReweightedFullKernel q lambda) x y z < 0 := by
  let A : ℝ → ℝ → ℝ := xiSquaredEulerOrbitKernel q
  let B : ℝ → ℝ → ℝ := fun u v =>
    xiSquaredEulerFullKernel u v - A u v
  have hA : symmetricThreePointDet A x y z < 0 :=
    xiSquaredEulerOrbitKernel_threePointDet_neg q hoff hx hxy hyz
  obtain ⟨L, hL, hdet⟩ := exists_symmetricThreePointDet_add_smul_neg A B hA
  refine ⟨L, hL, ?_⟩
  intro lambda hlambda
  have h := hdet lambda hlambda
  have hkernel : (fun u v => B u v + lambda * A u v) =
      xiSquaredEulerReweightedFullKernel q lambda := by
    funext u v
    dsimp only [A, B, xiSquaredEulerReweightedFullKernel]
    ring
  rw [hkernel] at h
  exact h

end

end RHTower
