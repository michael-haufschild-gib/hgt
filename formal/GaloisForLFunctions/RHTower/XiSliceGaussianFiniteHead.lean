import GaloisForLFunctions.RHTower.XiSliceGaussianTailRealBounds
import GaloisForLFunctions.RHTower.XiSliceClusterDetectionOrder

/-!
# Gaussian comparisons retaining central Xi zeros

Splitting the canonical product at a nonnegative radius gives a finite polynomial
head with a nonzero scalar and the complementary Xi tail. Copies at the center
contribute their exact factors `z²`. The full-slice Gaussian comparisons therefore
hold at every real center, including centers where `XiC` vanishes.
-/

open Complex Filter Topology
namespace RHTower
noncomputable section

/-- The scalar multiplying the finite slice polynomial after removing a radius head. -/
def xiSliceGaussianFiniteHeadScalar (t R : ℝ) : ℂ :=
  XiC 0 ^ 2 * xiCanonicalProductOff (xiSliceGaussianRadiusHead t R) t ^ 2 *
    ∏ q ∈ xiSliceGaussianRadiusHead t R,
      Complex.exp (2 * (t : ℂ) / xiSpectralPoint q) / xiSpectralPoint q ^ 2

/-- The finite polynomial head, retaining central zero copies as factors `z²`. -/
def xiSliceGaussianFiniteHead (t R : ℝ) (z : ℂ) : ℂ :=
  xiSliceGaussianFiniteHeadScalar t R *
    ∏ q ∈ xiSliceGaussianRadiusHead t R, (z ^ 2 + (xiSpectralPoint q - t) ^ 2)

private theorem gaussianRadiusHead_contains_center (t : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (q : XiZeroCopy) (hq : xiSpectralPoint q = t) : q ∈ xiSliceGaussianRadiusHead t R := by
  rw [mem_xiSliceGaussianRadiusHead, hq, sub_self, norm_zero]
  exact hR

/-- Removing every copy at the center leaves a nonzero scalar, even when the slice vanishes there. -/
theorem xiSliceGaussianFiniteHeadScalar_ne_zero (t : ℝ) {R : ℝ} (hR : 0 ≤ R) :
    xiSliceGaussianFiniteHeadScalar t R ≠ 0 := by
  classical
  unfold xiSliceGaussianFiniteHeadScalar
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero 2 XiC_zero_ne)
    (pow_ne_zero 2 (xiCanonicalProductOff_ne_zero (gaussianRadiusHead_contains_center t hR)))) ?_
  exact Finset.prod_ne_zero_iff.mpr fun q _ =>
    div_ne_zero (Complex.exp_ne_zero _) (pow_ne_zero 2 (xiSpectralPoint_ne_zero q))

private theorem gaussianTail_eq_off_slice (t : ℝ) {R : ℝ} (hR : 0 ≤ R) (z : ℂ) :
    xiCanonicalProductOff (xiSliceGaussianRadiusHead t R) ((t : ℂ) - I * z) *
      xiCanonicalProductOff (xiSliceGaussianRadiusHead t R) ((t : ℂ) + I * z) =
    xiCanonicalProductOff (xiSliceGaussianRadiusHead t R) t ^ 2 *
      xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) z := by
  let H := xiSliceGaussianRadiusHead t R
  -- Both complement presentations retain the same multiplicity copies.
  let e : {q : XiZeroCopy // q ∉ H} ≃ XiZeroCopyOff H :=
    { toFun := fun q => ⟨q.val, q.property⟩
      invFun := fun q => ⟨q.val, q.property⟩
      left_inv := fun q => rfl
      right_inv := fun q => rfl }
  have hlim : HasProd (fun q : XiZeroCopyOff H => 1 + z ^ 2 * xiSliceGaussianReciprocal t q)
      (xiCanonicalProductOff H ((t : ℂ) - I * z) * xiCanonicalProductOff H ((t : ℂ) + I * z) /
        xiCanonicalProductOff H t ^ 2) := by
    simpa only [HasProd, SummationFilter.unconditional, H,
      xiSliceGaussianReciprocal, div_eq_mul_inv] using
      tendsto_prod_off_one_add_sq_div (gaussianRadiusHead_contains_center t hR) z
  have heq : xiSliceGaussianTail t H z =
      xiCanonicalProductOff H ((t : ℂ) - I * z) * xiCanonicalProductOff H ((t : ℂ) + I * z) /
        xiCanonicalProductOff H t ^ 2 := by
    calc
      _ = ∏' q : XiZeroCopyOff H, (1 + z ^ 2 * xiSliceGaussianReciprocal t q) :=
        e.tprod_eq (fun q : XiZeroCopyOff H => 1 + z ^ 2 * xiSliceGaussianReciprocal t q)
      _ = _ := hlim.tprod_eq
  have hP := xiCanonicalProductOff_ne_zero (gaussianRadiusHead_contains_center t hR)
  have hm := (eq_div_iff (pow_ne_zero 2 hP)).mp heq
  exact hm.symm.trans (mul_comm _ _)

/-- The actual Xi slice factors into a finite polynomial and the complementary tail at every center. -/
theorem xiSliceProduct_eq_gaussianFiniteHead_mul_tail (t : ℝ) {R : ℝ} (hR : 0 ≤ R) (z : ℂ) :
    xiSliceProduct t z = xiSliceGaussianFiniteHead t R z *
      xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) z := by
  classical
  let H := xiSliceGaussianRadiusHead t R
  let P := xiCanonicalProductOff H
  have hXi (w : ℂ) : XiC w = XiC 0 *
      (∏ q ∈ H, weierstrassE1 (w / xiSpectralPoint q)) * P w := by
    dsimp only [P]
    rw [mul_assoc, ← xiCanonicalProduct_eq_prod_mul_off]
    simpa only [Pi.mul_apply] using congrFun XiC_eq_constant_mul_canonicalProduct w
  have hpair (q : XiZeroCopy) :
      weierstrassE1 (((t : ℂ) - I * z) / xiSpectralPoint q) *
        weierstrassE1 (((t : ℂ) + I * z) / xiSpectralPoint q) =
      (z ^ 2 + (xiSpectralPoint q - t) ^ 2) *
        (Complex.exp (2 * (t : ℂ) / xiSpectralPoint q) / xiSpectralPoint q ^ 2) := by
    rw [weierstrassE1_pair_eq_sq_sub _ _ _ (xiSpectralPoint_ne_zero q)]
    have hsq : (I * z) ^ 2 = -z ^ 2 := by ring_nf; rw [I_sq]; ring
    rw [hsq]
    ring
  rw [xiSliceProduct_eq_XiC_mul, hXi ((t : ℂ) - I * z), hXi ((t : ℂ) + I * z)]
  calc
    _ = XiC 0 ^ 2 *
        (∏ q ∈ H, (weierstrassE1 (((t : ℂ) - I * z) / xiSpectralPoint q) *
          weierstrassE1 (((t : ℂ) + I * z) / xiSpectralPoint q))) *
        (P ((t : ℂ) - I * z) * P ((t : ℂ) + I * z)) := by
          rw [Finset.prod_mul_distrib]
          ring
    _ = XiC 0 ^ 2 * (∏ q ∈ H, ((z ^ 2 + (xiSpectralPoint q - t) ^ 2) *
        (Complex.exp (2 * (t : ℂ) / xiSpectralPoint q) / xiSpectralPoint q ^ 2))) *
        (P t ^ 2 * xiSliceGaussianTail t H z) := by
          rw [Finset.prod_congr rfl (fun q _ => hpair q), gaussianTail_eq_off_slice t hR]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      unfold xiSliceGaussianFiniteHead xiSliceGaussianFiniteHeadScalar
      dsimp only [H, P]
      ring

/-- The full-source Gaussian comparison retains central zeros and has no central nonvanishing premise. -/
theorem norm_xiSliceProduct_compensated_sub_finiteHead_le (t : ℝ) {R : ℝ}
    (hR : 0 < R) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖Complex.exp (-(z ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
        xiSliceProduct t z - xiSliceGaussianFiniteHead t R z‖ ≤
      ‖xiSliceGaussianFiniteHead t R z‖ *
        (Real.exp (‖z‖ ^ 4 * xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)) - 1) := by
  rw [xiSliceProduct_eq_gaussianFiniteHead_mul_tail t (R := R) hR.le]
  have heq : Complex.exp (-(z ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
        (xiSliceGaussianFiniteHead t R z * xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) z) -
      xiSliceGaussianFiniteHead t R z =
      xiSliceGaussianFiniteHead t R z *
        (Complex.exp (-(z ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
          xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) z - 1) := by ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_xiSliceGaussianTail_compensated_sub_one_le t hR hz) (norm_nonneg _)

/-- On the whole real axis the full-source relative tail error is at most its fourth moment times `x⁴`. -/
theorem norm_xiSliceProduct_real_compensated_sub_finiteHead_le (t : ℝ) {R : ℝ}
    (hR : 4 ≤ R) (x : ℝ) :
    ‖Complex.exp (-((x : ℂ) ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
        xiSliceProduct t x - xiSliceGaussianFiniteHead t R x‖ ≤
      ‖xiSliceGaussianFiniteHead t R x‖ *
        (x ^ 4 * xiSliceGaussianTailFourth t (xiSliceGaussianRadiusHead t R)) := by
  rw [xiSliceProduct_eq_gaussianFiniteHead_mul_tail t (R := R) (by linarith only [hR])]
  have heq : Complex.exp (-((x : ℂ) ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
        (xiSliceGaussianFiniteHead t R x * xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) x) -
      xiSliceGaussianFiniteHead t R x =
      xiSliceGaussianFiniteHead t R x *
        (Complex.exp (-((x : ℂ) ^ 2 * xiSliceGaussianTailQuadratic t (xiSliceGaussianRadiusHead t R))) *
          xiSliceGaussianTail t (xiSliceGaussianRadiusHead t R) x - 1) := by ring
  rw [heq, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_xiSliceGaussianTail_real_compensated_sub_one_le t hR x) (norm_nonneg _)

end
end RHTower

