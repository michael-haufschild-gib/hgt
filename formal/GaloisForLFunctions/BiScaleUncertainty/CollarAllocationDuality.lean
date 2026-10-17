import GaloisForLFunctions.BiScaleUncertainty.IntegratedOriginCollarLeverage

/-!
# Marginal prices and rigidity for collar allocation

Explicit supporting prices of the shared-origin block norm give a nonnegative comparison
remainder. It splits exactly into radial curvature and block-direction discrepancies;
zero remainder forces equality of the aggregate block norms. The same prices yield a
quantitative strict improvement when physical capacity is added, including zero blocks.

The literal logarithmic-grid prices are measurable, bounded, and integrable at the origin.
The continuous physical-allocation gap theorem is proved in `CollarAllocationDuality.md`;
its general physical pullback and integration are not yet formalized here.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {ι κ : Type*}

/-- The Euclidean size of one collar-density block. -/
def collarBlockSize (s : Finset κ) (a : κ → ℝ) : ℝ :=
  Real.sqrt (∑ k ∈ s, a k ^ 2)

/-- Canonical unit direction, zero on an empty or vanishing block. -/
def collarBlockDirection (s : Finset κ) (a : κ → ℝ) (k : κ) : ℝ :=
  a k / collarBlockSize s a

theorem collarBlockDirection_sq_sum_le (s : Finset κ) (a : κ → ℝ) :
    (∑ k ∈ s, collarBlockDirection s a k ^ 2) ≤ 1 := by
  have hq : collarBlockSize s a ^ 2 = ∑ k ∈ s, a k ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg (a k))
  simp only [collarBlockDirection, div_pow, ← Finset.sum_div, ← hq]
  by_cases h : collarBlockSize s a = 0 <;> simp [h]

theorem collarBlockDirection_pairing (s : Finset κ) (a : κ → ℝ) :
    (∑ k ∈ s, a k * collarBlockDirection s a k) = collarBlockSize s a := by
  have hq : collarBlockSize s a ^ 2 = ∑ k ∈ s, a k ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg (a k))
  simp only [collarBlockDirection]
  simp_rw [show ∀ k, a k * (a k / collarBlockSize s a) =
    a k ^ 2 / collarBlockSize s a by intro k; ring]
  rw [← Finset.sum_div, ← hq]
  by_cases h : collarBlockSize s a = 0
  · simp [h]
  · field_simp

/-- Shared-origin support value for the complete density array. -/
def collarDualScale (M : Finset ι) (s : ι → Finset κ) (a : ι → κ → ℝ) (W : ℝ) : ℝ :=
  Real.sqrt (W ^ 2 + blockWeightNorm M s a ^ 2)

/-- Common radial factor of the physical marginal prices. -/
def collarDualRadius (M : Finset ι) (s : ι → Finset κ) (a : ι → κ → ℝ) (W : ℝ) : ℝ :=
  blockWeightNorm M s a / collarDualScale M s a W

/-- Canonical marginal price of a collar density; zero blocks require no choice. -/
def collarDualSlope (M : Finset ι) (s : ι → Finset κ) (a : ι → κ → ℝ)
    (W : ℝ) (m : ι) (k : κ) : ℝ :=
  collarDualRadius M s a W * collarBlockDirection (s m) (a m) k

theorem collarDualScale_pos (M : Finset ι) (s : ι → Finset κ) (a : ι → κ → ℝ)
    {W : ℝ} (hW : 0 < W) : 0 < collarDualScale M s a W := by
  apply Real.sqrt_pos.2
  exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hW) (sq_nonneg _)

theorem collarDualRadius_sphere (M : Finset ι) (s : ι → Finset κ) (a : ι → κ → ℝ)
    {W : ℝ} (hW : 0 < W) :
    (W / collarDualScale M s a W) ^ 2 + collarDualRadius M s a W ^ 2 = 1 := by
  have hD := (collarDualScale_pos M s a hW).ne'
  have hsq : collarDualScale M s a W ^ 2 = W ^ 2 + blockWeightNorm M s a ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  unfold collarDualRadius
  rw [div_pow, div_pow, ← add_div, ← hsq, div_self (pow_ne_zero _ hD)]

theorem collarDualSlope_sphere (M : Finset ι) (s : ι → Finset κ) (a : ι → κ → ℝ)
    {W : ℝ} (hW : 0 < W) (m : ι) :
    (W / collarDualScale M s a W) ^ 2 +
      (∑ k ∈ s m, collarDualSlope M s a W m k ^ 2) ≤ 1 := by
  have h := mul_le_mul_of_nonneg_left (collarBlockDirection_sq_sum_le (s m) (a m))
    (sq_nonneg (collarDualRadius M s a W))
  simp only [collarDualSlope, mul_pow, ← Finset.mul_sum]
  linarith [collarDualRadius_sphere M s a hW]

theorem collarDualSlope_pairing (M : Finset ι) (s : ι → Finset κ) (a : ι → κ → ℝ)
    (W : ℝ) :
    (∑ m ∈ M, ∑ k ∈ s m, a m k * collarDualSlope M s a W m k) =
      collarDualRadius M s a W * blockWeightNorm M s a := by
  unfold collarDualSlope
  simp_rw [show ∀ m k, a m k * (collarDualRadius M s a W * collarBlockDirection (s m) (a m) k) =
    collarDualRadius M s a W * (a m k * collarBlockDirection (s m) (a m) k) by intros; ring]
  simp_rw [← Finset.mul_sum, collarBlockDirection_pairing]
  rfl

theorem collarDualSlope_attains (M : Finset ι) (s : ι → Finset κ) (a : ι → κ → ℝ)
    {W : ℝ} (hW : 0 < W) :
    W * (W / collarDualScale M s a W) +
      (∑ m ∈ M, ∑ k ∈ s m, a m k * collarDualSlope M s a W m k) =
      collarDualScale M s a W := by
  rw [collarDualSlope_pairing]
  have hD := (collarDualScale_pos M s a hW).ne'
  have hsq : collarDualScale M s a W ^ 2 = W ^ 2 + blockWeightNorm M s a ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  unfold collarDualRadius
  field_simp
  nlinarith only [hsq]

/-- The explicit marginal prices support the entire shared-origin norm, including zero blocks. -/
theorem collarDualSlope_supports (M : Finset ι) (hM : M.Nonempty) (s : ι → Finset κ)
    (a b : ι → κ → ℝ) {W : ℝ} (hW : 0 < W) :
    collarDualScale M s a W +
      (∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k) * collarDualSlope M s a W m k) ≤
      collarDualScale M s b W := by
  have h := shared_origin_weighted_sum_le M hM s b (collarDualSlope M s a W) W
    (W / collarDualScale M s a W) 1 (by norm_num)
    (fun m _ => by simpa using collarDualSlope_sphere M s a hW m)
  have heq := collarDualSlope_attains M s a hW
  simp only [mul_one] at h
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  change W * (W / collarDualScale M s a W) + _ ≤ collarDualScale M s b W at h
  linarith

/-- Nonnegative nonlinear remainder in physical-allocation comparison. -/
def collarDualRemainder (M : Finset ι) (s : ι → Finset κ)
    (a b : ι → κ → ℝ) (W : ℝ) : ℝ :=
  collarDualScale M s b W - collarDualScale M s a W -
    ∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k) * collarDualSlope M s a W m k

theorem collarDualRemainder_nonneg (M : Finset ι) (hM : M.Nonempty)
    (s : ι → Finset κ) (a b : ι → κ → ℝ) {W : ℝ} (hW : 0 < W) :
    0 ≤ collarDualRemainder M s a b W := by
  have h := collarDualSlope_supports M hM s a b hW
  unfold collarDualRemainder
  linarith

/-- One block's nonnegative directional discrepancy, with a canonical zero-block rule. -/
def collarBlockRemainder (s : Finset κ) (a b : κ → ℝ) : ℝ :=
  collarBlockSize s b - ∑ k ∈ s, b k * collarBlockDirection s a k

theorem collarBlockRemainder_nonneg (s : Finset κ) (a b : κ → ℝ) :
    0 ≤ collarBlockRemainder s a b := by
  have h := sphere_weighted_sum_le_sqrt_mul s 0 b (collarBlockDirection s a) 0 1
    (by norm_num) (by simpa using collarBlockDirection_sq_sum_le s a)
  simp only [zero_mul, zero_add, zero_pow (by norm_num : 2 ≠ 0), mul_one] at h
  exact sub_nonneg.mpr h

/-- Radial discrepancy after the individual block directions have been matched. -/
def collarRadialRemainder (W A B : ℝ) : ℝ :=
  Real.sqrt (W ^ 2 + B ^ 2) - Real.sqrt (W ^ 2 + A ^ 2) -
    (A / Real.sqrt (W ^ 2 + A ^ 2)) * (B - A)

/-- Exact curvature of the radial cost. In particular, the remainder detects changes of total block norm. -/
theorem collarRadialRemainder_rationalized {W A B : ℝ}
    (hW : 0 < W) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    collarRadialRemainder W A B =
      W ^ 2 * (B - A) ^ 2 /
        (Real.sqrt (W ^ 2 + A ^ 2) *
          (Real.sqrt (W ^ 2 + A ^ 2) * Real.sqrt (W ^ 2 + B ^ 2) + W ^ 2 + A * B)) := by
  let S := Real.sqrt (W ^ 2 + A ^ 2)
  let T := Real.sqrt (W ^ 2 + B ^ 2)
  have hS : 0 < S := Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg (sq_pos_of_pos hW) (sq_nonneg _))
  have hT : 0 < T := Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg (sq_pos_of_pos hW) (sq_nonneg _))
  have hSsq : S ^ 2 = W ^ 2 + A ^ 2 := Real.sq_sqrt (by positivity)
  have hTsq : T ^ 2 = W ^ 2 + B ^ 2 := Real.sq_sqrt (by positivity)
  have hd : 0 < S * T + W ^ 2 + A * B := by positivity
  have heq : collarRadialRemainder W A B = (S * T - (W ^ 2 + A * B)) / S := by
    change T - S - A / S * (B - A) = _
    field_simp
    nlinarith only [hSsq]
  have hdet : (S * T - (W ^ 2 + A * B)) * (S * T + W ^ 2 + A * B) =
      W ^ 2 * (B - A) ^ 2 := by
    calc
      _ = S ^ 2 * T ^ 2 - (W ^ 2 + A * B) ^ 2 := by ring
      _ = _ := by rw [hSsq, hTsq]; ring
  rw [heq]
  change _ = _ / (S * (S * T + W ^ 2 + A * B))
  calc
    _ = ((S * T - (W ^ 2 + A * B)) * (S * T + W ^ 2 + A * B)) /
        (S * (S * T + W ^ 2 + A * B)) := by
      field_simp
    _ = _ := by rw [hdet]

theorem collarRadialRemainder_nonneg {W A B : ℝ}
    (hW : 0 < W) (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ collarRadialRemainder W A B := by
  rw [collarRadialRemainder_rationalized hW hA hB]
  positivity

theorem collarRadialRemainder_eq_zero_iff {W A B : ℝ}
    (hW : 0 < W) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    collarRadialRemainder W A B = 0 ↔ B = A := by
  constructor
  · intro hz
    by_contra hBA
    have hdiff : B - A ≠ 0 := sub_ne_zero.mpr hBA
    have hp : 0 < collarRadialRemainder W A B := by
      rw [collarRadialRemainder_rationalized hW hA hB]
      positivity
    linarith
  · rintro rfl
    simp [collarRadialRemainder]

theorem collarDualSlope_test_pairing (M : Finset ι) (s : ι → Finset κ)
    (a b : ι → κ → ℝ) (W : ℝ) :
    (∑ m ∈ M, ∑ k ∈ s m, b m k * collarDualSlope M s a W m k) =
      collarDualRadius M s a W *
        ∑ m ∈ M, ∑ k ∈ s m, b m k * collarBlockDirection (s m) (a m) k := by
  unfold collarDualSlope
  simp_rw [show ∀ m k, b m k * (collarDualRadius M s a W * collarBlockDirection (s m) (a m) k) =
    collarDualRadius M s a W * (b m k * collarBlockDirection (s m) (a m) k) by intros; ring]
  simp_rw [← Finset.mul_sum]

/-- Exact decomposition into radial curvature and the sum of block-direction discrepancies. -/
theorem collarDualRemainder_decomposition (M : Finset ι) (s : ι → Finset κ)
    (a b : ι → κ → ℝ) (W : ℝ) :
    collarDualRemainder M s a b W =
      collarRadialRemainder W (blockWeightNorm M s a) (blockWeightNorm M s b) +
        collarDualRadius M s a W * ∑ m ∈ M, collarBlockRemainder (s m) (a m) (b m) := by
  unfold collarDualRemainder
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [collarDualSlope_test_pairing, collarDualSlope_pairing]
  simp only [collarBlockRemainder, Finset.sum_sub_distrib]
  change collarDualScale M s b W - collarDualScale M s a W -
    (collarDualRadius M s a W * _ - collarDualRadius M s a W * blockWeightNorm M s a) =
      collarRadialRemainder W (blockWeightNorm M s a) (blockWeightNorm M s b) +
        collarDualRadius M s a W * (blockWeightNorm M s b - _)
  unfold collarRadialRemainder collarDualRadius collarDualScale
  ring

/-- Vanishing comparison error forces equality of aggregate block norms. -/
theorem collarDualRemainder_zero_forces_blockNorm (M : Finset ι) (s : ι → Finset κ)
    (a b : ι → κ → ℝ) {W : ℝ} (hW : 0 < W)
    (hzero : collarDualRemainder M s a b W = 0) :
    blockWeightNorm M s b = blockWeightNorm M s a := by
  have hA := blockWeightNorm_nonneg M s a
  have hB := blockWeightNorm_nonneg M s b
  have hrad := collarRadialRemainder_nonneg hW hA hB
  have hdir : 0 ≤ collarDualRadius M s a W *
      ∑ m ∈ M, collarBlockRemainder (s m) (a m) (b m) :=
    mul_nonneg (div_nonneg hA (Real.sqrt_nonneg _))
      (Finset.sum_nonneg fun m _ => collarBlockRemainder_nonneg (s m) (a m) (b m))
  rw [collarDualRemainder_decomposition] at hzero
  exact (collarRadialRemainder_eq_zero_iff hW hA hB).1 (by linarith)

/-- Exact fibre coefficient comparison, before the common physical mass cancels on integration. -/
theorem collarDual_kernel_comparison (M : Finset ι) (s : ι → Finset κ)
    (a b : ι → κ → ℝ) (W : ℝ) :
    (W + (∑ m ∈ M, ∑ k ∈ s m, b m k) - collarDualScale M s b W) -
      (W + (∑ m ∈ M, ∑ k ∈ s m, a m k) - collarDualScale M s a W) =
      (∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k)) -
        (∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k) * collarDualSlope M s a W m k) -
          collarDualRemainder M s a b W := by
  unfold collarDualRemainder
  simp_rw [Finset.sum_sub_distrib]
  ring

theorem collarDualRadius_nonneg (M : Finset ι) (s : ι → Finset κ)
    (a : ι → κ → ℝ) (W : ℝ) : 0 ≤ collarDualRadius M s a W :=
  div_nonneg (blockWeightNorm_nonneg M s a) (Real.sqrt_nonneg _)

theorem collarDualRadius_lt_one (M : Finset ι) (s : ι → Finset κ)
    (a : ι → κ → ℝ) {W : ℝ} (hW : 0 < W) : collarDualRadius M s a W < 1 := by
  apply (div_lt_one (collarDualScale_pos M s a hW)).2
  apply Real.lt_sqrt (blockWeightNorm_nonneg M s a) |>.2
  nlinarith [sq_pos_of_pos hW]

theorem collarBlockDirection_le_one (s : Finset κ) (a : κ → ℝ) (k : κ) (hk : k ∈ s) :
    collarBlockDirection s a k ≤ 1 := by
  apply div_le_one_of_le₀ _ (Real.sqrt_nonneg _)
  exact Real.le_sqrt_of_sq_le
    (Finset.single_le_sum (f := fun j => a j ^ 2) (fun j _ => sq_nonneg _) hk)

theorem collarDualSlope_le_radius (M : Finset ι) (s : ι → Finset κ)
    (a : ι → κ → ℝ) (W : ℝ) (m : ι) (k : κ) (hk : k ∈ s m) :
    collarDualSlope M s a W m k ≤ collarDualRadius M s a W := by
  exact mul_le_of_le_one_right (collarDualRadius_nonneg M s a W)
    (collarBlockDirection_le_one (s m) (a m) k hk)

theorem collarDualSlope_nonneg (M : Finset ι) (s : ι → Finset κ)
    (a : ι → κ → ℝ) (W : ℝ) (m : ι) (k : κ) (ha : 0 ≤ a m k) :
    0 ≤ collarDualSlope M s a W m k :=
  mul_nonneg (collarDualRadius_nonneg M s a W) (div_nonneg ha (Real.sqrt_nonneg _))

/-- The dual remainder has a collar-mass bound; singular origin terms cancel before integration. -/
theorem collarDualRemainder_le_blockNorm_add (M : Finset ι) (s : ι → Finset κ)
    (a b : ι → κ → ℝ) {W : ℝ} (hW : 0 < W)
    (ha : ∀ m ∈ M, ∀ k ∈ s m, 0 ≤ a m k)
    (hb : ∀ m ∈ M, ∀ k ∈ s m, 0 ≤ b m k) :
    collarDualRemainder M s a b W ≤ blockWeightNorm M s a + blockWeightNorm M s b := by
  have hA := blockWeightNorm_nonneg M s a
  have hB := blockWeightNorm_nonneg M s b
  have hupper : collarDualScale M s b W ≤ W + blockWeightNorm M s b := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [mul_nonneg hW.le hB]⟩
  have hlower : W ≤ collarDualScale M s a W :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
  have hpa : collarDualRadius M s a W * blockWeightNorm M s a ≤ blockWeightNorm M s a :=
    mul_le_of_le_one_left hA (collarDualRadius_lt_one M s a hW).le
  have hpb : 0 ≤ ∑ m ∈ M, ∑ k ∈ s m, b m k * collarDualSlope M s a W m k :=
    Finset.sum_nonneg fun m hm => Finset.sum_nonneg fun k hk =>
      mul_nonneg (hb m hm k hk) (collarDualSlope_nonneg M s a W m k (ha m hm k hk))
  unfold collarDualRemainder
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [collarDualSlope_pairing]
  linarith

/-- Joint origin-to-collar coefficient for a finite array. -/
def collarAllocationKernel (M : Finset ι) (s : ι → Finset κ) (a : ι → κ → ℝ) (W : ℝ) : ℝ :=
  W + (∑ m ∈ M, ∑ k ∈ s m, a m k) - collarDualScale M s a W

theorem collarAllocationKernel_support_upper (M : Finset ι) (hM : M.Nonempty)
    (s : ι → Finset κ) (a b : ι → κ → ℝ) {W : ℝ} (hW : 0 < W) :
    collarAllocationKernel M s b W - collarAllocationKernel M s a W ≤
      ∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k) * (1 - collarDualSlope M s a W m k) := by
  have h := collarDualSlope_supports M hM s a b hW
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  unfold collarAllocationKernel
  linarith

/-- Quantitative capacity saturation: every added nonnegative density improves the coefficient,
with loss bounded by the final radial price. -/
theorem collarAllocationKernel_monotone_bounds (M : Finset ι) (hM : M.Nonempty)
    (s : ι → Finset κ) (a b : ι → κ → ℝ) {W : ℝ} (hW : 0 < W)
    (ha : ∀ m ∈ M, ∀ k ∈ s m, 0 ≤ a m k)
    (hab : ∀ m ∈ M, ∀ k ∈ s m, a m k ≤ b m k) :
    (1 - collarDualRadius M s b W) * (∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k)) ≤
        collarAllocationKernel M s b W - collarAllocationKernel M s a W ∧
    collarAllocationKernel M s b W - collarAllocationKernel M s a W ≤
      ∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k) := by
  have hrev := collarAllocationKernel_support_upper M hM s b a hW
  have heq : (∑ m ∈ M, ∑ k ∈ s m,
      (a m k - b m k) * (1 - collarDualSlope M s b W m k)) =
        -(∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k) * (1 - collarDualSlope M s b W m k)) := by
    simp_rw [show ∀ m k, (a m k - b m k) * (1 - collarDualSlope M s b W m k) =
      -((b m k - a m k) * (1 - collarDualSlope M s b W m k)) by intros; ring,
      Finset.sum_neg_distrib]
  rw [heq] at hrev
  have hlow : (∑ m ∈ M, ∑ k ∈ s m,
      (b m k - a m k) * (1 - collarDualRadius M s b W)) ≤
        ∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k) * (1 - collarDualSlope M s b W m k) := by
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_left (collarDualSlope_le_radius M s b W m k hk) 1)
      (sub_nonneg.mpr (hab m hm k hk))
  simp only [← Finset.sum_mul] at hlow
  constructor
  · nlinarith only [hlow, hrev]
  · apply (collarAllocationKernel_support_upper M hM s a b hW).trans
    apply Finset.sum_le_sum
    intro m hm
    apply Finset.sum_le_sum
    intro k hk
    exact mul_le_of_le_one_right (sub_nonneg.mpr (hab m hm k hk))
      (sub_le_self 1 (collarDualSlope_nonneg M s a W m k (ha m hm k hk)))

theorem collarAllocationKernel_strict_mono (M : Finset ι) (hM : M.Nonempty)
    (s : ι → Finset κ) (a b : ι → κ → ℝ) {W : ℝ} (hW : 0 < W)
    (ha : ∀ m ∈ M, ∀ k ∈ s m, 0 ≤ a m k)
    (hab : ∀ m ∈ M, ∀ k ∈ s m, a m k ≤ b m k)
    (hmass : 0 < ∑ m ∈ M, ∑ k ∈ s m, (b m k - a m k)) :
    collarAllocationKernel M s a W < collarAllocationKernel M s b W := by
  have h := (collarAllocationKernel_monotone_bounds M hM s a b hW ha hab).1
  have hp := mul_pos (sub_pos.mpr (collarDualRadius_lt_one M s b hW)) hmass
  linarith

/-- Canonical dual prices vary measurably with the densities, including vanishing blocks. -/
theorem measurable_collarDualSlope {X : Type*} [MeasurableSpace X]
    (M : Finset ι) (s : ι → Finset κ) (a : X → ι → κ → ℝ) (W : X → ℝ)
    (ha : ∀ m k, Measurable fun x => a x m k) (hW : Measurable W) (m : ι) (k : κ) :
    Measurable fun x => collarDualSlope M s (a x) (W x) m k := by
  have hq (j : ι) : Measurable fun x => collarBlockSize (s j) (a x j) :=
    Real.continuous_sqrt.measurable.comp ((s j).measurable_sum fun l _ => (ha j l).pow_const 2)
  have hA : Measurable fun x => blockWeightNorm M s (a x) :=
    M.measurable_sum fun j _ => hq j
  have hS : Measurable fun x => collarDualScale M s (a x) (W x) :=
    Real.continuous_sqrt.measurable.comp ((hW.pow_const 2).add (hA.pow_const 2))
  exact (hA.div hS).mul ((ha m k).div (hq m))

/-- Explicit dual prices for the verified finite-grid physical partition. -/
def logarithmicCollarDualSlope (n : ℕ) (j : ℕ × Bool) (k : ℕ) (y : ℝ) : ℝ :=
  collarDualSlope (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => logarithmicCollarWeight n j.2 k y) (archLevySinhWeight y) j k

theorem measurable_logarithmicCollarDualSlope (n : ℕ) (j : ℕ × Bool) (k : ℕ) :
    Measurable (logarithmicCollarDualSlope n j k) := by
  exact measurable_collarDualSlope (logarithmicSignedCosets n)
    (fun j => logarithmicCosetNodes n j.1)
    (fun y j k => logarithmicCollarWeight n j.2 k y) archLevySinhWeight
    (fun j k => measurable_logarithmicCollarWeight n k j.2)
    measurable_archLevySinhWeight j k

theorem logarithmicCollarDualSlope_bounds (n : ℕ) (j : ℕ × Bool) (k : ℕ)
    (hk : k ∈ logarithmicCosetNodes n j.1) {y : ℝ} (hy : 0 < y) :
    0 ≤ logarithmicCollarDualSlope n j k y ∧ logarithmicCollarDualSlope n j k y < 1 := by
  let M := logarithmicSignedCosets n
  let s := fun j : ℕ × Bool => logarithmicCosetNodes n j.1
  let a := fun (j : ℕ × Bool) k => logarithmicCollarWeight n j.2 k y
  change 0 ≤ collarDualSlope M s a (archLevySinhWeight y) j k ∧
    collarDualSlope M s a (archLevySinhWeight y) j k < 1
  constructor
  · exact collarDualSlope_nonneg M s a (archLevySinhWeight y) j k
      (logarithmicCollarWeight_nonneg n k j.2 y)
  · exact (collarDualSlope_le_radius M s a (archLevySinhWeight y) j k hk).trans_lt
      (collarDualRadius_lt_one M s a (archLevySinhWeight_pos hy))

/-- The marginal price has an ordinary real integral across the singular origin endpoint. -/
theorem integrableOn_logarithmicCollarDualSlope (n : ℕ) (j : ℕ × Bool) (k : ℕ)
    (hk : k ∈ logarithmicCosetNodes n j.1) :
    IntegrableOn (logarithmicCollarDualSlope n j k) (Ioo 0 logarithmicCollarRadius) := by
  apply volume.integrableOn_of_bounded (M := 1)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    (measurable_logarithmicCollarDualSlope n j k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  have h := logarithmicCollarDualSlope_bounds n j k hk hy.1
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2.le

end
end GaloisForLFunctions.BiScaleUncertainty
