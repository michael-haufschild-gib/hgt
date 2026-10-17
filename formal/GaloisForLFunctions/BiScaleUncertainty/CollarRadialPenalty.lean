import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarCutoffStability

/-!
# Finite radial penalties and localized collar perturbations

Every independent-coset coefficient is physical mass minus an integrable radial
penalty. The singular origin weight is kept inside the difference. Adding a
small amount of density changes this penalty quadratically relative to the
origin weight, even when the added density shares old odd-coset blocks.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
variable {ι κ : Type*}

def collarRadialPenalty (W A : ℝ) : ℝ := Real.sqrt (W ^ 2 + A ^ 2) - W

theorem collarRadialPenalty_nonneg (W A : ℝ) : 0 ≤ collarRadialPenalty W A :=
  sub_nonneg.mpr (Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg A)))

theorem collarRadialPenalty_le {W A : ℝ} (hW : 0 ≤ W) (hA : 0 ≤ A) :
    collarRadialPenalty W A ≤ A := by
  have h : Real.sqrt (W ^ 2 + A ^ 2) ≤ W + A :=
    Real.sqrt_le_iff.mpr ⟨add_nonneg hW hA, by nlinarith [mul_nonneg hW hA]⟩
  exact sub_le_iff_le_add.mpr (by linarith)

theorem collarRadialPenalty_mono {W A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) :
    collarRadialPenalty W A ≤ collarRadialPenalty W B := by
  apply sub_le_sub_right
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (sub_nonneg.mpr hAB) (show 0 ≤ B + A by linarith)]

/-- The increment is controlled by added mass, with no separation of blocks. -/
theorem collarRadialPenalty_increment {W A B G : ℝ} (hW : 0 < W)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hBG : B ≤ A + G) :
    2 * W * (collarRadialPenalty W B - collarRadialPenalty W A) ≤
      2 * A * G + G ^ 2 := by
  have hsa := Real.sq_sqrt (show 0 ≤ W ^ 2 + A ^ 2 by positivity)
  have hsb := Real.sq_sqrt (show 0 ≤ W ^ 2 + B ^ 2 by positivity)
  have hla : W ≤ Real.sqrt (W ^ 2 + A ^ 2) :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg A))
  have hlb : W ≤ Real.sqrt (W ^ 2 + B ^ 2) :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg B))
  unfold collarRadialPenalty
  by_cases h : Real.sqrt (W ^ 2 + B ^ 2) ≤ Real.sqrt (W ^ 2 + A ^ 2)
  · have hm := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 2 * W by positivity)
      (sub_nonpos.mpr h)
    nlinarith [mul_nonneg hA hG, sq_nonneg G]
  · have hp := mul_nonneg (sub_nonneg.mpr (le_of_not_ge h))
      (show 0 ≤ Real.sqrt (W ^ 2 + B ^ 2) + Real.sqrt (W ^ 2 + A ^ 2) - 2 * W by
        linarith)
    have hsq := mul_nonneg (sub_nonneg.mpr hBG) (show 0 ≤ A + G + B by positivity)
    nlinarith

theorem collarRadialPenalty_increment_le {W A B G : ℝ} (hW : 0 < W)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hG : 0 ≤ G) (hBG : B ≤ A + G) :
    collarRadialPenalty W B - collarRadialPenalty W A ≤
      (2 * A * G + G ^ 2) / (2 * W) := by
  apply (le_div_iff₀ (by positivity : 0 < 2 * W)).mpr
  simpa only [mul_comm] using collarRadialPenalty_increment hW hA hB hG hBG

theorem blockWeightNorm_mono (M : Finset ι) (s : ι → Finset κ)
    (a b : ι → κ → ℝ)
    (ha : ∀ j ∈ M, ∀ k ∈ s j, 0 ≤ a j k)
    (hab : ∀ j ∈ M, ∀ k ∈ s j, a j k ≤ b j k) :
    blockWeightNorm M s a ≤ blockWeightNorm M s b := by
  apply Finset.sum_le_sum
  intro j hj
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro k hk
  have h := ha j hj k hk
  have h' := hab j hj k hk
  nlinarith [mul_nonneg (sub_nonneg.mpr h') (show 0 ≤ b j k + a j k by linarith)]

/-- Coordinatewise additions can enlarge the total block norm by at most their mass. -/
theorem blockWeightNorm_le_add_mass (M : Finset ι) (s : ι → Finset κ)
    (a b e : ι → κ → ℝ)
    (hb : ∀ j ∈ M, ∀ k ∈ s j, 0 ≤ b j k)
    (he : ∀ j ∈ M, ∀ k ∈ s j, 0 ≤ e j k)
    (hab : ∀ j ∈ M, ∀ k ∈ s j, b j k ≤ a j k + e j k) :
    blockWeightNorm M s b ≤ blockWeightNorm M s a +
      ∑ j ∈ M, ∑ k ∈ s j, e j k := by
  rw [blockWeightNorm, blockWeightNorm, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  let d := collarBlockDirection (s j) (b j)
  have hd := collarBlockDirection_sq_sum_le (s j) (b j)
  have hq := Real.sq_sqrt (Finset.sum_nonneg (fun k (_ : k ∈ s j) => sq_nonneg (a j k)))
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (s j) (a j) d
  have hmul := mul_le_of_le_one_right
    (Finset.sum_nonneg (fun k (_ : k ∈ s j) => sq_nonneg (a j k))) hd
  have ha : (∑ k ∈ s j, a j k * d k) ≤ Real.sqrt (∑ k ∈ s j, a j k ^ 2) := by
    have hs := Real.sqrt_nonneg (∑ k ∈ s j, a j k ^ 2)
    change _ ≤ (∑ k ∈ s j, a j k ^ 2) * (∑ k ∈ s j, d k ^ 2) at hc
    change (∑ k ∈ s j, a j k ^ 2) * (∑ k ∈ s j, d k ^ 2) ≤ _ at hmul
    nlinarith
  have hb' := collarBlockDirection_pairing (s j) (b j)
  change (∑ k ∈ s j, b j k * d k) = Real.sqrt (∑ k ∈ s j, b j k ^ 2) at hb'
  rw [← hb']
  calc
    _ ≤ ∑ k ∈ s j, (a j k * d k + e j k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hd0 : 0 ≤ d k := div_nonneg (hb j hj k hk) (Real.sqrt_nonneg _)
      have hd1 := collarBlockDirection_le_one (s j) (b j) k hk
      have h1 := mul_le_mul_of_nonneg_right (hab j hj k hk) hd0
      have h2 := mul_le_of_le_one_right (he j hj k hk) hd1
      change e j k * d k ≤ e j k at h2
      nlinarith
    _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith

namespace PhysicalCollarPartition
variable {n : ℕ}

def radialPenalty (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  collarRadialPenalty (archLevySinhWeight y) (ρ.blockNorm y)

theorem radialPenalty_eq_mass_sub_kernel (ρ : PhysicalCollarPartition n) (y : ℝ) :
    ρ.radialPenalty y = ρ.mass y - ρ.kernel y := by
  unfold radialPenalty collarRadialPenalty kernel
  ring

theorem integrableOn_radialPenalty (ρ : PhysicalCollarPartition n) :
    IntegrableOn ρ.radialPenalty (Ioo 0 logarithmicCollarRadius) := by
  rw [show ρ.radialPenalty = (fun y => ρ.mass y - ρ.kernel y) from
    funext ρ.radialPenalty_eq_mass_sub_kernel]
  exact ρ.integrableOn_mass.sub ρ.integrableOn_kernel

theorem radialPenalty_bounds (ρ : PhysicalCollarPartition n) {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ ρ.radialPenalty y ∧ ρ.radialPenalty y ≤ ρ.mass y :=
  ⟨collarRadialPenalty_nonneg _ _,
    (collarRadialPenalty_le (archLevySinhWeight_nonneg hy) (ρ.blockNorm_nonneg y)).trans
      (ρ.blockNorm_le_mass y)⟩

/-- Exact finite decomposition; neither singular term is integrated separately. -/
theorem coefficient_eq_mass_sub_penalty (ρ : PhysicalCollarPartition n) :
    ρ.coefficient =
      (∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x) -
      ∫ y in Ioo 0 logarithmicCollarRadius, ρ.radialPenalty y := by
  rw [← ρ.integral_mass, show ρ.radialPenalty = fun y => ρ.mass y - ρ.kernel y from
    funext ρ.radialPenalty_eq_mass_sub_kernel,
    integral_sub ρ.integrableOn_mass ρ.integrableOn_kernel]
  unfold coefficient
  ring

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
