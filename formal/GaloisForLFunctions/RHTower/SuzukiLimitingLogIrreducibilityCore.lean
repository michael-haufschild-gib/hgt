import GaloisForLFunctions.RHTower.SuzukiLimitingLogOperator

/-!
# Suzuki limiting logarithmic form: Markov identity and irreducibility core

This file formalizes the hard Beurling--Deny calculation behind Suzuki's 2026 ground-state
argument. On the literal real source core, it proves:

* exact positive/negative and modulus decompositions of the finite-part energy;
* product-measure integrability of the singular `1 / |x - y|` jump kernel;
* nonnegativity and strict positivity of the cross-sign interaction;
* strict energy loss under modulus for every genuinely sign-changing core vector.

All statements are unconditional. No abstract positivity-improving theorem is assumed: the
strict interaction is proved directly from positivity of the open sign sets and of the jump
kernel on their product rectangle.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

def suzukiRealPositivePart (u : ℝ → ℝ) : ℝ → ℝ := fun x => (u x)⁺

def suzukiRealNegativePart (u : ℝ → ℝ) : ℝ → ℝ := fun x => (u x)⁻

@[simp] theorem suzukiRealPositivePart_nonneg (u : ℝ → ℝ) (x : ℝ) :
    0 ≤ suzukiRealPositivePart u x := posPart_nonneg _

@[simp] theorem suzukiRealNegativePart_nonneg (u : ℝ → ℝ) (x : ℝ) :
    0 ≤ suzukiRealNegativePart u x := negPart_nonneg _

theorem suzukiRealPositivePart_sub_negativePart (u : ℝ → ℝ) (x : ℝ) :
    suzukiRealPositivePart u x - suzukiRealNegativePart u x = u x := by
  exact posPart_sub_negPart (u x)

theorem suzukiRealPositivePart_mul_negativePart (u : ℝ → ℝ) (x : ℝ) :
    suzukiRealPositivePart u x * suzukiRealNegativePart u x = 0 := by
  by_cases hx : 0 ≤ u x
  · rw [suzukiRealNegativePart, negPart_eq_zero.2 hx, mul_zero]
  · rw [suzukiRealPositivePart, posPart_eq_zero.2 (le_of_not_ge hx), zero_mul]

theorem suzuki_signed_jump_split (u : ℝ → ℝ) (x y : ℝ) :
    (u x - u y) ^ 2 =
      (suzukiRealPositivePart u x - suzukiRealPositivePart u y) ^ 2 +
      (suzukiRealNegativePart u x - suzukiRealNegativePart u y) ^ 2 +
      2 * (suzukiRealPositivePart u x * suzukiRealNegativePart u y +
        suzukiRealPositivePart u y * suzukiRealNegativePart u x) := by
  rw [← suzukiRealPositivePart_sub_negativePart u x,
    ← suzukiRealPositivePart_sub_negativePart u y]
  have hx := suzukiRealPositivePart_mul_negativePart u x
  have hy := suzukiRealPositivePart_mul_negativePart u y
  nlinarith

theorem suzuki_signed_square_split (u : ℝ → ℝ) (x : ℝ) :
    u x ^ 2 = suzukiRealPositivePart u x ^ 2 +
      suzukiRealNegativePart u x ^ 2 := by
  rw [← suzukiRealPositivePart_sub_negativePart u x,
    ]
  have hx := suzukiRealPositivePart_mul_negativePart u x
  nlinarith

theorem four_mul_positive_negative_le_jump (u : ℝ → ℝ) (x y : ℝ) :
    4 * (suzukiRealPositivePart u x * suzukiRealNegativePart u y) ≤
      (u x - u y) ^ 2 := by
  by_cases hpx : 0 < suzukiRealPositivePart u x
  · have hux : 0 < u x := by
      by_contra h
      have hzero : suzukiRealPositivePart u x = 0 := by
        exact posPart_eq_zero.2 (le_of_not_gt h)
      linarith
    by_cases hny : 0 < suzukiRealNegativePart u y
    · have huy : u y < 0 := by
        by_contra h
        have hzero : suzukiRealNegativePart u y = 0 := by
          exact negPart_eq_zero.2 (le_of_not_gt h)
        linarith
      have hpxeq : suzukiRealPositivePart u x = u x := by
        exact posPart_eq_self.2 hux.le
      have hnyeq : suzukiRealNegativePart u y = -u y := by
        exact negPart_eq_neg.2 huy.le
      rw [hpxeq, hnyeq]
      nlinarith [sq_nonneg (u x + u y)]
    · have hny0 : suzukiRealNegativePart u y = 0 :=
        le_antisymm (le_of_not_gt hny) (suzukiRealNegativePart_nonneg u y)
      rw [hny0, mul_zero, mul_zero]
      exact sq_nonneg _
  · have hpx0 : suzukiRealPositivePart u x = 0 :=
      le_antisymm (le_of_not_gt hpx) (suzukiRealPositivePart_nonneg u x)
    rw [hpx0, zero_mul, mul_zero]
    exact sq_nonneg _

theorem abs_suzukiRealPositivePart_sub_le (u : ℝ → ℝ) (x y : ℝ) :
    |suzukiRealPositivePart u x - suzukiRealPositivePart u y| ≤ |u x - u y| := by
  have h := lipschitzWith_posPart.dist_le_mul (u x) (u y)
  simpa only [suzukiRealPositivePart, Real.dist_eq, NNReal.coe_one, one_mul] using h

theorem abs_suzukiRealNegativePart_sub_le (u : ℝ → ℝ) (x y : ℝ) :
    |suzukiRealNegativePart u x - suzukiRealNegativePart u y| ≤ |u x - u y| := by
  have h := lipschitzWith_negPart.dist_le_mul (u x) (u y)
  simpa only [suzukiRealNegativePart, Real.dist_eq, NNReal.coe_one, one_mul] using h

theorem suzukiRealPositivePart_jump_sq_le (u : ℝ → ℝ) (x y : ℝ) :
    (suzukiRealPositivePart u x - suzukiRealPositivePart u y) ^ 2 ≤
      (u x - u y) ^ 2 := by
  exact sq_le_sq.mpr (abs_suzukiRealPositivePart_sub_le u x y)

theorem suzukiRealNegativePart_jump_sq_le (u : ℝ → ℝ) (x y : ℝ) :
    (suzukiRealNegativePart u x - suzukiRealNegativePart u y) ^ 2 ≤
      (u x - u y) ^ 2 := by
  exact sq_le_sq.mpr (abs_suzukiRealNegativePart_sub_le u x y)

theorem continuous_suzukiRealPositivePart {u : ℝ → ℝ} (hu : Continuous u) :
    Continuous (suzukiRealPositivePart u) :=
  lipschitzWith_posPart.continuous.comp hu

theorem continuous_suzukiRealNegativePart {u : ℝ → ℝ} (hu : Continuous u) :
    Continuous (suzukiRealNegativePart u) :=
  lipschitzWith_negPart.continuous.comp hu

def suzukiUnitJumpKernel (u : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  (u z.1 - u z.2) ^ 2 * |z.1 - z.2|⁻¹

theorem suzukiUnitJumpKernel_nonneg (u : ℝ → ℝ) (z : ℝ × ℝ) :
    0 ≤ suzukiUnitJumpKernel u z :=
  mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (abs_nonneg _))

theorem integrable_suzukiUnitJumpKernel_product
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    Integrable (suzukiUnitJumpKernel u)
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod
        (volume.restrict (Ioc (-1 : ℝ) 1))) := by
  have henergy := suzukiFinitePartDifferenceEnergy_intervalIntegrable
    (by norm_num : (0 : ℝ) < 1) u.smooth
  have hmeas : AEStronglyMeasurable (suzukiUnitJumpKernel u)
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod
        (volume.restrict (Ioc (-1 : ℝ) 1))) := by
    apply Measurable.aestronglyMeasurable
    unfold suzukiUnitJumpKernel
    exact (((u.continuous.measurable.comp measurable_fst).sub
      (u.continuous.measurable.comp measurable_snd)).pow_const 2).mul
        (((measurable_fst.sub measurable_snd).abs).inv)
  rw [integrable_prod_iff hmeas]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hi := henergy.1 x (Ioc_subset_Icc_self hx)
    exact hi.1
  · have ho : Integrable
        (fun x => ∫ y in Ioc (-1 : ℝ) 1,
          (u x - u y) ^ 2 * |x - y|⁻¹)
        (volume.restrict (Ioc (-1 : ℝ) 1)) := by
      simpa only [IntegrableOn,
        intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
        using henergy.2.1
    refine ho.congr ?_
    filter_upwards with x
    apply integral_congr_ae
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact (abs_of_nonneg (suzukiUnitJumpKernel_nonneg u (x, y))).symm

def suzukiUnitSignCrossKernel (u : ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  suzukiRealPositivePart u z.1 * suzukiRealNegativePart u z.2 *
    |z.1 - z.2|⁻¹

theorem suzukiUnitSignCrossKernel_nonneg (u : ℝ → ℝ) (z : ℝ × ℝ) :
    0 ≤ suzukiUnitSignCrossKernel u z := by
  exact mul_nonneg
    (mul_nonneg (suzukiRealPositivePart_nonneg u z.1)
      (suzukiRealNegativePart_nonneg u z.2))
    (inv_nonneg.mpr (abs_nonneg _))

theorem integrable_suzukiUnitPositivePartJumpKernel_product
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    Integrable (suzukiUnitJumpKernel (suzukiRealPositivePart u))
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod
        (volume.restrict (Ioc (-1 : ℝ) 1))) := by
  apply (integrable_suzukiUnitJumpKernel_product u).mono
  · apply Measurable.aestronglyMeasurable
    unfold suzukiUnitJumpKernel
    exact ((((continuous_suzukiRealPositivePart u.continuous).measurable.comp
      measurable_fst).sub
      ((continuous_suzukiRealPositivePart u.continuous).measurable.comp
        measurable_snd)).pow_const 2).mul
          (((measurable_fst.sub measurable_snd).abs).inv)
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (suzukiUnitJumpKernel_nonneg (suzukiRealPositivePart u) z),
      abs_of_nonneg (suzukiUnitJumpKernel_nonneg u z)]
    exact mul_le_mul_of_nonneg_right
      (suzukiRealPositivePart_jump_sq_le u z.1 z.2)
      (inv_nonneg.mpr (abs_nonneg _))

theorem integrable_suzukiUnitNegativePartJumpKernel_product
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    Integrable (suzukiUnitJumpKernel (suzukiRealNegativePart u))
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod
        (volume.restrict (Ioc (-1 : ℝ) 1))) := by
  apply (integrable_suzukiUnitJumpKernel_product u).mono
  · apply Measurable.aestronglyMeasurable
    unfold suzukiUnitJumpKernel
    exact ((((continuous_suzukiRealNegativePart u.continuous).measurable.comp
      measurable_fst).sub
      ((continuous_suzukiRealNegativePart u.continuous).measurable.comp
        measurable_snd)).pow_const 2).mul
          (((measurable_fst.sub measurable_snd).abs).inv)
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (suzukiUnitJumpKernel_nonneg (suzukiRealNegativePart u) z),
      abs_of_nonneg (suzukiUnitJumpKernel_nonneg u z)]
    exact mul_le_mul_of_nonneg_right
      (suzukiRealNegativePart_jump_sq_le u z.1 z.2)
      (inv_nonneg.mpr (abs_nonneg _))

theorem integrable_suzukiUnitSignCrossKernel_product
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    Integrable (suzukiUnitSignCrossKernel u)
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod
        (volume.restrict (Ioc (-1 : ℝ) 1))) := by
  apply (integrable_suzukiUnitJumpKernel_product u).mono
  · apply Measurable.aestronglyMeasurable
    unfold suzukiUnitSignCrossKernel
    exact (((continuous_suzukiRealPositivePart u.continuous).measurable.comp
      measurable_fst).mul
      ((continuous_suzukiRealNegativePart u.continuous).measurable.comp
        measurable_snd)).mul
          (((measurable_fst.sub measurable_snd).abs).inv)
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (suzukiUnitSignCrossKernel_nonneg u z),
      abs_of_nonneg (suzukiUnitJumpKernel_nonneg u z)]
    have hfour := four_mul_positive_negative_le_jump u z.1 z.2
    have hcross : suzukiRealPositivePart u z.1 *
        suzukiRealNegativePart u z.2 ≤ (u z.1 - u z.2) ^ 2 := by
      have hpn := mul_nonneg (suzukiRealPositivePart_nonneg u z.1)
        (suzukiRealNegativePart_nonneg u z.2)
      linarith
    exact mul_le_mul_of_nonneg_right hcross
      (inv_nonneg.mpr (abs_nonneg _))

def suzukiUnitSignInteraction (u : ℝ → ℝ) : ℝ :=
  ∫ z : ℝ × ℝ,
    (suzukiUnitSignCrossKernel u z +
      suzukiUnitSignCrossKernel u (z.2, z.1))
    ∂((volume.restrict (Ioc (-1 : ℝ) 1)).prod
      (volume.restrict (Ioc (-1 : ℝ) 1)))

theorem integrable_suzukiUnitSignCrossKernel_swap_product
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    Integrable (fun z : ℝ × ℝ => suzukiUnitSignCrossKernel u (z.2, z.1))
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod
        (volume.restrict (Ioc (-1 : ℝ) 1))) := by
  simpa only [Function.comp_def, Prod.swap] using
    (integrable_suzukiUnitSignCrossKernel_product u).swap

theorem suzukiFinitePartDifferenceEnergy_eq_productIntegral_of_integrable
    (u : ℝ → ℝ)
    (hint : Integrable (suzukiUnitJumpKernel u)
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod
        (volume.restrict (Ioc (-1 : ℝ) 1)))) :
    suzukiFinitePartDifferenceEnergy 1 u =
      ∫ z : ℝ × ℝ, suzukiUnitJumpKernel u z
        ∂((volume.restrict (Ioc (-1 : ℝ) 1)).prod
          (volume.restrict (Ioc (-1 : ℝ) 1))) := by
  unfold suzukiFinitePartDifferenceEnergy
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  exact (integral_prod _ hint).symm

theorem suzukiFinitePartDifferenceEnergy_signed_split
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartDifferenceEnergy 1 u =
      suzukiFinitePartDifferenceEnergy 1 (suzukiRealPositivePart u) +
      suzukiFinitePartDifferenceEnergy 1 (suzukiRealNegativePart u) +
      2 * suzukiUnitSignInteraction u := by
  have hu := suzukiFinitePartDifferenceEnergy_eq_productIntegral_of_integrable u
    (integrable_suzukiUnitJumpKernel_product u)
  have hp := suzukiFinitePartDifferenceEnergy_eq_productIntegral_of_integrable
    (suzukiRealPositivePart u)
    (integrable_suzukiUnitPositivePartJumpKernel_product u)
  have hn := suzukiFinitePartDifferenceEnergy_eq_productIntegral_of_integrable
    (suzukiRealNegativePart u)
    (integrable_suzukiUnitNegativePartJumpKernel_product u)
  rw [hu, hp, hn]
  unfold suzukiUnitSignInteraction
  let μ := (volume.restrict (Ioc (-1 : ℝ) 1)).prod
    (volume.restrict (Ioc (-1 : ℝ) 1))
  have hpInt := integrable_suzukiUnitPositivePartJumpKernel_product u
  have hnInt := integrable_suzukiUnitNegativePartJumpKernel_product u
  have hcInt := integrable_suzukiUnitSignCrossKernel_product u
  have hcsInt := integrable_suzukiUnitSignCrossKernel_swap_product u
  calc
    (∫ z : ℝ × ℝ, suzukiUnitJumpKernel u z ∂μ) =
        ∫ z : ℝ × ℝ,
          (suzukiUnitJumpKernel (suzukiRealPositivePart u) z +
            suzukiUnitJumpKernel (suzukiRealNegativePart u) z) +
          2 * (suzukiUnitSignCrossKernel u z +
            suzukiUnitSignCrossKernel u (z.2, z.1)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      unfold suzukiUnitJumpKernel suzukiUnitSignCrossKernel
      rw [suzuki_signed_jump_split]
      rw [abs_sub_comm z.2 z.1]
      ring
    _ = (∫ z : ℝ × ℝ,
          suzukiUnitJumpKernel (suzukiRealPositivePart u) z +
            suzukiUnitJumpKernel (suzukiRealNegativePart u) z ∂μ) +
        ∫ z : ℝ × ℝ, 2 * (suzukiUnitSignCrossKernel u z +
          suzukiUnitSignCrossKernel u (z.2, z.1)) ∂μ :=
      integral_add (hpInt.add hnInt) ((hcInt.add hcsInt).const_mul 2)
    _ = (∫ z : ℝ × ℝ,
          suzukiUnitJumpKernel (suzukiRealPositivePart u) z ∂μ) +
        (∫ z : ℝ × ℝ,
          suzukiUnitJumpKernel (suzukiRealNegativePart u) z ∂μ) +
        2 * ∫ z : ℝ × ℝ, (suzukiUnitSignCrossKernel u z +
          suzukiUnitSignCrossKernel u (z.2, z.1)) ∂μ := by
      rw [integral_add hpInt hnInt, integral_const_mul]

theorem support_suzukiRealPositivePart_subset (u : ℝ → ℝ) :
    Function.support (suzukiRealPositivePart u) ⊆ Function.support u := by
  intro x hx hux
  apply hx
  simp [suzukiRealPositivePart, hux]

theorem support_suzukiRealNegativePart_subset (u : ℝ → ℝ) :
    Function.support (suzukiRealNegativePart u) ⊆ Function.support u := by
  intro x hx hux
  apply hx
  simp [suzukiRealNegativePart, hux]

theorem suzukiFinitePartLogPotential_signed_split
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartLogPotential 1 u =
      suzukiFinitePartLogPotential 1 (suzukiRealPositivePart u) +
      suzukiFinitePartLogPotential 1 (suzukiRealNegativePart u) := by
  have hpInt := (suzukiFinitePartLogPotential_integrable_upper
    (by norm_num : (0 : ℝ) < 1) u.supportRadius_nonneg
    u.supportRadius_lt_aperture
    (continuous_suzukiRealPositivePart u.continuous)
    ((support_suzukiRealPositivePart_subset u).trans u.support_subset)).1
  have hnInt := (suzukiFinitePartLogPotential_integrable_upper
    (by norm_num : (0 : ℝ) < 1) u.supportRadius_nonneg
    u.supportRadius_lt_aperture
    (continuous_suzukiRealNegativePart u.continuous)
    ((support_suzukiRealNegativePart_subset u).trans u.support_subset)).1
  unfold suzukiFinitePartLogPotential
  rw [← intervalIntegral.integral_add hpInt hnInt]
  apply intervalIntegral.integral_congr
  intro x _
  change Real.log (1 ^ 2 - x ^ 2) * u x ^ 2 =
    Real.log (1 ^ 2 - x ^ 2) * suzukiRealPositivePart u x ^ 2 +
      Real.log (1 ^ 2 - x ^ 2) * suzukiRealNegativePart u x ^ 2
  rw [← mul_add, ← suzuki_signed_square_split]

/-- Exact Beurling--Deny sign decomposition on Suzuki's smooth real core.  The only coupling
between positive and negative parts is the strictly nonnegative `1/|x-y|` jump interaction. -/
theorem suzukiFinitePartEnergy_signed_split
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartEnergy 1 u =
      suzukiFinitePartEnergy 1 (suzukiRealPositivePart u) +
      suzukiFinitePartEnergy 1 (suzukiRealNegativePart u) +
      (1 / 2 : ℝ) * suzukiUnitSignInteraction u := by
  unfold suzukiFinitePartEnergy
  rw [suzukiFinitePartDifferenceEnergy_signed_split,
    suzukiFinitePartLogPotential_signed_split]
  ring

/-- Strict irreducibility of Suzuki's jump kernel on the smooth real core: if both signs occur
inside the aperture, their `1/|x-y|` interaction has strictly positive mass. -/
theorem suzukiUnitSignInteraction_pos
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1)
    (hp : ∃ x ∈ Ioo (-1 : ℝ) 1, 0 < suzukiRealPositivePart u x)
    (hn : ∃ y ∈ Ioo (-1 : ℝ) 1, 0 < suzukiRealNegativePart u y) :
    0 < suzukiUnitSignInteraction u := by
  let S : Set ℝ := Ioc (-1 : ℝ) 1
  let μ : Measure ℝ := volume.restrict S
  let A : Set ℝ := {x | 0 < suzukiRealPositivePart u x} ∩ Ioo (-1 : ℝ) 1
  let B : Set ℝ := {y | 0 < suzukiRealNegativePart u y} ∩ Ioo (-1 : ℝ) 1
  obtain ⟨x, hxI, hpx⟩ := hp
  obtain ⟨y, hyI, hny⟩ := hn
  have hAopen : IsOpen A := by
    exact (isOpen_lt continuous_const
      (continuous_suzukiRealPositivePart u.continuous)).inter isOpen_Ioo
  have hBopen : IsOpen B := by
    exact (isOpen_lt continuous_const
      (continuous_suzukiRealNegativePart u.continuous)).inter isOpen_Ioo
  have hxA : x ∈ A := ⟨hpx, hxI⟩
  have hyB : y ∈ B := ⟨hny, hyI⟩
  have hAvol : 0 < volume A := hAopen.measure_pos volume ⟨x, hxA⟩
  have hBvol : 0 < volume B := hBopen.measure_pos volume ⟨y, hyB⟩
  have hAS : A ⊆ S := fun _ h => Ioo_subset_Ioc_self h.2
  have hBS : B ⊆ S := fun _ h => Ioo_subset_Ioc_self h.2
  have hAμ : μ A = volume A := by
    rw [Measure.restrict_apply hAopen.measurableSet]
    exact congrArg volume (inter_eq_left.mpr hAS)
  have hBμ : μ B = volume B := by
    rw [Measure.restrict_apply hBopen.measurableSet]
    exact congrArg volume (inter_eq_left.mpr hBS)
  have hrect : 0 < (μ.prod μ) (A ×ˢ B) := by
    rw [Measure.prod_prod, hAμ, hBμ]
    exact ENNReal.mul_pos hAvol.ne' hBvol.ne'
  have hrectSupport : A ×ˢ B ⊆ Function.support (suzukiUnitSignCrossKernel u) := by
    rintro z ⟨hzA, hzB⟩
    have hpz : 0 < suzukiRealPositivePart u z.1 := hzA.1
    have hnz : 0 < suzukiRealNegativePart u z.2 := hzB.1
    have hxy : z.1 ≠ z.2 := by
      intro h
      have hnz' : 0 < suzukiRealNegativePart u z.1 := by
        rwa [h]
      have hdisjoint := suzukiRealPositivePart_mul_negativePart u z.1
      nlinarith
    unfold Function.support suzukiUnitSignCrossKernel
    exact mul_ne_zero (mul_ne_zero hpz.ne' hnz.ne')
      (inv_ne_zero (abs_ne_zero.mpr (sub_ne_zero.mpr hxy)))
  have hsupport : 0 < (μ.prod μ)
      (Function.support (suzukiUnitSignCrossKernel u)) :=
    hrect.trans_le (measure_mono hrectSupport)
  have hcrossPos : 0 < ∫ z : ℝ × ℝ, suzukiUnitSignCrossKernel u z ∂μ.prod μ :=
    (integral_pos_iff_support_of_nonneg
      (suzukiUnitSignCrossKernel_nonneg u)
      (by
        simpa only [μ, S] using integrable_suzukiUnitSignCrossKernel_product u)).2
      hsupport
  have hswapNonneg : 0 ≤ ∫ z : ℝ × ℝ,
      suzukiUnitSignCrossKernel u (z.2, z.1) ∂μ.prod μ := by
    exact integral_nonneg_of_ae (Eventually.of_forall fun z =>
      suzukiUnitSignCrossKernel_nonneg u (z.2, z.1))
  unfold suzukiUnitSignInteraction
  change 0 < ∫ z : ℝ × ℝ,
    (suzukiUnitSignCrossKernel u z +
      suzukiUnitSignCrossKernel u (z.2, z.1)) ∂μ.prod μ
  rw [integral_add
    (by simpa only [μ, S] using integrable_suzukiUnitSignCrossKernel_product u)
    (by simpa only [μ, S] using integrable_suzukiUnitSignCrossKernel_swap_product u)]
  linarith

def suzukiRealAbsolute (u : ℝ → ℝ) : ℝ → ℝ := fun x => |u x|

@[simp] theorem suzukiRealAbsolute_nonneg (u : ℝ → ℝ) (x : ℝ) :
    0 ≤ suzukiRealAbsolute u x := abs_nonneg _

theorem suzukiRealAbsolute_eq_positivePart_add_negativePart
    (u : ℝ → ℝ) (x : ℝ) :
    suzukiRealAbsolute u x =
      suzukiRealPositivePart u x + suzukiRealNegativePart u x := by
  exact (posPart_add_negPart (u x)).symm

theorem continuous_suzukiRealAbsolute {u : ℝ → ℝ} (hu : Continuous u) :
    Continuous (suzukiRealAbsolute u) := hu.abs

theorem abs_suzukiRealAbsolute_sub_le (u : ℝ → ℝ) (x y : ℝ) :
    |suzukiRealAbsolute u x - suzukiRealAbsolute u y| ≤ |u x - u y| := by
  exact abs_abs_sub_abs_le_abs_sub _ _

theorem suzukiRealAbsolute_jump_sq_le (u : ℝ → ℝ) (x y : ℝ) :
    (suzukiRealAbsolute u x - suzukiRealAbsolute u y) ^ 2 ≤
      (u x - u y) ^ 2 := by
  exact sq_le_sq.mpr (abs_suzukiRealAbsolute_sub_le u x y)

theorem suzuki_absolute_jump_split (u : ℝ → ℝ) (x y : ℝ) :
    (u x - u y) ^ 2 =
      (suzukiRealAbsolute u x - suzukiRealAbsolute u y) ^ 2 +
      4 * (suzukiRealPositivePart u x * suzukiRealNegativePart u y +
        suzukiRealPositivePart u y * suzukiRealNegativePart u x) := by
  rw [← suzukiRealPositivePart_sub_negativePart u x,
    ← suzukiRealPositivePart_sub_negativePart u y,
    suzukiRealAbsolute_eq_positivePart_add_negativePart,
    suzukiRealAbsolute_eq_positivePart_add_negativePart]
  have hx := suzukiRealPositivePart_mul_negativePart u x
  have hy := suzukiRealPositivePart_mul_negativePart u y
  nlinarith

theorem integrable_suzukiUnitAbsoluteJumpKernel_product
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    Integrable (suzukiUnitJumpKernel (suzukiRealAbsolute u))
      ((volume.restrict (Ioc (-1 : ℝ) 1)).prod
        (volume.restrict (Ioc (-1 : ℝ) 1))) := by
  apply (integrable_suzukiUnitJumpKernel_product u).mono
  · apply Measurable.aestronglyMeasurable
    unfold suzukiUnitJumpKernel
    exact ((((continuous_suzukiRealAbsolute u.continuous).measurable.comp
      measurable_fst).sub
      ((continuous_suzukiRealAbsolute u.continuous).measurable.comp
        measurable_snd)).pow_const 2).mul
          (((measurable_fst.sub measurable_snd).abs).inv)
  · filter_upwards with z
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (suzukiUnitJumpKernel_nonneg (suzukiRealAbsolute u) z),
      abs_of_nonneg (suzukiUnitJumpKernel_nonneg u z)]
    exact mul_le_mul_of_nonneg_right
      (suzukiRealAbsolute_jump_sq_le u z.1 z.2)
      (inv_nonneg.mpr (abs_nonneg _))

theorem suzukiFinitePartDifferenceEnergy_absolute_split
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartDifferenceEnergy 1 u =
      suzukiFinitePartDifferenceEnergy 1 (suzukiRealAbsolute u) +
      4 * suzukiUnitSignInteraction u := by
  have hu := suzukiFinitePartDifferenceEnergy_eq_productIntegral_of_integrable u
    (integrable_suzukiUnitJumpKernel_product u)
  have ha := suzukiFinitePartDifferenceEnergy_eq_productIntegral_of_integrable
    (suzukiRealAbsolute u) (integrable_suzukiUnitAbsoluteJumpKernel_product u)
  rw [hu, ha]
  unfold suzukiUnitSignInteraction
  let μ := (volume.restrict (Ioc (-1 : ℝ) 1)).prod
    (volume.restrict (Ioc (-1 : ℝ) 1))
  have haInt := integrable_suzukiUnitAbsoluteJumpKernel_product u
  have hcInt := integrable_suzukiUnitSignCrossKernel_product u
  have hcsInt := integrable_suzukiUnitSignCrossKernel_swap_product u
  calc
    (∫ z : ℝ × ℝ, suzukiUnitJumpKernel u z ∂μ) =
        ∫ z : ℝ × ℝ,
          suzukiUnitJumpKernel (suzukiRealAbsolute u) z +
            4 * (suzukiUnitSignCrossKernel u z +
              suzukiUnitSignCrossKernel u (z.2, z.1)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with z
      unfold suzukiUnitJumpKernel suzukiUnitSignCrossKernel
      rw [suzuki_absolute_jump_split]
      rw [abs_sub_comm z.2 z.1]
      ring
    _ = (∫ z : ℝ × ℝ,
          suzukiUnitJumpKernel (suzukiRealAbsolute u) z ∂μ) +
        ∫ z : ℝ × ℝ, 4 * (suzukiUnitSignCrossKernel u z +
          suzukiUnitSignCrossKernel u (z.2, z.1)) ∂μ :=
      integral_add haInt ((hcInt.add hcsInt).const_mul 4)
    _ = (∫ z : ℝ × ℝ,
          suzukiUnitJumpKernel (suzukiRealAbsolute u) z ∂μ) +
        4 * ∫ z : ℝ × ℝ, (suzukiUnitSignCrossKernel u z +
          suzukiUnitSignCrossKernel u (z.2, z.1)) ∂μ := by
      rw [integral_const_mul]

theorem support_suzukiRealAbsolute_subset (u : ℝ → ℝ) :
    Function.support (suzukiRealAbsolute u) ⊆ Function.support u := by
  intro x hx hux
  apply hx
  simp [suzukiRealAbsolute, hux]

theorem suzukiFinitePartLogPotential_absolute
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartLogPotential 1 (suzukiRealAbsolute u) =
      suzukiFinitePartLogPotential 1 u := by
  unfold suzukiFinitePartLogPotential
  apply intervalIntegral.integral_congr
  intro x _
  simp only [suzukiRealAbsolute, sq_abs]

/-- Exact modulus identity on Suzuki's real source core.  Sign changes cost precisely the
strictly positive cross interaction of the `1/|x-y|` jump kernel. -/
theorem suzukiFinitePartEnergy_absolute_split
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartEnergy 1 u =
      suzukiFinitePartEnergy 1 (suzukiRealAbsolute u) +
      suzukiUnitSignInteraction u := by
  unfold suzukiFinitePartEnergy
  rw [suzukiFinitePartDifferenceEnergy_absolute_split,
    suzukiFinitePartLogPotential_absolute]
  ring

theorem suzukiUnitSignInteraction_nonneg
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    0 ≤ suzukiUnitSignInteraction u := by
  unfold suzukiUnitSignInteraction
  exact integral_nonneg_of_ae (Eventually.of_forall fun z =>
    add_nonneg (suzukiUnitSignCrossKernel_nonneg u z)
      (suzukiUnitSignCrossKernel_nonneg u (z.2, z.1)))

/-- Markov modulus contraction for the exact Suzuki finite-part energy. -/
theorem suzukiFinitePartEnergy_absolute_le
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1) :
    suzukiFinitePartEnergy 1 (suzukiRealAbsolute u) ≤
      suzukiFinitePartEnergy 1 u := by
  rw [suzukiFinitePartEnergy_absolute_split]
  exact le_add_of_nonneg_right (suzukiUnitSignInteraction_nonneg u)

/-- Strict core irreducibility: every continuous source-core vector taking both signs loses
strict finite-part energy under modulus. -/
theorem suzukiFinitePartEnergy_absolute_lt_of_sign_change
    (u : GaloisForLFunctions.RHTower.SuzukiRestrictedWeilCore 1)
    (hp : ∃ x ∈ Ioo (-1 : ℝ) 1, 0 < suzukiRealPositivePart u x)
    (hn : ∃ y ∈ Ioo (-1 : ℝ) 1, 0 < suzukiRealNegativePart u y) :
    suzukiFinitePartEnergy 1 (suzukiRealAbsolute u) <
      suzukiFinitePartEnergy 1 u := by
  rw [suzukiFinitePartEnergy_absolute_split]
  exact lt_add_of_pos_right _ (suzukiUnitSignInteraction_pos u hp hn)



end RHTower


