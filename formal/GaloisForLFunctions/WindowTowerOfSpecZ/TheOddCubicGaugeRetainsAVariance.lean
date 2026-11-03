import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddLogarithmicPairGap

/-!
# A cubic moment remainder for odd logarithmic jumps

The reflected logarithmic kernel dominates `15/4` times the product of the
positive cubic gauge. Retaining the ground-state square therefore controls
the full odd sector apart from one explicit cubic moment.
-/

noncomputable section
open Real MeasureTheory Set
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory ArithmeticIncidencePositivity

private theorem cubic_weight_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 3 * (1 - 4 * x ^ 2 / 5) ≤ 4 / 15 := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx, hx1]
  have hp : 0 ≤ 16 * (x ^ 2) ^ 2 * (1 - x ^ 2) + 8 * x ^ 2 + 3 := by positivity
  have hs := mul_nonneg (sq_nonneg (3 - 4 * x ^ 2)) hp
  have he : (3 - 4 * x ^ 2) ^ 2 *
      (16 * (x ^ 2) ^ 2 * (1 - x ^ 2) + 8 * x ^ 2 + 3) =
      27 - 400 * (x ^ 3 * (1 - 4 * x ^ 2 / 5)) ^ 2 := by ring
  rw [he] at hs
  nlinarith only [hs, sq_nonneg (x ^ 3 * (1 - 4 * x ^ 2 / 5) - 4 / 15)]

private theorem cubic_kernel_minorant_ordered {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) (hyx : y < x) :
    (15 / 4 : ℝ) * oddCubicGauge x * oddCubicGauge y ≤ principalOddKernel x y := by
  have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
  have hy2 : y ^ 2 ≤ 1 := by nlinarith only [hy.1, hy.2]
  have ha : 0 ≤ x * (1 - 4 * x ^ 2 / 5) :=
    mul_nonneg hx.1.le (by linarith only [hx2])
  have hd : 0 < x ^ 2 - y ^ 2 := by nlinarith only [hx.1, hy.1, hyx]
  have hd' : (1 - 4 * y ^ 2 / 5) * (x ^ 2 - y ^ 2) ≤ x ^ 2 := by
    calc
      (1 - 4 * y ^ 2 / 5) * (x ^ 2 - y ^ 2) ≤ 1 * x ^ 2 :=
        mul_le_mul (by nlinarith only [sq_nonneg y]) (by nlinarith only [sq_nonneg y])
          hd.le zero_le_one
      _ = x ^ 2 := one_mul _
  have hbound : x * (1 - 4 * x ^ 2 / 5) *
      ((1 - 4 * y ^ 2 / 5) * (x ^ 2 - y ^ 2)) ≤ 4 / 15 := by
    calc
      _ ≤ x * (1 - 4 * x ^ 2 / 5) * x ^ 2 := mul_le_mul_of_nonneg_left hd' ha
      _ = x ^ 3 * (1 - 4 * x ^ 2 / 5) := by ring
      _ ≤ 4 / 15 := cubic_weight_bound hx.1.le hx.2.le
  have hk : principalOddKernel x y = y / (x ^ 2 - y ^ 2) := by
    unfold principalOddKernel
    rw [abs_of_pos (sub_pos.mpr hyx)]
    field_simp [(sub_pos.mpr hyx).ne', (add_pos hx.1 hy.1).ne', hd.ne']
    ring
  rw [hk, le_div_iff₀ hd]
  have hm := mul_le_mul_of_nonneg_left hbound hy.1.le
  unfold oddCubicGauge
  nlinarith only [hm]

/-- The reflected logarithmic kernel dominates a rank-one cubic kernel. -/
theorem principalOddKernel_cubic_minorant {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) (hne : x ≠ y) :
    (15 / 4 : ℝ) * oddCubicGauge x * oddCubicGauge y ≤ principalOddKernel x y := by
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have h := cubic_kernel_minorant_ordered hy hx hxy
    have hk : principalOddKernel y x = principalOddKernel x y := by
      unfold principalOddKernel
      rw [abs_sub_comm, add_comm]
    rw [hk] at h
    nlinarith only [h]
  · exact cubic_kernel_minorant_ordered hx hy hyx

/-- Keeping the ground-state square retains a cubic moment variance. -/
theorem principalOddKernel_cubic_remainder (F : ℝ → ℝ) {x y : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    F x ^ 2 / oddCubicGauge x *
        (principalOddKernel x y * (oddCubicGauge x - oddCubicGauge y)) +
      F y ^ 2 / oddCubicGauge y *
        (principalOddKernel y x * (oddCubicGauge y - oddCubicGauge x)) +
      (15 / 4 : ℝ) * (F x * oddCubicGauge y - F y * oddCubicGauge x) ^ 2 ≤
      principalOddKernel x y * (F x - F y) ^ 2 := by
  by_cases he : x = y
  · simp [he]
  have ha : 0 < oddCubicGauge x := by
    linarith only [oddCubicGauge_lower hx.1.le hx.2.le, hx.1]
  have hb : 0 < oddCubicGauge y := by
    linarith only [oddCubicGauge_lower hy.1.le hy.2.le, hy.1]
  have hk : principalOddKernel y x = principalOddKernel x y := by
    unfold principalOddKernel
    rw [abs_sub_comm, add_comm]
  rw [hk]
  have hm : (15 / 4 : ℝ) ≤ principalOddKernel x y / (oddCubicGauge x * oddCubicGauge y) := by
    rw [le_div_iff₀ (mul_pos ha hb)]
    simpa only [mul_assoc] using principalOddKernel_cubic_minorant hx hy he
  have hs := mul_le_mul_of_nonneg_right hm
    (sq_nonneg (F x * oddCubicGauge y - F y * oddCubicGauge x))
  have hid : principalOddKernel x y * (F x - F y) ^ 2 -
      (F x ^ 2 / oddCubicGauge x * (principalOddKernel x y * (oddCubicGauge x - oddCubicGauge y)) +
      F y ^ 2 / oddCubicGauge y * (principalOddKernel x y * (oddCubicGauge y - oddCubicGauge x))) =
      principalOddKernel x y / (oddCubicGauge x * oddCubicGauge y) *
        (F x * oddCubicGauge y - F y * oddCubicGauge x) ^ 2 := by
    field_simp [ha.ne', hb.ne']
    ring
  linarith only [hid, hs]

private theorem cubic_transform_bound {F : ℝ → ℝ} {K x y : ℝ}
    (hF0 : F 0 = 0)
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|)
    (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    |F x ^ 2 / oddCubicGauge x *
      (principalOddKernel x y * (oddCubicGauge x - oddCubicGauge y))| ≤ 17 / 2 * K ^ 2 := by
  have hg := oddCubicGauge_lower hx.1.le hx.2.le
  have hg0 : 0 < oddCubicGauge x := by linarith only [hg, hx.1]
  have hf := hFL x ⟨hx.1.le, hx.2.le⟩ 0 ⟨le_rfl, zero_le_one⟩
  rw [hF0, sub_zero, sub_zero, abs_of_pos hx.1] at hf
  have hf2 : F x ^ 2 ≤ K ^ 2 * x ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (F x)) hf 2
    simpa only [sq_abs, mul_pow] using h
  have hs : x ^ 2 ≤ x := by nlinarith only [hx.1, hx.2]
  have hq : F x ^ 2 / oddCubicGauge x ≤ 5 * K ^ 2 := by
    rw [div_le_iff₀ hg0]
    nlinarith only [hf2, mul_le_mul_of_nonneg_left hs (sq_nonneg K),
      mul_le_mul_of_nonneg_left hg (show 0 ≤ 5 * K ^ 2 by positivity)]
  have hkernel : |principalOddKernel x y * (oddCubicGauge x - oddCubicGauge y)| ≤ 17 / 10 := by
    by_cases he : x = y
    · simp [he]
      norm_num
    have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr he)
    have hk0 : 0 ≤ principalOddKernel x y :=
      (show 0 ≤ (15 / 4 : ℝ) * oddCubicGauge x * oddCubicGauge y by
        have := oddCubicGauge_lower hy.1.le hy.2.le
        have : 0 ≤ oddCubicGauge y := by linarith only [this, hy.1]
        positivity).trans (principalOddKernel_cubic_minorant hx hy he)
    have hk1 : principalOddKernel x y ≤ 1 / (2 * |x - y|) := by
      unfold principalOddKernel
      have hxy0 : 0 < x + y := add_pos hx.1 hy.1
      have : 0 ≤ 1 / (2 * (x + y)) := by positivity
      linarith only [this]
    have hx2 : x ^ 2 ≤ 1 := by nlinarith only [hx.1, hx.2]
    have hy2 : y ^ 2 ≤ 1 := by nlinarith only [hy.1, hy.2]
    have hxy : x * y ≤ 1 :=
      (mul_le_mul hx.2.le hy.2.le hy.1.le (by norm_num)).trans (by norm_num)
    have hp : |1 - 4 / 5 * (x ^ 2 + x * y + y ^ 2)| ≤ 17 / 5 := by
      rw [abs_le]
      constructor <;> nlinarith only [hx2, hy2, hxy, sq_nonneg x, sq_nonneg y,
        mul_nonneg hx.1.le hy.1.le]
    have heq : oddCubicGauge x - oddCubicGauge y =
        (x - y) * (1 - 4 / 5 * (x ^ 2 + x * y + y ^ 2)) := by
      unfold oddCubicGauge
      ring
    rw [abs_mul, abs_of_nonneg hk0, heq, abs_mul]
    calc
      _ ≤ (1 / (2 * |x - y|)) * (|x - y| * (17 / 5)) :=
        mul_le_mul hk1 (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
          (by positivity) (by positivity)
      _ = 17 / 10 := by field_simp; ring
  rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) hg0.le)]
  calc
    _ ≤ (5 * K ^ 2) * (17 / 10) :=
      mul_le_mul hq hkernel (abs_nonneg _) (by positivity)
    _ = 17 / 2 * K ^ 2 := by ring

private theorem integrable_unit_square {G : ℝ × ℝ → ℝ} {C : ℝ} (hG : Measurable G)
    (hb : ∀ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, |G (x, y)| ≤ C) :
    Integrable G ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hG.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
  rw [Real.norm_eq_abs]
  exact hb p.1 hp.1 p.2 hp.2


private theorem cubic_gauge_square_integral :
    (∫ x in Ioo (0 : ℝ) 1, oddCubicGauge x ^ 2) = 11 / 105 := by
  unfold oddCubicGauge
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have he : (fun x : ℝ => (x * (1 - 4 * x ^ 2 / 5)) ^ 2) =
      (fun x => x ^ 2 - (8 / 5) * x ^ 4 + (16 / 25) * x ^ 6) := by funext x; ring
  rw [he, intervalIntegral.integral_add
    ((by fun_prop : Continuous (fun x : ℝ => x ^ 2 - (8 / 5) * x ^ 4)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => (16 / 25) * x ^ 6)).intervalIntegrable _ _),
    intervalIntegral.integral_sub
    ((by fun_prop : Continuous (fun x : ℝ => x ^ 2)).intervalIntegrable _ _)
    ((by fun_prop : Continuous (fun x : ℝ => (8 / 5) * x ^ 4)).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  norm_num [integral_pow]

private theorem cubic_variance_integral {F : ℝ → ℝ} (hF : Continuous F) :
    (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
      (F x * oddCubicGauge y - F y * oddCubicGauge x) ^ 2) =
      (22 / 105 : ℝ) * (∫ x in Ioo (0 : ℝ) 1, F x ^ 2) -
      2 * (∫ x in Ioo (0 : ℝ) 1, F x * oddCubicGauge x) ^ 2 := by
  have hh : Continuous oddCubicGauge := by unfold oddCubicGauge; fun_prop
  have hIF : IntegrableOn (fun x => F x ^ 2) (Ioo (0 : ℝ) 1) :=
    (hF.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hIh : IntegrableOn (fun x => oddCubicGauge x ^ 2) (Ioo (0 : ℝ) 1) :=
    (hh.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hIFh : IntegrableOn (fun x => F x * oddCubicGauge x) (Ioo (0 : ℝ) 1) :=
    (hF.mul hh).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hrow : ∀ x : ℝ,
      (∫ y in Ioo (0 : ℝ) 1, (F x * oddCubicGauge y - F y * oddCubicGauge x) ^ 2) =
      F x ^ 2 * (∫ y in Ioo (0 : ℝ) 1, oddCubicGauge y ^ 2) +
      oddCubicGauge x ^ 2 * (∫ y in Ioo (0 : ℝ) 1, F y ^ 2) -
      (2 * (F x * oddCubicGauge x)) * (∫ y in Ioo (0 : ℝ) 1, F y * oddCubicGauge y) := by
    intro x
    have he : (fun y => (F x * oddCubicGauge y - F y * oddCubicGauge x) ^ 2) =
        (fun y => F x ^ 2 * oddCubicGauge y ^ 2 + oddCubicGauge x ^ 2 * F y ^ 2 -
          (2 * (F x * oddCubicGauge x)) * (F y * oddCubicGauge y)) := by funext y; ring
    rw [he, integral_sub
      (f := fun y => F x ^ 2 * oddCubicGauge y ^ 2 + oddCubicGauge x ^ 2 * F y ^ 2)
      (g := fun y => (2 * (F x * oddCubicGauge x)) * (F y * oddCubicGauge y))
      ((hIh.const_mul _).add (hIF.const_mul _)) (hIFh.const_mul _),
      integral_add (f := fun y => F x ^ 2 * oddCubicGauge y ^ 2)
        (g := fun y => oddCubicGauge x ^ 2 * F y ^ 2) (hIh.const_mul _) (hIF.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [setIntegral_congr_fun measurableSet_Ioo (fun x _ => hrow x),
    integral_sub
      (f := fun x => F x ^ 2 * (∫ y in Ioo (0 : ℝ) 1, oddCubicGauge y ^ 2) +
        oddCubicGauge x ^ 2 * (∫ y in Ioo (0 : ℝ) 1, F y ^ 2))
      (g := fun x => (2 * (F x * oddCubicGauge x)) *
        (∫ y in Ioo (0 : ℝ) 1, F y * oddCubicGauge y))
      ((hIF.mul_const _).add (hIh.mul_const _))
      ((hIFh.const_mul 2).mul_const _),
    integral_add
      (f := fun x => F x ^ 2 * (∫ y in Ioo (0 : ℝ) 1, oddCubicGauge y ^ 2))
      (g := fun x => oddCubicGauge x ^ 2 * (∫ y in Ioo (0 : ℝ) 1, F y ^ 2))
      (hIF.mul_const _) (hIh.mul_const _),
    integral_mul_const, integral_mul_const, integral_mul_const, integral_const_mul,
    cubic_gauge_square_integral]
  ring

/-- The cubic ground-state estimate retains the full rank-one variance. -/
theorem principalOddKernel_cubic_energy_ge {F : ℝ → ℝ}
    (hFc : Continuous F) (hF0 : F 0 = 0) {K : ℝ}
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|) :
    2 * (∫ x in Ioo (0 : ℝ) 1,
      F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x) +
      (11 / 14 : ℝ) * (∫ x in Ioo (0 : ℝ) 1, F x ^ 2) -
      (15 / 2 : ℝ) * (∫ x in Ioo (0 : ℝ) 1, F x * oddCubicGauge x) ^ 2 ≤
      ∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
        principalOddKernel x y * (F x - F y) ^ 2 := by
  let G : ℝ × ℝ → ℝ := fun p => F p.1 ^ 2 / oddCubicGauge p.1 *
    (principalOddKernel p.1 p.2 * (oddCubicGauge p.1 - oddCubicGauge p.2))
  let E : ℝ × ℝ → ℝ := fun p => principalOddKernel p.1 p.2 * (F p.1 - F p.2) ^ 2
  let V : ℝ × ℝ → ℝ := fun p =>
    (F p.1 * oddCubicGauge p.2 - F p.2 * oddCubicGauge p.1) ^ 2
  have hmG : Measurable G := by unfold G principalOddKernel oddCubicGauge; fun_prop
  have hIG := integrable_unit_square hmG (fun x hx y hy => cubic_transform_bound hF0 hFL hx hy)
  have hIGs : Integrable (fun p : ℝ × ℝ => G (p.2, p.1))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    integrable_unit_square (hmG.comp (measurable_snd.prodMk measurable_fst))
      (fun x hx y hy => cubic_transform_bound hF0 hFL hy hx)
  have hIE : Integrable E
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) :=
    principalOddKernel_energy_integrable hFc hFL
  have hIV : Integrable V
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    rw [Measure.prod_restrict]
    have hcV : Continuous V := by unfold V oddCubicGauge; fun_prop
    exact (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      hcV.continuousOn).mono_set (Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have hcmp : (∫ p, G p + G (p.2, p.1) + (15 / 4 : ℝ) * V p
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) ≤
      ∫ p, E p ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
    apply integral_mono_ae ((hIG.add hIGs).add (hIV.const_mul _)) hIE
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp
    exact principalOddKernel_cubic_remainder F hp.1 hp.2
  have hinner : ∀ x ∈ Ioo (0 : ℝ) 1, (∫ y in Ioo (0 : ℝ) 1, G (x, y)) =
      F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x := by
    intro x hx
    dsimp [G]
    rw [integral_const_mul, principalOddKernel_gauge_integral hx.1 hx.2.le]
  rw [integral_add (f := fun p => G p + G (p.2, p.1))
      (g := fun p => (15 / 4 : ℝ) * V p) (hIG.add hIGs) (hIV.const_mul _),
    integral_add hIG hIGs,
    integral_const_mul,
    ← integral_integral (f := fun x y => G (x, y)) hIG,
    ← integral_integral (f := fun x y => G (y, x)) hIGs,
    ← integral_integral (f := fun x y => E (x, y)) hIE,
    ← integral_integral (f := fun x y => V (x, y)) hIV] at hcmp
  have hs : (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, G (y, x)) =
      ∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, G (x, y) :=
    integral_integral_swap (f := fun x y => G (y, x)) hIGs
  change (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, G (x, y)) +
    (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1, G (y, x)) +
    (15 / 4 : ℝ) * (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
      (F x * oddCubicGauge y - F y * oddCubicGauge x) ^ 2) ≤ _ at hcmp
  rw [hs, setIntegral_congr_fun measurableSet_Ioo hinner, cubic_variance_integral hFc] at hcmp
  dsimp [E] at hcmp
  linarith only [hcmp]

/-- The odd logarithmic gap improves by `11/28`, at the cost of one cubic moment. -/
theorem folded_logarithmic_jump_cubic_gap {F : ℝ → ℝ} (hFc : Continuous F)
    (hF0 : F 0 = 0) (hF1 : F 1 = 0) {K : ℝ}
    (hFL : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |F u - F v| ≤ K * |u - v|) :
    (Real.log 2 + 7 / 5 + 11 / 28) * (2 * ∫ x in Ioo (0 : ℝ) 1, F x ^ 2) ≤
      (∫ x in Ioo (0 : ℝ) 1, ∫ y in Ioo (0 : ℝ) 1,
        principalOddKernel x y * (F x - F y) ^ 2) +
      2 * (∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * oddLogKilling x) +
      (15 / 2 : ℝ) * (∫ x in Ioo (0 : ℝ) 1, F x * oddCubicGauge x) ^ 2 := by
  have hIP := (principalOddKernel_energy_ge hFc hF0 hFL).1
  have hgap := principalOddKernel_cubic_energy_ge hFc hF0 hFL
  have hIK := oddLogKilling_integrable hFc hF0 hF1 hFL
  have hIF : IntegrableOn (fun x => F x ^ 2) (Ioo (0 : ℝ) 1) :=
    (hFc.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hp : (Real.log 2 + 7 / 5) * (∫ x in Ioo (0 : ℝ) 1, F x ^ 2) ≤
      (∫ x in Ioo (0 : ℝ) 1, F x ^ 2 * oddLogKilling x) +
        ∫ x in Ioo (0 : ℝ) 1,
          F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x := by
    rw [← integral_const_mul, ← integral_add hIK hIP]
    apply setIntegral_mono_on (hIF.const_mul _) (hIK.add hIP) measurableSet_Ioo
    intro x hx
    have h := mul_le_mul_of_nonneg_left (oddCubicGauge_potential_lower hx.1 hx.2)
      (sq_nonneg (F x))
    unfold oddLogKilling
    change (Real.log 2 + 7 / 5) * F x ^ 2 ≤
      F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2 + Real.log (x + 1) - Real.log x) +
        F x ^ 2 / oddCubicGauge x * cubicSurplusMain 1 0 (-4 / 5) 1 x
    calc
      _ = F x ^ 2 * (Real.log 2 + 7 / 5) := by ring
      _ ≤ F x ^ 2 * (Real.log 2 - Real.log (1 - x ^ 2) / 2 +
          (Real.log (x + 1) - Real.log x) +
          cubicSurplusMain 1 0 (-4 / 5) 1 x / oddCubicGauge x) := h
      _ = _ := by ring
  nlinarith only [hp, hgap]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.folded_logarithmic_jump_cubic_gap
