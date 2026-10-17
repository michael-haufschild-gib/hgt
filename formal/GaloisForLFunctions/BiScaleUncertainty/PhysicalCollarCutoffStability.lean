import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarCutoffMonotonicity

/-!
# Quantitative stability of the optimized collar coefficient

Future nodes cannot reach the physical interval below `log N - log 2 / 2`.
Retain that part of any larger partition and fill its complement with an old-grid
partition. The lost coefficient is at most the physical tail mass, uniformly over
all competitors and without assuming an optimizing partition exists.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section

/-- Physical interval protected from every future node's collar. -/
def logarithmicCollarRetention (n : ℕ) : ℝ :=
  logarithmicCollarEndpoint n - logarithmicCollarRadius

theorem logarithmicCollarRadius_le_retention (n : ℕ) :
    logarithmicCollarRadius ≤ logarithmicCollarRetention n := by
  have h := logarithmicCollarNode_ge_log_two n
  change Real.log 2 ≤ logarithmicCollarEndpoint n at h
  unfold logarithmicCollarRetention logarithmicCollarRadius
  linarith

theorem logarithmicCollarRetention_lt_endpoint (n : ℕ) :
    logarithmicCollarRetention n < logarithmicCollarEndpoint n :=
  sub_lt_self _ logarithmicCollarRadius_pos

/-- Indicator of the physical region in which larger-cutoff partitions may differ. -/
def collarRetentionPrice (n : ℕ) : ℝ → ℝ :=
  (Ici (logarithmicCollarRetention n)).indicator (fun _ => 1)

theorem measurable_collarRetentionPrice (n : ℕ) : Measurable (collarRetentionPrice n) :=
  measurable_const.indicator measurableSet_Ici

theorem collarRetentionPrice_bounds (n : ℕ) (x : ℝ) :
    0 ≤ collarRetentionPrice n x ∧ collarRetentionPrice n x ≤ 1 := by
  by_cases hx : logarithmicCollarRetention n ≤ x <;>
    simp [collarRetentionPrice, mem_Ici, hx]

/-- Uniformly finite weight of the part not protected from future collars. -/
def collarCutoffTailMass (n : ℕ) : ℝ :=
  ∫ x in Ioi (logarithmicCollarRetention n), archLevySinhWeight x

theorem integrableOn_archWeight_retention_tail (n : ℕ) :
    IntegrableOn archLevySinhWeight (Ioi (logarithmicCollarRetention n)) :=
  integrableOn_archWeight_collar_tail.mono_set (fun _ hx =>
    (logarithmicCollarRadius_le_retention n).trans_lt hx)

theorem collarCutoffTailMass_nonneg (n : ℕ) : 0 ≤ collarCutoffTailMass n :=
  setIntegral_nonneg measurableSet_Ioi fun _ hx =>
    (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans
      ((logarithmicCollarRadius_le_retention n).trans_lt hx))).le

namespace PhysicalCollarPartition
variable {n m : ℕ}

theorem extra_share_zero_below_retention (η : PhysicalCollarPartition m) {k : ℕ}
    (hk : n + 1 ≤ k) {x : ℝ} (hx : x < logarithmicCollarRetention n) : η.share k x = 0 := by
  apply η.supported k x
  intro hc
  have ht : logarithmicCollarEndpoint n ≤ logarithmicCollarNode k :=
    logarithmicCollarEndpoint_monotone (by omega)
  have hl := hc.1.1
  unfold logarithmicCollarRetention at hx
  linarith

/-- Copy every protected old-node share and fill the remaining old physical interval. -/
def retract (η : PhysicalCollarPartition m) (hm : n ≤ m) : PhysicalCollarPartition n where
  share k x := if x < logarithmicCollarRetention n then
      if k < n + 1 then η.share k x else 0
    else (equalMultiplicity n).share k x
  measurable_share := by
    intro k
    apply Measurable.ite measurableSet_Iio
    · by_cases hk : k < n + 1
      · simpa only [if_pos hk] using η.measurable_share k
      · simpa only [if_neg hk] using (measurable_const : Measurable (fun _ : ℝ => (0 : ℝ)))
    · exact (equalMultiplicity n).measurable_share k
  nonneg := by
    intro k x
    split_ifs <;> first | exact η.nonneg k x | exact le_rfl |
      exact (equalMultiplicity n).nonneg k x
  supported := by
    intro k x hx
    by_cases hxr : x < logarithmicCollarRetention n
    · simp only [if_pos hxr]
      split_ifs with hk
      · apply η.supported k x
        intro hc
        exact hx ⟨hc.1, hc.2.1, hxr.trans (logarithmicCollarRetention_lt_endpoint n)⟩
      · rfl
    · simp only [if_neg hxr]
      exact (equalMultiplicity n).supported k x hx
  partition := by
    intro x
    by_cases hxr : x < logarithmicCollarRetention n
    · simp only [if_pos hxr]
      have hsum : (∑ k ∈ Finset.range (n + 1), η.share k x) =
          ∑ k ∈ Finset.range (m + 1), η.share k x := by
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_range] at hk ⊢
          omega
        · intro k _ hk
          apply η.extra_share_zero_below_retention (n := n) (x := x) ?_ hxr
          simp only [Finset.mem_range] at hk
          omega
      rw [Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk)), hsum, η.partition]
      have hxn := hxr.trans (logarithmicCollarRetention_lt_endpoint n)
      have hxm := hxn.trans_le (logarithmicCollarEndpoint_monotone hm)
      simp only [indicator_apply, mem_Ioo, hxn, hxm, and_true]
    · simp only [if_neg hxr]
      exact (equalMultiplicity n).partition x

/-- Below the retention threshold the padded smaller array is exactly the original array. -/
theorem pad_retract_weight_eq (η : PhysicalCollarPartition m) (hm : n ≤ m)
    (σ : Bool) (k : ℕ) (y : ℝ)
    (hx : logarithmicCollarNode k + collarSignedOffset σ y < logarithmicCollarRetention n) :
    collarArrayPad n (fun σ k => (η.retract hm).weight σ k y) σ k = η.weight σ k y := by
  by_cases hk : k < n + 1
  · simp only [collarArrayPad, weight, density, retract, if_pos hx, if_pos hk]
  · have hz := η.extra_share_zero_below_retention (n := n) (k := k) (by omega) hx
    simp only [collarArrayPad, if_neg hk, weight, density, hz, zero_mul]

/-- Pulled-back mass of the potentially lost physical tail. -/
def retentionFibre (η : PhysicalCollarPartition m) (n : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (η.weight false k y * collarRetentionPrice n (logarithmicCollarNode k - y) +
     η.weight true k y * collarRetentionPrice n (logarithmicCollarNode k + y))

theorem kernel_sub_retract_le_retentionFibre (η : PhysicalCollarPartition m) (hm : n ≤ m)
    {y : ℝ} (hy : 0 < y) : η.kernel y - (η.retract hm).kernel y ≤ η.retentionFibre n y := by
  let a := collarArrayPad n (fun σ k => (η.retract hm).weight σ k y)
  let e := fun σ k => η.weight σ k y *
    collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset σ y)
  have ha (σ : Bool) (k : ℕ) : 0 ≤ a σ k := by
    dsimp [a, collarArrayPad]
    split_ifs
    · exact (η.retract hm).weight_nonneg σ k y
    · exact le_rfl
  have he (σ : Bool) (k : ℕ) : 0 ≤ e σ k :=
    mul_nonneg (η.weight_nonneg σ k y) (collarRetentionPrice_bounds n _).1
  have hab (σ : Bool) (k : ℕ) : η.weight σ k y ≤ a σ k + e σ k := by
    by_cases hx : logarithmicCollarNode k + collarSignedOffset σ y < logarithmicCollarRetention n
    · have heq : a σ k = η.weight σ k y := η.pad_retract_weight_eq hm σ k y hx
      rw [heq]
      exact le_add_of_nonneg_right (he σ k)
    · have hp : collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset σ y) = 1 := by
        exact indicator_of_mem (show logarithmicCollarNode k + collarSignedOffset σ y ∈
          Ici (logarithmicCollarRetention n) from le_of_not_gt hx) (fun _ => (1 : ℝ))
      dsimp only [e]
      rw [hp, mul_one]
      exact le_add_of_nonneg_left (ha σ k)
  have h := logarithmicArrayKernel_error_bound m a (fun σ k => η.weight σ k y) e
    (archLevySinhWeight_pos hy) ha he hab
  dsimp only [a] at h
  rw [logarithmicArrayKernel_pad hm] at h
  rw [η.kernel_eq_allocationKernel, (η.retract hm).kernel_eq_allocationKernel]
  simpa only [logarithmicArrayKernel, e, retentionFibre, collarSignedOffset,
    Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] using h

theorem integrableOn_retention_weight (η : PhysicalCollarPartition m) (n : ℕ)
    (σ : Bool) (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :
    IntegrableOn (fun y => η.weight σ k y *
      collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset σ y))
      (Ioo 0 logarithmicCollarRadius) := by
  have hx : Measurable (fun y => logarithmicCollarNode k + collarSignedOffset σ y) := by
    cases σ <;> simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound m)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    ((η.measurable_weight σ k).mul ((measurable_collarRetentionPrice n).comp hx)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖η.weight σ k y *
      collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset σ y)‖ ≤
        logarithmicCollarWeightBound m
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (η.weight_nonneg σ k y)
      (collarRetentionPrice_bounds n _).1)]
    exact (mul_le_of_le_one_right (η.weight_nonneg σ k y)
      (collarRetentionPrice_bounds n _).2).trans (η.weight_le_bound σ k hk y)

theorem integrableOn_retentionFibre (η : PhysicalCollarPartition m) (n : ℕ) :
    IntegrableOn (η.retentionFibre n) (Ioo 0 logarithmicCollarRadius) := by
  apply integrable_finsetSum
  intro k hk
  have h1 := η.integrableOn_retention_weight n false k hk
  have h2 := η.integrableOn_retention_weight n true k hk
  have hh : IntegrableOn (fun y =>
      η.weight false k y * collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset false y) +
      η.weight true k y * collarRetentionPrice n (logarithmicCollarNode k + collarSignedOffset true y))
      (Ioo 0 logarithmicCollarRadius) := h1.add h2
  simpa only [IntegrableOn, collarSignedOffset, Bool.false_eq_true, ↓reduceIte,
    ← sub_eq_add_neg] using hh

theorem integral_retentionFibre (η : PhysicalCollarPartition m) (n : ℕ) :
    (∫ y in Ioo 0 logarithmicCollarRadius, η.retentionFibre n y) =
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint m),
        archLevySinhWeight x * collarRetentionPrice n x := by
  have htrans := η.integral_signed_cost_transport (fun _ => collarRetentionPrice n)
    (fun _ => measurable_collarRetentionPrice n) (fun _ _ x => collarRetentionPrice_bounds n x)
  have h1 (k : ℕ) (hk : k ∈ Finset.range (m + 1)) := η.integrableOn_retention_weight n false k hk
  have h2 (k : ℕ) (hk : k ∈ Finset.range (m + 1)) := η.integrableOn_retention_weight n true k hk
  simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte, ← sub_eq_add_neg] at h1 h2
  unfold retentionFibre
  rw [integral_finsetSum (Finset.range (m + 1))
    (f := fun k y => η.weight false k y * collarRetentionPrice n (logarithmicCollarNode k - y) +
      η.weight true k y * collarRetentionPrice n (logarithmicCollarNode k + y))
    (fun k hk => (h1 k hk).add (h2 k hk))]
  have hsum := Finset.sum_congr rfl (fun k hk => integral_add (h1 k hk) (h2 k hk))
  rw [hsum, htrans]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  simp only [density, ← Finset.sum_mul, η.partition, indicator_of_mem hx, one_mul]

/-- The transported error cannot exceed the entire remaining weight tail. -/
theorem integral_retentionFibre_le_tail (η : PhysicalCollarPartition m) (n : ℕ) :
    (∫ y in Ioo 0 logarithmicCollarRadius, η.retentionFibre n y) ≤ collarCutoffTailMass n := by
  rw [η.integral_retentionFibre]
  have heq : (fun x => archLevySinhWeight x * collarRetentionPrice n x) =
      (Ici (logarithmicCollarRetention n)).indicator archLevySinhWeight := by
    funext x
    by_cases hx : x ∈ Ici (logarithmicCollarRetention n) <;>
      simp [collarRetentionPrice, hx]
  rw [heq, setIntegral_indicator measurableSet_Ici]
  apply setIntegral_mono_set (integrableOn_archWeight_retention_tail n)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans
      ((logarithmicCollarRadius_le_retention n).trans_lt hx))).le
  · filter_upwards [volume.ae_ne (logarithmicCollarRetention n)] with x hx
    intro hs
    exact lt_of_le_of_ne hs.2 (Ne.symm hx)

/-- A concrete smaller-grid repair loses at most the unprotected physical tail. -/
theorem coefficient_sub_retract_le_tail (η : PhysicalCollarPartition m) (hm : n ≤ m) :
    η.coefficient - (η.retract hm).coefficient ≤ collarCutoffTailMass n := by
  have h := integral_mono_ae (η.integrableOn_kernel.sub (η.retract hm).integrableOn_kernel)
    (η.integrableOn_retentionFibre n) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      exact η.kernel_sub_retract_le_retentionFibre hm hy.1)
  change (∫ y in Ioo 0 logarithmicCollarRadius, η.kernel y - (η.retract hm).kernel y) ≤
    ∫ y in Ioo 0 logarithmicCollarRadius, η.retentionFibre n y at h
  rw [integral_sub η.integrableOn_kernel (η.retract hm).integrableOn_kernel] at h
  exact h.trans (η.integral_retentionFibre_le_tail n)

/-- Uniform cutoff comparison for the full continuous allocation supremum. -/
theorem optimalCoefficient_sub_le_tail {n m : ℕ} (hm : n ≤ m) :
    optimalCoefficient m - optimalCoefficient n ≤ collarCutoffTailMass n := by
  have h : optimalCoefficient m ≤ optimalCoefficient n + collarCutoffTailMass n := by
    apply csSup_le
    · exact ⟨(equalMultiplicity m).coefficient, equalMultiplicity m, rfl⟩
    · rintro c ⟨η, rfl⟩
      have hc := η.coefficient_sub_retract_le_tail hm
      have hp : (η.retract hm).coefficient ≤ optimalCoefficient n :=
        le_csSup (coefficient_range_bddAbove n) ⟨η.retract hm, rfl⟩
      linarith
  linarith

end PhysicalCollarPartition

/-- The positive finite limiting optimum has a certified cutoff error. -/
theorem limitingCollarCoefficient_sub_bounds (n : ℕ) :
    0 ≤ limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n ∧
    limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n ≤
      collarCutoffTailMass n := by
  have hl : PhysicalCollarPartition.optimalCoefficient n ≤ limitingCollarCoefficient := by
    rw [← monotoneCollarCoefficient_eq_optimalCoefficient]
    exact le_ciSup monotoneCollarCoefficient_bddAbove n
  have hu : limitingCollarCoefficient ≤
      PhysicalCollarPartition.optimalCoefficient n + collarCutoffTailMass n := by
    apply ciSup_le
    intro m
    rw [monotoneCollarCoefficient_eq_optimalCoefficient]
    rcases le_total n m with hnm | hmn
    · have h := PhysicalCollarPartition.optimalCoefficient_sub_le_tail hnm
      linarith
    · exact (PhysicalCollarPartition.optimalCoefficient_monotone hmn).trans
        (le_add_of_nonneg_right (collarCutoffTailMass_nonneg n))
  constructor <;> linarith

/-- The archimedean weight has an explicit exponential majorant above every positive cutoff. -/
theorem archWeight_le_cutoff_exponential {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) :
    archLevySinhWeight x ≤ (2 / (1 - Real.exp (-2 * a))) * Real.exp (-(1 / 2) * x) := by
  have hx : 0 < x := ha.trans_le hax
  have hd : 0 < 1 - Real.exp (-2 * a) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hden : 1 - Real.exp (-2 * a) ≤ 1 - Real.exp (-2 * x) :=
    sub_le_sub_left (Real.exp_le_exp.mpr (by linarith)) 1
  rw [archLevySinhWeight, RHTower.ArchimedeanAnomaly.exp_half_div_sinh_eq hx,
    RHTower.archLevyDensity]
  calc
    _ ≤ 2 * (Real.exp (-x / 2) / (1 - Real.exp (-2 * a))) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (Real.exp_pos _).le hd hden) (by norm_num)
    _ = _ := by rw [show -x / 2 = -(1 / 2 : ℝ) * x by ring]; ring

/-- Explicit finite error for the allocation hierarchy, before logarithmic simplification. -/
theorem collarCutoffTailMass_le_exponential (n : ℕ) :
    collarCutoffTailMass n ≤
      4 * Real.exp (-logarithmicCollarRetention n / 2) /
        (1 - Real.exp (-2 * logarithmicCollarRetention n)) := by
  have ha : 0 < logarithmicCollarRetention n :=
    logarithmicCollarRadius_pos.trans_le (logarithmicCollarRadius_le_retention n)
  have he := (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num)
    (logarithmicCollarRetention n)).const_mul
      (2 / (1 - Real.exp (-2 * logarithmicCollarRetention n)))
  have h := setIntegral_mono_ae_restrict (integrableOn_archWeight_retention_tail n) he (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact archWeight_le_cutoff_exponential ha hx.le)
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)] at h
  change collarCutoffTailMass n ≤ _ at h
  calc
    _ ≤ (2 / (1 - Real.exp (-2 * logarithmicCollarRetention n))) *
        (-Real.exp (-(1 / 2) * logarithmicCollarRetention n) / (-(1 / 2))) := h
    _ = _ := by
      rw [show -(1 / 2 : ℝ) * logarithmicCollarRetention n =
        -logarithmicCollarRetention n / 2 by ring]
      ring

private theorem exp_retention_half (n : ℕ) :
    Real.exp (-logarithmicCollarRetention n / 2) =
      Real.exp (logarithmicCollarRadius / 2) / Real.sqrt ((n + 2 : ℕ) : ℝ) := by
  have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have hs : Real.exp (logarithmicCollarEndpoint n / 2) = Real.sqrt ((n + 2 : ℕ) : ℝ) := by
    have hsq : Real.exp (logarithmicCollarEndpoint n / 2) ^ 2 = ((n + 2 : ℕ) : ℝ) := by
      rw [pow_two, ← Real.exp_add]
      have he : logarithmicCollarEndpoint n / 2 + logarithmicCollarEndpoint n / 2 =
          logarithmicCollarEndpoint n := by ring
      rw [he]
      exact Real.exp_log hN
    rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]
  have he : -logarithmicCollarRetention n / 2 =
      logarithmicCollarRadius / 2 - logarithmicCollarEndpoint n / 2 := by
    unfold logarithmicCollarRetention
    ring
  rw [he, Real.exp_sub, hs]

private theorem exp_retention_two (n : ℕ) :
    Real.exp (-2 * logarithmicCollarRetention n) = 2 / (((n + 2 : ℕ) : ℝ) ^ 2) := by
  have hN : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
  have he : -2 * logarithmicCollarRetention n = Real.log 2 -
      (logarithmicCollarEndpoint n + logarithmicCollarEndpoint n) := by
    unfold logarithmicCollarRetention logarithmicCollarRadius
    ring
  rw [he, Real.exp_sub, Real.exp_add, Real.exp_log (by norm_num),
    show Real.exp (logarithmicCollarEndpoint n) = ((n + 2 : ℕ) : ℝ) from Real.exp_log hN,
    pow_two]

/-- The lost physical tail is bounded at the inverse-square-root scale of the grid cutoff. -/
theorem collarCutoffTailMass_le_inverse_sqrt (n : ℕ) :
    collarCutoffTailMass n ≤
      4 * Real.exp (logarithmicCollarRadius / 2) /
        (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) := by
  have h := collarCutoffTailMass_le_exponential n
  rw [exp_retention_half, exp_retention_two] at h
  simpa only [← mul_div_assoc, div_div] using h

/-- A uniform, explicit cutoff error for the positive monotone allocation optimum. -/
theorem optimalCoefficient_quantitative_saturation (n : ℕ) :
    0 ≤ limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n ∧
    limitingCollarCoefficient - PhysicalCollarPartition.optimalCoefficient n ≤
      4 * Real.exp (logarithmicCollarRadius / 2) /
        (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) :=
  ⟨(limitingCollarCoefficient_sub_bounds n).1,
    (limitingCollarCoefficient_sub_bounds n).2.trans (collarCutoffTailMass_le_inverse_sqrt n)⟩

/-- Every finite trial partition certifies the limiting optimum, with separate
finite-allocation and cutoff errors and no optimizer-existence premise. -/
theorem limitingCollarCoefficient_trial_certificate {n : ℕ} (ρ : PhysicalCollarPartition n) :
    0 ≤ limitingCollarCoefficient - ρ.coefficient ∧
    limitingCollarCoefficient - ρ.coefficient ≤ ρ.gap +
      4 * Real.exp (logarithmicCollarRadius / 2) /
        (Real.sqrt ((n + 2 : ℕ) : ℝ) * (1 - 2 / (((n + 2 : ℕ) : ℝ) ^ 2))) := by
  have htail := optimalCoefficient_quantitative_saturation n
  have hgap := ρ.optimalCoefficient_gap_bounds
  constructor <;> linarith

end
end GaloisForLFunctions.BiScaleUncertainty
