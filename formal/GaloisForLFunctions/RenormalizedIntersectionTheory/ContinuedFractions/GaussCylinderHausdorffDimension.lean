import GaloisForLFunctions.RenormalizedIntersectionTheory.ContinuedFractions.SubcriticalGaussTraceSummability
import GaloisForLFunctions.RenormalizedIntersectionTheory.ContinuedFractions.GaussTraceSummabilityBoundary
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# A uniform dimension gap for bounded-digit Gauss cylinders

The exact inverse-branch endpoint intervals cover their limit set at every
word length. Their diameters shrink geometrically, and the weighted cylinder
estimate makes their `(1-β/(n+1))`-dimensional covering cost tend to zero.
Thus every finite digit alphabet has a quantitative Hausdorff dimension gap.
-/

open Filter Topology
open scoped ENNReal NNReal MeasureTheory
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundedDigits
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDigitPerturbation
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerSubcriticalTraces
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerTraceBoundary

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCylinderDimension
noncomputable section

/-- The closed interval between the two endpoints of an actual inverse branch. -/
def cylinder (k : ℕ) (a : Word k) : Set ℝ :=
  Set.uIcc (realWordMap k a 0) (realWordMap k a 1)

/-- Points lying in a bounded-digit cylinder at every depth. -/
def limitSet (n : ℕ) : Set ℝ :=
  ⋂ k : ℕ, ⋃ a : Fin k → Fin n, cylinder k (word a)

theorem limitSet_cylinder_cover (n k : ℕ) :
    limitSet n ⊆ ⋃ a : Fin k → Fin n, cylinder k (word a) :=
  Set.iInter_subset (fun l : ℕ => ⋃ a : Fin l → Fin n, cylinder l (word a)) k

/-- The dimension exponent supplied by the absolute logarithmic perturbation constant. -/
def dimensionExponent (n : ℕ) : ℝ := 1 - eta n

theorem dimensionExponent_bounds (n : ℕ) :
    0 < dimensionExponent n ∧ dimensionExponent n < 1 := by
  have h0 := eta_pos n
  have h1 := eta_le_quarter n
  unfold dimensionExponent
  constructor <;> linarith only [h0, h1]

private theorem digit_mem_interval (i : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ((((i + 1 : ℕ) : ℝ) + x)⁻¹) ∈ Set.Icc (0 : ℝ) 1 := by
  have hi : (1 : ℝ) ≤ (i + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le i)
  have hd : 0 < ((i + 1 : ℕ) : ℝ) + x := by linarith only [hi, hx.1]
  refine ⟨(inv_pos.mpr hd).le, (inv_le_one₀ hd).mpr ?_⟩
  linarith only [hi, hx.1]

private theorem digit_antitone (i : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hxy : x ≤ y) :
    ((((i + 1 : ℕ) : ℝ) + y)⁻¹) ≤ ((((i + 1 : ℕ) : ℝ) + x)⁻¹) := by
  have hi : (0 : ℝ) < (i + 1 : ℕ) := by exact_mod_cast Nat.succ_pos i
  simpa only [one_div] using one_div_le_one_div_of_le
    (add_pos_of_pos_of_nonneg hi hx.1)
    (show ((i + 1 : ℕ) : ℝ) + x ≤ ((i + 1 : ℕ) : ℝ) + y by linarith only [hxy])

/-- Every actual Gauss word is monotone or antitone on the closed unit interval. -/
theorem realWordMap_monotone_or_antitone (k : ℕ) (a : Word k) :
    MonotoneOn (realWordMap k a) (Set.Icc (0 : ℝ) 1) ∨
      AntitoneOn (realWordMap k a) (Set.Icc (0 : ℝ) 1) := by
  induction k with
  | zero => exact Or.inl (fun _ _ _ _ h => h)
  | succ k ih =>
      rcases ih (Fin.tail a) with hm | hm
      · exact Or.inr (fun x hx y hy hxy =>
          hm (digit_mem_interval (a 0) hy) (digit_mem_interval (a 0) hx)
            (digit_antitone (a 0) hx hxy))
      · exact Or.inl (fun x hx y hy hxy =>
          hm (digit_mem_interval (a 0) hy) (digit_mem_interval (a 0) hx)
            (digit_antitone (a 0) hx hxy))

/-- The image of the unit interval lies between the two actual branch endpoints. -/
theorem realWordMap_mem_cylinder (k : ℕ) (a : Word k) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : realWordMap k a x ∈ cylinder k a := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  rcases realWordMap_monotone_or_antitone k a with hm | hm
  · rw [cylinder, Set.uIcc_of_le (hm h0 h1 zero_le_one)]
    exact ⟨hm h0 hx hx.1, hm hx h1 hx.2⟩
  · rw [cylinder, Set.uIcc_of_ge (hm h0 h1 zero_le_one)]
    exact ⟨hm hx h1 hx.2, hm h0 hx hx.1⟩

/-- Actual real inverse branches are continuous throughout the closed unit interval. -/
theorem continuousOn_realWordMap (k : ℕ) (a : Word k) :
    ContinuousOn (realWordMap k a) (Set.Icc (0 : ℝ) 1) := by
  induction k with
  | zero => exact continuous_id.continuousOn
  | succ k ih =>
      have hg : ContinuousOn (fun x : ℝ => (((a 0 + 1 : ℕ) : ℝ) + x)⁻¹)
          (Set.Icc (0 : ℝ) 1) := by
        apply (continuous_const.continuousOn.add continuous_id.continuousOn).inv₀
        intro x hx
        have hi : (0 : ℝ) < (a 0 + 1 : ℕ) := by exact_mod_cast Nat.succ_pos (a 0)
        exact (add_pos_of_pos_of_nonneg hi hx.1).ne'
      exact (ih (Fin.tail a)).comp hg (fun x hx => digit_mem_interval (a 0) hx)

/-- The cylinder is exactly the image of the unit interval under its actual inverse branch. -/
theorem realWordMap_image_interval (k : ℕ) (a : Word k) :
    realWordMap k a '' Set.Icc (0 : ℝ) 1 = cylinder k a := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact realWordMap_mem_cylinder k a hx
  · have h := intermediate_value_uIcc
      (a := (0 : ℝ)) (b := 1) (f := realWordMap k a)
      (by simpa only [Set.uIcc_of_le zero_le_one] using continuousOn_realWordMap k a)
    simpa only [cylinder, Set.uIcc_of_le zero_le_one] using h

/-- Every nonempty digit alphabet contains the periodic point of the digit-one branch. -/
theorem limitSet_nonempty (n : ℕ) : (limitSet (n + 1)).Nonempty := by
  let a : Word 1 := fun _ => 0
  let x : ℝ := (fixedPoint 0 a).re
  have hx : x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨(fixedPoint_real_interval 0 a).1.le, (fixedPoint_real_interval 0 a).2.le⟩
  have hf : (1 + x)⁻¹ = x := by
    have h := (fixedPoint_spec 0 a).2.1
    rw [fixedPoint_eq_real 0 a, wordMap_ofReal] at h
    have hr : realWordMap 1 a x = x := by exact_mod_cast h
    simpa only [realWordMap, a, Nat.zero_add, Nat.cast_one] using hr
  have hiterate (k : ℕ) : realWordMap k (fun _ => 0) x = x := by
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [realWordMap]
        have htail : Fin.tail (fun _ : Fin (k + 1) => (0 : ℕ)) =
            (fun _ : Fin k => 0) := by funext j; rfl
        rw [htail]
        simpa only [Nat.zero_add, Nat.cast_one, hf] using ih
  refine ⟨x, ?_⟩
  simp only [limitSet, Set.mem_iInter, Set.mem_iUnion]
  intro k
  refine ⟨fun _ => 0, ?_⟩
  have h := realWordMap_mem_cylinder k (word (fun _ : Fin k => (0 : Fin (n + 1)))) hx
  change realWordMap k (fun _ => 0) x ∈ cylinder k (word (fun _ : Fin k => (0 : Fin (n + 1)))) at h
  rwa [hiterate] at h

private theorem ediam_uIcc_le (a b : ℝ) :
    Metric.ediam (Set.uIcc a b) ≤ ENNReal.ofReal |b - a| := by
  apply Metric.ediam_le
  intro x hx y hy
  rw [edist_dist]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq]
  rcases le_total a b with hab | hba
  · rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx hy
    rw [abs_of_nonneg (sub_nonneg.mpr hab), abs_le]
    constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]
  · rw [Set.uIcc_of_ge hba, Set.mem_Icc] at hx hy
    rw [abs_of_nonpos (sub_nonpos.mpr hba), abs_le]
    constructor <;> linarith only [hx.1, hx.2, hy.1, hy.2]

/-- The exact cylinder probability bounds its ambient extended diameter. -/
theorem ediam_cylinder_le (k : ℕ) (a : Word k) :
    Metric.ediam (cylinder k a) ≤ ENNReal.ofReal (probability k a) := by
  simpa only [cylinder, MayerCylinderEndpoints.endpoint_distance_eq_probability] using
    ediam_uIcc_le (realWordMap k a 0) (realWordMap k a 1)

private theorem probability_le_inverse_square (k : ℕ) (a : Word k) :
    probability k a ≤ (wordMatrix k a 1 1 : ℝ)⁻¹ ^ 2 := by
  have hd : (0 : ℝ) < wordMatrix k a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row k a).2
  have hc : (0 : ℝ) ≤ wordMatrix k a 1 0 := Nat.cast_nonneg _
  calc
    _ ≤ 1 / ((wordMatrix k a 1 1 : ℝ) * wordMatrix k a 1 1) :=
      one_div_le_one_div_of_le (mul_pos hd hd)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hc) hd.le)
    _ = _ := by simp only [one_div, mul_inv_rev, pow_two]

/-- Every pair of digits shrinks the maximum cylinder width by at least a factor of four. -/
theorem probability_even_le (k : ℕ) (a : Word (2 * k + 2)) :
    probability (2 * k + 2) a ≤ (1 / 4 : ℝ) ^ (k + 1) := by
  have hg : (2 : ℝ) ^ (k + 1) ≤ wordMatrix (2 * k + 2) a 1 1 := by
    exact_mod_cast even_denominator_growth (k + 1) a
  have hi : (wordMatrix (2 * k + 2) a 1 1 : ℝ)⁻¹ ≤ ((2 : ℝ) ^ (k + 1))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos (by norm_num) _) hg
  calc
    _ ≤ (wordMatrix (2 * k + 2) a 1 1 : ℝ)⁻¹ ^ 2 := probability_le_inverse_square _ a
    _ ≤ (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hi 2
    _ = (1 / 4 : ℝ) ^ (k + 1) := by
      rw [← inv_pow, ← pow_mul, Nat.mul_comm (k + 1) 2, pow_mul, inv_pow]
      norm_num

/-- Power-sums of cylinder widths inherit the subcritical multiplier estimate. -/
theorem probability_power_mass_le (n k : ℕ) :
    (∑ a : Fin (k + 1) → Fin n, probability (k + 1) (word a) ^ dimensionExponent n) ≤
      (2 : ℝ) ^ dimensionExponent n * (2 * cutoffRate n ^ (k + 1)) := by
  have hs := (dimensionExponent_bounds n).1.le
  have hpoint (a : Fin (k + 1) → Fin n) :
      probability (k + 1) (word a) ^ dimensionExponent n ≤
        (2 : ℝ) ^ dimensionExponent n * wordMultiplier k (word a) ^ (-exponent n) := by
    have hl : 0 < wordMultiplier k (word a) :=
      zero_lt_one.trans (one_lt_wordMultiplier k (word a))
    have hb : probability (k + 1) (word a) ≤
        2 * wordMultiplier k (word a) ^ (-(2 : ℝ)) := by
      have h := half_probability_le_multiplier k (word a)
      linarith only [h]
    have he : -(2 : ℝ) * dimensionExponent n = -exponent n := by
      unfold dimensionExponent exponent
      ring
    calc
      _ ≤ (2 * wordMultiplier k (word a) ^ (-(2 : ℝ))) ^ dimensionExponent n :=
        Real.rpow_le_rpow
          (show 0 ≤ probability (k + 1) (word a) by unfold probability; positivity) hb hs
      _ = (2 : ℝ) ^ dimensionExponent n *
          (wordMultiplier k (word a) ^ (-(2 : ℝ))) ^ dimensionExponent n :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hl.le _)
      _ = (2 : ℝ) ^ dimensionExponent n *
          wordMultiplier k (word a) ^ (-(2 : ℝ) * dimensionExponent n) :=
        congrArg (fun y : ℝ => (2 : ℝ) ^ dimensionExponent n * y)
          (Real.rpow_mul hl.le (-(2 : ℝ)) (dimensionExponent n)).symm
      _ = _ := congrArg
        (fun y : ℝ => (2 : ℝ) ^ dimensionExponent n * wordMultiplier k (word a) ^ y) he
  calc
    _ ≤ ∑ a : Fin (k + 1) → Fin n,
        (2 : ℝ) ^ dimensionExponent n * wordMultiplier k (word a) ^ (-exponent n) :=
      Finset.sum_le_sum (fun a _ => hpoint a)
    _ = (2 : ℝ) ^ dimensionExponent n *
        ∑ a : Fin (k + 1) → Fin n, wordMultiplier k (word a) ^ (-exponent n) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (multiplier_mass_le n k) (Real.rpow_nonneg (by norm_num) _)

/-- The bounded-digit limit set has zero Hausdorff measure at the explicit subunit exponent. -/
theorem hausdorffMeasure_limitSet_eq_zero (n : ℕ) :
    MeasureTheory.Measure.hausdorffMeasure (dimensionExponent n) (limitSet n) = 0 := by
  let r : ℕ → ℝ≥0∞ := fun k => (ENNReal.ofReal (1 / 4 : ℝ)) ^ (k + 1)
  let t : ∀ k : ℕ, (Fin (2 * k + 2) → Fin n) → Set ℝ :=
    fun k a => cylinder (2 * k + 2) (word a)
  have hr : Tendsto r atTop (𝓝 0) :=
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : ENNReal.ofReal (1 / 4 : ℝ) < 1)).comp
      (tendsto_add_atTop_nat 1)
  have ht : ∀ᶠ k in atTop, ∀ a, Metric.ediam (t k a) ≤ r k := by
    exact Eventually.of_forall fun k a => by
      apply (ediam_cylinder_le _ (word a)).trans
      have h := ENNReal.ofReal_le_ofReal (probability_even_le k (word a))
      simpa only [r, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4)] using h
  have hcover : ∀ᶠ k in atTop, limitSet n ⊆ ⋃ a, t k a :=
    Eventually.of_forall fun k => limitSet_cylinder_cover n (2 * k + 2)
  have hcostBound (k : ℕ) :
      (∑ a : Fin (2 * k + 2) → Fin n, Metric.ediam (t k a) ^ dimensionExponent n) ≤
        ENNReal.ofReal ((2 : ℝ) ^ dimensionExponent n * (2 * cutoffRate n ^ (2 * k + 2))) := by
    calc
      _ ≤ ∑ a : Fin (2 * k + 2) → Fin n,
          ENNReal.ofReal (probability (2 * k + 2) (word a) ^ dimensionExponent n) := by
        apply Finset.sum_le_sum
        intro a _
        have h := ENNReal.rpow_le_rpow (ediam_cylinder_le _ (word a)) (dimensionExponent_bounds n).1.le
        simpa only [ENNReal.ofReal_rpow_of_nonneg
          (show 0 ≤ probability (2 * k + 2) (word a) by unfold probability; positivity)
          (dimensionExponent_bounds n).1.le] using h
      _ = ENNReal.ofReal (∑ a : Fin (2 * k + 2) → Fin n,
          probability (2 * k + 2) (word a) ^ dimensionExponent n) := by
        rw [ENNReal.ofReal_sum_of_nonneg
          (fun (a : Fin (2 * k + 2) → Fin n) _ => Real.rpow_nonneg
            (show 0 ≤ probability (2 * k + 2) (word a) by unfold probability; positivity)
            (dimensionExponent n))]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (probability_power_mass_le n (2 * k + 1))
  have hq := cutoffRate_bounds n
  have hq2 : cutoffRate n ^ 2 < 1 := by
    have h := mul_pos (sub_pos.mpr hq.2) (add_pos zero_lt_one hq.1)
    nlinarith only [h]
  have hp : Tendsto (fun k : ℕ => cutoffRate n ^ (2 * k + 2)) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (cutoffRate n)) hq2).comp
      (tendsto_add_atTop_nat 1)
    exact h.congr' (Eventually.of_forall fun k => calc
      (cutoffRate n ^ 2) ^ (k + 1) = cutoffRate n ^ (2 * (k + 1)) :=
        (pow_mul (cutoffRate n) 2 (k + 1)).symm
      _ = cutoffRate n ^ (2 * k + 2) :=
        congrArg (fun m : ℕ => cutoffRate n ^ m) (by omega))
  have hmass : Tendsto (fun k : ℕ =>
      ENNReal.ofReal ((2 : ℝ) ^ dimensionExponent n * (2 * cutoffRate n ^ (2 * k + 2))))
      atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal
      ((hp.const_mul 2).const_mul ((2 : ℝ) ^ dimensionExponent n))
    simpa only [mul_zero, ENNReal.ofReal_zero] using h
  have hcost : Tendsto (fun k : ℕ =>
      ∑ a : Fin (2 * k + 2) → Fin n, Metric.ediam (t k a) ^ dimensionExponent n)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmass (fun _ => bot_le) hcostBound
  have hle := MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum
    (dimensionExponent n) (limitSet n) r hr t ht hcover
  rw [hcost.liminf_eq] at hle
  exact bot_unique hle

/-- The dimension gap is at least the same `β/(n+1)` supplied by weighted cylinder contraction. -/
theorem dimH_limitSet_le (n : ℕ) :
    dimH (limitSet n) ≤ ENNReal.ofReal (1 - eta n) := by
  have hzero : MeasureTheory.Measure.hausdorffMeasure (dimensionExponent n) (limitSet n) ≠ ∞ := by
    rw [hausdorffMeasure_limitSet_eq_zero n]
    exact ENNReal.zero_ne_top
  apply dimH_le_of_hausdorffMeasure_ne_top (s := limitSet n)
    (d := Real.toNNReal (dimensionExponent n))
  simpa only [Real.coe_toNNReal _ (dimensionExponent_bounds n).1.le] using hzero

#print axioms probability_even_le
#print axioms realWordMap_mem_cylinder
#print axioms realWordMap_image_interval
#print axioms limitSet_nonempty
#print axioms probability_power_mass_le
#print axioms hausdorffMeasure_limitSet_eq_zero
#print axioms dimH_limitSet_le

end
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCylinderDimension
