import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarDualPrices

/-!
# Exact continuous dual certificate for physical collar allocation

For every pair of admissible partitions, the incumbent coefficient plus its dual gap minus
the competing coefficient equals the competitor's nonnegative physical price slack plus a
nonnegative integrable fibre remainder. No analytic or transport bridge is assumed.

Consequences include a finite positive optimal supremum, a rigorous bound on every possible
improvement, complementary allocation, and aggregate-norm rigidity under a sharp certificate.
For the first grid N=2 the certificate vanishes and the physical optimum is identified exactly.
Existence of an optimizing partition for general N is not asserted.
-/

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace GaloisForLFunctions.BiScaleUncertainty
noncomputable section
namespace PhysicalCollarPartition
variable {n : ℕ}

theorem integrableOn_mass (ρ : PhysicalCollarPartition n) :
    IntegrableOn ρ.mass (Ioo 0 logarithmicCollarRadius) :=
  integrable_finsetSum (Finset.range (n + 1)) (fun k hk =>
    (ρ.integrableOn_weight false k hk).add (ρ.integrableOn_weight true k hk))

def floorCost (ρ : PhysicalCollarPartition n) (x : ℝ) : ℝ := archLevySinhWeight x * ρ.priceFloor x

theorem archWeight_le_physical_bound {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    archLevySinhWeight x ≤ logarithmicCollarWeightBound n := by
  apply div_le_div₀ (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    linarith [hx.2]
  · exact Real.sinh_pos_iff.mpr logarithmicCollarRadius_pos
  · exact Real.sinh_le_sinh.mpr hx.1.le

theorem integrableOn_physical_archWeight (n : ℕ) :
    IntegrableOn archLevySinhWeight (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) := by
  apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound n)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    measurable_archLevySinhWeight.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg
    (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx.1)).le]
  exact archWeight_le_physical_bound hx

theorem integrableOn_floorCost (ρ : PhysicalCollarPartition n) :
    IntegrableOn ρ.floorCost (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) := by
  apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound n)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    (measurable_archLevySinhWeight.mul ρ.measurable_priceFloor).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hw0 := (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx.1)).le
  change ‖archLevySinhWeight x * ρ.priceFloor x‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (ρ.priceFloor_nonneg x))]
  exact (mul_le_of_le_one_right hw0 (ρ.priceFloor_le_one x)).trans (archWeight_le_physical_bound hx)

theorem physicalSlack_eq_sum (ρ η : PhysicalCollarPartition n) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    ρ.physicalCost η x - ρ.floorCost x = ∑ k ∈ Finset.range (n + 1),
      η.density k x * (ρ.physicalPrice k x - ρ.priceFloor x) := by
  have hm : (∑ k ∈ Finset.range (n + 1), η.density k x) = archLevySinhWeight x := by
    simp only [density, ← Finset.sum_mul, η.partition, indicator_of_mem hx, one_mul]
  simp only [physicalCost, floorCost, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hm]

theorem physicalSlack_nonneg (ρ η : PhysicalCollarPartition n) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    0 ≤ ρ.physicalCost η x - ρ.floorCost x := by
  rw [ρ.physicalSlack_eq_sum η hx]
  apply Finset.sum_nonneg
  intro k hk
  by_cases hxk : x ∈ logarithmicPhysicalCollar n k
  · exact mul_nonneg (η.density_nonneg k x) (sub_nonneg.mpr (ρ.priceFloor_le_active k hk hxk))
  · simp [density, η.supported k x hxk]

theorem physicalSlack_term_nonneg (ρ η : PhysicalCollarPartition n) (k : ℕ)
    (hk : k ∈ Finset.range (n + 1)) (x : ℝ) :
    0 ≤ η.density k x * (ρ.physicalPrice k x - ρ.priceFloor x) := by
  by_cases hxk : x ∈ logarithmicPhysicalCollar n k
  · exact mul_nonneg (η.density_nonneg k x) (sub_nonneg.mpr (ρ.priceFloor_le_active k hk hxk))
  · simp [density, η.supported k x hxk]

def slack (ρ η : PhysicalCollarPartition n) : ℝ :=
  ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n),
    (ρ.physicalCost η x - ρ.floorCost x)

def gap (ρ : PhysicalCollarPartition n) : ℝ := ρ.slack ρ

theorem slack_nonneg (ρ η : PhysicalCollarPartition n) : 0 ≤ ρ.slack η := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact ρ.physicalSlack_nonneg η hx

theorem gap_nonneg (ρ : PhysicalCollarPartition n) : 0 ≤ ρ.gap := ρ.slack_nonneg ρ

/-- A zero canonical certificate is exactly the complementary physical-allocation law. -/
theorem gap_eq_zero_iff_complementary (ρ : PhysicalCollarPartition n) :
    ρ.gap = 0 ↔ ∀ᵐ x ∂volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)),
      ∀ k ∈ Finset.range (n + 1), 0 < ρ.share k x → ρ.physicalPrice k x = ρ.priceFloor x := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n))]
      (fun x => ρ.physicalCost ρ x - ρ.floorCost x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact ρ.physicalSlack_nonneg ρ hx
  have hi := (ρ.integrable_physicalCost ρ).integrableOn.sub ρ.integrableOn_floorCost
  rw [gap, slack, integral_eq_zero_iff_of_nonneg_ae hn hi]
  constructor
  · intro hz
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioo] with x hxzero hx
    intro k hk hshare
    have hsum : (∑ j ∈ Finset.range (n + 1),
        ρ.density j x * (ρ.physicalPrice j x - ρ.priceFloor x)) = 0 :=
      (ρ.physicalSlack_eq_sum ρ hx).symm.trans hxzero
    have hle := Finset.single_le_sum
      (f := fun j => ρ.density j x * (ρ.physicalPrice j x - ρ.priceFloor x))
      (fun j hj => ρ.physicalSlack_term_nonneg ρ j hj x) hk
    rw [hsum] at hle
    have hp : 0 < ρ.density k x :=
      mul_pos hshare (archLevySinhWeight_pos (logarithmicCollarRadius_pos.trans hx.1))
    have hprod := le_antisymm hle (ρ.physicalSlack_term_nonneg ρ k hk x)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hp.ne')
  · intro hcomp
    filter_upwards [hcomp, ae_restrict_mem measurableSet_Ioo] with x hc hx
    change ρ.physicalCost ρ x - ρ.floorCost x = 0
    rw [ρ.physicalSlack_eq_sum ρ hx]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hz : ρ.share k x = 0
    · simp [density, hz]
    · have hp : 0 < ρ.share k x := lt_of_le_of_ne (ρ.nonneg k x) (Ne.symm hz)
      simp [hc k hk hp]

def remainder (ρ η : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  collarDualRemainder (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => ρ.weight j.2 k y) (fun j k => η.weight j.2 k y) (archLevySinhWeight y)

theorem remainder_nonneg (ρ η : PhysicalCollarPartition n) {y : ℝ} (hy : 0 < y) :
    0 ≤ ρ.remainder η y :=
  collarDualRemainder_nonneg (logarithmicSignedCosets n) (logarithmicSignedCosets_nonempty n)
    (fun j => logarithmicCosetNodes n j.1) (fun j k => ρ.weight j.2 k y)
    (fun j k => η.weight j.2 k y) (archLevySinhWeight_pos hy)

/-- The comparison remainder consists entirely of bounded combined quantities. -/
theorem remainder_eq_combined (ρ η : PhysicalCollarPartition n) (y : ℝ) :
    ρ.remainder η y = (ρ.kernel y - η.kernel y) + (η.mass y - ρ.mass y) -
      (ρ.fibreCost η y - ρ.fibreCost ρ y) := by
  change Real.sqrt (archLevySinhWeight y ^ 2 + η.blockNorm y ^ 2) -
    Real.sqrt (archLevySinhWeight y ^ 2 + ρ.blockNorm y ^ 2) -
    (∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1,
      (η.weight j.2 k y - ρ.weight j.2 k y) * ρ.dualSlope j k y) = _
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  rw [← ρ.fibreCost_eq_signed_sum η y, ← ρ.fibreCost_eq_signed_sum ρ y]
  unfold kernel
  ring

theorem integrableOn_remainder (ρ η : PhysicalCollarPartition n) :
    IntegrableOn (ρ.remainder η) (Ioo 0 logarithmicCollarRadius) := by
  have heq : ρ.remainder η = fun y => (ρ.kernel y - η.kernel y) + (η.mass y - ρ.mass y) -
      (ρ.fibreCost η y - ρ.fibreCost ρ y) := funext (ρ.remainder_eq_combined η)
  rw [heq]
  exact ((ρ.integrableOn_kernel.sub η.integrableOn_kernel).add
    (η.integrableOn_mass.sub ρ.integrableOn_mass)).sub
      ((ρ.integrableOn_fibreCost η).sub (ρ.integrableOn_fibreCost ρ))

theorem integral_remainder_nonneg (ρ η : PhysicalCollarPartition n) :
    0 ≤ ∫ y in Ioo 0 logarithmicCollarRadius, ρ.remainder η y := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact ρ.remainder_nonneg η hy.1

theorem integral_remainder (ρ η : PhysicalCollarPartition n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, ρ.remainder η y) =
      ρ.coefficient - η.coefficient -
        ((∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), ρ.physicalCost η x) -
         (∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), ρ.physicalCost ρ x)) := by
  simp_rw [ρ.remainder_eq_combined η]
  rw [integral_sub
      (f := fun y => (ρ.kernel y - η.kernel y) + (η.mass y - ρ.mass y))
      (g := fun y => ρ.fibreCost η y - ρ.fibreCost ρ y)
      ((ρ.integrableOn_kernel.sub η.integrableOn_kernel).add
        (η.integrableOn_mass.sub ρ.integrableOn_mass))
      ((ρ.integrableOn_fibreCost η).sub (ρ.integrableOn_fibreCost ρ)),
    integral_add (f := fun y => ρ.kernel y - η.kernel y) (g := fun y => η.mass y - ρ.mass y)
      (ρ.integrableOn_kernel.sub η.integrableOn_kernel)
      (η.integrableOn_mass.sub ρ.integrableOn_mass),
    integral_sub ρ.integrableOn_kernel η.integrableOn_kernel,
    integral_sub η.integrableOn_mass ρ.integrableOn_mass,
    integral_sub (ρ.integrableOn_fibreCost η) (ρ.integrableOn_fibreCost ρ),
    η.integral_mass, ρ.integral_mass, sub_self, add_zero,
    ρ.integral_fibreCost η, ρ.integral_fibreCost ρ]
  rfl

/-- Exact continuous dual gap for arbitrary admissible physical partitions. All analytic
and transport obligations are proved from admissibility, including the singular origin. -/
theorem exact_dual_gap (ρ η : PhysicalCollarPartition n) :
    ρ.coefficient + ρ.gap - η.coefficient = ρ.slack η +
      ∫ y in Ioo 0 logarithmicCollarRadius, ρ.remainder η y := by
  have hE := ρ.integral_remainder η
  unfold gap slack
  rw [integral_sub (ρ.integrable_physicalCost ρ).integrableOn ρ.integrableOn_floorCost,
    integral_sub (ρ.integrable_physicalCost η).integrableOn ρ.integrableOn_floorCost]
  linarith only [hE]

theorem coefficient_le_dual_bound (ρ η : PhysicalCollarPartition n) :
    η.coefficient ≤ ρ.coefficient + ρ.gap := by
  have h := ρ.exact_dual_gap η
  linarith [ρ.slack_nonneg η, ρ.integral_remainder_nonneg η]

theorem optimal_of_gap_zero (ρ : PhysicalCollarPartition n) (hρ : ρ.gap = 0)
    (η : PhysicalCollarPartition n) : η.coefficient ≤ ρ.coefficient := by
  simpa [hρ] using ρ.coefficient_le_dual_bound η

theorem coefficient_le_physical_mass (ρ : PhysicalCollarPartition n) :
    ρ.coefficient ≤ ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n),
      archLevySinhWeight x := by
  rw [← ρ.integral_mass]
  apply integral_mono_ae ρ.integrableOn_kernel ρ.integrableOn_mass
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact (ρ.kernel_bounds hy.1.le).2

/-- The finite physical optimum is a supremum; no existence of an optimizing partition is assumed. -/
def optimalCoefficient (n : ℕ) : ℝ :=
  sSup (Set.range (fun ρ : PhysicalCollarPartition n => ρ.coefficient))

theorem coefficient_range_bddAbove (n : ℕ) :
    BddAbove (Set.range (fun ρ : PhysicalCollarPartition n => ρ.coefficient)) := by
  refine ⟨∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x, ?_⟩
  rintro c ⟨ρ, rfl⟩
  exact ρ.coefficient_le_physical_mass

theorem equalMultiplicity_coefficient (n : ℕ) :
    (equalMultiplicity n).coefficient = logarithmicCollarRealConstant n := rfl

theorem optimalCoefficient_pos (n : ℕ) : 0 < optimalCoefficient n := by
  have h : (equalMultiplicity n).coefficient ≤ optimalCoefficient n :=
    le_csSup (coefficient_range_bddAbove n) ⟨equalMultiplicity n, rfl⟩
  rw [equalMultiplicity_coefficient] at h
  exact (logarithmicCollarRealConstant_pos n).trans_le h

/-- The computed nonnegative dual gap controls the full continuous optimization error. -/
theorem optimalCoefficient_gap_bounds (ρ : PhysicalCollarPartition n) :
    0 ≤ optimalCoefficient n - ρ.coefficient ∧ optimalCoefficient n - ρ.coefficient ≤ ρ.gap := by
  have hlo : ρ.coefficient ≤ optimalCoefficient n :=
    le_csSup (coefficient_range_bddAbove n) ⟨ρ, rfl⟩
  have hu : optimalCoefficient n ≤ ρ.coefficient + ρ.gap := by
    apply csSup_le
    · exact ⟨(equalMultiplicity n).coefficient, equalMultiplicity n, rfl⟩
    · rintro c ⟨η, rfl⟩
      exact ρ.coefficient_le_dual_bound η
  constructor <;> linarith

/-- Any equally good competitor to a zero-gap partition preserves its aggregate block norm a.e. -/
theorem aggregate_rigidity_of_gap_zero (ρ η : PhysicalCollarPartition n)
    (hρ : ρ.gap = 0) (hη : η.coefficient = ρ.coefficient) :
    η.blockNorm =ᵐ[volume.restrict (Ioo 0 logarithmicCollarRadius)] ρ.blockNorm := by
  have hE := ρ.exact_dual_gap η
  have hzero : (∫ y in Ioo 0 logarithmicCollarRadius, ρ.remainder η y) = 0 := by
    linarith [ρ.slack_nonneg η, ρ.integral_remainder_nonneg η]
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 logarithmicCollarRadius)] ρ.remainder η := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact ρ.remainder_nonneg η hy.1
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn (ρ.integrableOn_remainder η)).1 hzero
  filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with y hy hmem
  exact collarDualRemainder_zero_forces_blockNorm (logarithmicSignedCosets n)
    (fun j => logarithmicCosetNodes n j.1) (fun j k => ρ.weight j.2 k y)
    (fun j k => η.weight j.2 k y) (archLevySinhWeight_pos hmem.1) hy

/-- For the first grid N=2, the unique active collar makes every admissible partition zero-gap. -/
theorem gap_zero_first_grid (ρ : PhysicalCollarPartition 0) : ρ.gap = 0 := by
  rw [ρ.gap_eq_zero_iff_complementary]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  intro k hk hshare
  have hk0 : k = 0 := by simp only [Finset.mem_range] at hk; omega
  subst k
  have hactive : x ∈ logarithmicPhysicalCollar 0 0 := by
    by_contra h
    have hz := ρ.supported 0 x h
    linarith
  simp [priceFloor, maskedPrice, hactive]

theorem optimalCoefficient_first_grid : optimalCoefficient 0 = logarithmicCollarRealConstant 0 := by
  have h := optimalCoefficient_gap_bounds (equalMultiplicity 0)
  rw [gap_zero_first_grid, equalMultiplicity_coefficient] at h
  linarith [h.1, h.2]

end PhysicalCollarPartition
end
end GaloisForLFunctions.BiScaleUncertainty
