import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarHilbertPrices
import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarDualCertificate

/-!
# Attainment of the original physical collar optimum

Native dual prices identify closed convex sublevels on the concrete allocation space.
Weak compactness and exact representative repair produce an original measurable partition
attaining the original coefficient supremum, without an assumed compactness certificate.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Finset
open scoped BigOperators ENNReal InnerProductSpace
open GaloisForLFunctions.HTGeometry
noncomputable section


namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

local instance : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩

/-- The canonical physical marginal price in the concrete allocation Hilbert space. -/
def priceClass {n : ℕ} (ρ : PhysicalCollarPartition n) : AllocationHilbert n :=
  boundedPriceClass n ρ.physicalPrice ρ.measurable_physicalPrice ρ.physicalPrice_bounds

theorem priceClass_inner {n : ℕ} (ρ η : PhysicalCollarPartition n) :
    inner ℝ (priceClass ρ) (allocationClass η) =
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), ρ.physicalCost η x :=
  boundedPriceClass_inner ρ.physicalPrice ρ.measurable_physicalPrice ρ.physicalPrice_bounds η

/-- The original dual prices give an affine upper support, exact at the base partition. -/
def coefficientUpperSupport {n : ℕ} (ρ : PhysicalCollarPartition n)
    (u : AllocationHilbert n) : ℝ :=
  ρ.coefficient + inner ℝ (priceClass ρ) (allocationClass ρ) - inner ℝ (priceClass ρ) u

theorem coefficient_le_upperSupport {n : ℕ} (ρ η : PhysicalCollarPartition n) :
    η.coefficient ≤ coefficientUpperSupport ρ (allocationClass η) := by
  have h := ρ.integral_remainder_nonneg η
  rw [ρ.integral_remainder η] at h
  unfold coefficientUpperSupport
  rw [priceClass_inner, priceClass_inner]
  linarith

@[simp] theorem coefficientUpperSupport_self {n : ℕ} (ρ : PhysicalCollarPartition n) :
    coefficientUpperSupport ρ (allocationClass ρ) = ρ.coefficient := by
  unfold coefficientUpperSupport
  ring

theorem coefficient_eq_of_allocationClass_eq {n : ℕ} {ρ η : PhysicalCollarPartition n}
    (h : allocationClass ρ = allocationClass η) : ρ.coefficient = η.coefficient := by
  have h₁ := coefficient_le_upperSupport ρ η
  have h₂ := coefficient_le_upperSupport η ρ
  rw [← h, coefficientUpperSupport_self] at h₁
  rw [h, coefficientUpperSupport_self] at h₂
  exact le_antisymm h₂ h₁

theorem coefficient_repair_class {n : ℕ} (ρ : PhysicalCollarPartition n) :
    (allocationRepair (allocationClass ρ)).coefficient = ρ.coefficient :=
  coefficient_eq_of_allocationClass_eq (allocationClass_repair (allocationClass_mem ρ))

theorem coefficient_sublevel_eq {n : ℕ} (t : ℝ) :
    {u : AllocationHilbert n | u ∈ allocationFeasible n ∧
      -(allocationRepair u).coefficient ≤ t} =
    allocationFeasible n ∩ ⋂ ρ : PhysicalCollarPartition n,
      {u | -coefficientUpperSupport ρ u ≤ t} := by
  ext u
  simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hu, ht⟩
    refine ⟨hu, fun ρ => ?_⟩
    have h := coefficient_le_upperSupport ρ (allocationRepair u)
    rw [allocationClass_repair hu] at h
    linarith
  · rintro ⟨hu, ht⟩
    refine ⟨hu, ?_⟩
    have h := ht (allocationRepair u)
    have he := coefficientUpperSupport_self (allocationRepair u)
    rw [allocationClass_repair hu] at he
    rw [he] at h
    exact h

theorem isClosed_coefficient_sublevel {n : ℕ} (t : ℝ) :
    IsClosed {u : AllocationHilbert n | u ∈ allocationFeasible n ∧
      -(allocationRepair u).coefficient ≤ t} := by
  rw [coefficient_sublevel_eq]
  refine (isClosed_allocationFeasible n).inter (isClosed_iInter fun ρ => ?_)
  apply isClosed_le _ continuous_const
  exact (continuous_const.sub (innerSL ℝ (priceClass ρ)).continuous).neg

theorem convex_coefficient_sublevel {n : ℕ} (t : ℝ) :
    Convex ℝ {u : AllocationHilbert n | u ∈ allocationFeasible n ∧
      -(allocationRepair u).coefficient ≤ t} := by
  rw [coefficient_sublevel_eq]
  refine (convex_allocationFeasible n).inter (convex_iInter fun ρ => ?_)
  intro u hu v hv a b ha hb hab
  change -coefficientUpperSupport ρ (a • u + b • v) ≤ t
  unfold coefficientUpperSupport at hu hv ⊢
  change -(ρ.coefficient + inner ℝ (priceClass ρ) (allocationClass ρ) -
    inner ℝ (priceClass ρ) u) ≤ t at hu
  change -(ρ.coefficient + inner ℝ (priceClass ρ) (allocationClass ρ) -
    inner ℝ (priceClass ρ) v) ≤ t at hv
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have h := add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
  have hc : a * (ρ.coefficient + inner ℝ (priceClass ρ) (allocationClass ρ)) +
      b * (ρ.coefficient + inner ℝ (priceClass ρ) (allocationClass ρ)) =
      ρ.coefficient + inner ℝ (priceClass ρ) (allocationClass ρ) := by rw [← add_mul, hab, one_mul]
  rw [← add_mul, hab, one_mul] at h
  linarith

/-- The supremum over the original measurable physical partitions is attained. -/
theorem exists_coefficient_maximizer (n : ℕ) :
    ∃ ρ : PhysicalCollarPartition n, ∀ η : PhysicalCollarPartition n,
      η.coefficient ≤ ρ.coefficient := by
  have hb : BddBelow ((fun u : AllocationHilbert n => -(allocationRepair u).coefficient) ''
      allocationFeasible n) := by
    refine ⟨-(∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n),
      archLevySinhWeight x), ?_⟩
    rintro _ ⟨u, _, rfl⟩
    exact neg_le_neg (allocationRepair u).coefficient_le_physical_mass
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_closedConvex_sublevels
    (allocationFeasible n) (allocationFeasible_nonempty n) (isClosed_allocationFeasible n)
    (convex_allocationFeasible n)
    (measureUnivNNReal (allocationMeasure n) ^ (2 : ℝ≥0∞).toReal⁻¹)
    (fun _ h => norm_allocationFeasible_le h)
    (fun u => -(allocationRepair u).coefficient) hb
    isClosed_coefficient_sublevel convex_coefficient_sublevel
  refine ⟨allocationRepair u, fun η => ?_⟩
  have h := hmin (allocationClass_mem η)
  change -(allocationRepair u).coefficient ≤
    -(allocationRepair (allocationClass η)).coefficient at h
  rw [coefficient_repair_class] at h
  linarith

theorem exists_coefficient_eq_optimalCoefficient (n : ℕ) :
    ∃ ρ : PhysicalCollarPartition n, ρ.coefficient = optimalCoefficient n := by
  obtain ⟨ρ, hρ⟩ := exists_coefficient_maximizer n
  refine ⟨ρ, le_antisymm (le_csSup (coefficient_range_bddAbove n) ⟨ρ, rfl⟩) ?_⟩
  change sSup (Set.range (fun η : PhysicalCollarPartition n => η.coefficient)) ≤ ρ.coefficient
  apply csSup_le (show (Set.range (fun η : PhysicalCollarPartition n => η.coefficient)).Nonempty
    from ⟨ρ.coefficient, ρ, rfl⟩)
  rintro _ ⟨η, rfl⟩
  exact hρ η

end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

end
