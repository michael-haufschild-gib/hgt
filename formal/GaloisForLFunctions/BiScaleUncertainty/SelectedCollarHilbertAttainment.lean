import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarHilbertPrices
import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarDualCertificate

/-!
# Variational attainment for selected finite collar nodes

The native signed dyadic blocks are restricted to an arbitrary finite node selection.
Their variable-mass objective has physical marginal price one minus the dual slope.
Exact transport and affine supports yield weakly closed convex superlevels.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Finset
open scoped BigOperators ENNReal InnerProductSpace
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

variable {n : ℕ}

def selectedWeight (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (σ : Bool) (k : ℕ) (y : ℝ) : ℝ := if k ∈ s then ρ.weight σ k y else 0

theorem selectedWeight_nonneg (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (σ : Bool) (k : ℕ) (y : ℝ) : 0 ≤ selectedWeight s ρ σ k y := by
  unfold selectedWeight
  split_ifs <;> simp_all [ρ.weight_nonneg]

theorem selectedWeight_le (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (σ : Bool) (k : ℕ) (y : ℝ) : selectedWeight s ρ σ k y ≤ ρ.weight σ k y := by
  unfold selectedWeight
  split_ifs <;> simp_all [ρ.weight_nonneg]

theorem measurable_selectedWeight (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (σ : Bool) (k : ℕ) : Measurable (selectedWeight s ρ σ k) := by
  change Measurable (fun y => if k ∈ s then ρ.weight σ k y else 0)
  by_cases hk : k ∈ s
  · simpa [selectedWeight, hk] using ρ.measurable_weight σ k
  · simp only [hk, if_false]
    exact measurable_const

def selectedMass (s : Finset ℕ) (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (selectedWeight s ρ false k y + selectedWeight s ρ true k y)

def selectedBlockNorm (s : Finset ℕ) (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  blockWeightNorm (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => selectedWeight s ρ j.2 k y)

def selectedKernel (s : Finset ℕ) (ρ : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  collarAllocationKernel (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => selectedWeight s ρ j.2 k y) (archLevySinhWeight y)

def selectedCoefficient (s : Finset ℕ) (ρ : PhysicalCollarPartition n) : ℝ :=
  ∫ y in Ioo 0 logarithmicCollarRadius, selectedKernel s ρ y

theorem selected_signed_sum (s : Finset ℕ) (ρ : PhysicalCollarPartition n) (y : ℝ) :
    (∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1,
      selectedWeight s ρ j.2 k y) = selectedMass s ρ y :=
  sum_logarithmicSignedCosets n (fun σ k => selectedWeight s ρ σ k y)

theorem selectedKernel_eq (s : Finset ℕ) (ρ : PhysicalCollarPartition n) (y : ℝ) :
    selectedKernel s ρ y = archLevySinhWeight y + selectedMass s ρ y -
      Real.sqrt (archLevySinhWeight y ^ 2 + selectedBlockNorm s ρ y ^ 2) := by
  unfold selectedKernel collarAllocationKernel collarDualScale
  rw [selected_signed_sum]
  rfl

theorem selectedBlockNorm_le_mass (s : Finset ℕ) (ρ : PhysicalCollarPartition n) (y : ℝ) :
    selectedBlockNorm s ρ y ≤ selectedMass s ρ y := by
  rw [← selected_signed_sum]
  apply sum_le_sum
  intro j _
  apply Real.sqrt_le_iff.mpr
  exact ⟨sum_nonneg (fun k _ => selectedWeight_nonneg s ρ j.2 k y),
    sum_sq_le_sq_sum_of_nonneg (fun k _ => selectedWeight_nonneg s ρ j.2 k y)⟩

theorem selectedMass_le_mass (s : Finset ℕ) (ρ : PhysicalCollarPartition n) (y : ℝ) :
    selectedMass s ρ y ≤ ρ.mass y :=
  sum_le_sum fun k _ => add_le_add (selectedWeight_le s ρ false k y) (selectedWeight_le s ρ true k y)

theorem selectedKernel_bounds (s : Finset ℕ) (ρ : PhysicalCollarPartition n) {y : ℝ}
    (hy : 0 ≤ y) : 0 ≤ selectedKernel s ρ y ∧ selectedKernel s ρ y ≤ ρ.mass y := by
  have hW := archLevySinhWeight_nonneg hy
  have hA : 0 ≤ selectedBlockNorm s ρ y := blockWeightNorm_nonneg _ _ _
  have hAB := selectedBlockNorm_le_mass s ρ y
  have hM := selectedMass_le_mass s ρ y
  have hu : Real.sqrt (archLevySinhWeight y ^ 2 + selectedBlockNorm s ρ y ^ 2) ≤
      archLevySinhWeight y + selectedBlockNorm s ρ y := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨add_nonneg hW hA, by nlinarith [mul_nonneg hW hA]⟩
  have hl : archLevySinhWeight y ≤
      Real.sqrt (archLevySinhWeight y ^ 2 + selectedBlockNorm s ρ y ^ 2) :=
    Real.le_sqrt_of_sq_le (le_add_of_nonneg_right (sq_nonneg _))
  rw [selectedKernel_eq]
  constructor <;> linarith

theorem measurable_selectedKernel (s : Finset ℕ) (ρ : PhysicalCollarPartition n) :
    Measurable (selectedKernel s ρ) := by
  have hm : Measurable (selectedMass s ρ) := (range (n + 1)).measurable_sum fun k _ =>
    (measurable_selectedWeight s ρ false k).add (measurable_selectedWeight s ρ true k)
  have hb : Measurable (selectedBlockNorm s ρ) := by
    apply (logarithmicSignedCosets n).measurable_sum
    intro j _
    exact Real.continuous_sqrt.measurable.comp
      ((logarithmicCosetNodes n j.1).measurable_sum fun k _ =>
        (measurable_selectedWeight s ρ j.2 k).pow_const 2)
  change Measurable (fun y => selectedKernel s ρ y)
  simp_rw [selectedKernel_eq]
  exact (measurable_archLevySinhWeight.add hm).sub
    (Real.continuous_sqrt.measurable.comp
      ((measurable_archLevySinhWeight.pow_const 2).add (hb.pow_const 2)))

theorem integrableOn_selectedKernel (s : Finset ℕ) (ρ : PhysicalCollarPartition n) :
    IntegrableOn (selectedKernel s ρ) (Ioo 0 logarithmicCollarRadius) := by
  apply ρ.integrableOn_mass.mono' (measurable_selectedKernel s ρ).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (selectedKernel_bounds s ρ hy.1.le).1]
  exact (selectedKernel_bounds s ρ hy.1.le).2

theorem selectedCoefficient_le_physical_mass (s : Finset ℕ) (ρ : PhysicalCollarPartition n) :
    selectedCoefficient s ρ ≤
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x := by
  rw [← ρ.integral_mass]
  apply integral_mono_ae (integrableOn_selectedKernel s ρ) ρ.integrableOn_mass
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact (selectedKernel_bounds s ρ hy.1.le).2

def selectedDualSlope (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (j : ℕ × Bool) (k : ℕ) (y : ℝ) : ℝ :=
  collarDualSlope (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => selectedWeight s ρ j.2 k y) (archLevySinhWeight y) j k

theorem measurable_selectedDualSlope (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (j : ℕ × Bool) (k : ℕ) : Measurable (selectedDualSlope s ρ j k) :=
  measurable_collarDualSlope (logarithmicSignedCosets n) (fun j => logarithmicCosetNodes n j.1)
    (fun y j k => selectedWeight s ρ j.2 k y) archLevySinhWeight
    (fun j k => measurable_selectedWeight s ρ j.2 k) measurable_archLevySinhWeight j k

theorem selectedDualSlope_bounds (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (j : ℕ × Bool) (k : ℕ) (hk : k ∈ logarithmicCosetNodes n j.1) (y : ℝ) :
    0 ≤ selectedDualSlope s ρ j k y ∧ selectedDualSlope s ρ j k y ≤ 1 := by
  refine ⟨collarDualSlope_nonneg _ _ _ _ _ _ (selectedWeight_nonneg s ρ j.2 k y), ?_⟩
  apply (collarDualSlope_le_radius (logarithmicSignedCosets n)
    (fun j => logarithmicCosetNodes n j.1)
    (fun j k => selectedWeight s ρ j.2 k y) (archLevySinhWeight y) j k hk).trans
  apply div_le_one_of_le₀ _ (Real.sqrt_nonneg _)
  exact Real.le_sqrt_of_sq_le (le_add_of_nonneg_left (sq_nonneg _))

def selectedMarginalPrice (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (k : ℕ) (x : ℝ) : ℝ :=
  if k ∈ s then 1 - if x < logarithmicCollarNode k then
    selectedDualSlope s ρ (logNodeOddPart k, false) k (logarithmicCollarNode k - x)
  else selectedDualSlope s ρ (logNodeOddPart k, true) k (x - logarithmicCollarNode k)
  else 0

theorem measurable_selectedMarginalPrice (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (k : ℕ) : Measurable (selectedMarginalPrice s ρ k) := by
  change Measurable (fun x => selectedMarginalPrice s ρ k x)
  by_cases hk : k ∈ s
  · simp only [selectedMarginalPrice, hk, if_true]
    exact measurable_const.sub (Measurable.ite measurableSet_Iio
      ((measurable_selectedDualSlope s ρ (logNodeOddPart k, false) k).comp
        (measurable_const.sub measurable_id))
      ((measurable_selectedDualSlope s ρ (logNodeOddPart k, true) k).comp
        (measurable_id.sub measurable_const)))
  · simp only [selectedMarginalPrice, hk, if_false]
    exact measurable_const

theorem selectedMarginalPrice_bounds (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (k : ℕ) (hk : k ∈ range (n + 1)) (x : ℝ) :
    0 ≤ selectedMarginalPrice s ρ k x ∧ selectedMarginalPrice s ρ k x ≤ 1 := by
  unfold selectedMarginalPrice
  split_ifs with hs hx
  · have h := selectedDualSlope_bounds s ρ (logNodeOddPart k, false) k (node_mem_own_coset k hk)
      (logarithmicCollarNode k - x)
    constructor <;> linarith
  · have h := selectedDualSlope_bounds s ρ (logNodeOddPart k, true) k (node_mem_own_coset k hk)
      (x - logarithmicCollarNode k)
    constructor <;> linarith
  · norm_num

theorem selectedMarginalPrice_offset (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (σ : Bool) (k : ℕ) {y : ℝ} (hy : 0 < y) :
    selectedMarginalPrice s ρ k (logarithmicCollarNode k + collarSignedOffset σ y) =
      if k ∈ s then 1 - selectedDualSlope s ρ (logNodeOddPart k, σ) k y else 0 := by
  unfold selectedMarginalPrice
  by_cases hs : k ∈ s
  · rw [if_pos hs, if_pos hs]
    cases σ
    · simp only [collarSignedOffset, Bool.false_eq_true, ↓reduceIte]
      rw [if_pos (by linarith)]
      congr 2
      ring
    · simp only [collarSignedOffset, ↓reduceIte]
      rw [if_neg (by linarith)]
      congr 2
      ring
  · rw [if_neg hs, if_neg hs]

def selectedCost (s : Finset ℕ) (ρ η : PhysicalCollarPartition n) (y : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1),
    (η.weight false k y * selectedMarginalPrice s ρ k (logarithmicCollarNode k - y) +
      η.weight true k y * selectedMarginalPrice s ρ k (logarithmicCollarNode k + y))

theorem selectedCost_eq (s : Finset ℕ) (ρ η : PhysicalCollarPartition n) {y : ℝ} (hy : 0 < y) :
    selectedCost s ρ η y =
      ∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1,
        selectedWeight s η j.2 k y * (1 - selectedDualSlope s ρ j k y) := by
  have h (σ : Bool) (k : ℕ) :
      η.weight σ k y * selectedMarginalPrice s ρ k
        (logarithmicCollarNode k + collarSignedOffset σ y) =
      selectedWeight s η σ k y * (1 - selectedDualSlope s ρ (logNodeOddPart k, σ) k y) := by
    rw [selectedMarginalPrice_offset s ρ σ k hy]
    unfold selectedWeight
    split_ifs <;> simp
  symm
  calc
    _ = ∑ j ∈ logarithmicSignedCosets n, ∑ k ∈ logarithmicCosetNodes n j.1,
        selectedWeight s η j.2 k y *
          (1 - selectedDualSlope s ρ (logNodeOddPart k, j.2) k y) := by
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro k hk
      rw [(mem_filter.mp hk).2]
    _ = _ := by
      rw [sum_logarithmicSignedCosets n (fun σ k => selectedWeight s η σ k y *
        (1 - selectedDualSlope s ρ (logNodeOddPart k, σ) k y))]
      unfold selectedCost
      apply sum_congr rfl
      intro k _
      exact congrArg₂ (· + ·)
        (by simpa [collarSignedOffset, sub_eq_add_neg] using (h false k).symm)
        (by simpa [collarSignedOffset] using (h true k).symm)

theorem integrableOn_selectedCost_term (s : Finset ℕ) (ρ η : PhysicalCollarPartition n)
    (σ : Bool) (k : ℕ) (hk : k ∈ range (n + 1)) :
    IntegrableOn (fun y => η.weight σ k y * selectedMarginalPrice s ρ k
      (logarithmicCollarNode k + collarSignedOffset σ y)) (Ioo 0 logarithmicCollarRadius) := by
  have hm : Measurable (fun y => logarithmicCollarNode k + collarSignedOffset σ y) := by
    cases σ <;> simp [collarSignedOffset] <;> fun_prop
  apply volume.integrableOn_of_bounded (M := logarithmicCollarWeightBound n)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    ((η.measurable_weight σ k).mul ((measurable_selectedMarginalPrice s ρ k).comp hm)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    change ‖η.weight σ k y * selectedMarginalPrice s ρ k
      (logarithmicCollarNode k + collarSignedOffset σ y)‖ ≤ logarithmicCollarWeightBound n
    have hp := selectedMarginalPrice_bounds s ρ k hk
      (logarithmicCollarNode k + collarSignedOffset σ y)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (η.weight_nonneg σ k y) hp.1)]
    exact (mul_le_of_le_one_right (η.weight_nonneg σ k y) hp.2).trans (η.weight_le_bound σ k hk y)

theorem integrableOn_selectedCost (s : Finset ℕ) (ρ η : PhysicalCollarPartition n) :
    IntegrableOn (selectedCost s ρ η) (Ioo 0 logarithmicCollarRadius) := by
  apply integrable_finsetSum
  intro k hk
  simpa [IntegrableOn, Pi.add_apply, collarSignedOffset, sub_eq_add_neg] using
    (integrableOn_selectedCost_term s ρ η false k hk).fun_add
      (integrableOn_selectedCost_term s ρ η true k hk)

theorem integral_selectedCost (s : Finset ℕ) (ρ η : PhysicalCollarPartition n) :
    (∫ y in Ioo 0 logarithmicCollarRadius, selectedCost s ρ η y) =
      ∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n),
        ∑ k ∈ range (n + 1), η.density k x * selectedMarginalPrice s ρ k x := by
  have hi (σ : Bool) (k : ℕ) (hk : k ∈ range (n + 1)) :=
    integrableOn_selectedCost_term s ρ η σ k hk
  unfold selectedCost
  rw [integral_finsetSum (range (n + 1)) (fun k hk => by
    simpa [IntegrableOn, Pi.add_apply, collarSignedOffset, sub_eq_add_neg] using
      (hi false k hk).fun_add (hi true k hk))]
  calc
    _ = ∑ k ∈ range (n + 1),
        ((∫ y in Ioo 0 logarithmicCollarRadius,
          η.weight false k y * selectedMarginalPrice s ρ k (logarithmicCollarNode k - y)) +
         (∫ y in Ioo 0 logarithmicCollarRadius,
          η.weight true k y * selectedMarginalPrice s ρ k (logarithmicCollarNode k + y))) := by
      apply sum_congr rfl
      intro k hk
      apply integral_add
      · simpa [IntegrableOn, collarSignedOffset, sub_eq_add_neg] using hi false k hk
      · simpa [IntegrableOn, collarSignedOffset] using hi true k hk
    _ = _ := η.integral_signed_cost_transport (selectedMarginalPrice s ρ)
      (measurable_selectedMarginalPrice s ρ) (selectedMarginalPrice_bounds s ρ)

theorem selectedKernel_support_upper (s : Finset ℕ) (ρ η : PhysicalCollarPartition n)
    {y : ℝ} (hy : 0 < y) :
    selectedKernel s η y - selectedKernel s ρ y ≤ selectedCost s ρ η y - selectedCost s ρ ρ y := by
  rw [selectedCost_eq s ρ η hy, selectedCost_eq s ρ ρ hy]
  have h := collarAllocationKernel_support_upper (logarithmicSignedCosets n)
    (logarithmicSignedCosets_nonempty n) (fun j => logarithmicCosetNodes n j.1)
    (fun j k => selectedWeight s ρ j.2 k y) (fun j k => selectedWeight s η j.2 k y)
    (archLevySinhWeight_pos hy)
  simpa only [selectedKernel, selectedDualSlope, sub_mul, sum_sub_distrib] using h

def selectedPriceClass (s : Finset ℕ) (ρ : PhysicalCollarPartition n) : AllocationHilbert n :=
  boundedPriceClass n (selectedMarginalPrice s ρ)
    (measurable_selectedMarginalPrice s ρ) (selectedMarginalPrice_bounds s ρ)

theorem selectedPriceClass_inner (s : Finset ℕ) (ρ η : PhysicalCollarPartition n) :
    inner ℝ (selectedPriceClass s ρ) (allocationClass η) =
      ∫ y in Ioo 0 logarithmicCollarRadius, selectedCost s ρ η y := by
  rw [integral_selectedCost]
  exact boundedPriceClass_inner _ _ _ η

def selectedUpperSupport (s : Finset ℕ) (ρ : PhysicalCollarPartition n)
    (u : AllocationHilbert n) : ℝ :=
  selectedCoefficient s ρ + inner ℝ (selectedPriceClass s ρ) u -
    inner ℝ (selectedPriceClass s ρ) (allocationClass ρ)

theorem selectedCoefficient_le_upperSupport (s : Finset ℕ) (ρ η : PhysicalCollarPartition n) :
    selectedCoefficient s η ≤ selectedUpperSupport s ρ (allocationClass η) := by
  have hi := integral_mono_ae ((integrableOn_selectedKernel s η).sub (integrableOn_selectedKernel s ρ))
    ((integrableOn_selectedCost s ρ η).sub (integrableOn_selectedCost s ρ ρ))
    (show ∀ᵐ y ∂volume.restrict (Ioo 0 logarithmicCollarRadius),
      selectedKernel s η y - selectedKernel s ρ y ≤ selectedCost s ρ η y - selectedCost s ρ ρ y by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      exact selectedKernel_support_upper s ρ η hy.1)
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrableOn_selectedKernel s η) (integrableOn_selectedKernel s ρ),
    integral_sub (integrableOn_selectedCost s ρ η) (integrableOn_selectedCost s ρ ρ)] at hi
  unfold selectedUpperSupport selectedCoefficient
  rw [selectedPriceClass_inner, selectedPriceClass_inner]
  linarith

@[simp] theorem selectedUpperSupport_self (s : Finset ℕ) (ρ : PhysicalCollarPartition n) :
    selectedUpperSupport s ρ (allocationClass ρ) = selectedCoefficient s ρ := by
  unfold selectedUpperSupport
  ring

theorem selectedCoefficient_eq_of_class_eq (s : Finset ℕ) {ρ η : PhysicalCollarPartition n}
    (h : allocationClass ρ = allocationClass η) : selectedCoefficient s ρ = selectedCoefficient s η := by
  have h₁ := selectedCoefficient_le_upperSupport s ρ η
  have h₂ := selectedCoefficient_le_upperSupport s η ρ
  rw [← h, selectedUpperSupport_self] at h₁
  rw [h, selectedUpperSupport_self] at h₂
  exact le_antisymm h₂ h₁

theorem selectedCoefficient_sublevel_eq (s : Finset ℕ) (t : ℝ) :
    {u : AllocationHilbert n | u ∈ allocationFeasible n ∧
      -selectedCoefficient s (allocationRepair u) ≤ t} =
    allocationFeasible n ∩ ⋂ ρ : PhysicalCollarPartition n, {u | -selectedUpperSupport s ρ u ≤ t} := by
  ext u
  simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hu, ht⟩
    refine ⟨hu, fun ρ => ?_⟩
    have h := selectedCoefficient_le_upperSupport s ρ (allocationRepair u)
    rw [allocationClass_repair hu] at h
    linarith
  · rintro ⟨hu, ht⟩
    refine ⟨hu, ?_⟩
    have h := ht (allocationRepair u)
    have he := selectedUpperSupport_self s (allocationRepair u)
    rw [allocationClass_repair hu] at he
    rwa [he] at h

theorem isClosed_selectedCoefficient_sublevel (s : Finset ℕ) (t : ℝ) :
    IsClosed {u : AllocationHilbert n | u ∈ allocationFeasible n ∧
      -selectedCoefficient s (allocationRepair u) ≤ t} := by
  rw [selectedCoefficient_sublevel_eq]
  refine (isClosed_allocationFeasible n).inter (isClosed_iInter fun ρ => ?_)
  apply isClosed_le _ continuous_const
  exact ((continuous_const.add (innerSL ℝ (selectedPriceClass s ρ)).continuous).sub continuous_const).neg

theorem convex_selectedCoefficient_sublevel (s : Finset ℕ) (t : ℝ) :
    Convex ℝ {u : AllocationHilbert n | u ∈ allocationFeasible n ∧
      -selectedCoefficient s (allocationRepair u) ≤ t} := by
  rw [selectedCoefficient_sublevel_eq]
  refine (convex_allocationFeasible n).inter (convex_iInter fun ρ => ?_)
  intro u hu v hv a b ha hb hab
  change -selectedUpperSupport s ρ (a • u + b • v) ≤ t
  change -selectedUpperSupport s ρ u ≤ t at hu
  change -selectedUpperSupport s ρ v ≤ t at hv
  unfold selectedUpperSupport at hu hv ⊢
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  have h := add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
  have hc : a * (selectedCoefficient s ρ - inner ℝ (selectedPriceClass s ρ) (allocationClass ρ)) +
      b * (selectedCoefficient s ρ - inner ℝ (selectedPriceClass s ρ) (allocationClass ρ)) =
      selectedCoefficient s ρ - inner ℝ (selectedPriceClass s ρ) (allocationClass ρ) := by
    rw [← add_mul, hab, one_mul]
  rw [← add_mul, hab, one_mul] at h
  linarith

local instance : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩

/-- Attainment for the literal selected-grid objective on physical allocations. -/
theorem exists_selectedCoefficient_maximizer (n : ℕ) (s : Finset ℕ) :
    ∃ ρ : PhysicalCollarPartition n, ∀ η : PhysicalCollarPartition n,
      selectedCoefficient s η ≤ selectedCoefficient s ρ := by
  have hb : BddBelow ((fun u : AllocationHilbert n => -selectedCoefficient s (allocationRepair u)) ''
      allocationFeasible n) := by
    refine ⟨-(∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x), ?_⟩
    rintro _ ⟨u, _, rfl⟩
    exact neg_le_neg (selectedCoefficient_le_physical_mass s (allocationRepair u))
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_closedConvex_sublevels
    (allocationFeasible n) (allocationFeasible_nonempty n) (isClosed_allocationFeasible n)
    (convex_allocationFeasible n)
    (measureUnivNNReal (allocationMeasure n) ^ (2 : ℝ≥0∞).toReal⁻¹)
    (fun _ h => norm_allocationFeasible_le h)
    (fun u => -selectedCoefficient s (allocationRepair u)) hb
    (isClosed_selectedCoefficient_sublevel s) (convex_selectedCoefficient_sublevel s)
  refine ⟨allocationRepair u, fun η => ?_⟩
  have h := hmin (allocationClass_mem η)
  change -selectedCoefficient s (allocationRepair u) ≤
    -selectedCoefficient s (allocationRepair (allocationClass η)) at h
  rw [selectedCoefficient_eq_of_class_eq s (allocationClass_repair (allocationClass_mem η))] at h
  linarith

end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

end
