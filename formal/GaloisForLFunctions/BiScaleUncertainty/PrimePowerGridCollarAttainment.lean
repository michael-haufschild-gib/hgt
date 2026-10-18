import GaloisForLFunctions.BiScaleUncertainty.SelectedCollarHilbertAttainment
import Mathlib.Algebra.IsPrimePow

/-!
# Exact partition attainment on arbitrary finite prime-power grids

Selected shares spend exactly one unit of mass on the actual selected collar union,
with zero allocation in its gaps. Null-set repair preserves the optimized coefficient.
Any finite set of prime powers is realized at its literal logarithmic nodes; no factorial
grid restriction or extra attainment premise is used.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Finset
open scoped BigOperators ENNReal InnerProductSpace
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition


def selectedIndices (n : ℕ) (s : Finset ℕ) : Finset ℕ := (range (n + 1)).filter (· ∈ s)

def selectedUnion (n : ℕ) (s : Finset ℕ) : Set ℝ :=
  ⋃ k ∈ selectedIndices n s, logarithmicPhysicalCollar n k

theorem measurableSet_selectedUnion (n : ℕ) (s : Finset ℕ) : MeasurableSet (selectedUnion n s) :=
  (selectedIndices n s).measurableSet_biUnion fun _ _ => measurableSet_Ioo.inter measurableSet_Ioo

theorem selectedUnion_subset (n : ℕ) (s : Finset ℕ) :
    selectedUnion n s ⊆ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) := by
  intro x hx
  obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
  obtain ⟨hk, hxk⟩ := Set.mem_iUnion.mp hxk
  have h : x ∈ ⋃ j ∈ range (n + 1), logarithmicPhysicalCollar n j := by
    simp only [mem_iUnion]
    exact ⟨k, (mem_filter.mp hk).1, hxk⟩
  change x ∈ ⋃ j ∈ range (n + 1), truncatedPhysicalCollar (Real.log ((j + 2 : ℕ) : ℝ))
    (Real.log 2 / 2) (Real.log ((n + 2 : ℕ) : ℝ)) at h
  rwa [truncated_logarithmic_collar_union] at h

def selectedBaselineShare (n : ℕ) (s : Finset ℕ) (k : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ selectedUnion n s then
    if k ∈ s then collarPhysicalShare (selectedIndices n s) (logarithmicPhysicalCollar n) k x else 0
    else (equalMultiplicity n).share k x

def selectedBaseline (n : ℕ) (s : Finset ℕ) : PhysicalCollarPartition n where
  share := selectedBaselineShare n s
  measurable_share k := by
    classical
    unfold selectedBaselineShare
    apply Measurable.ite (measurableSet_selectedUnion n s)
    · by_cases hk : k ∈ s
      · simp only [hk, if_true]
        exact measurable_collarPhysicalShare _ _
          (fun _ => measurableSet_Ioo.inter measurableSet_Ioo) k
      · simp only [hk, if_false]
        exact measurable_const
    · exact (equalMultiplicity n).measurable_share k
  nonneg k x := by
    classical
    unfold selectedBaselineShare
    split_ifs
    · exact collarPhysicalShare_nonneg _ _ _ _
    · exact le_rfl
    · exact (equalMultiplicity n).nonneg k x
  supported k x hx := by
    classical
    unfold selectedBaselineShare
    split_ifs
    · simp [collarPhysicalShare, hx]
    · rfl
    · exact (equalMultiplicity n).supported k x hx
  partition x := by
    classical
    by_cases hx : x ∈ selectedUnion n s
    · simp only [selectedBaselineShare, hx, if_true]
      rw [← sum_filter]
      change (∑ k ∈ selectedIndices n s, collarPhysicalShare (selectedIndices n s)
        (logarithmicPhysicalCollar n) k x) = _
      rw [collarPhysicalShare_partition]
      exact congrArg (fun E : Set ℝ => E.indicator (fun _ => (1 : ℝ)) x)
        (show (⋃ k ∈ (range (n + 1)).filter (· ∈ s), logarithmicPhysicalCollar n k) =
          selectedUnion n s from rfl) |>.trans (by
          rw [indicator_of_mem hx, indicator_of_mem (selectedUnion_subset n s hx)])
    · simpa only [selectedBaselineShare, hx, if_false] using (equalMultiplicity n).partition x

/-- The selected collars spend all physical mass on their actual union. -/
def IsSelectedPartition {n : ℕ} (s : Finset ℕ) (ρ : PhysicalCollarPartition n) : Prop :=
  ∀ k ∈ range (n + 1), k ∉ s → ∀ x ∈ selectedUnion n s, ρ.share k x = 0

theorem selectedBaseline_isSelected (n : ℕ) (s : Finset ℕ) :
    IsSelectedPartition s (selectedBaseline n s) := by
  classical
  intro k _ hk x hx
  simp [selectedBaseline, selectedBaselineShare, hx, hk]

def selectedFibre (n : ℕ) (s : Finset ℕ) (x : ℝ) : Set (AllocationVector n) :=
  {v | v ∈ allocationFibre n x ∧ ∀ k : Fin (n + 1), k.val ∉ s →
    x ∈ selectedUnion n s → v k = 0}

theorem isClosed_selectedFibre (n : ℕ) (s : Finset ℕ) (x : ℝ) :
    IsClosed (selectedFibre n s x) := by
  simp only [selectedFibre, setOf_and, setOf_forall]
  refine (isClosed_allocationFibre n x).inter (isClosed_iInter fun k => isClosed_iInter fun _ =>
    isClosed_iInter fun _ => ?_)
  exact isClosed_eq (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) k) continuous_const

theorem convex_selectedFibre (n : ℕ) (s : Finset ℕ) (x : ℝ) :
    Convex ℝ (selectedFibre n s x) := by
  intro u hu v hv a b ha hb hab
  refine ⟨convex_allocationFibre n x hu.1 hv.1 ha hb hab, ?_⟩
  intro k hk hx
  change a * u k + b * v k = 0
  rw [hu.2 k hk hx, hv.2 k hk hx, mul_zero, mul_zero, add_zero]

def selectedFeasible (n : ℕ) (s : Finset ℕ) : Set (AllocationHilbert n) :=
  {u | ∀ᵐ x ∂allocationMeasure n, u x ∈ selectedFibre n s x}

theorem selectedFeasible_subset (n : ℕ) (s : Finset ℕ) :
    selectedFeasible n s ⊆ allocationFeasible n := by
  intro u h
  change ∀ᵐ x ∂allocationMeasure n, u x ∈ selectedFibre n s x at h
  exact h.mono fun _ hx => hx.1

theorem isClosed_selectedFeasible (n : ℕ) (s : Finset ℕ) : IsClosed (selectedFeasible n s) :=
  isClosed_L2_fibreConstraints (allocationMeasure n) (selectedFibre n s) (isClosed_selectedFibre n s)

theorem convex_selectedFeasible (n : ℕ) (s : Finset ℕ) : Convex ℝ (selectedFeasible n s) :=
  convex_L2_fibreConstraints (allocationMeasure n) (selectedFibre n s) (convex_selectedFibre n s)

theorem allocationClass_selected {n : ℕ} {s : Finset ℕ} {ρ : PhysicalCollarPartition n}
    (hρ : IsSelectedPartition s ρ) : allocationClass ρ ∈ selectedFeasible n s := by
  filter_upwards [(memLp_allocationVector ρ).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioo] with x hx hxI
  change (memLp_allocationVector ρ).toLp (allocationVector ρ) x ∈ selectedFibre n s x
  rw [hx]
  exact ⟨allocationVector_mem ρ hxI, fun k hk hu => hρ k.val (mem_range.mpr k.isLt) hk x hu⟩

theorem selectedFeasible_nonempty (n : ℕ) (s : Finset ℕ) : (selectedFeasible n s).Nonempty :=
  ⟨allocationClass (selectedBaseline n s), allocationClass_selected (selectedBaseline_isSelected n s)⟩

def selectedBadSet {n : ℕ} (s : Finset ℕ) (ρ : PhysicalCollarPartition n) : Set ℝ :=
  selectedUnion n s ∩ {x | ¬ ∀ k : Fin (n + 1), k.val ∉ s → ρ.share k.val x = 0}

local instance {n : ℕ} (s : Finset ℕ) (ρ : PhysicalCollarPartition n) (x : ℝ) :
    Decidable (x ∈ selectedBadSet s ρ) := Classical.propDecidable _

theorem measurableSet_selectedBadSet {n : ℕ} (s : Finset ℕ) (ρ : PhysicalCollarPartition n) :
    MeasurableSet (selectedBadSet s ρ) := by
  apply (measurableSet_selectedUnion n s).inter
  have h : MeasurableSet {x | ∀ k : Fin (n + 1), k.val ∉ s → ρ.share k.val x = 0} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_eq_fun (ρ.measurable_share k.val) measurable_const
  exact h.compl

def selectedRepair {n : ℕ} (s : Finset ℕ) (ρ : PhysicalCollarPartition n) : PhysicalCollarPartition n where
  share k x := (selectedBadSet s ρ).piecewise ((selectedBaseline n s).share k) (ρ.share k) x
  measurable_share k := (selectedBaseline n s).measurable_share k |>.piecewise
    (measurableSet_selectedBadSet s ρ) (ρ.measurable_share k)
  nonneg k x := by
    classical
    by_cases hx : x ∈ selectedBadSet s ρ <;> simp only [Set.piecewise, hx, if_true, if_false]
    · exact (selectedBaseline n s).nonneg k x
    · exact ρ.nonneg k x
  supported k x hx := by
    classical
    by_cases hb : x ∈ selectedBadSet s ρ <;> simp only [Set.piecewise, hb, if_true, if_false]
    · exact (selectedBaseline n s).supported k x hx
    · exact ρ.supported k x hx
  partition x := by
    classical
    by_cases hx : x ∈ selectedBadSet s ρ <;> simp only [Set.piecewise, hx, if_true, if_false]
    · exact (selectedBaseline n s).partition x
    · exact ρ.partition x

theorem selectedRepair_isSelected {n : ℕ} (s : Finset ℕ) (ρ : PhysicalCollarPartition n) :
    IsSelectedPartition s (selectedRepair s ρ) := by
  classical
  intro k hk hs x hx
  by_cases hb : x ∈ selectedBadSet s ρ
  · change (selectedBadSet s ρ).piecewise _ _ x = 0
    rw [Set.piecewise_eq_of_mem _ _ _ hb]
    exact selectedBaseline_isSelected n s k hk hs x hx
  · change (selectedBadSet s ρ).piecewise _ _ x = 0
    rw [Set.piecewise_eq_of_notMem _ _ _ hb]
    have hg : ∀ j : Fin (n + 1), j.val ∉ s → ρ.share j.val x = 0 := by
      by_contra h
      exact hb ⟨hx, h⟩
    exact hg ⟨k, mem_range.mp hk⟩ hs

theorem allocationClass_selectedRepair {n : ℕ} {s : Finset ℕ} {ρ : PhysicalCollarPartition n}
    (hρ : allocationClass ρ ∈ selectedFeasible n s) :
    allocationClass (selectedRepair s ρ) = allocationClass ρ := by
  classical
  apply Lp.ext
  filter_upwards [(memLp_allocationVector ρ).coeFn_toLp,
    (memLp_allocationVector (selectedRepair s ρ)).coeFn_toLp, hρ] with x hx hy hgood
  have hg : allocationVector ρ x ∈ selectedFibre n s x := by
    change (memLp_allocationVector ρ).toLp (allocationVector ρ) x ∈ selectedFibre n s x at hgood
    rwa [hx] at hgood
  have hb : x ∉ selectedBadSet s ρ := by
    rintro ⟨hxU, hbad⟩
    apply hbad
    intro k hk
    exact hg.2 k hk hxU
  change (memLp_allocationVector (selectedRepair s ρ)).toLp
    (allocationVector (selectedRepair s ρ)) x = (memLp_allocationVector ρ).toLp (allocationVector ρ) x
  rw [hy, hx]
  ext k
  change (selectedBadSet s ρ).piecewise ((selectedBaseline n s).share k.val) (ρ.share k.val) x = _
  rw [Set.piecewise_eq_of_notMem _ _ _ hb]
  rfl

local instance : Fact ((2 : ENNReal) ≠ ∞) := ⟨by norm_num⟩

/-- Attainment on any finite selected grid, with exact pointwise mass allocation on its union. -/
theorem exists_selectedPartition_maximizer (n : ℕ) (s : Finset ℕ) :
    ∃ ρ : PhysicalCollarPartition n, IsSelectedPartition s ρ ∧
      ∀ η : PhysicalCollarPartition n, IsSelectedPartition s η →
        selectedCoefficient s η ≤ selectedCoefficient s ρ := by
  have hb : BddBelow ((fun u : AllocationHilbert n => -selectedCoefficient s (allocationRepair u)) ''
      selectedFeasible n s) := by
    refine ⟨-(∫ x in Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n), archLevySinhWeight x), ?_⟩
    rintro _ ⟨u, _, rfl⟩
    exact neg_le_neg (selectedCoefficient_le_physical_mass s (allocationRepair u))
  have heq (t : ℝ) : {u : AllocationHilbert n | u ∈ selectedFeasible n s ∧
        -selectedCoefficient s (allocationRepair u) ≤ t} =
      selectedFeasible n s ∩ {u | u ∈ allocationFeasible n ∧
        -selectedCoefficient s (allocationRepair u) ≤ t} := by
    ext u
    exact ⟨fun h => ⟨h.1, selectedFeasible_subset n s h.1, h.2⟩,
      fun h => ⟨h.1, h.2.2⟩⟩
  obtain ⟨u, hu, hmin⟩ := exists_isMinOn_closedConvex_sublevels
    (selectedFeasible n s) (selectedFeasible_nonempty n s) (isClosed_selectedFeasible n s)
    (convex_selectedFeasible n s)
    (measureUnivNNReal (allocationMeasure n) ^ (2 : ℝ≥0∞).toReal⁻¹)
    (fun _ h => norm_allocationFeasible_le (selectedFeasible_subset n s h))
    (fun u => -selectedCoefficient s (allocationRepair u)) hb
    (fun t => by rw [heq]; exact (isClosed_selectedFeasible n s).inter (isClosed_selectedCoefficient_sublevel s t))
    (fun t => by rw [heq]; exact (convex_selectedFeasible n s).inter (convex_selectedCoefficient_sublevel s t))
  have hclass : allocationClass (allocationRepair u) = u :=
    allocationClass_repair (selectedFeasible_subset n s hu)
  have hsel : allocationClass (allocationRepair u) ∈ selectedFeasible n s := hclass.symm ▸ hu
  refine ⟨selectedRepair s (allocationRepair u), selectedRepair_isSelected s _, fun η hη => ?_⟩
  have h := hmin (allocationClass_selected hη)
  change -selectedCoefficient s (allocationRepair u) ≤
    -selectedCoefficient s (allocationRepair (allocationClass η)) at h
  rw [selectedCoefficient_eq_of_class_eq s (allocationClass_repair (allocationClass_mem η))] at h
  rw [selectedCoefficient_eq_of_class_eq s (allocationClass_selectedRepair hsel)]
  linarith

/-- Exact selected-grid physical partition identity; gaps outside the selected union carry zero. -/
theorem selectedShare_partition {n : ℕ} {s : Finset ℕ} {ρ : PhysicalCollarPartition n}
    (hρ : IsSelectedPartition s ρ) (x : ℝ) :
    (∑ k ∈ selectedIndices n s, ρ.share k x) =
      (selectedUnion n s).indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : x ∈ selectedUnion n s
  · rw [indicator_of_mem hx]
    have hp := ρ.partition x
    rw [indicator_of_mem (selectedUnion_subset n s hx)] at hp
    rw [← hp]
    apply sum_subset (filter_subset _ _)
    intro k hk hks
    exact hρ k hk (by simpa [selectedIndices, hk] using hks) x hx
  · rw [indicator_of_notMem hx]
    apply sum_eq_zero
    intro k hk
    apply ρ.supported
    intro hxk
    apply hx
    simp only [selectedUnion, mem_iUnion]
    exact ⟨k, hk, hxk⟩

/-- Indices of any finite collection of actual prime powers, with no factorial-grid restriction. -/
def primePowerGridIndices (P : Finset ℕ) : Finset ℕ := P.image (fun m => m - 2)

def primePowerGridWindow (P : Finset ℕ) : ℕ := P.sup id

theorem primePowerGrid_node (P : Finset ℕ) (hP : ∀ m ∈ P, IsPrimePow m)
    {m : ℕ} (hm : m ∈ P) :
    m - 2 ∈ selectedIndices (primePowerGridWindow P) (primePowerGridIndices P) ∧
      logarithmicCollarNode (m - 2) = Real.log (m : ℝ) := by
  have h2 := (hP m hm).two_le
  have hmN : m ≤ primePowerGridWindow P := Finset.le_sup (f := id) hm
  refine ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), mem_image.mpr ⟨m, hm, rfl⟩⟩, ?_⟩
  simp only [logarithmicCollarNode, Nat.sub_add_cancel h2]

/-- The actual finite prime-power-grid coefficient attains its supremum over its original
measurable physical partitions, with the selected mass spent exactly on the collar union. -/
theorem exists_primePowerGrid_collar_optimizer (P : Finset ℕ)
    (hP : ∀ m ∈ P, IsPrimePow m) :
    ∃ ρ : PhysicalCollarPartition (primePowerGridWindow P),
      IsSelectedPartition (primePowerGridIndices P) ρ ∧
      (∀ x, (∑ k ∈ selectedIndices (primePowerGridWindow P) (primePowerGridIndices P), ρ.share k x) =
        (selectedUnion (primePowerGridWindow P) (primePowerGridIndices P)).indicator (fun _ => (1 : ℝ)) x) ∧
      (∀ m ∈ P, logarithmicCollarNode (m - 2) = Real.log (m : ℝ)) ∧
      ∀ η : PhysicalCollarPartition (primePowerGridWindow P),
        IsSelectedPartition (primePowerGridIndices P) η →
        selectedCoefficient (primePowerGridIndices P) η ≤ selectedCoefficient (primePowerGridIndices P) ρ := by
  obtain ⟨ρ, hρ, hmax⟩ := exists_selectedPartition_maximizer (primePowerGridWindow P) (primePowerGridIndices P)
  exact ⟨ρ, hρ, selectedShare_partition hρ, fun m hm => (primePowerGrid_node P hP hm).2, hmax⟩

end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

end
