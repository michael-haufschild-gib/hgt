import GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import GaloisForLFunctions.HTGeometry.ClosedConvexHilbertAttainment

/-!
# Exact Hilbert coordinates for physical collar partitions

The original measurable shares form a bounded closed convex subset of a concrete finite-vector L2 space. Every feasible L2 class is repaired on exceptional representatives to an original pointwise physical partition; no relaxation gap is assumed.
-/

set_option autoImplicit false
open MeasureTheory Set Filter Topology Finset
open scoped BigOperators ENNReal InnerProductSpace
open GaloisForLFunctions.HTGeometry
noncomputable section


namespace GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

def allocationMeasure (n : ℕ) : Measure ℝ :=
  volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n))

instance allocationMeasure_finite (n : ℕ) : IsFiniteMeasure (allocationMeasure n) :=
  inferInstanceAs (IsFiniteMeasure
    (volume.restrict (Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n))))

abbrev AllocationVector (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))
abbrev AllocationHilbert (n : ℕ) := Lp (AllocationVector n) 2 (allocationMeasure n)

/-- Exactly the original nonnegativity, collar support and physical partition constraints. -/
def allocationFibre (n : ℕ) (x : ℝ) : Set (AllocationVector n) :=
  {v | (∀ k, 0 ≤ v k) ∧
    (∀ k, x ∉ logarithmicPhysicalCollar n k.val → v k = 0) ∧ ∑ k, v k = 1}

theorem isClosed_allocationFibre (n : ℕ) (x : ℝ) : IsClosed (allocationFibre n x) := by
  simp only [allocationFibre, setOf_and, setOf_forall]
  apply IsClosed.inter
  · exact isClosed_iInter (fun k => isClosed_le continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) k))
  · apply IsClosed.inter
    · exact isClosed_iInter (fun k => isClosed_iInter (fun _ =>
        isClosed_eq (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) k) continuous_const))
    · exact isClosed_eq (by fun_prop) continuous_const

theorem convex_allocationFibre (n : ℕ) (x : ℝ) : Convex ℝ (allocationFibre n x) := by
  intro u hu v hv a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro k
    change 0 ≤ a * u k + b * v k
    exact add_nonneg (mul_nonneg ha (hu.1 k)) (mul_nonneg hb (hv.1 k))
  · intro k hk
    change a * u k + b * v k = 0
    rw [hu.2.1 k hk, hv.2.1 k hk]
    ring
  · change (∑ k, (a * u k + b * v k)) = 1
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hu.2.2, hv.2.2, mul_one, mul_one]
    exact hab

theorem norm_le_one_of_mem_allocationFibre {n : ℕ} {x : ℝ} {v : AllocationVector n}
    (hv : v ∈ allocationFibre n x) : ‖v‖ ≤ 1 := by
  have hsq : ‖v‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, ← hv.2.2]
    apply sum_le_sum
    intro k _
    have hk : v k ≤ 1 := by
      rw [← hv.2.2]
      exact single_le_sum (fun j _ => hv.1 j) (mem_univ k)
    nlinarith [hv.1 k]
  nlinarith [norm_nonneg v]

def allocationFeasible (n : ℕ) : Set (AllocationHilbert n) :=
  {u | ∀ᵐ x ∂allocationMeasure n, u x ∈ allocationFibre n x}

theorem isClosed_allocationFeasible (n : ℕ) : IsClosed (allocationFeasible n) :=
  isClosed_L2_fibreConstraints (allocationMeasure n) (allocationFibre n) (isClosed_allocationFibre n)

theorem convex_allocationFeasible (n : ℕ) : Convex ℝ (allocationFeasible n) :=
  convex_L2_fibreConstraints (allocationMeasure n) (allocationFibre n) (convex_allocationFibre n)

theorem norm_allocationFeasible_le {n : ℕ} {u : AllocationHilbert n}
    (hu : u ∈ allocationFeasible n) :
    ‖u‖ ≤ measureUnivNNReal (allocationMeasure n) ^ (2 : ℝ≥0∞).toReal⁻¹ := by
  change (∀ᵐ x ∂allocationMeasure n, u x ∈ allocationFibre n x) at hu
  simpa only [mul_one] using Lp.norm_le_of_ae_bound (f := u) zero_le_one
    (hu.mono (fun _ hx => norm_le_one_of_mem_allocationFibre hx))

def allocationVector {n : ℕ} (ρ : PhysicalCollarPartition n) (x : ℝ) : AllocationVector n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm (fun k => ρ.share k.val x)

theorem allocationVector_mem {n : ℕ} (ρ : PhysicalCollarPartition n) {x : ℝ}
    (hx : x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n)) :
    allocationVector ρ x ∈ allocationFibre n x := by
  refine ⟨fun k => ρ.nonneg k.val x, fun k hk => ρ.supported k.val x hk, ?_⟩
  change (∑ k : Fin (n + 1), ρ.share k.val x) = 1
  rw [Fin.sum_univ_eq_sum_range (fun k => ρ.share k x), ρ.partition, indicator_of_mem hx]

theorem measurable_allocationVector {n : ℕ} (ρ : PhysicalCollarPartition n) :
    Measurable (allocationVector ρ) := by
  apply (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).measurable.comp
  exact measurable_pi_lambda _ (fun k => ρ.measurable_share k.val)

theorem memLp_allocationVector {n : ℕ} (ρ : PhysicalCollarPartition n) :
    MemLp (allocationVector ρ) 2 (allocationMeasure n) := by
  apply MemLp.of_bound (measurable_allocationVector ρ).aestronglyMeasurable 1
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact norm_le_one_of_mem_allocationFibre (allocationVector_mem ρ hx)

def allocationClass {n : ℕ} (ρ : PhysicalCollarPartition n) : AllocationHilbert n :=
  (memLp_allocationVector ρ).toLp (allocationVector ρ)

theorem allocationClass_mem {n : ℕ} (ρ : PhysicalCollarPartition n) :
    allocationClass ρ ∈ allocationFeasible n := by
  filter_upwards [(memLp_allocationVector ρ).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioo] with x hx hxI
  change (memLp_allocationVector ρ).toLp (allocationVector ρ) x ∈ allocationFibre n x
  rw [hx]
  exact allocationVector_mem ρ hxI

theorem allocationFeasible_nonempty (n : ℕ) : (allocationFeasible n).Nonempty :=
  ⟨allocationClass (equalMultiplicity n), allocationClass_mem _⟩

def allocationGoodSet {n : ℕ} (u : AllocationHilbert n) : Set ℝ :=
  {x | x ∈ Ioo logarithmicCollarRadius (logarithmicCollarEndpoint n) ∧
    u x ∈ allocationFibre n x}

theorem measurableSet_allocationGoodSet {n : ℕ} (u : AllocationHilbert n) :
    MeasurableSet (allocationGoodSet u) := by
  have hcoord (k : Fin (n + 1)) : Measurable (fun x => u x k) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) k).measurable.comp
      (Lp.stronglyMeasurable u).measurable
  have hnon : MeasurableSet {x | ∀ k, 0 ≤ u x k} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k => measurableSet_le measurable_const (hcoord k))
  have hsupp : MeasurableSet {x | ∀ k : Fin (n + 1),
      x ∉ logarithmicPhysicalCollar n k.val → u x k = 0} := by
    simp only [setOf_forall, imp_iff_not_or, not_not, setOf_or]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.union
    · exact measurableSet_Ioo.inter measurableSet_Ioo
    · exact measurableSet_eq_fun (hcoord k) measurable_const
  have hsum : MeasurableSet {x | (∑ k, u x k) = 1} :=
    measurableSet_eq_fun (Finset.measurable_sum _ (fun k _ => hcoord k)) measurable_const
  exact measurableSet_Ioo.inter (hnon.inter (hsupp.inter hsum))

local instance {n : ℕ} (u : AllocationHilbert n) (x : ℝ) :
    Decidable (x ∈ allocationGoodSet u) := Classical.propDecidable _

def repairedShare {n : ℕ} (u : AllocationHilbert n) (k : ℕ) (x : ℝ) : ℝ :=
  if hk : k < n + 1 then
    if x ∈ allocationGoodSet u then u x ⟨k, hk⟩ else (equalMultiplicity n).share k x
  else 0

theorem repairedShare_active {n : ℕ} (u : AllocationHilbert n) {k : ℕ}
    (hk : k < n + 1) (x : ℝ) :
    repairedShare u k x =
      if x ∈ allocationGoodSet u then u x ⟨k, hk⟩ else (equalMultiplicity n).share k x :=
  dif_pos hk

/-- Repair only the exceptional representatives; every resulting share is pointwise admissible. -/
def allocationRepair {n : ℕ} (u : AllocationHilbert n) : PhysicalCollarPartition n where
  share := repairedShare u
  measurable_share k := by
    by_cases hk : k < n + 1
    · have heq : repairedShare u k = fun x => if x ∈ allocationGoodSet u then u x ⟨k, hk⟩
          else (equalMultiplicity n).share k x := funext (fun x => repairedShare_active u hk x)
      rw [heq]
      exact Measurable.ite (measurableSet_allocationGoodSet u)
        ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) ⟨k, hk⟩).measurable.comp
          (Lp.stronglyMeasurable u).measurable)
        ((equalMultiplicity n).measurable_share k)
    · change Measurable (fun x => repairedShare u k x)
      simp only [repairedShare, dif_neg hk]
      exact measurable_const
  nonneg k x := by
    by_cases hk : k < n + 1
    · rw [repairedShare_active u hk]
      split_ifs with hx
      · exact hx.2.1 ⟨k, hk⟩
      · exact (equalMultiplicity n).nonneg k x
    · simp only [repairedShare, dif_neg hk, le_refl]
  supported k x hx := by
    by_cases hk : k < n + 1
    · rw [repairedShare_active u hk]
      split_ifs with hgood
      · exact hgood.2.2.1 ⟨k, hk⟩ hx
      · exact (equalMultiplicity n).supported k x hx
    · exact dif_neg hk
  partition x := by
    by_cases hx : x ∈ allocationGoodSet u
    · rw [indicator_of_mem hx.1]
      calc (∑ k ∈ range (n + 1), repairedShare u k x) =
          (∑ k : Fin (n + 1), repairedShare u k.val x) :=
            (Fin.sum_univ_eq_sum_range (fun k => repairedShare u k x) (n + 1)).symm
        _ = (∑ k : Fin (n + 1), u x k) := by
          apply sum_congr rfl
          intro k hk
          rw [repairedShare_active u k.isLt, if_pos hx]
        _ = 1 := hx.2.2.2
    · rw [← (equalMultiplicity n).partition x]
      apply sum_congr rfl
      intro k hk
      rw [repairedShare_active u (mem_range.mp hk), if_neg hx]

/-- No a.e. relaxation gap: every feasible Hilbert vector has an original physical partition. -/
theorem allocationClass_repair {n : ℕ} {u : AllocationHilbert n}
    (hu : u ∈ allocationFeasible n) : allocationClass (allocationRepair u) = u := by
  apply Lp.ext
  filter_upwards [(memLp_allocationVector (allocationRepair u)).coeFn_toLp,
    hu, ae_restrict_mem measurableSet_Ioo] with x hx hux hxI
  change (memLp_allocationVector (allocationRepair u)).toLp
    (allocationVector (allocationRepair u)) x = u x
  rw [hx]
  ext k
  change repairedShare u k.val x = u x k
  rw [repairedShare_active u k.isLt, if_pos (show x ∈ allocationGoodSet u from ⟨hxI, hux⟩)]

theorem allocationClass_range (n : ℕ) :
    Set.range (allocationClass (n := n)) = allocationFeasible n := by
  ext u
  constructor
  · rintro ⟨ρ, rfl⟩
    exact allocationClass_mem ρ
  · intro hu
    exact ⟨allocationRepair u, allocationClass_repair hu⟩

end GaloisForLFunctions.BiScaleUncertainty.PhysicalCollarPartition

end
