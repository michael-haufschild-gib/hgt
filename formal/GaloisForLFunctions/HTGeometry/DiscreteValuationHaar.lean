import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Residue cardinality and additive Haar scaling

For a nontrivial integer-valued field with compact valuation ring, reduction has
finite index equal to the residue cardinality. Its kernel is a uniformizer multiple
of the integer ring. The finite-index measure formula therefore identifies the
additive Haar scaling of a uniformizer exactly.
-/

namespace GaloisForLFunctions.HTGeometry.DiscreteValuationHaar

open MeasureTheory MeasureTheory.Measure
open scoped WithZero WithZeroMulInt Pointwise ENNReal NNReal

noncomputable section

variable (K : Type*) [Field K] [Valued K ℤᵐ⁰]

abbrev Integer := (Valued.v : Valuation K ℤᵐ⁰).integer
abbrev Residue := IsLocalRing.ResidueField (Integer K)

variable [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)]

local instance : (Valued.v : Valuation K ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 from one_lt_two)

local instance : NormedField K := Valued.toNormedField K ℤᵐ⁰

local instance : ProperSpace K :=
  Valued.integer.properSpace_iff_compactSpace_integer.mpr inferInstance

local instance : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩

local instance : IsDiscreteValuationRing (Integer K) :=
  (Valued.v : Valuation K ℤᵐ⁰).valuationSubring_isDiscreteValuationRing

instance residue_finite : Finite (Residue K) :=
  (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstance : CompactSpace (Integer K))).2.2

/-- The compact open integer ring fixes additive Haar normalization. -/
def integerPositiveCompacts : TopologicalSpace.PositiveCompacts K where
  carrier := (Valued.v : Valuation K ℤᵐ⁰).integer
  isCompact' := isCompact_iff_compactSpace.mpr inferInstance
  interior_nonempty' := by
    have hopen : IsOpen ((Valued.v : Valuation K ℤᵐ⁰).integer : Set K) :=
      Valued.isOpen_valuationSubring K
    rw [hopen.interior_eq]
    refine ⟨0, ?_⟩
    change (Valued.v : Valuation K ℤᵐ⁰) 0 ≤ 1
    rw [map_zero]
    exact zero_le_one

def normalizedHaar : Measure K := Measure.addHaarMeasure (integerPositiveCompacts K)

instance normalizedHaar_isAddHaar : (normalizedHaar K).IsAddHaarMeasure := by
  unfold normalizedHaar
  infer_instance

instance normalizedHaar_regular : (normalizedHaar K).Regular := by
  unfold normalizedHaar
  infer_instance

@[simp] theorem normalizedHaar_integer :
    normalizedHaar K ((Valued.v : Valuation K ℤᵐ⁰).integer : Set K) = 1 :=
  Measure.addHaarMeasure_self

/-- Additive kernel of the actual residue homomorphism. -/
def residueKernel : AddSubgroup (Integer K) :=
  (IsLocalRing.residue (Integer K)).toAddMonoidHom.ker

instance residueKernel_finiteIndex : (residueKernel K).FiniteIndex := by
  unfold residueKernel
  infer_instance

omit [CompactSpace (Integer K)] in
theorem residueKernel_index : (residueKernel K).index = Nat.card (Residue K) := by
  rw [residueKernel, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.mpr (IsLocalRing.residue_surjective (R := Integer K))]
  simp

omit [CompactSpace (Integer K)] in
theorem residueKernel_mem_iff (x : Integer K) :
    x ∈ residueKernel K ↔ Valued.v (x : K) < 1 := by
  change IsLocalRing.residue (Integer K) x = 0 ↔ _
  rw [IsLocalRing.residue_eq_zero_iff]
  exact Valuation.mem_maximalIdeal_iff K (Valued.v : Valuation K ℤᵐ⁰)

omit [CompactSpace (Integer K)] in
theorem residueKernel_measurableSet : MeasurableSet (residueKernel K : Set (Integer K)) := by
  have hball : IsOpen {x : K | Valued.v x < 1} := by
    simpa only [Valuation.restrict_lt_one_iff] using Valued.isOpen_ball K 1
  have hset : (residueKernel K : Set (Integer K)) =
      ((↑) : Integer K → K) ⁻¹' {x : K | Valued.v x < 1} := by
    ext x
    exact residueKernel_mem_iff K x
  rw [hset]
  exact (hball.preimage continuous_subtype_val).measurableSet

/-- A valuation-ring uniformizer viewed as a nonzero field element. -/
def uniformizerUnit (π : Integer K) (hπ : Irreducible π) : Kˣ :=
  Units.mk0 (π : K) (fun h => hπ.ne_zero (Subtype.ext h))

omit [CompactSpace (Integer K)] in
theorem residueKernel_image (π : Integer K) (hπ : Irreducible π) :
    ((↑) : Integer K → K) '' (residueKernel K : Set (Integer K)) =
      uniformizerUnit K π hπ • ((Valued.v : Valuation K ℤᵐ⁰).integer : Set K) := by
  have hker (x : Integer K) : x ∈ residueKernel K ↔ x ∈ Ideal.span {π} := by
    change IsLocalRing.residue (Integer K) x = 0 ↔ _
    rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp ((hker y).mp hy)
    rw [Set.mem_smul_set]
    refine ⟨(z : K), z.2, ?_⟩
    change (π : K) * z = (y : K)
    have hz' : π * z = y := by simpa only [mul_comm] using hz
    exact congrArg ((↑) : Integer K → K) hz'
  · rw [Set.mem_smul_set]
    rintro ⟨y, hy, rfl⟩
    refine ⟨π * ⟨y, hy⟩, (hker _).mpr ?_, rfl⟩
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton π))

/-- Multiplication by a uniformizer scales additive Haar measure by the inverse residue size. -/
theorem uniformizer_distribHaarChar (π : Integer K) (hπ : Irreducible π) :
    distribHaarChar K (uniformizerUnit K π hπ) = (Nat.card (Residue K) : ℝ≥0)⁻¹ := by
  let μ : Measure K := normalizedHaar K
  let s : Set K := (Valued.v : Valuation K ℤᵐ⁰).integer
  have hμs : μ s = 1 := normalizedHaar_integer K
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := s)
    (by rw [hμs]; exact one_ne_zero) (by rw [hμs]; exact ENNReal.one_ne_top)
  let f : Integer K →+ K := (Valued.v : Valuation K ℤᵐ⁰).integer.subtype.toAddMonoidHom
  let ν : Measure (Integer K) := μ.comap f
  have hopen : IsOpen ((Valued.v : Valuation K ℤᵐ⁰).integer : Set K) :=
    Valued.isOpen_valuationSubring K
  letI : IsAddLeftInvariant ν :=
    IsAddLeftInvariant.comap μ hopen.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hindex := AddSubgroup.index_mul_measure (residueKernel K)
    (residueKernel_measurableSet K) ν
  rw [residueKernel_index K] at hindex
  have hkernel : ν (residueKernel K) =
      μ (((↑) : Integer K → K) '' (residueKernel K : Set (Integer K))) :=
    comap_subtype_coe_apply hopen.measurableSet μ _
  have huniv : ν Set.univ = μ s := by
    rw [show ν Set.univ = μ (((↑) : Integer K → K) '' Set.univ) from
      comap_subtype_coe_apply hopen.measurableSet μ _]
    congr 1
    exact Subtype.coe_image_univ _
  rw [hkernel, huniv, residueKernel_image K π hπ] at hindex
  change (Nat.card (Residue K) : ℝ≥0∞) * μ (uniformizerUnit K π hπ • s) = μ s at hindex
  have hq : Nat.card (Residue K) ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hq' : (Nat.card (Residue K) : ℝ≥0) ≠ 0 := by exact_mod_cast hq
  rw [← hindex, ENNReal.coe_inv hq', ENNReal.coe_natCast,
    ENNReal.inv_mul_cancel_left (by exact_mod_cast hq) (by simp)]

end
end GaloisForLFunctions.HTGeometry.DiscreteValuationHaar

