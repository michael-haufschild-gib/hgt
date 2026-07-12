import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Order.SuccPred.IntervalSucc
import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryAlgebra
import GaloisForLFunctions.HTGeometry.LinftyPositiveAperture
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open ProbabilityTheory

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]

theorem continuous_cdf_of_noAtoms : Continuous (cdf μ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hzero : (cdf μ).measure {x} = 0 := by
    rw [measure_cdf μ]
    exact measure_singleton x
  rw [StieltjesFunction.measure_singleton] at hzero
  have hdiff : cdf μ x - Function.leftLim (cdf μ) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hzero
  have hleft : Function.leftLim (cdf μ) x = cdf μ x := by
    apply le_antisymm
    · exact (monotone_cdf μ).leftLim_le le_rfl
    · linarith
  rw [(monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim]
  rw [hleft, (cdf μ).rightLim_eq]

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open ProbabilityTheory
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]

theorem exists_cdf_eq_of_mem_Ioo {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ∃ x : ℝ, cdf μ x = q := by
  have haev : ∀ᶠ x : ℝ in atBot, cdf μ x < q :=
    (tendsto_cdf_atBot μ) (Iio_mem_nhds hq.1)
  have hbev : ∀ᶠ x : ℝ in atTop, q < cdf μ x :=
    (tendsto_cdf_atTop μ) (Ioi_mem_nhds hq.2)
  obtain ⟨a, ha⟩ := haev.exists
  obtain ⟨b, hb⟩ := hbev.exists
  exact intermediate_value_univ a b (continuous_cdf_of_noAtoms μ)
    ⟨ha.le, hb.le⟩

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open ProbabilityTheory

def partitionQuantile (n : ℕ) : ℝ := (n + 1 : ℝ) / (n + 2 : ℝ)

lemma partitionQuantile_mem_Ioo (n : ℕ) : partitionQuantile n ∈ Ioo (0 : ℝ) 1 := by
  dsimp [partitionQuantile]
  constructor
  · positivity
  · rw [div_lt_one (by positivity)]
    norm_num

lemma partitionQuantile_strictMono : StrictMono partitionQuantile := by
  intro n m hnm
  dsimp [partitionQuantile]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  nlinarith

variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]

noncomputable def cdfPartitionCut (n : ℕ) : ℝ :=
  Classical.choose (exists_cdf_eq_of_mem_Ioo μ (partitionQuantile_mem_Ioo n))

lemma cdf_cdfPartitionCut (n : ℕ) : cdf μ (cdfPartitionCut μ n) = partitionQuantile n :=
  Classical.choose_spec (exists_cdf_eq_of_mem_Ioo μ (partitionQuantile_mem_Ioo n))

lemma cdfPartitionCut_strictMono : StrictMono (cdfPartitionCut μ) := by
  intro n m hnm
  by_contra h
  have hle : cdfPartitionCut μ m ≤ cdfPartitionCut μ n := le_of_not_gt h
  have hcdf := monotone_cdf μ hle
  rw [cdf_cdfPartitionCut, cdf_cdfPartitionCut] at hcdf
  exact (not_le_of_gt (partitionQuantile_strictMono hnm)) hcdf

noncomputable def cdfPartitionPiece (n : ℕ) : Set ℝ :=
  Ioc (cdfPartitionCut μ n) (cdfPartitionCut μ (n + 1))

lemma measurableSet_cdfPartitionPiece (n : ℕ) : MeasurableSet (cdfPartitionPiece μ n) :=
  measurableSet_Ioc

lemma measure_cdfPartitionPiece_ne_zero (n : ℕ) : μ (cdfPartitionPiece μ n) ≠ 0 := by
  have h : (cdf μ).measure
      (Ioc (cdfPartitionCut μ n) (cdfPartitionCut μ (n + 1))) ≠ 0 := by
    rw [StieltjesFunction.measure_Ioc, cdf_cdfPartitionCut, cdf_cdfPartitionCut]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (sub_pos.mpr (partitionQuantile_strictMono (Nat.lt_succ_self n))))
  simpa only [cdfPartitionPiece, measure_cdf μ] using h

lemma cdfPartitionPiece_pairwiseDisjoint :
    Pairwise (fun n m => Disjoint (cdfPartitionPiece μ n) (cdfPartitionPiece μ m)) := by
  simpa only [cdfPartitionPiece, Order.succ_eq_add_one] using
    (cdfPartitionCut_strictMono μ).monotone.pairwise_disjoint_on_Ioc_succ

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open ProbabilityTheory
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]

noncomputable def realCdfBlockPiece {k : ℕ} (j : ℕ) (l : Fin (k + 1)) : Set ℝ :=
  cdfPartitionPiece μ (Nat.pair j l)

lemma measurableSet_realCdfBlockPiece {k : ℕ} (j : ℕ) (l : Fin (k + 1)) :
    MeasurableSet (realCdfBlockPiece μ j l) :=
  measurableSet_cdfPartitionPiece μ _

lemma measure_realCdfBlockPiece_ne_zero {k : ℕ} (j : ℕ) (l : Fin (k + 1)) :
    μ (realCdfBlockPiece μ j l) ≠ 0 :=
  measure_cdfPartitionPiece_ne_zero μ _

lemma realCdfBlockPiece_disjoint {k : ℕ}
    (j m : ℕ) (l r : Fin (k + 1)) (h : (j, l) ≠ (m, r)) :
    Disjoint (realCdfBlockPiece μ j l) (realCdfBlockPiece μ m r) := by
  apply cdfPartitionPiece_pairwiseDisjoint μ
  intro hpair
  apply h
  rw [Nat.pair_eq_pair] at hpair
  exact Prod.ext hpair.1 (Fin.ext hpair.2)

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Filter Set OnePoint
open scoped ENNReal Topology OnePoint
noncomputable section

noncomputable def onePointRealPartMeasure (η : Measure (OnePoint ℝ)) : Measure ℝ :=
  Measure.comap ((↑) : ℝ → OnePoint ℝ) η

lemma onePoint_coe_measurableEmbedding :
    MeasurableEmbedding ((↑) : ℝ → OnePoint ℝ) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding

variable (η : Measure (OnePoint ℝ)) [IsProbabilityMeasure η] [NoAtoms η]

omit [IsProbabilityMeasure η] in
lemma onePointRealPart_ae_range : ∀ᵐ t ∂η, t ∈ Set.range ((↑) : ℝ → OnePoint ℝ) := by
  rw [ae_iff]
  change η (Set.range ((↑) : ℝ → OnePoint ℝ))ᶜ = 0
  rw [OnePoint.compl_range_coe]
  exact measure_singleton (∞ : OnePoint ℝ)

@[reducible] noncomputable def onePointRealPart_isProbabilityMeasure :
    IsProbabilityMeasure (onePointRealPartMeasure η) :=
  onePoint_coe_measurableEmbedding.isProbabilityMeasure_comap
    (onePointRealPart_ae_range η)

@[reducible] noncomputable def onePointRealPart_noAtoms : NoAtoms (onePointRealPartMeasure η) where
  measure_singleton x := by
    rw [onePointRealPartMeasure, Measure.comap_apply _ (onePoint_coe_measurableEmbedding.injective)
      onePoint_coe_measurableEmbedding.measurableSet_image' _ (measurableSet_singleton x)]
    rw [Set.image_singleton]
    exact measure_singleton (x : OnePoint ℝ)

noncomputable def onePointCdfBlockPiece {k : ℕ} (j : ℕ) (l : Fin (k + 1)) :
    Set (OnePoint ℝ) := by
  letI : IsProbabilityMeasure (onePointRealPartMeasure η) :=
    onePointRealPart_isProbabilityMeasure η
  letI : NoAtoms (onePointRealPartMeasure η) := onePointRealPart_noAtoms η
  exact ((↑) : ℝ → OnePoint ℝ) '' realCdfBlockPiece (onePointRealPartMeasure η) j l

lemma measurableSet_onePointCdfBlockPiece {k : ℕ} (j : ℕ) (l : Fin (k + 1)) :
    MeasurableSet (onePointCdfBlockPiece η j l) := by
  apply onePoint_coe_measurableEmbedding.measurableSet_image'
  letI : IsProbabilityMeasure (onePointRealPartMeasure η) :=
    onePointRealPart_isProbabilityMeasure η
  letI : NoAtoms (onePointRealPartMeasure η) := onePointRealPart_noAtoms η
  exact measurableSet_realCdfBlockPiece (onePointRealPartMeasure η) j l

lemma measure_onePointCdfBlockPiece_ne_zero {k : ℕ} (j : ℕ) (l : Fin (k + 1)) :
    η (onePointCdfBlockPiece η j l) ≠ 0 := by
  letI : IsProbabilityMeasure (onePointRealPartMeasure η) :=
    onePointRealPart_isProbabilityMeasure η
  letI : NoAtoms (onePointRealPartMeasure η) := onePointRealPart_noAtoms η
  rw [onePointCdfBlockPiece, ← Measure.comap_apply _
    onePoint_coe_measurableEmbedding.injective
    onePoint_coe_measurableEmbedding.measurableSet_image' _
    (measurableSet_realCdfBlockPiece (onePointRealPartMeasure η) j l)]
  exact measure_realCdfBlockPiece_ne_zero (onePointRealPartMeasure η) j l

lemma onePointCdfBlockPiece_disjoint {k : ℕ}
    (j m : ℕ) (l r : Fin (k + 1)) (h : (j, l) ≠ (m, r)) :
    Disjoint (onePointCdfBlockPiece η j l) (onePointCdfBlockPiece η m r) := by
  letI : IsProbabilityMeasure (onePointRealPartMeasure η) :=
    onePointRealPart_isProbabilityMeasure η
  letI : NoAtoms (onePointRealPartMeasure η) := onePointRealPart_noAtoms η
  exact Set.disjoint_image_of_injective onePoint_coe_measurableEmbedding.injective
    (realCdfBlockPiece_disjoint (onePointRealPartMeasure η) j m l r h)

end
end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Filter Set OnePoint
open scoped ENNReal Topology OnePoint
noncomputable section

/-- **Atomless projective finite-constraint aperture.** For an atomless probability law on the
real projective line, every finite continuous-linear constraint fiber through density one contains
a closed embedded Hilbert cube of strictly positive densities. -/
theorem exists_positive_closedEmbeddedHilbertCube_in_atomlessProjectiveConstraintFiber
    (η : Measure (OnePoint ℝ)) [IsProbabilityMeasure η] [NoAtoms η]
    {k : ℕ} (T : (Lp ℝ ⊤ η) →L[ℝ] (Fin k → ℝ))
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ v : ℕ → Lp ℝ ⊤ η,
      ∃ ell : ℕ → (Lp ℝ ⊤ η) →L[ℝ] ℝ,
      (∀ n, ‖v n‖ = 1) ∧ (∀ n, T (v n) = 0) ∧
      (∀ n m, ell n (v m) = if n = m then 1 else 0) ∧
      Topology.IsClosedEmbedding
        (affinePositiveHilbertCubeMap (linftyOne η) delta v) ∧
      ∀ t : SignedHilbertCube,
        T (affinePositiveHilbertCubeMap (linftyOne η) delta v t) = T (linftyOne η) ∧
        LinftyStrictlyPositive η
          (affinePositiveHilbertCubeMap (linftyOne η) delta v t) := by
  exact exists_positive_closedEmbeddedHilbertCube_in_linfty_finiteConstraintFiber
    η T hdelta0 hdelta1 (onePointCdfBlockPiece η)
    (measurableSet_onePointCdfBlockPiece η)
    (measure_onePointCdfBlockPiece_ne_zero η)
    (fun j l m r h => onePointCdfBlockPiece_disjoint η j m l r h)

end
end GaloisForLFunctions.HTGeometry
