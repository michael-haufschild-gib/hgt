import GaloisForLFunctions.HTGeometry.LinftyPositiveAperture
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.NatEmbedding

/-!
# Infinite support forces positive Hilbert-cube apertures

An infinite Hausdorff support contains countably many pairwise-disjoint nonempty open subsets.
Intersecting their ambient realizations with the measure support turns them into measurable sets
of positive measure. Consequently every finite continuous-linear constraint fiber through the
constant-one density contains a closed Hilbert cube of strictly positive densities whenever the
underlying finite Borel measure has infinite topological support. No atomlessness assumption is
needed.
-/

namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Set Topology
open scoped Topology ENNReal
noncomputable section

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [T2Space X] [HereditarilyLindelofSpace X]
  (μ : Measure X)

noncomputable def infiniteSupportOpenPieces (hμ : μ.support.Infinite) :
    ℕ → Set μ.support := by
  letI : Infinite μ.support := hμ.to_subtype
  exact Classical.choose (exists_seq_infinite_isOpen_pairwise_disjoint μ.support)

omit [BorelSpace X] [HereditarilyLindelofSpace X] in
lemma infiniteSupportOpenPieces_infinite (hμ : μ.support.Infinite) (n : ℕ) :
    (infiniteSupportOpenPieces μ hμ n).Infinite := by
  letI : Infinite μ.support := hμ.to_subtype
  exact (Classical.choose_spec
    (exists_seq_infinite_isOpen_pairwise_disjoint μ.support)).1 n

omit [BorelSpace X] [HereditarilyLindelofSpace X] in
lemma infiniteSupportOpenPieces_isOpen (hμ : μ.support.Infinite) (n : ℕ) :
    IsOpen (infiniteSupportOpenPieces μ hμ n) := by
  letI : Infinite μ.support := hμ.to_subtype
  exact (Classical.choose_spec
    (exists_seq_infinite_isOpen_pairwise_disjoint μ.support)).2.1 n

omit [BorelSpace X] [HereditarilyLindelofSpace X] in
lemma infiniteSupportOpenPieces_pairwiseDisjoint (hμ : μ.support.Infinite) :
    Pairwise (fun n m => Disjoint (infiniteSupportOpenPieces μ hμ n)
      (infiniteSupportOpenPieces μ hμ m)) := by
  letI : Infinite μ.support := hμ.to_subtype
  exact (Classical.choose_spec
    (exists_seq_infinite_isOpen_pairwise_disjoint μ.support)).2.2

noncomputable def infiniteSupportPositivePieces (hμ : μ.support.Infinite) : ℕ → Set X :=
  fun n => Subtype.val '' infiniteSupportOpenPieces μ hμ n

omit [HereditarilyLindelofSpace X] in
lemma measurableSet_infiniteSupportPositivePieces (hμ : μ.support.Infinite) (n : ℕ) :
    MeasurableSet (infiniteSupportPositivePieces μ hμ n) := by
  apply (MeasurableEmbedding.subtype_coe Measure.isClosed_support.measurableSet).measurableSet_image'
  exact (infiniteSupportOpenPieces_isOpen μ hμ n).measurableSet

omit [BorelSpace X] [HereditarilyLindelofSpace X] in
lemma infiniteSupportPositivePieces_pairwiseDisjoint (hμ : μ.support.Infinite) :
    Pairwise (fun n m => Disjoint (infiniteSupportPositivePieces μ hμ n)
      (infiniteSupportPositivePieces μ hμ m)) := by
  intro n m hnm
  exact Set.disjoint_image_of_injective Subtype.val_injective
    (infiniteSupportOpenPieces_pairwiseDisjoint μ hμ hnm)

omit [BorelSpace X] in
lemma measure_infiniteSupportPositivePieces_pos (hμ : μ.support.Infinite) (n : ℕ) :
    0 < μ (infiniteSupportPositivePieces μ hμ n) := by
  obtain ⟨y, hy⟩ := (infiniteSupportOpenPieces_infinite μ hμ n).nonempty
  obtain ⟨V, hVopen, hVpre⟩ := isOpen_induced_iff.mp
    (infiniteSupportOpenPieces_isOpen μ hμ n)
  have hyV : (y : X) ∈ V := by
    have : y ∈ Subtype.val ⁻¹' V := by simpa [hVpre] using hy
    exact this
  have hVpos : 0 < μ V :=
    (Measure.mem_support_iff_forall (μ := μ) (y : X)).mp y.2 V (hVopen.mem_nhds hyV)
  have himage : infiniteSupportPositivePieces μ hμ n = V ∩ μ.support := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzV : z ∈ Subtype.val ⁻¹' V := by
        rw [hVpre]
        exact hz
      exact ⟨hzV, z.2⟩
    · rintro ⟨hxV, hxsupp⟩
      refine ⟨⟨x, hxsupp⟩, ?_, rfl⟩
      rw [← hVpre]
      exact hxV
  rw [himage, measure_inter_conull]
  · exact hVpos
  · exact mem_ae_iff.mp Measure.support_mem_ae

omit [BorelSpace X] in
lemma measure_infiniteSupportPositivePieces_ne_zero (hμ : μ.support.Infinite) (n : ℕ) :
    μ (infiniteSupportPositivePieces μ hμ n) ≠ 0 :=
  ne_of_gt (measure_infiniteSupportPositivePieces_pos μ hμ n)

noncomputable def infiniteSupportBlockPiece {k : ℕ} (hμ : μ.support.Infinite)
    (j : ℕ) (l : Fin (k + 1)) : Set X :=
  infiniteSupportPositivePieces μ hμ (Nat.pair j l)

omit [HereditarilyLindelofSpace X] in
lemma measurableSet_infiniteSupportBlockPiece {k : ℕ} (hμ : μ.support.Infinite)
    (j : ℕ) (l : Fin (k + 1)) :
    MeasurableSet (infiniteSupportBlockPiece μ hμ j l) :=
  measurableSet_infiniteSupportPositivePieces μ hμ _

omit [BorelSpace X] in
lemma measure_infiniteSupportBlockPiece_ne_zero {k : ℕ} (hμ : μ.support.Infinite)
    (j : ℕ) (l : Fin (k + 1)) :
    μ (infiniteSupportBlockPiece μ hμ j l) ≠ 0 :=
  measure_infiniteSupportPositivePieces_ne_zero μ hμ _

omit [BorelSpace X] [HereditarilyLindelofSpace X] in
lemma infiniteSupportBlockPiece_disjoint {k : ℕ} (hμ : μ.support.Infinite)
    (j m : ℕ) (l r : Fin (k + 1)) (h : (j, l) ≠ (m, r)) :
    Disjoint (infiniteSupportBlockPiece μ hμ j l)
      (infiniteSupportBlockPiece μ hμ m r) := by
  apply infiniteSupportPositivePieces_pairwiseDisjoint μ hμ
  intro hpair
  apply h
  rw [Nat.pair_eq_pair] at hpair
  exact Prod.ext hpair.1 (Fin.ext hpair.2)

variable [IsFiniteMeasure μ]

/-- Every finite continuous-linear constraint fiber through density one over a measure with
infinite topological support contains a closed Hilbert cube of strictly positive densities. -/
theorem exists_positive_closedEmbeddedHilbertCube_in_infiniteSupportConstraintFiber
    (hμ : μ.support.Infinite) {k : ℕ}
    (T : (Lp ℝ ⊤ μ) →L[ℝ] (Fin k → ℝ))
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1) :
    ∃ v : ℕ → Lp ℝ ⊤ μ, ∃ ell : ℕ → (Lp ℝ ⊤ μ) →L[ℝ] ℝ,
      (∀ n, ‖v n‖ = 1) ∧ (∀ n, T (v n) = 0) ∧
      (∀ n m, ell n (v m) = if n = m then 1 else 0) ∧
      Topology.IsClosedEmbedding
        (affinePositiveHilbertCubeMap (linftyOne μ) delta v) ∧
      ∀ t : SignedHilbertCube,
        T (affinePositiveHilbertCubeMap (linftyOne μ) delta v t) = T (linftyOne μ) ∧
        LinftyStrictlyPositive μ
          (affinePositiveHilbertCubeMap (linftyOne μ) delta v t) := by
  exact exists_positive_closedEmbeddedHilbertCube_in_linfty_finiteConstraintFiber
    μ T hdelta0 hdelta1 (infiniteSupportBlockPiece μ hμ)
    (measurableSet_infiniteSupportBlockPiece μ hμ)
    (measure_infiniteSupportBlockPiece_ne_zero μ hμ)
    (fun j l m r h => infiniteSupportBlockPiece_disjoint μ hμ j m l r h)

end
end GaloisForLFunctions.HTGeometry
