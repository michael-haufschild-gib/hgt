import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Compact calibration globalization

Weak-star compactness forces a family of norming constraints to globalize from all finite
subfamilies. Consequently failure of one common normer always has a finite witness, even in an
infinite-dimensional seminormed space.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Metric Set

variable {E ι : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- Norming functionals in the weak-star dual unit ball. -/
def weakNormingFace (v : E) : Set (WeakDual ℝ E) :=
  {φ | ‖WeakDual.toStrongDual φ‖ ≤ 1 ∧ WeakDual.toStrongDual φ v = ‖v‖}

/-- Every weak-star norming face is closed. -/
theorem isClosed_weakNormingFace (v : E) : IsClosed (weakNormingFace v) := by
  rw [show weakNormingFace v =
      (WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1) ∩
        {φ | WeakDual.toStrongDual φ v = ‖v‖} by
    ext φ
    simp [weakNormingFace, mem_closedBall, dist_zero_right]]
  exact (WeakDual.isClosed_closedBall 0 1).inter
    (isClosed_eq (WeakBilin.eval_continuous _ _) continuous_const)

/-- Hahn--Banach supplies a norming functional for every individual vector. -/
theorem weakNormingFace_nonempty (v : E) : (weakNormingFace v).Nonempty := by
  obtain ⟨g, hg, hgv⟩ := exists_dual_vector'' ℝ v
  exact ⟨StrongDual.toWeakDual g, by simpa [weakNormingFace] using And.intro hg hgv⟩

/-- Every norming face lies in the weak-star compact dual unit ball. -/
theorem weakNormingFace_subset_closedBall (v : E) : weakNormingFace v ⊆
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1 := by
  intro φ hφ
  simpa [weakNormingFace, mem_closedBall, dist_zero_right] using hφ.1

/-- If every finite packet has one common norming functional, weak-star compactness produces one
functional norming the entire family. -/
theorem global_common_normer_of_finite
    (v : ι → E)
    (hfinite : ∀ s : Finset ι, ∃ φ : StrongDual ℝ E,
      ‖φ‖ ≤ 1 ∧ ∀ i ∈ s, φ (v i) = ‖v i‖) :
    ∃ φ : StrongDual ℝ E, ‖φ‖ ≤ 1 ∧ ∀ i, φ (v i) = ‖v i‖ := by
  let K : Set (WeakDual ℝ E) :=
    WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) 1
  have hK : IsCompact K := WeakDual.isCompact_closedBall 0 1
  have hclosed : ∀ i, IsClosed (weakNormingFace (v i)) :=
    fun i => isClosed_weakNormingFace (v i)
  have hfip : ∀ s : Finset ι, (K ∩ ⋂ i ∈ s, weakNormingFace (v i)).Nonempty := by
    intro s
    obtain ⟨φ, hnorm, heval⟩ := hfinite s
    refine ⟨StrongDual.toWeakDual φ, ?_, ?_⟩
    · simpa [K, mem_closedBall, dist_zero_right] using hnorm
    · simp only [mem_iInter]
      intro i hi
      simpa [weakNormingFace] using And.intro hnorm (heval i hi)
  obtain ⟨φ, hφK, hφall⟩ :=
    hK.inter_iInter_nonempty (fun i => weakNormingFace (v i)) hclosed hfip
  refine ⟨WeakDual.toStrongDual φ, ?_, ?_⟩
  · simpa [K, mem_closedBall, dist_zero_right] using hφK
  · intro i
    have hi : φ ∈ weakNormingFace (v i) := mem_iInter.mp hφall i
    exact hi.2

/-- A family has one global normer exactly when every finite packet has one. -/
theorem common_normer_iff_finset (v : ι → E) :
    (∃ φ : StrongDual ℝ E, ‖φ‖ ≤ 1 ∧ ∀ i, φ (v i) = ‖v i‖) ↔
      ∀ s : Finset ι, ∃ φ : StrongDual ℝ E,
        ‖φ‖ ≤ 1 ∧ ∀ i ∈ s, φ (v i) = ‖v i‖ := by
  constructor
  · rintro ⟨φ, hnorm, heval⟩ s
    exact ⟨φ, hnorm, fun i _ => heval i⟩
  · exact global_common_normer_of_finite v

/-- Failure of global common calibration always appears on a finite packet. -/
theorem finite_witness_of_no_common_normer (v : ι → E)
    (hglobal : ¬ ∃ φ : StrongDual ℝ E, ‖φ‖ ≤ 1 ∧ ∀ i, φ (v i) = ‖v i‖) :
    ∃ s : Finset ι, ¬ ∃ φ : StrongDual ℝ E,
      ‖φ‖ ≤ 1 ∧ ∀ i ∈ s, φ (v i) = ‖v i‖ := by
  contrapose! hglobal
  exact global_common_normer_of_finite v hglobal

end GaloisForLFunctions.HTGeometry
