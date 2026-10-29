import GaloisForLFunctions.HTGeometry.LoopEisenstein.RealIwasawaExistence
import GaloisForLFunctions.HTGeometry.LoopEisenstein.RealRotationMatrices
import GaloisForLFunctions.HTGeometry.LoopEisenstein.MatrixLaurentLeading

/-!
# Borel intersections of the two simple rotation groups

The finite matrix has a strictly integral lower-left entry precisely when
its constant residue vanishes. The affine matrix instead tests the
coefficient of degree minus one in its upper-right entry. In either copy,
the resulting triangular rotation is a scalar sign.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2

noncomputable section

variable (F : Type*) [Field F]

theorem finiteSL2Embedding_mem_borel_iff (g : SL2 F) :
    finiteSL2Embedding F g ∈ positiveBorel F ↔ g 1 0 = 0 := by
  constructor
  · intro hg
    have hi := projection_mem_laurentIwahori F hg
    rw [projection_finiteSL2Embedding] at hi
    have hv := ((mem_laurentIwahori F _).1 hi).2
    change laurentValuation F ((PowerSeries.C (g 1 0) : PowerSeries F) : LaurentSeries F) < 1 at hv
    simpa only [PowerSeries.constantCoeff_C] using
      (valuation_powerSeries_lt_one_iff F (PowerSeries.C (g 1 0))).1 hv
  · exact finiteSL2Embedding_upperTriangular F g

theorem affineSimpleSL2Embedding_mem_borel_iff (g : SL2 F) :
    affineSimpleSL2Embedding F g ∈ positiveBorel F ↔ g 1 0 = 0 := by
  constructor
  · intro hg
    have hi := projection_mem_laurentIwahori F hg
    rw [projection_affineSimpleSL2Embedding] at hi
    by_contra hc
    have hA : (!![0, (sl2Swap F g) 0 1; 0, 0] : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by
      intro hz
      apply hc
      have he := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A 0 1) hz
      change (sl2Swap F g) 0 1 = 0 at he
      rw [coe_sl2Swap] at he
      exact he
    exact not_mem_laurentIwahori_of_negative_lead F
      (affineConstantSL2Map_hasLeadAt F (sl2Swap F g)) (by omega) hA hi
  · exact affineSimpleSL2Embedding_upperTriangular F g

/-- Only the two finite coroot signs lie in both the finite rotation group and Borel. -/
theorem finiteCompact_borel_eq_sign {g : LoopSL2 ℝ}
    (hg : g ∈ finiteCompact) (hb : g ∈ positiveBorel ℝ) :
    g = 1 ∨ g = finiteCoroot ℝ (-1) := by
  obtain ⟨h, hh, rfl⟩ := hg
  rcases rotation_upperTriangular_eq_sign h hh
      ((finiteSL2Embedding_mem_borel_iff ℝ h).1 hb) with he | he
  · left
    rw [he, map_one]
  · right
    rw [he, finiteSL2Embedding_diagonal]

/-- The affine scalar sign includes its exact nontrivial central sign. -/
theorem affineCompact_borel_eq_sign {g : LoopSL2 ℝ}
    (hg : g ∈ affineCompact) (hb : g ∈ positiveBorel ℝ) :
    g = 1 ∨ g = centralEmbedding ℝ (-1) * finiteCoroot ℝ (-1) := by
  obtain ⟨h, hh, rfl⟩ := hg
  rcases rotation_upperTriangular_eq_sign h hh
      ((affineSimpleSL2Embedding_mem_borel_iff ℝ h).1 hb) with he | he
  · left
    rw [he, map_one]
  · right
    rw [he, affineSimpleSL2Embedding_diagonal, affineCoroot_eq_central_finite]
    simp

theorem finite_sign_mem_finiteCompact : finiteCoroot ℝ (-1) ∈ finiteCompact :=
  ⟨sl2Diagonal (-1), sl2Diagonal_neg_one_mem_rotation,
    finiteSL2Embedding_diagonal ℝ (-1)⟩

theorem affine_sign_mem_affineCompact : affineCoroot ℝ (-1) ∈ affineCompact :=
  ⟨sl2Diagonal (-1), sl2Diagonal_neg_one_mem_rotation,
    affineSimpleSL2Embedding_diagonal ℝ (-1)⟩

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopSL2
