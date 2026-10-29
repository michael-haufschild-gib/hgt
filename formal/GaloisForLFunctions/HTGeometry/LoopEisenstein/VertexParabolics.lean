import GaloisForLFunctions.HTGeometry.LoopEisenstein.SimpleRankOneEmbeddings
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LoopBruhatDecomposition

/-!
# The two vertex parabolics

The standard and adjacent power-series lattices give two subgroups containing
the Iwahori. Reduction at their vertices expresses every central parabolic
element as a Borel factor times an element of the corresponding simple SL₂.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- The matrix stabilizer of the standard power-series lattice. -/
def positiveVertexMatrices : Subgroup (SL2 (LaurentSeries F)) := (powerSeriesSL2Map F).range

/-- The matrix stabilizer of the adjacent lattice `diag(1,X) F[[X]]²`. -/
def affineVertexMatrices : Subgroup (SL2 (LaurentSeries F)) :=
  (positiveVertexMatrices F).comap (sl2Rescale (laurentXUnit F))

theorem laurentIwahori_le_positiveVertex : laurentIwahori F ≤ positiveVertexMatrices F := by
  rintro g ⟨p, _, rfl⟩
  exact ⟨p, rfl⟩

theorem laurentIwahori_le_affineVertex : laurentIwahori F ≤ affineVertexMatrices F := by
  intro g hg
  have he : (sl2Rescale (laurentXUnit F) g : Matrix (Fin 2) (Fin 2) (LaurentSeries F)) =
      latticeConjugate F g := by
    rw [coe_sl2Rescale, latticeConjugate_entries]
  have hv : matrixValuationContent (laurentValuation F)
      (sl2Rescale (laurentXUnit F) g) ≤ 1 := by
    rw [he]
    exact laurentIwahori_conjugate_content_le_one F hg
  exact exists_powerSeriesSL2_of_integral F _
    ((matrixValuationContent_le_iff _ _ _).1 hv)

@[simp] theorem powerSeriesReduction_constant (g : SL2 F) :
    powerSeriesReduction F (constantPowerSeriesSL2Map F g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [powerSeriesReduction_apply, constantPowerSeriesSL2Map_apply,
    PowerSeries.constantCoeff_C]

/-- Removing the constant reduction leaves a matrix in the congruence kernel. -/
theorem powerSeriesReduction_residual (p : PowerSeriesSL2 F) :
    powerSeriesReduction F (p * (constantPowerSeriesSL2Map F (powerSeriesReduction F p))⁻¹) = 1 := by
  rw [map_mul, map_inv, powerSeriesReduction_constant, mul_inv_cancel]

theorem powerSeries_residual_mem_iwahori (p : PowerSeriesSL2 F) :
    p * (constantPowerSeriesSL2Map F (powerSeriesReduction F p))⁻¹ ∈ iwahoriMatrices F := by
  apply (mem_iwahoriMatrices F _).2
  exact congrArg (fun h : SL2 F => h 1 0) (powerSeriesReduction_residual F p)

/-- Shifting an integral matrix with zero upper-right residue still gives an Iwahori matrix. -/
theorem affineShift_mem_laurentIwahori (p : PowerSeriesSL2 F)
    (hb : PowerSeries.constantCoeff (p 0 1) = 0) :
    sl2Rescale (laurentXUnit F)⁻¹ (powerSeriesSL2Map F p) ∈ laurentIwahori F := by
  obtain ⟨s, hs⟩ := PowerSeries.X_dvd_iff.2 hb
  have hu : (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
      (p 0 1 : LaurentSeries F) = (s : LaurentSeries F) := by
    rw [hs, PowerSeries.coe_mul, PowerSeries.coe_X]
    change (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) *
      ((laurentXUnit F : LaurentSeries F) * (s : LaurentSeries F)) = _
    rw [← mul_assoc]
    simp
  have hl : (laurentXUnit F : LaurentSeries F) * (p 1 0 : LaurentSeries F) =
      ((PowerSeries.X * p 1 0 : PowerSeries F) : LaurentSeries F) := by
    rw [PowerSeries.coe_mul, PowerSeries.coe_X]
    rfl
  have he : (sl2Rescale (laurentXUnit F)⁻¹ (powerSeriesSL2Map F p) :
      Matrix (Fin 2) (Fin 2) (LaurentSeries F)) =
      !![(p 0 0 : LaurentSeries F), (s : LaurentSeries F);
        ((PowerSeries.X * p 1 0 : PowerSeries F) : LaurentSeries F), (p 1 1 : LaurentSeries F)] := by
    rw [coe_sl2Rescale, inv_inv]
    change !![(p 0 0 : LaurentSeries F),
      (((laurentXUnit F)⁻¹ : (LaurentSeries F)ˣ) : LaurentSeries F) * (p 0 1 : LaurentSeries F);
      (laurentXUnit F : LaurentSeries F) * (p 1 0 : LaurentSeries F), (p 1 1 : LaurentSeries F)] = _
    rw [hu, hl]
  apply (mem_laurentIwahori F _).2
  constructor
  · intro i j
    rw [he]
    fin_cases i <;> fin_cases j <;> exact valuation_powerSeries_le_one F _
  · rw [he]
    apply (valuation_powerSeries_lt_one_iff F (PowerSeries.X * p 1 0)).2
    rw [map_mul, PowerSeries.constantCoeff_X, zero_mul]

theorem affineShift_residual_mem_iwahori (p : PowerSeriesSL2 F) :
    sl2Rescale (laurentXUnit F)⁻¹
      (powerSeriesSL2Map F (p * (constantPowerSeriesSL2Map F (powerSeriesReduction F p))⁻¹))
        ∈ laurentIwahori F := by
  apply affineShift_mem_laurentIwahori
  exact congrArg (fun h : SL2 F => h 0 1) (powerSeriesReduction_residual F p)

namespace LoopSL2

/-- The central parabolic over the standard vertex. -/
def positiveVertex : Subgroup (LoopSL2 F) :=
  (positiveVertexMatrices F).comap (projection F)

/-- The central parabolic over the adjacent vertex. -/
def affineVertex : Subgroup (LoopSL2 F) :=
  (affineVertexMatrices F).comap (projection F)

theorem positiveBorel_le_positiveVertex : positiveBorel F ≤ positiveVertex F := by
  intro g hg
  exact laurentIwahori_le_positiveVertex F (projection_mem_laurentIwahori F hg)

theorem positiveBorel_le_affineVertex : positiveBorel F ≤ affineVertex F := by
  intro g hg
  exact laurentIwahori_le_affineVertex F (projection_mem_laurentIwahori F hg)

/-- The standard vertex parabolic is a Borel times the finite simple subgroup. -/
theorem positiveVertex_borel_finite {g : LoopSL2 F} (hg : g ∈ positiveVertex F) :
    ∃ b ∈ positiveBorel F, ∃ h : SL2 F, b * finiteSL2Embedding F h = g := by
  obtain ⟨p, hp⟩ := hg
  let h := powerSeriesReduction F p
  let b := g * (finiteSL2Embedding F h)⁻¹
  have hb : b ∈ positiveBorel F := by
    apply (mem_positiveBorel_iff_projection F b).2
    have he : projection F b =
        powerSeriesSL2Map F (p * (constantPowerSeriesSL2Map F h)⁻¹) := by
      change projection F (g * (finiteSL2Embedding F h)⁻¹) = _
      rw [map_mul, map_inv, projection_finiteSL2Embedding, ← hp, map_mul, map_inv]
      rfl
    rw [he]
    exact ⟨_, powerSeries_residual_mem_iwahori F p, rfl⟩
  refine ⟨b, hb, h, ?_⟩
  change (g * (finiteSL2Embedding F h)⁻¹) * finiteSL2Embedding F h = g
  group

/-- The adjacent vertex parabolic is a Borel times the affine simple subgroup. -/
theorem affineVertex_borel_affine {g : LoopSL2 F} (hg : g ∈ affineVertex F) :
    ∃ b ∈ positiveBorel F, ∃ h : SL2 F, b * affineSimpleSL2Embedding F h = g := by
  obtain ⟨p, hp⟩ := hg
  have hproj : projection F g = sl2Rescale (laurentXUnit F)⁻¹ (powerSeriesSL2Map F p) := by
    have he := congrArg (sl2Rescale (laurentXUnit F)⁻¹) hp
    rw [sl2Rescale_inverse] at he
    exact he.symm
  let h := powerSeriesReduction F p
  let b := g * (affineSL2Embedding F h)⁻¹
  have hb : b ∈ positiveBorel F := by
    apply (mem_positiveBorel_iff_projection F b).2
    have he : projection F b = sl2Rescale (laurentXUnit F)⁻¹
        (powerSeriesSL2Map F (p * (constantPowerSeriesSL2Map F h)⁻¹)) := by
      change projection F (g * (affineSL2Embedding F h)⁻¹) = _
      rw [map_mul, map_inv, projection_affineSL2Embedding, hproj,
        map_mul, map_mul, map_inv, map_inv]
      rfl
    rw [he]
    exact affineShift_residual_mem_iwahori F p
  refine ⟨b, hb, sl2Swap F h, ?_⟩
  change (g * (affineSL2Embedding F h)⁻¹) * affineSL2Embedding F (sl2Swap F (sl2Swap F h)) = g
  rw [sl2Swap_involutive]
  group

theorem finiteSL2Embedding_upperTriangular (g : SL2 F) (hc : g 1 0 = 0) :
    finiteSL2Embedding F g ∈ positiveBorel F := by
  apply positiveEmbedding_mem_positiveBorel
  apply (mem_iwahoriMatrices F _).2
  rw [constantPowerSeriesSL2Map_apply, PowerSeries.constantCoeff_C]
  exact hc

theorem affineSimpleSL2Embedding_upperTriangular (g : SL2 F) (hc : g 1 0 = 0) :
    affineSimpleSL2Embedding F g ∈ positiveBorel F := by
  apply (mem_positiveBorel_iff_projection F _).2
  rw [projection_affineSimpleSL2Embedding]
  apply affineShift_mem_laurentIwahori
  rw [constantPowerSeriesSL2Map_apply, PowerSeries.constantCoeff_C, coe_sl2Swap]
  exact hc

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
