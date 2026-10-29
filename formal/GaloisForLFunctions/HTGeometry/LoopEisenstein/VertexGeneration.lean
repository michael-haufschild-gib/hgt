import GaloisForLFunctions.HTGeometry.LoopEisenstein.VertexParabolics

/-!
# Generation by the two vertex parabolics

The vertex stabilizers contain the two Weyl matrices `W(1)` and `W(X)`.
Their quotient gives a unit translation. Its integral powers and the
finite reflection give every affine Weyl representative; Bruhat then
proves generation of the full central extension.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein

noncomputable section

variable (F : Type*) [Field F]

/-- The matrix diagonal torus is multiplicative before taking central lifts. -/
def sl2DiagonalHom : Fˣ →* SL2 F where
  toFun := sl2Diagonal
  map_one' := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [sl2Diagonal]
  map_mul' := sl2Diagonal_mul

private theorem constant_weyl_matrix :
    constantLaurentSL2Map F (sl2WeylLower (1 : Fˣ)) = sl2WeylLower 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [constantLaurentSL2Map_apply, sl2WeylLower]

private theorem rescale_uniformizer_weyl :
    sl2Rescale (laurentXUnit F) (sl2WeylLower (laurentXUnit F)) = sl2WeylLower 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_sl2Rescale, sl2WeylLower, Units.val_inv_eq_inv_val, (laurentXUnit F).ne_zero]

namespace LoopSL2

/-- The two central parabolics together contain every central discrepancy. -/
private theorem vertex_sup_mem_of_projection_eq {g h : LoopSL2 F}
    (he : projection F g = projection F h)
    (hh : h ∈ positiveVertex F ⊔ affineVertex F) :
    g ∈ positiveVertex F ⊔ affineVertex F := by
  have hb : g * h⁻¹ ∈ positiveBorel F := by
    apply (mem_positiveBorel_iff_projection F _).2
    rw [map_mul, map_inv, he, mul_inv_cancel]
    exact (laurentIwahori F).one_mem
  have hb' : g * h⁻¹ ∈ positiveVertex F ⊔ affineVertex F :=
    le_sup_left (positiveBorel_le_positiveVertex F hb)
  have hm := (positiveVertex F ⊔ affineVertex F).mul_mem hb' hh
  simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

theorem finiteWeylLift_mem_positiveVertex : finiteWeylLift F ∈ positiveVertex F := by
  refine ⟨constantPowerSeriesSL2Map F (sl2WeylLower 1), ?_⟩
  exact constant_weyl_matrix F

theorem uniformizerWeyl_mem_affineVertex :
    SL2SymbolExtension.weylLower (laurentTameHom F) (laurentXUnit F) ∈ affineVertex F := by
  refine ⟨constantPowerSeriesSL2Map F (sl2WeylLower 1), ?_⟩
  change constantLaurentSL2Map F (sl2WeylLower 1) =
    sl2Rescale (laurentXUnit F) (sl2WeylLower (laurentXUnit F))
  rw [constant_weyl_matrix, rescale_uniformizer_weyl]

theorem translation_one_mem_vertex_sup :
    translationLift F 1 ∈ positiveVertex F ⊔ affineVertex F := by
  let w := SL2SymbolExtension.weylLower (laurentTameHom F) (laurentXUnit F)
  have hw : w ∈ positiveVertex F ⊔ affineVertex F :=
    le_sup_right (uniformizerWeyl_mem_affineVertex F)
  have hs : finiteWeylLift F ∈ positiveVertex F ⊔ affineVertex F :=
    le_sup_left (finiteWeylLift_mem_positiveVertex F)
  apply vertex_sup_mem_of_projection_eq F (h := w * (finiteWeylLift F)⁻¹)
  · rw [map_mul, map_inv]
    change sl2Diagonal (laurentXUnit F ^ (-(1 : ℤ))) =
      sl2WeylLower (laurentXUnit F) * (sl2WeylLower 1)⁻¹
    rw [zpow_neg_one, sl2WeylLower_inv]
    exact (by simpa only [mul_one] using sl2WeylLower_relative (laurentXUnit F) 1).symm
  · exact (positiveVertex F ⊔ affineVertex F).mul_mem hw
      ((positiveVertex F ⊔ affineVertex F).inv_mem hs)

/-- Central defects do not affect generation by the two vertex stabilizers. -/
theorem translation_mem_vertex_sup (m : ℤ) :
    translationLift F m ∈ positiveVertex F ⊔ affineVertex F := by
  apply vertex_sup_mem_of_projection_eq F (h := translationLift F 1 ^ m)
  · rw [map_zpow]
    change sl2Diagonal (laurentXUnit F ^ (-m)) =
      sl2Diagonal (laurentXUnit F ^ (-(1 : ℤ))) ^ m
    rw [zpow_neg_one]
    have he := map_zpow (sl2DiagonalHom (LaurentSeries F)) (laurentXUnit F)⁻¹ m
    change sl2Diagonal (((laurentXUnit F)⁻¹) ^ m) = sl2Diagonal ((laurentXUnit F)⁻¹) ^ m at he
    rw [inv_zpow, ← zpow_neg] at he
    exact he
  · exact (positiveVertex F ⊔ affineVertex F).zpow_mem (translation_one_mem_vertex_sup F) m

theorem affineWeylLift_mem_vertex_sup (w : AffineA1.Weyl) :
    affineWeylLift F w ∈ positiveVertex F ⊔ affineVertex F := by
  cases w with
  | r m => exact translation_mem_vertex_sup F (show ℤ from m)
  | sr m => exact (positiveVertex F ⊔ affineVertex F).mul_mem
      (le_sup_left (finiteWeylLift_mem_positiveVertex F)) (translation_mem_vertex_sup F (show ℤ from m))

/-- The two actual vertex parabolics generate every element of the central loop group. -/
theorem mem_vertex_sup (g : LoopSL2 F) : g ∈ positiveVertex F ⊔ affineVertex F := by
  obtain ⟨w, l, hl, r, hr, he⟩ := exists_bruhat F g
  have hl' : l ∈ positiveVertex F ⊔ affineVertex F :=
    le_sup_left (positiveBorel_le_positiveVertex F hl)
  have hr' : r ∈ positiveVertex F ⊔ affineVertex F :=
    le_sup_left (positiveBorel_le_positiveVertex F hr)
  have hg : g = l⁻¹ * affineWeylLift F w * r⁻¹ := by
    rw [← he]
    group
  rw [hg]
  exact (positiveVertex F ⊔ affineVertex F).mul_mem
    ((positiveVertex F ⊔ affineVertex F).mul_mem
      ((positiveVertex F ⊔ affineVertex F).inv_mem hl') (affineWeylLift_mem_vertex_sup F w))
    ((positiveVertex F ⊔ affineVertex F).inv_mem hr')

theorem vertex_sup_eq_top : positiveVertex F ⊔ affineVertex F = ⊤ :=
  le_antisymm le_top (fun g _ => mem_vertex_sup F g)

end LoopSL2

end

end GaloisForLFunctions.HTGeometry.LoopEisenstein
