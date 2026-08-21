import GaloisForLFunctions.HTGeometry.HomologyTransport
import GaloisForLFunctions.HTGeometry.PuncturedSpace
import GaloisForLFunctions.HTGeometry.ExcisionPair

/-!
# The puncturing induction

Inside the punctured product the two star-shaped pieces are open, cover it, and meet in the
punctured factor times the line.  Excision and the two long exact sequences then relate the homology
of the punctured product in degree `n + 2` to that of the punctured factor in degree `n + 1`.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] (W : Type v) [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ W] in
theorem upperPiece_subset_punct : upperPiece W ⊆ punct (W × ℝ) := by
  intro p hp hp0
  exact hp ⟨congrArg Prod.fst hp0, le_of_eq (congrArg Prod.snd hp0)⟩

omit [NormedSpace ℝ W] in
theorem lowerPiece_subset_punct : lowerPiece W ⊆ punct (W × ℝ) := by
  intro p hp hp0
  exact hp ⟨congrArg Prod.fst hp0, ge_of_eq (congrArg Prod.snd hp0)⟩

omit [NormedSpace ℝ W] in
theorem inter_subset_punct : {p : W × ℝ | p.1 ≠ 0} ⊆ punct (W × ℝ) := by
  intro p hp hp0
  exact hp (congrArg Prod.fst hp0)

/-- The upper piece, as a subset of the punctured product. -/
def upperSub : Set ↥(punct (W × ℝ)) := {p | (p : W × ℝ) ∈ upperPiece W}

/-- The lower piece, as a subset of the punctured product. -/
def lowerSub : Set ↥(punct (W × ℝ)) := {p | (p : W × ℝ) ∈ lowerPiece W}

omit [NormedSpace ℝ W] in
theorem isOpen_upperSub : IsOpen (upperSub W) :=
  (isOpen_upperPiece W).preimage continuous_subtype_val

omit [NormedSpace ℝ W] in
theorem isOpen_lowerSub : IsOpen (lowerSub W) :=
  (isOpen_lowerPiece W).preimage continuous_subtype_val

omit [NormedSpace ℝ W] in
theorem union_subs : upperSub W ∪ lowerSub W = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  have hp : (p : W × ℝ) ∈ upperPiece W ∪ lowerPiece W := by
    rw [union_pieces]
    exact p.2
  exact hp

omit [NormedSpace ℝ W] in
theorem inter_subs_eq :
    lowerSub W ∩ upperSub W = {p : ↥(punct (W × ℝ)) | (p : W × ℝ) ∈ {q : W × ℝ | q.1 ≠ 0}} := by
  ext p
  constructor
  · rintro ⟨hl, hu⟩
    have : (p : W × ℝ) ∈ upperPiece W ∩ lowerPiece W := ⟨hu, hl⟩
    rwa [inter_pieces] at this
  · intro hp
    have : (p : W × ℝ) ∈ upperPiece W ∩ lowerPiece W := by rwa [inter_pieces]
    exact ⟨this.2, this.1⟩

/-- The intersection of the two pieces is homeomorphic to the punctured factor times the line. -/
noncomputable def interSubHomeomorph :
    ↥(lowerSub W ∩ upperSub W) ≃ₜ ↥(punct W) × ℝ :=
  (Homeomorph.setCongr (inter_subs_eq W)).trans
    ((subsetSubtypeHomeomorph {q : W × ℝ | q.1 ≠ 0} (inter_subset_punct W)).trans
      (punctProdHomeomorph W))

/-- The upper piece of the punctured product is contractible. -/
theorem isZero_homology_upperSub (k : ℕ) :
    IsZero ((singChainComplex R ↥(upperSub W)).homology (k + 1)) := by
  refine isZero_homology_of_homotopyEquiv R
    (Homeomorph.toHomotopyEquiv
      (subsetSubtypeHomeomorph (upperPiece W) (upperPiece_subset_punct W))) (k + 1) ?_
  exact isZero_homology_starConvex R (mem_upperPiece_center W) (starConvex_upperPiece W) k

/-- The lower piece of the punctured product is contractible. -/
theorem isZero_homology_lowerSub (k : ℕ) :
    IsZero ((singChainComplex R ↥(lowerSub W)).homology (k + 1)) := by
  refine isZero_homology_of_homotopyEquiv R
    (Homeomorph.toHomotopyEquiv
      (subsetSubtypeHomeomorph (lowerPiece W) (lowerPiece_subset_punct W))) (k + 1) ?_
  exact isZero_homology_starConvex R (mem_lowerPiece_center W) (starConvex_lowerPiece W) k

omit [NormedSpace ℝ W] in
theorem compl_upperSub_subset : (upperSub W)ᶜ ⊆ lowerSub W := by
  intro p hp
  have hmem : p ∈ upperSub W ∪ lowerSub W := by
    rw [union_subs]
    trivial
  rcases hmem with h | h
  · exact absurd h hp
  · exact h

omit [NormedSpace ℝ W] in
theorem excision_hypothesis : closure ((upperSub W)ᶜ) ⊆ interior (lowerSub W) := by
  rw [IsClosed.closure_eq ((isOpen_upperSub W).isClosed_compl), (isOpen_lowerSub W).interior_eq]
  exact compl_upperSub_subset W

/-- **The puncturing induction step.** -/
theorem nonempty_homology_punct_iso (k : ℕ) :
    Nonempty ((singChainComplex R ↥(punct (W × ℝ))).homology (k + 2)
      ≅ (singChainComplex R ↥(punct W)).homology (k + 1)) := by
  have hBz1 : IsZero ((subcomplexOfSubset R (lowerSub W)).complex.homology (k + 2)) :=
    isZero_homology_subcomplexOfSubset R _ _ (isZero_homology_lowerSub R W (k + 1))
  have hBz2 : IsZero ((subcomplexOfSubset R (lowerSub W)).complex.homology (k + 1)) :=
    isZero_homology_subcomplexOfSubset R _ _ (isZero_homology_lowerSub R W k)
  have hAz1 : IsZero ((subcomplexOfSubset R (upperSub W)).complex.homology (k + 2)) :=
    isZero_homology_subcomplexOfSubset R _ _ (isZero_homology_upperSub R W (k + 1))
  have hAz2 : IsZero ((subcomplexOfSubset R (upperSub W)).complex.homology (k + 1)) :=
    isZero_homology_subcomplexOfSubset R _ _ (isZero_homology_upperSub R W k)
  haveI i1 : IsIso (HomologicalComplex.homologyMap
      (subcomplexOfSubset R (lowerSub W)).proj (k + 2)) :=
    ModuleSubcomplex.isIso_homologyMap_proj _ (k + 1) hBz1 hBz2
  haveI i2 := isIso_homologyMap_excision R (lowerSub W) (upperSub W) (excision_hypothesis W) (k + 2)
  haveI i3 : IsIso ((pairSub R (Set.inter_subset_right :
      lowerSub W ∩ upperSub W ⊆ upperSub W)).connecting (k + 2) (k + 1) rfl) :=
    ModuleSubcomplex.isIso_connecting_of_isZero _ k hAz1 hAz2
  haveI i4' : IsIso (ModuleSubcomplex.restrictHom (subcomplexOfSubset R (upperSub W))
        (subcomplexOfSubset R (lowerSub W ∩ upperSub W))
        (fun j => subChains_mono R Set.inter_subset_right j)).subMap :=
    ModuleSubcomplex.isIso_restrictHom_subMap' (subcomplexOfSubset R (upperSub W))
      (subcomplexOfSubset R (lowerSub W ∩ upperSub W))
      (fun j => subChains_mono R Set.inter_subset_right j)
  exact ⟨asIso (HomologicalComplex.homologyMap
      (subcomplexOfSubset R (lowerSub W)).proj (k + 2))
    ≪≫ (asIso (HomologicalComplex.homologyMap
      ((excPairHom R (lowerSub W) (upperSub W)).quotMap
        ≫ (excHom R (lowerSub W) (upperSub W)).quotMap) (k + 2))).symm
    ≪≫ asIso ((pairSub R (Set.inter_subset_right :
      lowerSub W ∩ upperSub W ⊆ upperSub W)).connecting (k + 2) (k + 1) rfl)
    ≪≫ (HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) (k + 1)).mapIso
      (@asIso _ _ _ _ _ (ModuleSubcomplex.isIso_restrictHom_subMap'
        (subcomplexOfSubset R (upperSub W))
        (subcomplexOfSubset R (lowerSub W ∩ upperSub W))
        (fun j => subChains_mono R Set.inter_subset_right j)))
    ≪≫ homologyIsoSubcomplex R (lowerSub W ∩ upperSub W) (k + 1)
    ≪≫ homologyIsoOfHomotopyEquiv R (Homeomorph.toHomotopyEquiv (interSubHomeomorph W)) (k + 1)
    ≪≫ homologyIsoOfHomotopyEquiv R (prodRealHomotopyEquiv ↥(punct W)) (k + 1)⟩

end GaloisForLFunctions.HTGeometry
