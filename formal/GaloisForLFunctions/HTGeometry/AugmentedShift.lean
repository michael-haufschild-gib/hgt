import GaloisForLFunctions.HTGeometry.AugmentedComplex

/-!
# The augmented complex is the ordinary one, shifted

Above degree one the augmented complex has the same objects and differentials as the ordinary
singular complex one degree lower, so their homologies agree after the shift.  The same holds for the
chains supported in a subspace.
-/

open CategoryTheory Limits

namespace GaloisForLFunctions.HTGeometry

universe v

variable (R : Type) [CommRing R] (X : Type v) [TopologicalSpace X]

theorem augChain_d_one_apply (c : C(topSimplex 0, X) →₀ R) :
    ((augChain R X).d 1 0) c = (ULift.moduleEquiv (R := R) (M := R)).symm (singAug R c) := by
  rw [augChain_d]
  rfl

theorem augChain_d_succ_apply (n : ℕ) (c : C(topSimplex (n + 1), X) →₀ R) :
    ((augChain R X).d (n + 2) (n + 1)) c = singBd R X n c := by
  rw [augChain_d]
  rfl

theorem augChain_d_eq (n : ℕ) :
    (augChain R X).d (n + 2) (n + 1) = (singChainComplex R X).d (n + 1) n := by
  rw [augChain_d_succ]
  rfl

/-- Above degree one the augmented complex agrees with the ordinary one, shifted. -/
noncomputable def augShiftSc (n : ℕ) :
    (augChain R X).sc' (n + 3) (n + 2) (n + 1) ≅ (singChainComplex R X).sc' (n + 2) (n + 1) n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      show 𝟙 _ ≫ (singChainComplex R X).d (n + 2) (n + 1)
        = (augChain R X).d (n + 3) (n + 2) ≫ 𝟙 _
      rw [augChain_d_eq R X (n + 1)]
      simp)
    (by
      show 𝟙 _ ≫ (singChainComplex R X).d (n + 1) n
        = (augChain R X).d (n + 2) (n + 1) ≫ 𝟙 _
      rw [augChain_d_eq R X n]
      simp)

/-- **The reduced homology agrees with the ordinary homology in positive degrees.** -/
noncomputable def augHomologyShift (n : ℕ) :
    (augChain R X).homology (n + 2) ≅ (singChainComplex R X).homology (n + 1) :=
  ShortComplex.homologyMapIso ((augChain R X).isoSc' (n + 3) (n + 2) (n + 1)
      (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ _)) ≪≫
    ShortComplex.homologyMapIso (augShiftSc R X n) ≪≫
    (ShortComplex.homologyMapIso ((singChainComplex R X).isoSc' (n + 2) (n + 1) n
      (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ _))).symm

/-- **The augmented complex of a path-connected space is exact in degree one**: a `0`-chain of total
coefficient zero is a boundary. -/
theorem exactAt_augChain_one [PathConnectedSpace X] : (augChain R X).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (ComplexShape.prev_eq' _ rfl)
      (ChainComplex.next_nat_succ 0), ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨c, rfl⟩ : ∃ c : C(topSimplex 0, X) →₀ R, c = x := ⟨x, rfl⟩
  have hx1 : ((augChain R X).d 1 0) c = 0 := hx
  rw [augChain_d] at hx1
  have hc : singAug R c = 0 := by
    have h2 : (ULift.moduleEquiv (R := R) (M := R)).symm (singAug R c) = 0 := hx1
    have h3 := congrArg (ULift.moduleEquiv (R := R) (M := R)) h2
    simpa using h3
  obtain ⟨d, hd⟩ := exists_singBd_eq_of_singAug_eq_zero R c hc
  refine ⟨d, ?_⟩
  show ((augChain R X).d 2 1) d = c
  rw [augChain_d]
  exact hd

theorem isZero_augHomology_one [PathConnectedSpace X] :
    IsZero ((augChain R X).homology 1) :=
  (exactAt_augChain_one R X).isZero_homology

variable (S : Set X)

theorem augSub_d_eq (n : ℕ) :
    (augSub R X S).complex.d (n + 2) (n + 1)
      = (subcomplexOfSubset R S).complex.d (n + 1) n := by
  rw [ModuleSubcomplex.complex_d, ModuleSubcomplex.complex_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
  show ((augChain R X).d (n + 2) (n + 1)).hom _
    = ((singChainComplex R X).d (n + 1) n).hom _
  rw [augChain_d_eq]
  rfl

/-- Above degree one the augmented subcomplex agrees with the ordinary one, shifted. -/
noncomputable def augSubShiftSc (n : ℕ) :
    (augSub R X S).complex.sc' (n + 3) (n + 2) (n + 1)
      ≅ (subcomplexOfSubset R S).complex.sc' (n + 2) (n + 1) n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      show 𝟙 _ ≫ (subcomplexOfSubset R S).complex.d (n + 2) (n + 1)
        = (augSub R X S).complex.d (n + 3) (n + 2) ≫ 𝟙 _
      rw [augSub_d_eq R X S (n + 1)]
      simp)
    (by
      show 𝟙 _ ≫ (subcomplexOfSubset R S).complex.d (n + 1) n
        = (augSub R X S).complex.d (n + 2) (n + 1) ≫ 𝟙 _
      rw [augSub_d_eq R X S n]
      simp)

/-- **The reduced homology of a subspace agrees with its ordinary homology in positive degrees.** -/
noncomputable def augSubHomologyShift (n : ℕ) :
    (augSub R X S).complex.homology (n + 2)
      ≅ (subcomplexOfSubset R S).complex.homology (n + 1) :=
  ShortComplex.homologyMapIso ((augSub R X S).complex.isoSc' (n + 3) (n + 2) (n + 1)
      (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ _)) ≪≫
    ShortComplex.homologyMapIso (augSubShiftSc R X S n) ≪≫
    (ShortComplex.homologyMapIso ((subcomplexOfSubset R S).complex.isoSc' (n + 2) (n + 1) n
      (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ _))).symm

theorem augQuot_d_eq (n : ℕ) :
    (augSub R X S).quotComplex.d (n + 2) (n + 1)
      = (subcomplexOfSubset R S).quotComplex.d (n + 1) n := by
  rw [ModuleSubcomplex.quotComplex_d, ModuleSubcomplex.quotComplex_d]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective ((augSub R X S).carrier (n + 2)) x
  show Submodule.Quotient.mk (((augChain R X).d (n + 2) (n + 1)).hom c)
    = (Submodule.Quotient.mk (((singChainComplex R X).d (n + 1) n).hom c) :
        _ ⧸ (subcomplexOfSubset R S).carrier n)
  rw [augChain_d_eq]
  rfl

/-- Above degree one the augmented quotient agrees with the ordinary one, shifted. -/
noncomputable def augQuotShiftSc (n : ℕ) :
    (augSub R X S).quotComplex.sc' (n + 3) (n + 2) (n + 1)
      ≅ (subcomplexOfSubset R S).quotComplex.sc' (n + 2) (n + 1) n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      show 𝟙 _ ≫ (subcomplexOfSubset R S).quotComplex.d (n + 2) (n + 1)
        = (augSub R X S).quotComplex.d (n + 3) (n + 2) ≫ 𝟙 _
      rw [augQuot_d_eq R X S (n + 1)]
      simp)
    (by
      show 𝟙 _ ≫ (subcomplexOfSubset R S).quotComplex.d (n + 1) n
        = (augSub R X S).quotComplex.d (n + 2) (n + 1) ≫ 𝟙 _
      rw [augQuot_d_eq R X S n]
      simp)

noncomputable def augQuotHomologyShiftSucc (n : ℕ) :
    (augSub R X S).quotComplex.homology (n + 2)
      ≅ (subcomplexOfSubset R S).quotComplex.homology (n + 1) :=
  ShortComplex.homologyMapIso ((augSub R X S).quotComplex.isoSc' (n + 3) (n + 2) (n + 1)
      (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ _)) ≪≫
    ShortComplex.homologyMapIso (augQuotShiftSc R X S n) ≪≫
    (ShortComplex.homologyMapIso ((subcomplexOfSubset R S).quotComplex.isoSc'
      (n + 2) (n + 1) n (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ _))).symm

theorem augQuot_d_one_zero : (augSub R X S).quotComplex.d 1 0 = 0 := by
  haveI hsub : Subsingleton ((augChain R X).X 0 ⧸ (augSub R X S).carrier 0) := by
    constructor
    intro a b
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq]
    exact Submodule.mem_top
  exact (ModuleCat.isZero_of_subsingleton
    (ModuleCat.of R ((augChain R X).X 0 ⧸ (augSub R X S).carrier 0))).eq_zero_of_tgt _

/-- In degree one the augmented quotient computes the relative homology in degree zero. -/
noncomputable def augQuotHomologyShiftZero :
    (augSub R X S).quotComplex.homology 1
      ≅ (subcomplexOfSubset R S).quotComplex.homology 0 := by
  refine ShortComplex.homologyMapIso ((augSub R X S).quotComplex.isoSc' 2 1 0
      (ComplexShape.prev_eq' _ rfl) (ChainComplex.next_nat_succ 0)) ≪≫ ?_
  refine shortComplexHomologyIsoQuot R _ (augQuot_d_one_zero R X S) ≪≫ ?_
  refine LinearEquiv.toModuleIso ?_ ≪≫ (homologyZeroIso R (subcomplexOfSubset R S).quotComplex).symm
  refine Submodule.quotEquivOfEq _ _ ?_
  show LinearMap.range ((augSub R X S).quotComplex.d 2 1).hom
    = LinearMap.range ((subcomplexOfSubset R S).quotComplex.d 1 0).hom
  rw [augQuot_d_eq R X S 0]
  rfl

end GaloisForLFunctions.HTGeometry

