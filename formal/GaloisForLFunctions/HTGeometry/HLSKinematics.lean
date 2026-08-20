import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.LinearAlgebra.SpecialLinearGroup
import Mathlib.Tactic

/-!
# Kinematics for Haag--Łopuszański--Sohnius systems

This module supplies the geometric layer missing from the algebraic
`SuperPoincare*` files: the real Minkowski vector space, its signature `(1, 3)`
quadratic form, its Lorentz group, the associated Poincaré semidirect product,
and Mathlib's Clifford-theoretic spin group.

It deliberately contains no scattering or classification claim.  HLS classifies
symmetries only after physical S-matrix assumptions are supplied separately.
-/

noncomputable section

open Matrix
open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

/-- Real four-momenta/events in coordinates `(E, p₁, p₂, p₃)`. -/
abbrev HLSMinkowskiVector := Fin 4 → ℝ

/-- Diagonal Minkowski metric of signature `(1, 3)`. -/
def hlsMinkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- The Minkowski quadratic form `E² - p₁² - p₂² - p₃²`. -/
def hlsMinkowskiForm : QuadraticForm ℝ HLSMinkowskiVector :=
  Matrix.toQuadraticForm' hlsMinkowskiMetric

/-- Minkowski bilinear pairing in the convention `p⁰q⁰ - p¹q¹ - p²q² - p³q³`. -/
def hlsMinkowskiPairing (p q : HLSMinkowskiVector) : ℝ :=
  p 0 * q 0 - p 1 * q 1 - p 2 * q 2 - p 3 * q 3

/-- The positive-energy timelike cone. -/
def hlsFutureTimelike (p : HLSMinkowskiVector) : Prop :=
  0 < p 0 ∧ 0 < hlsMinkowskiForm p

/-- Mass-shell predicate for mass `m`. -/
def hlsMassShell (m : ℝ) (p : HLSMinkowskiVector) : Prop :=
  hlsMinkowskiForm p = m ^ 2

/-- Coordinate expansion of the HLS Minkowski form. -/
theorem hlsMinkowskiForm_apply (p : HLSMinkowskiVector) :
    hlsMinkowskiForm p = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := by
  simp [hlsMinkowskiForm, hlsMinkowskiMetric, Matrix.toQuadraticForm',
    LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toLinearMap₂'_apply,
    Fin.sum_univ_four]
  ring

/-- The quadratic form is the self-pairing of the Minkowski bilinear form. -/
theorem hlsMinkowskiForm_eq_pairing_self (p : HLSMinkowskiVector) :
    hlsMinkowskiForm p = hlsMinkowskiPairing p p := by
  rw [hlsMinkowskiForm_apply]
  simp only [hlsMinkowskiPairing]
  ring

/-- Polarization identity for the concrete Minkowski quadratic form. -/
theorem hlsMinkowskiForm_add (p q : HLSMinkowskiVector) :
    hlsMinkowskiForm (p + q) = hlsMinkowskiForm p + hlsMinkowskiForm q +
      2 * hlsMinkowskiPairing p q := by
  rw [hlsMinkowskiForm_apply, hlsMinkowskiForm_apply, hlsMinkowskiForm_apply]
  simp only [Pi.add_apply, hlsMinkowskiPairing]
  ring

/-- The Minkowski pairing is symmetric. -/
theorem hlsMinkowskiPairing_symm (p q : HLSMinkowskiVector) :
    hlsMinkowskiPairing p q = hlsMinkowskiPairing q p := by
  simp only [hlsMinkowskiPairing]
  ring

/-- The Minkowski pairing is additive in its second argument. -/
theorem hlsMinkowskiPairing_add_right (p q r : HLSMinkowskiVector) :
    hlsMinkowskiPairing p (q + r) =
      hlsMinkowskiPairing p q + hlsMinkowskiPairing p r := by
  simp only [Pi.add_apply, hlsMinkowskiPairing]
  ring

/-- The Minkowski pairing is additive in its first argument. -/
theorem hlsMinkowskiPairing_add_left (p q r : HLSMinkowskiVector) :
    hlsMinkowskiPairing (p + q) r =
      hlsMinkowskiPairing p r + hlsMinkowskiPairing q r := by
  rw [hlsMinkowskiPairing_symm, hlsMinkowskiPairing_add_right,
    hlsMinkowskiPairing_symm p r, hlsMinkowskiPairing_symm q r]

/-- Linear Lorentz transformations: precisely the invertible real linear maps preserving
the Minkowski quadratic form. -/
def hlsLorentzGroup : Subgroup (HLSMinkowskiVector ≃ₗ[ℝ] HLSMinkowskiVector) where
  carrier := {g | ∀ p, hlsMinkowskiForm (g p) = hlsMinkowskiForm p}
  one_mem' := by intro p; rfl
  mul_mem' := by
    intro g h hg hh p
    exact (hg (h p)).trans (hh p)
  inv_mem' := by
    intro g hg p
    simpa using (hg (g.symm p)).symm

/-- Proper orthochronous Lorentz transformations, characterized without topology by preservation
of the Minkowski form, determinant `1`, and preservation of the full future-timelike cone. -/
def hlsProperOrthoLorentzGroup :
    Subgroup (HLSMinkowskiVector ≃ₗ[ℝ] HLSMinkowskiVector) where
  carrier := {g | (∀ p, hlsMinkowskiForm (g p) = hlsMinkowskiForm p) ∧
    g.det = 1 ∧ ∀ p, hlsFutureTimelike (g p) ↔ hlsFutureTimelike p}
  one_mem' := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      rfl
    · simp
    · intro p
      rfl
  mul_mem' := by
    intro g h hg hh
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact (hg.1 (h p)).trans (hh.1 p)
    · simp [hg.2.1, hh.2.1]
    · intro p
      exact (hg.2.2 (h p)).trans (hh.2.2 p)
  inv_mem' := by
    intro g hg
    refine ⟨?_, ?_, ?_⟩
    · intro p
      simpa using (hg.1 (g.symm p)).symm
    · simp [hg.2.1]
    · intro p
      simpa using (hg.2.2 (g.symm p)).symm

/-- Inclusion of the proper orthochronous component into the full Lorentz group. -/
def hlsProperOrthoLorentzToLorentz : hlsProperOrthoLorentzGroup →* hlsLorentzGroup where
  toFun g := ⟨g.1, g.2.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The natural action of Lorentz transformations on the additive translation group. -/
def hlsLorentzAction : hlsLorentzGroup →* MulAut (Multiplicative HLSMinkowskiVector) where
  toFun g := g.1.toAddEquiv.toMultiplicative
  map_one' := by
    ext p
    rfl
  map_mul' := by
    intro g h
    ext p
    rfl

/-- Natural action of the proper orthochronous Lorentz group on translations. -/
def hlsProperOrthoLorentzAction :
    hlsProperOrthoLorentzGroup →* MulAut (Multiplicative HLSMinkowskiVector) where
  toFun g := g.1.toAddEquiv.toMultiplicative
  map_one' := by
    ext p
    rfl
  map_mul' := by
    intro g h
    ext p
    rfl

/-- Poincaré group: translations semidirect Lorentz transformations. -/
abbrev HLSPoincareGroup :=
  Multiplicative HLSMinkowskiVector ⋊[hlsLorentzAction] hlsLorentzGroup

/-- Physical Poincaré group built from proper orthochronous Lorentz transformations. -/
abbrev HLSPhysicalPoincareGroup :=
  Multiplicative HLSMinkowskiVector ⋊[hlsProperOrthoLorentzAction]
    hlsProperOrthoLorentzGroup

/-- Translation topology transported from the underlying real Minkowski vector space. -/
abbrev hlsTranslationTopology : TopologicalSpace (Multiplicative HLSMinkowskiVector) :=
  TopologicalSpace.induced (fun x => x.toAdd) inferInstance

/-- Subspace topology on proper orthochronous Lorentz transformations, via pointwise action on
Minkowski vectors. -/
abbrev hlsProperOrthoLorentzTopology : TopologicalSpace hlsProperOrthoLorentzGroup :=
  TopologicalSpace.induced (fun g => (g : HLSMinkowskiVector → HLSMinkowskiVector)) inferInstance

/-- Product topology on the translation--Lorentz coordinates of the physical Poincaré group. -/
abbrev hlsPhysicalPoincareTopology : TopologicalSpace HLSPhysicalPoincareGroup :=
  TopologicalSpace.induced (fun x => (x.left.toAdd, x.right))
    (@instTopologicalSpaceProd (Multiplicative HLSMinkowskiVector) hlsProperOrthoLorentzGroup
      hlsTranslationTopology hlsProperOrthoLorentzTopology)

/-- Topological-group laws for the explicit physical Poincaré topology. -/
structure HLSPoincareTopologicalGroupData where
  multiplication_continuous : @Continuous
    (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup) HLSPhysicalPoincareGroup
    (@instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
      hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology)
    hlsPhysicalPoincareTopology (fun x => x.1 * x.2)
  inversion_continuous : @Continuous HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
    hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology Inv.inv

/-- Every Minkowski vector is its finite coordinate expansion in the standard basis. -/
theorem hlsMinkowski_expand (p : HLSMinkowskiVector) :
    p = ∑ i, p i • Pi.single i 1 := by
  ext i
  classical
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

/-- Multiplication in the proper orthochronous Lorentz group is continuous for the explicit
pointwise topology. -/
theorem hlsProperOrthoLorentz_mul_continuous : @Continuous
    (hlsProperOrthoLorentzGroup × hlsProperOrthoLorentzGroup)
    hlsProperOrthoLorentzGroup
    (@instTopologicalSpaceProd hlsProperOrthoLorentzGroup hlsProperOrthoLorentzGroup
      hlsProperOrthoLorentzTopology hlsProperOrthoLorentzTopology)
    hlsProperOrthoLorentzTopology (fun gh => gh.1 * gh.2) := by
  letI : TopologicalSpace hlsProperOrthoLorentzGroup := hlsProperOrthoLorentzTopology
  letI : TopologicalSpace
      (hlsProperOrthoLorentzGroup × hlsProperOrthoLorentzGroup) :=
    @instTopologicalSpaceProd hlsProperOrthoLorentzGroup hlsProperOrthoLorentzGroup
      hlsProperOrthoLorentzTopology hlsProperOrthoLorentzTopology
  apply continuous_induced_rng.2
  change @Continuous
    (hlsProperOrthoLorentzGroup × hlsProperOrthoLorentzGroup)
    (HLSMinkowskiVector → HLSMinkowskiVector)
    (@instTopologicalSpaceProd hlsProperOrthoLorentzGroup hlsProperOrthoLorentzGroup
      hlsProperOrthoLorentzTopology hlsProperOrthoLorentzTopology)
    inferInstance (fun gh => ((gh.1 * gh.2 : hlsProperOrthoLorentzGroup) :
      HLSMinkowskiVector → HLSMinkowskiVector))
  rw [continuous_pi_iff]
  intro p
  rw [continuous_pi_iff]
  intro i
  have h_eval (q : HLSMinkowskiVector) : @Continuous hlsProperOrthoLorentzGroup
      HLSMinkowskiVector hlsProperOrthoLorentzTopology inferInstance (fun g => g.1 q) := by
    exact (continuous_apply q).comp continuous_induced_dom
  have h_formula : (fun gh : hlsProperOrthoLorentzGroup × hlsProperOrthoLorentzGroup =>
      ((gh.1 * gh.2 : hlsProperOrthoLorentzGroup).1 p) i) =
      fun gh => ∑ j, (gh.2.1 p j) * (gh.1.1 (Pi.single j 1) i) := by
    funext gh
    change (gh.1.1 (gh.2.1 p)) i = _
    calc
      (gh.1.1 (gh.2.1 p)) i =
          (gh.1.1 (∑ j, (gh.2.1 p) j • Pi.single j 1)) i := by
            rw [← hlsMinkowski_expand (gh.2.1 p)]
      _ = (∑ j, gh.1.1 ((gh.2.1 p) j • Pi.single j 1)) i := by
            rw [map_sum]
      _ = ∑ j, (gh.2.1 p j) * (gh.1.1 (Pi.single j 1) i) := by
            simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h_formula]
  apply continuous_finsetSum
  intro j _
  have hh : @Continuous
      (hlsProperOrthoLorentzGroup × hlsProperOrthoLorentzGroup) ℝ
      (@instTopologicalSpaceProd hlsProperOrthoLorentzGroup hlsProperOrthoLorentzGroup
        hlsProperOrthoLorentzTopology hlsProperOrthoLorentzTopology)
      inferInstance (fun gh => gh.2.1 p j) :=
    (continuous_apply j).comp ((h_eval p).comp continuous_snd)
  have hg : @Continuous
      (hlsProperOrthoLorentzGroup × hlsProperOrthoLorentzGroup) ℝ
      (@instTopologicalSpaceProd hlsProperOrthoLorentzGroup hlsProperOrthoLorentzGroup
        hlsProperOrthoLorentzTopology hlsProperOrthoLorentzTopology)
      inferInstance (fun gh => gh.1.1 (Pi.single j 1) i) :=
    (continuous_apply i).comp ((h_eval (Pi.single j 1)).comp continuous_fst)
  exact hh.mul hg

/-- Signs of the diagonal Minkowski metric in the standard coordinate basis. -/
def hlsMinkowskiCoordinateSign : Fin 4 → ℝ := ![1, -1, -1, -1]

/-- The inverse of a proper Lorentz transformation has a coordinate formula polynomial in the
forward transformation. -/
theorem hlsProperOrthoLorentz_inv_apply (g : hlsProperOrthoLorentzGroup)
    (p : HLSMinkowskiVector) (i : Fin 4) :
    (g.1.symm p) i = hlsMinkowskiCoordinateSign i *
      hlsMinkowskiPairing (g.1 (Pi.single i 1)) p := by
  have hsum := g.2.1 (Pi.single i 1 + g.1.symm p)
  rw [map_add, hlsMinkowskiForm_add, hlsMinkowskiForm_add] at hsum
  rw [g.2.1 (Pi.single i 1), g.2.1 (g.1.symm p)] at hsum
  have hpair : hlsMinkowskiPairing (g.1 (Pi.single i 1)) (g.1 (g.1.symm p)) =
      hlsMinkowskiPairing (Pi.single i 1) (g.1.symm p) := by
    linarith
  simp only [LinearEquiv.apply_symm_apply] at hpair
  fin_cases i <;> simp [hlsMinkowskiCoordinateSign, hlsMinkowskiPairing] at hpair ⊢ <;>
    linarith

/-- Inversion in the proper orthochronous Lorentz group is continuous for the explicit
pointwise topology. -/
theorem hlsProperOrthoLorentz_inv_continuous : @Continuous hlsProperOrthoLorentzGroup
    hlsProperOrthoLorentzGroup hlsProperOrthoLorentzTopology hlsProperOrthoLorentzTopology
    Inv.inv := by
  letI : TopologicalSpace hlsProperOrthoLorentzGroup := hlsProperOrthoLorentzTopology
  apply continuous_induced_rng.2
  change @Continuous hlsProperOrthoLorentzGroup
    (HLSMinkowskiVector → HLSMinkowskiVector) hlsProperOrthoLorentzTopology inferInstance
    (fun g => ((g⁻¹ : hlsProperOrthoLorentzGroup) : HLSMinkowskiVector → HLSMinkowskiVector))
  rw [continuous_pi_iff]
  intro p
  rw [continuous_pi_iff]
  intro i
  have h_eval (q : HLSMinkowskiVector) : @Continuous hlsProperOrthoLorentzGroup
      HLSMinkowskiVector hlsProperOrthoLorentzTopology inferInstance (fun g => g.1 q) := by
    exact (continuous_apply q).comp continuous_induced_dom
  have h_pairing (q : HLSMinkowskiVector) : @Continuous HLSMinkowskiVector ℝ
      inferInstance inferInstance (fun v => hlsMinkowskiPairing v q) := by
    simp only [hlsMinkowskiPairing]
    fun_prop
  have h_formula : (fun g : hlsProperOrthoLorentzGroup => ((g⁻¹).1 p) i) =
      fun g => hlsMinkowskiCoordinateSign i *
        hlsMinkowskiPairing (g.1 (Pi.single i 1)) p := by
    funext g
    exact hlsProperOrthoLorentz_inv_apply g p i
  rw [h_formula]
  exact continuous_const.mul ((h_pairing p).comp (h_eval (Pi.single i 1)))

/-- The defining proper Lorentz action on Minkowski vectors is jointly continuous. -/
theorem hlsProperOrthoLorentz_action_continuous : @Continuous
    (hlsProperOrthoLorentzGroup × HLSMinkowskiVector) HLSMinkowskiVector
    (@instTopologicalSpaceProd hlsProperOrthoLorentzGroup HLSMinkowskiVector
      hlsProperOrthoLorentzTopology inferInstance)
    inferInstance (fun gp => gp.1.1 gp.2) := by
  letI : TopologicalSpace hlsProperOrthoLorentzGroup := hlsProperOrthoLorentzTopology
  letI : TopologicalSpace (hlsProperOrthoLorentzGroup × HLSMinkowskiVector) :=
    @instTopologicalSpaceProd hlsProperOrthoLorentzGroup HLSMinkowskiVector
      hlsProperOrthoLorentzTopology inferInstance
  rw [continuous_pi_iff]
  intro i
  have h_eval (q : HLSMinkowskiVector) : @Continuous hlsProperOrthoLorentzGroup
      HLSMinkowskiVector hlsProperOrthoLorentzTopology inferInstance (fun g => g.1 q) := by
    exact (continuous_apply q).comp continuous_induced_dom
  have h_formula : (fun gp : hlsProperOrthoLorentzGroup × HLSMinkowskiVector =>
      gp.1.1 gp.2 i) =
      fun gp => ∑ j, (gp.2 j) * (gp.1.1 (Pi.single j 1) i) := by
    funext gp
    calc
      (gp.1.1 gp.2) i = (gp.1.1 (∑ j, gp.2 j • Pi.single j 1)) i := by
        rw [← hlsMinkowski_expand gp.2]
      _ = (∑ j, gp.1.1 (gp.2 j • Pi.single j 1)) i := by
        rw [map_sum]
      _ = ∑ j, gp.2 j * (gp.1.1 (Pi.single j 1) i) := by
        simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h_formula]
  apply continuous_finsetSum
  intro j _
  have hp : @Continuous (hlsProperOrthoLorentzGroup × HLSMinkowskiVector) ℝ
      (@instTopologicalSpaceProd hlsProperOrthoLorentzGroup HLSMinkowskiVector
        hlsProperOrthoLorentzTopology inferInstance)
      inferInstance (fun gp => gp.2 j) :=
    (continuous_apply j).comp continuous_snd
  have hg : @Continuous (hlsProperOrthoLorentzGroup × HLSMinkowskiVector) ℝ
      (@instTopologicalSpaceProd hlsProperOrthoLorentzGroup HLSMinkowskiVector
        hlsProperOrthoLorentzTopology inferInstance)
      inferInstance (fun gp => gp.1.1 (Pi.single j 1) i) :=
    (continuous_apply i).comp ((h_eval (Pi.single j 1)).comp continuous_fst)
  exact hp.mul hg

/-- Multiplication in the physical Poincaré group is continuous for its translation--Lorentz
product topology. -/
theorem hlsPhysicalPoincare_mul_continuous : @Continuous
    (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup) HLSPhysicalPoincareGroup
    (@instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
      hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology)
    hlsPhysicalPoincareTopology (fun xy => xy.1 * xy.2) := by
  letI : TopologicalSpace (Multiplicative HLSMinkowskiVector) := hlsTranslationTopology
  letI : TopologicalSpace hlsProperOrthoLorentzGroup := hlsProperOrthoLorentzTopology
  letI : TopologicalSpace HLSPhysicalPoincareGroup := hlsPhysicalPoincareTopology
  letI : TopologicalSpace
      (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup) :=
    @instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
      hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology
  have h_toAdd : @Continuous (Multiplicative HLSMinkowskiVector) HLSMinkowskiVector
      hlsTranslationTopology inferInstance (fun a => a.toAdd) :=
    continuous_induced_dom
  have h_coord : @Continuous HLSPhysicalPoincareGroup
      (Multiplicative HLSMinkowskiVector × hlsProperOrthoLorentzGroup)
      hlsPhysicalPoincareTopology
      (@instTopologicalSpaceProd (Multiplicative HLSMinkowskiVector)
        hlsProperOrthoLorentzGroup hlsTranslationTopology hlsProperOrthoLorentzTopology)
      (fun x => (x.left.toAdd, x.right)) :=
    continuous_induced_dom
  have h_left : @Continuous HLSPhysicalPoincareGroup HLSMinkowskiVector
      hlsPhysicalPoincareTopology inferInstance (fun x => x.left.toAdd) :=
    h_toAdd.comp ((continuous_fst).comp h_coord)
  have h_right : @Continuous HLSPhysicalPoincareGroup hlsProperOrthoLorentzGroup
      hlsPhysicalPoincareTopology hlsProperOrthoLorentzTopology (fun x => x.right) :=
    (continuous_snd).comp h_coord
  have h_action_args : @Continuous
      (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup)
      (hlsProperOrthoLorentzGroup × HLSMinkowskiVector)
      (@instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
        hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology)
      (@instTopologicalSpaceProd hlsProperOrthoLorentzGroup HLSMinkowskiVector
        hlsProperOrthoLorentzTopology inferInstance)
      (fun xy => (xy.1.right, xy.2.left.toAdd)) :=
    (h_right.comp continuous_fst).prodMk (h_left.comp continuous_snd)
  have h_action : @Continuous
      (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup) HLSMinkowskiVector
      (@instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
        hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology)
      inferInstance (fun xy => xy.1.right.1 xy.2.left.toAdd) :=
    hlsProperOrthoLorentz_action_continuous.comp h_action_args
  have h_translation : @Continuous
      (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup) HLSMinkowskiVector
      (@instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
        hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology)
      inferInstance (fun xy => xy.1.left.toAdd + xy.1.right.1 xy.2.left.toAdd) :=
    (h_left.comp continuous_fst).add h_action
  have h_lorentz : @Continuous
      (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup) hlsProperOrthoLorentzGroup
      (@instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
        hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology)
      hlsProperOrthoLorentzTopology (fun xy => xy.1.right * xy.2.right) :=
    hlsProperOrthoLorentz_mul_continuous.comp
      ((h_right.comp continuous_fst).prodMk (h_right.comp continuous_snd))
  have h_translation_mult : @Continuous
      (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup)
      (Multiplicative HLSMinkowskiVector)
      (@instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
        hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology)
      hlsTranslationTopology (fun xy => (xy.1 * xy.2).left) := by
    apply continuous_induced_rng.2
    change @Continuous
        (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup) HLSMinkowskiVector
        (@instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
          hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology)
        inferInstance (fun xy => (xy.1 * xy.2).left.toAdd)
    convert h_translation using 1
    funext xy
    rw [SemidirectProduct.mul_def]
    rfl
  apply continuous_induced_rng.2
  change @Continuous
      (HLSPhysicalPoincareGroup × HLSPhysicalPoincareGroup)
      (Multiplicative HLSMinkowskiVector × hlsProperOrthoLorentzGroup)
      (@instTopologicalSpaceProd HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
        hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology)
      (@instTopologicalSpaceProd (Multiplicative HLSMinkowskiVector)
        hlsProperOrthoLorentzGroup hlsTranslationTopology hlsProperOrthoLorentzTopology)
      (fun xy => ((xy.1 * xy.2).left, (xy.1 * xy.2).right))
  exact h_translation_mult.prodMk h_lorentz

/-- Inversion in the physical Poincaré group is continuous for its translation--Lorentz
product topology. -/
theorem hlsPhysicalPoincare_inv_continuous : @Continuous
    HLSPhysicalPoincareGroup HLSPhysicalPoincareGroup
    hlsPhysicalPoincareTopology hlsPhysicalPoincareTopology Inv.inv := by
  letI : TopologicalSpace (Multiplicative HLSMinkowskiVector) := hlsTranslationTopology
  letI : TopologicalSpace hlsProperOrthoLorentzGroup := hlsProperOrthoLorentzTopology
  letI : TopologicalSpace HLSPhysicalPoincareGroup := hlsPhysicalPoincareTopology
  have h_toAdd : @Continuous (Multiplicative HLSMinkowskiVector) HLSMinkowskiVector
      hlsTranslationTopology inferInstance (fun a => a.toAdd) :=
    continuous_induced_dom
  have h_coord : @Continuous HLSPhysicalPoincareGroup
      (Multiplicative HLSMinkowskiVector × hlsProperOrthoLorentzGroup)
      hlsPhysicalPoincareTopology
      (@instTopologicalSpaceProd (Multiplicative HLSMinkowskiVector)
        hlsProperOrthoLorentzGroup hlsTranslationTopology hlsProperOrthoLorentzTopology)
      (fun x => (x.left.toAdd, x.right)) :=
    continuous_induced_dom
  have h_left : @Continuous HLSPhysicalPoincareGroup HLSMinkowskiVector
      hlsPhysicalPoincareTopology inferInstance (fun x => x.left.toAdd) :=
    h_toAdd.comp ((continuous_fst).comp h_coord)
  have h_right : @Continuous HLSPhysicalPoincareGroup hlsProperOrthoLorentzGroup
      hlsPhysicalPoincareTopology hlsProperOrthoLorentzTopology (fun x => x.right) :=
    (continuous_snd).comp h_coord
  have h_inv_right : @Continuous HLSPhysicalPoincareGroup hlsProperOrthoLorentzGroup
      hlsPhysicalPoincareTopology hlsProperOrthoLorentzTopology (fun x => x.right⁻¹) :=
    hlsProperOrthoLorentz_inv_continuous.comp h_right
  have h_inv_action_args : @Continuous HLSPhysicalPoincareGroup
      (hlsProperOrthoLorentzGroup × HLSMinkowskiVector)
      hlsPhysicalPoincareTopology
      (@instTopologicalSpaceProd hlsProperOrthoLorentzGroup HLSMinkowskiVector
        hlsProperOrthoLorentzTopology inferInstance)
      (fun x => (x.right⁻¹, x.left.toAdd)) :=
    h_inv_right.prodMk h_left
  have h_inv_action : @Continuous HLSPhysicalPoincareGroup HLSMinkowskiVector
      hlsPhysicalPoincareTopology inferInstance (fun x => (x.right⁻¹).1 x.left.toAdd) :=
    hlsProperOrthoLorentz_action_continuous.comp h_inv_action_args
  have h_translation : @Continuous HLSPhysicalPoincareGroup HLSMinkowskiVector
      hlsPhysicalPoincareTopology inferInstance (fun x => -((x.right⁻¹).1 x.left.toAdd)) :=
    h_inv_action.neg
  have h_translation_mult : @Continuous HLSPhysicalPoincareGroup
      (Multiplicative HLSMinkowskiVector) hlsPhysicalPoincareTopology hlsTranslationTopology
      (fun x => (x⁻¹).left) := by
    apply continuous_induced_rng.2
    change @Continuous HLSPhysicalPoincareGroup HLSMinkowskiVector
      hlsPhysicalPoincareTopology inferInstance (fun x => (x⁻¹).left.toAdd)
    convert h_translation using 1
    funext x
    rw [SemidirectProduct.inv_left]
    simp [hlsProperOrthoLorentzAction]
  apply continuous_induced_rng.2
  change @Continuous HLSPhysicalPoincareGroup
      (Multiplicative HLSMinkowskiVector × hlsProperOrthoLorentzGroup)
      hlsPhysicalPoincareTopology
      (@instTopologicalSpaceProd (Multiplicative HLSMinkowskiVector)
        hlsProperOrthoLorentzGroup hlsTranslationTopology hlsProperOrthoLorentzTopology)
      (fun x => ((x⁻¹).left, (x⁻¹).right))
  convert h_translation_mult.prodMk h_inv_right using 1
  funext x
  rw [SemidirectProduct.inv_right]

/-- Closed topological-group certificate for the physical Poincaré group. -/
theorem hlsPhysicalPoincareTopologicalGroupData : HLSPoincareTopologicalGroupData where
  multiplication_continuous := hlsPhysicalPoincare_mul_continuous
  inversion_continuous := hlsPhysicalPoincare_inv_continuous

/-- A physical Poincaré translation with trivial Lorentz component. -/
def hlsTranslation (a : HLSMinkowskiVector) : HLSPhysicalPoincareGroup :=
  ⟨Multiplicative.ofAdd a, 1⟩

/-- A pure proper-orthochronous Lorentz transformation with zero translation. -/
def hlsLorentzAt (g : hlsProperOrthoLorentzGroup) : HLSPhysicalPoincareGroup :=
  ⟨1, g⟩

/-- Translation by parameter `t` in Minkowski coordinate `μ`. -/
def hlsTranslationAt (μ : Fin 4) (t : ℝ) : HLSPhysicalPoincareGroup :=
  hlsTranslation (Pi.single μ t)

/-- The coordinate translation flow starts at the identity. -/
theorem hlsTranslationAt_zero (μ : Fin 4) : hlsTranslationAt μ 0 = 1 := by
  ext <;> simp [hlsTranslationAt, hlsTranslation]

/-- Coordinate translations form a one-parameter subgroup. -/
theorem hlsTranslationAt_add (μ : Fin 4) (s t : ℝ) :
    hlsTranslationAt μ (s + t) = hlsTranslationAt μ s * hlsTranslationAt μ t := by
  ext <;> simp [hlsTranslationAt, hlsTranslation, Pi.single_add]

/-- All Minkowski translations form the translation subgroup of the physical Poincaré group. -/
theorem hlsTranslation_zero : hlsTranslation 0 = 1 := by
  ext <;> simp [hlsTranslation]

/-- Poincaré translations respect vector addition. -/
theorem hlsTranslation_add (a b : HLSMinkowskiVector) :
    hlsTranslation (a + b) = hlsTranslation a * hlsTranslation b := by
  ext <;> simp [hlsTranslation]

/-- Pure Lorentz transformations form their canonical subgroup. -/
theorem hlsLorentzAt_one : hlsLorentzAt 1 = 1 := by
  ext <;> simp [hlsLorentzAt]

/-- The pure-Lorentz embedding is multiplicative. -/
theorem hlsLorentzAt_mul (g h : hlsProperOrthoLorentzGroup) :
    hlsLorentzAt (g * h) = hlsLorentzAt g * hlsLorentzAt h := by
  ext <;> simp [hlsLorentzAt]

/-- The full translation subgroup is continuous for the explicit physical Poincaré topology. -/
theorem hlsTranslation_continuous : @Continuous HLSMinkowskiVector HLSPhysicalPoincareGroup
    inferInstance hlsPhysicalPoincareTopology hlsTranslation := by
  apply continuous_induced_rng.2
  change @Continuous HLSMinkowskiVector
    (Multiplicative HLSMinkowskiVector × hlsProperOrthoLorentzGroup)
    inferInstance (@instTopologicalSpaceProd (Multiplicative HLSMinkowskiVector)
      hlsProperOrthoLorentzGroup hlsTranslationTopology hlsProperOrthoLorentzTopology)
      (fun a => (Multiplicative.ofAdd a, 1))
  refine @Continuous.prodMk (Multiplicative HLSMinkowskiVector) hlsProperOrthoLorentzGroup
    HLSMinkowskiVector hlsTranslationTopology hlsProperOrthoLorentzTopology inferInstance
    (fun a => Multiplicative.ofAdd a) (fun _ => 1) ?_ ?_
  · apply continuous_induced_rng.2
    exact continuous_id
  · apply continuous_induced_rng.2
    exact continuous_const

/-- The pure-Lorentz embedding is continuous for the explicit physical Poincaré topology. -/
theorem hlsLorentzAt_continuous : @Continuous hlsProperOrthoLorentzGroup
    HLSPhysicalPoincareGroup hlsProperOrthoLorentzTopology hlsPhysicalPoincareTopology
    hlsLorentzAt := by
  apply continuous_induced_rng.2
  change @Continuous hlsProperOrthoLorentzGroup
    (Multiplicative HLSMinkowskiVector × hlsProperOrthoLorentzGroup)
    hlsProperOrthoLorentzTopology
    (@instTopologicalSpaceProd (Multiplicative HLSMinkowskiVector)
      hlsProperOrthoLorentzGroup hlsTranslationTopology hlsProperOrthoLorentzTopology)
      (fun g => (1, g))
  refine @Continuous.prodMk (Multiplicative HLSMinkowskiVector) hlsProperOrthoLorentzGroup
    hlsProperOrthoLorentzGroup hlsTranslationTopology hlsProperOrthoLorentzTopology
    hlsProperOrthoLorentzTopology (fun _ => 1) (fun g => g) ?_ ?_
  · apply continuous_induced_rng.2
    change @Continuous hlsProperOrthoLorentzGroup HLSMinkowskiVector
      hlsProperOrthoLorentzTopology inferInstance (fun _ => 0)
    exact @continuous_const hlsProperOrthoLorentzGroup HLSMinkowskiVector
      hlsProperOrthoLorentzTopology inferInstance 0
  · exact @continuous_id hlsProperOrthoLorentzGroup hlsProperOrthoLorentzTopology

/-- Translation followed by Lorentz transformation gives the canonical factorization of every
physical Poincaré element. -/
theorem hlsPoincare_factorization (x : HLSPhysicalPoincareGroup) :
    x = hlsTranslation x.left.toAdd * hlsLorentzAt x.right := by
  ext <;> simp [hlsTranslation, hlsLorentzAt]

/-- Lorentz transformations act on translations by the defining semidirect-product law. -/
theorem hlsLorentzAt_mul_translation (g : hlsProperOrthoLorentzGroup)
    (a : HLSMinkowskiVector) :
    hlsLorentzAt g * hlsTranslation a =
      hlsTranslation (g.1 a) * hlsLorentzAt g := by
  change (⟨1, g⟩ : HLSPhysicalPoincareGroup) *
      (⟨Multiplicative.ofAdd a, 1⟩ : HLSPhysicalPoincareGroup) =
    (⟨Multiplicative.ofAdd (g.1 a), 1⟩ : HLSPhysicalPoincareGroup) *
      (⟨1, g⟩ : HLSPhysicalPoincareGroup)
  rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def]
  simp [hlsProperOrthoLorentzAction]

/-- Coordinate translation is continuous for the explicit physical Poincaré topology. -/
theorem hlsTranslationAt_continuous (μ : Fin 4) : @Continuous ℝ HLSPhysicalPoincareGroup
    inferInstance hlsPhysicalPoincareTopology (hlsTranslationAt μ) := by
  let f : ℝ → HLSMinkowskiVector := fun t => Pi.single μ t
  apply continuous_induced_rng.2
  change @Continuous ℝ (Multiplicative HLSMinkowskiVector × hlsProperOrthoLorentzGroup)
    inferInstance (@instTopologicalSpaceProd (Multiplicative HLSMinkowskiVector)
      hlsProperOrthoLorentzGroup hlsTranslationTopology hlsProperOrthoLorentzTopology)
      (fun t => (Multiplicative.ofAdd (f t), 1))
  refine @Continuous.prodMk (Multiplicative HLSMinkowskiVector) hlsProperOrthoLorentzGroup ℝ
    hlsTranslationTopology hlsProperOrthoLorentzTopology inferInstance
      (fun t => Multiplicative.ofAdd (f t)) (fun _ => 1) ?_ ?_
  · apply continuous_induced_rng.2
    change Continuous f
    rw [continuous_pi_iff]
    intro i
    dsimp [f]
    by_cases h : i = μ
    · subst i
      convert continuous_id using 1
      ext a
      simp
    · simpa [h] using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  · apply continuous_induced_rng.2
    exact continuous_const

/-- The Clifford spin group of the HLS Minkowski form. -/
abbrev HLSSpinGroup := spinGroup hlsMinkowskiForm

/-- Conjugation by a Clifford-spin element as an algebra equivalence of the ambient Clifford
algebra. -/
def hlsSpinConjugation (s : HLSSpinGroup) :
    CliffordAlgebra hlsMinkowskiForm ≃ₐ[ℝ] CliffordAlgebra hlsMinkowskiForm :=
  MulSemiringAction.toAlgEquiv ℝ _ (ConjAct.toConjAct (spinGroup.toUnits s))

/-- Concrete Clifford-spin conjugation on the subspace represented by Clifford vectors. -/
def hlsSpinConjugationOnCliffordVectors (s : HLSSpinGroup) :
    LinearMap.range (CliffordAlgebra.ι hlsMinkowskiForm) →ₗ[ℝ]
      LinearMap.range (CliffordAlgebra.ι hlsMinkowskiForm) :=
  ((hlsSpinConjugation s).toLinearMap.domRestrict
    (LinearMap.range (CliffordAlgebra.ι hlsMinkowskiForm))).codRestrict
      (LinearMap.range (CliffordAlgebra.ι hlsMinkowskiForm)) (by
        rintro ⟨x, p, rfl⟩
        exact spinGroup.conjAct_smul_ι_mem_range_ι s.property p)

/-- Clifford-spin conjugation sends each represented Minkowski vector to another represented
vector. -/
theorem hlsSpinConjugationOnCliffordVectors_apply_ι (s : HLSSpinGroup)
    (p : HLSMinkowskiVector) :
    (hlsSpinConjugationOnCliffordVectors s
      ⟨CliffordAlgebra.ι hlsMinkowskiForm p, LinearMap.mem_range_self _ p⟩ :
      CliffordAlgebra hlsMinkowskiForm) = hlsSpinConjugation s (CliffordAlgebra.ι hlsMinkowskiForm p) :=
  rfl

/-- The Clifford embedding of Minkowski vectors is injective.  Mathlib's equivalence with the
exterior algebra gives this without any signature-specific axiom. -/
theorem hlsCliffordIota_injective :
    Function.Injective (CliffordAlgebra.ι hlsMinkowskiForm) := by
  intro p q hpq
  apply (ExteriorAlgebra.ι_inj ℝ p q).mp
  simpa [CliffordAlgebra.equivExterior] using
    congrArg (CliffordAlgebra.equivExterior hlsMinkowskiForm) hpq

/-- Clifford-spin conjugation is an invertible linear action on represented Minkowski vectors. -/
def hlsSpinConjugationOnCliffordVectorsEquiv (s : HLSSpinGroup) :
    LinearMap.range (CliffordAlgebra.ι hlsMinkowskiForm) ≃ₗ[ℝ]
      LinearMap.range (CliffordAlgebra.ι hlsMinkowskiForm) :=
  { hlsSpinConjugationOnCliffordVectors s with
    invFun := hlsSpinConjugationOnCliffordVectors s⁻¹
    left_inv := by
      intro x
      apply Subtype.ext
      exact show hlsSpinConjugation s⁻¹
          (hlsSpinConjugation s (x : CliffordAlgebra hlsMinkowskiForm)) = x by
        simp [hlsSpinConjugation]
    right_inv := by
      intro x
      apply Subtype.ext
      exact show hlsSpinConjugation s
          (hlsSpinConjugation s⁻¹ (x : CliffordAlgebra hlsMinkowskiForm)) = x by
        simp [hlsSpinConjugation] }

/-- Identifies Minkowski space with the subspace of Clifford vectors. -/
def hlsCliffordIotaRangeEquiv : HLSMinkowskiVector ≃ₗ[ℝ]
    LinearMap.range (CliffordAlgebra.ι hlsMinkowskiForm) :=
  LinearEquiv.ofInjective (CliffordAlgebra.ι hlsMinkowskiForm) hlsCliffordIota_injective

/-- Concrete Lorentz linear equivalence induced by a Clifford-spin element. -/
def hlsSpinMinkowskiLinearEquiv (s : HLSSpinGroup) : HLSMinkowskiVector ≃ₗ[ℝ]
    HLSMinkowskiVector :=
  (hlsCliffordIotaRangeEquiv.trans (hlsSpinConjugationOnCliffordVectorsEquiv s)).trans
    hlsCliffordIotaRangeEquiv.symm

/-- The induced Minkowski action is characterized by Clifford-spin conjugation. -/
theorem hlsCliffordIota_spinMinkowskiLinearEquiv (s : HLSSpinGroup) (p : HLSMinkowskiVector) :
    CliffordAlgebra.ι hlsMinkowskiForm (hlsSpinMinkowskiLinearEquiv s p) =
      hlsSpinConjugation s (CliffordAlgebra.ι hlsMinkowskiForm p) := by
  change (hlsCliffordIotaRangeEquiv (hlsSpinMinkowskiLinearEquiv s p) :
    CliffordAlgebra hlsMinkowskiForm) = hlsSpinConjugation s
      (CliffordAlgebra.ι hlsMinkowskiForm p)
  simp [hlsSpinMinkowskiLinearEquiv, hlsCliffordIotaRangeEquiv,
    hlsSpinConjugationOnCliffordVectorsEquiv, hlsSpinConjugationOnCliffordVectors]

/-- The concrete Clifford-spin action preserves the Minkowski quadratic form. -/
theorem hlsSpinMinkowskiLinearEquiv_preserves_minkowski (s : HLSSpinGroup)
    (p : HLSMinkowskiVector) :
    hlsMinkowskiForm (hlsSpinMinkowskiLinearEquiv s p) = hlsMinkowskiForm p := by
  apply FaithfulSMul.algebraMap_injective ℝ (CliffordAlgebra hlsMinkowskiForm)
  calc
    algebraMap ℝ (CliffordAlgebra hlsMinkowskiForm)
        (hlsMinkowskiForm (hlsSpinMinkowskiLinearEquiv s p)) =
        CliffordAlgebra.ι hlsMinkowskiForm (hlsSpinMinkowskiLinearEquiv s p) *
          CliffordAlgebra.ι hlsMinkowskiForm (hlsSpinMinkowskiLinearEquiv s p) := by
          symm
          exact CliffordAlgebra.ι_sq_scalar _ _
    _ = hlsSpinConjugation s (CliffordAlgebra.ι hlsMinkowskiForm p) *
          hlsSpinConjugation s (CliffordAlgebra.ι hlsMinkowskiForm p) := by
          rw [hlsCliffordIota_spinMinkowskiLinearEquiv]
    _ = hlsSpinConjugation s
          (CliffordAlgebra.ι hlsMinkowskiForm p * CliffordAlgebra.ι hlsMinkowskiForm p) := by
          symm
          exact map_mul _ _ _
    _ = hlsSpinConjugation s
          (algebraMap ℝ (CliffordAlgebra hlsMinkowskiForm) (hlsMinkowskiForm p)) := by
          rw [CliffordAlgebra.ι_sq_scalar]
    _ = algebraMap ℝ (CliffordAlgebra hlsMinkowskiForm) (hlsMinkowskiForm p) := by
          exact (hlsSpinConjugation s).commutes _

/-- The canonical Clifford construction gives a genuine homomorphism from Spin to the full
Lorentz group.  Establishing that its image is exactly the proper orthochronous component is
kept separate below. -/
def hlsCliffordSpinToLorentz : HLSSpinGroup →* hlsLorentzGroup where
  toFun s := ⟨hlsSpinMinkowskiLinearEquiv s,
    hlsSpinMinkowskiLinearEquiv_preserves_minkowski s⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    change hlsSpinMinkowskiLinearEquiv 1 p = p
    apply hlsCliffordIota_injective
    rw [hlsCliffordIota_spinMinkowskiLinearEquiv]
    simp [hlsSpinConjugation]
  map_mul' := by
    intro s t
    apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    change hlsSpinMinkowskiLinearEquiv (s * t) p =
      hlsSpinMinkowskiLinearEquiv s (hlsSpinMinkowskiLinearEquiv t p)
    apply hlsCliffordIota_injective
    rw [hlsCliffordIota_spinMinkowskiLinearEquiv,
      hlsCliffordIota_spinMinkowskiLinearEquiv,
      hlsCliffordIota_spinMinkowskiLinearEquiv]
    simp [hlsSpinConjugation, mul_smul]

/-- The algebraic Spin action with its Lorentz subgroup coercion exposed. -/
def hlsCliffordSpinToLinearEquiv : HLSSpinGroup →*
    (HLSMinkowskiVector ≃ₗ[ℝ] HLSMinkowskiVector) :=
  (Subgroup.subtype hlsLorentzGroup).comp hlsCliffordSpinToLorentz

/-- The physical `Spin⁺(1,3)` subgroup: exactly the Spin elements whose concrete Clifford action
is proper and preserves time orientation.  This avoids identifying Mathlib's full algebraic spin
group with the physical connected component. -/
abbrev HLSSpinPlusGroup : Subgroup HLSSpinGroup :=
  Subgroup.comap hlsCliffordSpinToLinearEquiv hlsProperOrthoLorentzGroup

/-- The canonical physical Spin-plus action on the proper orthochronous Lorentz group. -/
def hlsSpinPlusToProperLorentz : HLSSpinPlusGroup →* hlsProperOrthoLorentzGroup :=
  (hlsCliffordSpinToLinearEquiv.comp (Subgroup.subtype HLSSpinPlusGroup)).codRestrict
    hlsProperOrthoLorentzGroup (fun s => s.property)

/-- Forgetting properness from the canonical Spin-plus action recovers Clifford conjugation. -/
theorem hlsSpinPlusToProperLorentz_canonical :
    hlsProperOrthoLorentzToLorentz.comp hlsSpinPlusToProperLorentz =
      hlsCliffordSpinToLorentz.comp (Subgroup.subtype HLSSpinPlusGroup) :=
  rfl

/-- A concrete spacelike unit vector used to exhibit the central kernel element of the
Clifford-spin action. -/
def hlsSpatialBasisOne : HLSMinkowskiVector := Pi.single 1 1

/-- The chosen spacelike basis vector has Minkowski square `-1`. -/
theorem hlsSpatialBasisOne_square : hlsMinkowskiForm hlsSpatialBasisOne = -1 := by
  rw [hlsMinkowskiForm_apply]
  change (0 : ℝ) ^ 2 - 1 ^ 2 - 0 ^ 2 - 0 ^ 2 = -1
  norm_num

/-- The central scalar `-1` belongs to the concrete Clifford spin group. -/
theorem hlsCliffordNegOne_mem_spin :
    (-1 : CliffordAlgebra hlsMinkowskiForm) ∈ HLSSpinGroup := by
  let e : HLSMinkowskiVector := hlsSpatialBasisOne
  have he : hlsMinkowskiForm e = -1 := hlsSpatialBasisOne_square
  have he_unit : IsUnit (hlsMinkowskiForm e) := by
    rw [he]
    exact isUnit_neg_one
  have hι_unit : IsUnit (CliffordAlgebra.ι hlsMinkowskiForm e) :=
    CliffordAlgebra.isUnit_ι_of_isUnit hlsMinkowskiForm he_unit
  let u : (CliffordAlgebra hlsMinkowskiForm)ˣ := hι_unit.unit
  have hu : (u : CliffordAlgebra hlsMinkowskiForm) = CliffordAlgebra.ι hlsMinkowskiForm e :=
    hι_unit.unit_spec
  have hu_lipschitz : u ∈ lipschitzGroup hlsMinkowskiForm := by
    change u ∈ Subgroup.closure
      ((fun x : (CliffordAlgebra hlsMinkowskiForm)ˣ =>
        (x : CliffordAlgebra hlsMinkowskiForm)) ⁻¹'
        Set.range (CliffordAlgebra.ι hlsMinkowskiForm))
    apply Subgroup.subset_closure
    exact ⟨e, hu⟩
  apply spinGroup.mem_iff.mpr
  constructor
  · apply pinGroup.mem_iff.mpr
    constructor
    · refine ⟨u * u, (lipschitzGroup hlsMinkowskiForm).mul_mem hu_lipschitz hu_lipschitz, ?_⟩
      change (u : CliffordAlgebra hlsMinkowskiForm) * u = -1
      rw [hu, CliffordAlgebra.ι_sq_scalar, he]
      simp
    · constructor <;> simp
  · exact (CliffordAlgebra.even hlsMinkowskiForm).neg_mem
      (CliffordAlgebra.even hlsMinkowskiForm).one_mem

/-- The central Clifford scalar `-1` as a Spin element. -/
def hlsSpinNegativeOne : HLSSpinGroup := ⟨-1, hlsCliffordNegOne_mem_spin⟩

/-- The central Clifford scalar `-1` acts trivially on Minkowski vectors. -/
theorem hlsSpinNegativeOne_action :
    hlsSpinMinkowskiLinearEquiv hlsSpinNegativeOne =
      LinearEquiv.refl ℝ HLSMinkowskiVector := by
  apply LinearEquiv.ext
  intro p
  apply hlsCliffordIota_injective
  rw [hlsCliffordIota_spinMinkowskiLinearEquiv]
  let u : (CliffordAlgebra hlsMinkowskiForm)ˣ := spinGroup.toUnits hlsSpinNegativeOne
  have hu_sq : u * u = 1 := by
    apply Units.ext
    change (u : CliffordAlgebra hlsMinkowskiForm) * u = 1
    simp [u, hlsSpinNegativeOne, spinGroup.toUnits]
  have hu_inv : u⁻¹ = u := by
    rw [← one_mul u⁻¹, ← hu_sq, mul_assoc, mul_inv_cancel, mul_one]
  change (u : CliffordAlgebra hlsMinkowskiForm) * CliffordAlgebra.ι hlsMinkowskiForm p *
      (↑(u⁻¹) : CliffordAlgebra hlsMinkowskiForm) = CliffordAlgebra.ι hlsMinkowskiForm p
  rw [hu_inv]
  simp [u, hlsSpinNegativeOne, spinGroup.toUnits]

/-- The central Clifford scalar `-1` lies in the physically selected Spin-plus subgroup. -/
def hlsSpinPlusNegativeOne : HLSSpinPlusGroup :=
  ⟨hlsSpinNegativeOne, by
    change hlsSpinMinkowskiLinearEquiv hlsSpinNegativeOne ∈ hlsProperOrthoLorentzGroup
    rw [hlsSpinNegativeOne_action]
    exact hlsProperOrthoLorentzGroup.one_mem⟩

/-- The canonical Spin-plus map sends its central `-1` to the Lorentz identity. -/
theorem hlsSpinPlusNegativeOne_maps_to_one :
    hlsSpinPlusToProperLorentz hlsSpinPlusNegativeOne = 1 := by
  apply Subtype.ext
  exact hlsSpinNegativeOne_action

/-- The central Spin-plus element `-1` is distinct from the identity. -/
theorem hlsSpinPlusNegativeOne_ne_one : hlsSpinPlusNegativeOne ≠ 1 := by
  intro h
  have hc := congrArg (fun s : HLSSpinPlusGroup =>
    (s.1 : CliffordAlgebra hlsMinkowskiForm)) h
  change (-1 : CliffordAlgebra hlsMinkowskiForm) = 1 at hc
  have hr : (-1 : ℝ) = 1 := by
    apply FaithfulSMul.algebraMap_injective ℝ (CliffordAlgebra hlsMinkowskiForm)
    simpa using hc
  norm_num at hr

/-- The canonical physical Spin-plus action has a nonidentity kernel element.  This is the
concrete half of the usual double-cover statement; surjectivity and exact kernel classification
remain separate obligations. -/
theorem hlsSpinPlusCoverKernel_exists_ne_one :
    ∃ k : hlsSpinPlusToProperLorentz.ker, k ≠ 1 := by
  refine ⟨⟨hlsSpinPlusNegativeOne,
    MonoidHom.mem_ker.mpr hlsSpinPlusNegativeOne_maps_to_one⟩, ?_⟩
  intro h
  have hu := congrArg (fun k : hlsSpinPlusToProperLorentz.ker =>
    (k.1 : HLSSpinPlusGroup)) h
  exact hlsSpinPlusNegativeOne_ne_one hu

/-- The two expected central kernel elements give an actual embedding of `Bool` into the
canonical Spin-plus kernel. -/
def hlsSpinPlusCoverKernelBool : Bool → hlsSpinPlusToProperLorentz.ker
  | false => 1
  | true => ⟨hlsSpinPlusNegativeOne,
    MonoidHom.mem_ker.mpr hlsSpinPlusNegativeOne_maps_to_one⟩

/-- The identity and central `-1` are distinct elements of the canonical Spin-plus kernel. -/
theorem hlsSpinPlusCoverKernelBool_injective :
    Function.Injective hlsSpinPlusCoverKernelBool := by
  intro a b h
  cases a <;> cases b
  · rfl
  · change (1 : hlsSpinPlusToProperLorentz.ker) =
      ⟨hlsSpinPlusNegativeOne,
        MonoidHom.mem_ker.mpr hlsSpinPlusNegativeOne_maps_to_one⟩ at h
    have hu := congrArg (fun k : hlsSpinPlusToProperLorentz.ker =>
      (k.1 : HLSSpinPlusGroup)) h
    exact False.elim (hlsSpinPlusNegativeOne_ne_one hu.symm)
  · change ⟨hlsSpinPlusNegativeOne,
      MonoidHom.mem_ker.mpr hlsSpinPlusNegativeOne_maps_to_one⟩ =
      (1 : hlsSpinPlusToProperLorentz.ker) at h
    have hu := congrArg (fun k : hlsSpinPlusToProperLorentz.ker =>
      (k.1 : HLSSpinPlusGroup)) h
    exact False.elim (hlsSpinPlusNegativeOne_ne_one hu)
  · rfl

/-- The canonical Spin-plus kernel contains the two-element central subgroup. -/
def hlsSpinPlusCoverKernelBoolEmbedding : Bool ↪ hlsSpinPlusToProperLorentz.ker :=
  ⟨hlsSpinPlusCoverKernelBool, hlsSpinPlusCoverKernelBool_injective⟩

/-- The remaining standard double-cover theorem for the explicitly defined physical
`Spin⁺(1,3)` map.  No arbitrary cover map is accepted: any future proof must establish these
properties for `hlsSpinPlusToProperLorentz` itself. -/
structure HLSSpinLorentzCoverData where
  surjective : Function.Surjective hlsSpinPlusToProperLorentz
  kernel_equiv_bool : hlsSpinPlusToProperLorentz.ker ≃ Bool

/-- Spin-plus action on translations through its canonical proper Lorentz action. -/
def hlsSpinTranslationAction : HLSSpinPlusGroup →*
    MulAut (Multiplicative HLSMinkowskiVector) :=
  hlsProperOrthoLorentzAction.comp hlsSpinPlusToProperLorentz

/-- Physical Spin-plus Poincaré group. -/
abbrev HLSSpinPoincareGroup :=
  Multiplicative HLSMinkowskiVector ⋊[hlsSpinTranslationAction] HLSSpinPlusGroup

/-- The canonical physical Spin-plus action induces a Poincaré homomorphism. -/
def hlsSpinPoincareToPhysical : HLSSpinPoincareGroup →* HLSPhysicalPoincareGroup where
  toFun x := ⟨x.left, hlsSpinPlusToProperLorentz x.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [hlsSpinTranslationAction]

/-- The induced Spin-plus Poincaré homomorphism is surjective once the canonical Spin-plus
double-cover theorem is supplied. -/
theorem hlsSpinPoincareToPhysical_surjective (cover : HLSSpinLorentzCoverData) :
    Function.Surjective hlsSpinPoincareToPhysical := by
  rintro ⟨translation, lorentz⟩
  obtain ⟨spin, hspin⟩ := cover.surjective lorentz
  refine ⟨⟨translation, spin⟩, ?_⟩
  ext
  · rfl
  · subst lorentz
    rfl

/-- Every element of the Lorentz group preserves the physical mass-shell invariant. -/
theorem hlsLorentz_preserves_minkowski (g : hlsLorentzGroup) (p : HLSMinkowskiVector) :
    hlsMinkowskiForm (g.1 p) = hlsMinkowskiForm p :=
  g.2 p

/-- Preserving the Minkowski quadratic form also preserves its polarized bilinear pairing. -/
theorem hlsLorentz_preserves_pairing (g : hlsLorentzGroup) (p q : HLSMinkowskiVector) :
    hlsMinkowskiPairing (g.1 p) (g.1 q) = hlsMinkowskiPairing p q := by
  have hsum := g.2 (p + q)
  rw [map_add, hlsMinkowskiForm_add, hlsMinkowskiForm_add] at hsum
  rw [g.2 p, g.2 q] at hsum
  linarith

/-- Lorentz transformations preserve every mass shell. -/
theorem hlsLorentz_preserves_massShell (g : hlsLorentzGroup) (m : ℝ)
    (p : HLSMinkowskiVector) :
    hlsMassShell m (g.1 p) ↔ hlsMassShell m p := by
  change hlsMinkowskiForm (g.1 p) = m ^ 2 ↔ hlsMinkowskiForm p = m ^ 2
  rw [hlsLorentz_preserves_minkowski]

/-- The concrete Clifford-spin action preserves every physical mass shell. -/
theorem hlsCliffordSpin_preserves_massShell (s : HLSSpinGroup) (m : ℝ)
    (p : HLSMinkowskiVector) :
    hlsMassShell m ((hlsCliffordSpinToLorentz s).1 p) ↔ hlsMassShell m p :=
  hlsLorentz_preserves_massShell (hlsCliffordSpinToLorentz s) m p

/-- Proper orthochronous Lorentz transformations preserve every physical mass shell. -/
theorem hlsProperOrthoLorentz_preserves_massShell (g : hlsProperOrthoLorentzGroup) (m : ℝ)
    (p : HLSMinkowskiVector) :
    hlsMassShell m (g.1 p) ↔ hlsMassShell m p := by
  change hlsMinkowskiForm (g.1 p) = m ^ 2 ↔ hlsMinkowskiForm p = m ^ 2
  rw [g.2.1]

/-- Proper orthochronous Lorentz transformations preserve the Minkowski pairing. -/
theorem hlsProperOrthoLorentz_preserves_pairing (g : hlsProperOrthoLorentzGroup)
    (p q : HLSMinkowskiVector) :
    hlsMinkowskiPairing (g.1 p) (g.1 q) = hlsMinkowskiPairing p q :=
  hlsLorentz_preserves_pairing (hlsProperOrthoLorentzToLorentz g) p q

/-- Proper orthochronous Lorentz transformations preserve the full future-timelike cone. -/
theorem hlsProperOrthoLorentz_preserves_futureTimelike (g : hlsProperOrthoLorentzGroup)
    (p : HLSMinkowskiVector) : hlsFutureTimelike (g.1 p) ↔ hlsFutureTimelike p :=
  g.2.2.2 p

/-- The canonical Spin-plus action preserves future timelike momenta. -/
theorem hlsSpinPlus_preserves_futureTimelike (s : HLSSpinPlusGroup)
    (p : HLSMinkowskiVector) :
    hlsFutureTimelike ((hlsSpinPlusToProperLorentz s).1 p) ↔ hlsFutureTimelike p :=
  hlsProperOrthoLorentz_preserves_futureTimelike (hlsSpinPlusToProperLorentz s) p

/-- The canonical Spin-plus action preserves all physical mass shells. -/
theorem hlsSpinPlus_preserves_massShell (s : HLSSpinPlusGroup) (m : ℝ)
    (p : HLSMinkowskiVector) :
    hlsMassShell m ((hlsSpinPlusToProperLorentz s).1 p) ↔ hlsMassShell m p :=
  hlsProperOrthoLorentz_preserves_massShell (hlsSpinPlusToProperLorentz s) m p

/-- Unit future timelike rest momentum for a unit-mass particle. -/
def hlsUnitRestMomentum : HLSMinkowskiVector := ![1, 0, 0, 0]

/-- Its energy is positive. -/
theorem hlsUnitRestMomentum_positive_energy : 0 < hlsUnitRestMomentum 0 := by
  norm_num [hlsUnitRestMomentum]

/-- Its Minkowski square is the unit mass squared. -/
theorem hlsUnitRestMomentum_mass_shell :
    hlsMinkowskiForm hlsUnitRestMomentum = 1 := by
  rw [hlsMinkowskiForm_apply]
  change (1 : ℝ) ^ 2 - 0 ^ 2 - 0 ^ 2 - 0 ^ 2 = 1
  norm_num

/-- Unit rest momentum is future timelike. -/
theorem hlsUnitRestMomentum_futureTimelike : hlsFutureTimelike hlsUnitRestMomentum := by
  constructor
  · exact hlsUnitRestMomentum_positive_energy
  · rw [hlsUnitRestMomentum_mass_shell]
    norm_num

end GaloisForLFunctions.HTGeometry
