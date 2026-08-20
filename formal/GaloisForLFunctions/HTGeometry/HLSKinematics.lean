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

/-- Translation by parameter `t` in Minkowski coordinate `μ`, viewed as a physical Poincaré
element with trivial Lorentz component. -/
def hlsTranslationAt (μ : Fin 4) (t : ℝ) : HLSPhysicalPoincareGroup :=
  ⟨Multiplicative.ofAdd (Pi.single μ t), 1⟩

/-- The coordinate translation flow starts at the identity. -/
theorem hlsTranslationAt_zero (μ : Fin 4) : hlsTranslationAt μ 0 = 1 := by
  ext <;> simp [hlsTranslationAt]

/-- Coordinate translations form a one-parameter subgroup. -/
theorem hlsTranslationAt_add (μ : Fin 4) (s t : ℝ) :
    hlsTranslationAt μ (s + t) = hlsTranslationAt μ s * hlsTranslationAt μ t := by
  ext <;> simp [hlsTranslationAt, Pi.single_add]

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

/-- Algebraic data of the spin double-cover map required to pass from Mathlib's Clifford spin
group to the proper orthochronous Lorentz group.  Its two-point kernel and surjectivity make the
covering degree explicit.  The canonical map to the full Lorentz group is constructed above;
this record isolates the still-needed proof that it restricts to a surjective proper two-fold
cover. -/
structure HLSSpinLorentzCoverData where
  toLorentz : HLSSpinGroup →* hlsProperOrthoLorentzGroup
  canonical : hlsProperOrthoLorentzToLorentz.comp toLorentz = hlsCliffordSpinToLorentz
  surjective : Function.Surjective toLorentz
  kernel_equiv_bool : toLorentz.ker ≃ Bool

/-- Spin action on translations induced by a supplied spin-to-Lorentz cover. -/
def hlsSpinTranslationAction (cover : HLSSpinLorentzCoverData) :
    HLSSpinGroup →* MulAut (Multiplicative HLSMinkowskiVector) :=
  hlsProperOrthoLorentzAction.comp cover.toLorentz

/-- Spin-Poincaré group associated to a supplied cover of the proper orthochronous Lorentz group. -/
abbrev HLSSpinPoincareGroup (cover : HLSSpinLorentzCoverData) :=
  Multiplicative HLSMinkowskiVector ⋊[hlsSpinTranslationAction cover] HLSSpinGroup

/-- The spin-to-Lorentz cover induces a homomorphism of the associated Poincaré groups. -/
def hlsSpinPoincareToPhysical (cover : HLSSpinLorentzCoverData) :
    HLSSpinPoincareGroup cover →* HLSPhysicalPoincareGroup where
  toFun x := ⟨x.left, cover.toLorentz x.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by
    ext <;> simp [hlsSpinTranslationAction]

/-- The induced spin-Poincaré homomorphism is surjective whenever the Lorentz cover is. -/
theorem hlsSpinPoincareToPhysical_surjective (cover : HLSSpinLorentzCoverData) :
    Function.Surjective (hlsSpinPoincareToPhysical cover) := by
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
