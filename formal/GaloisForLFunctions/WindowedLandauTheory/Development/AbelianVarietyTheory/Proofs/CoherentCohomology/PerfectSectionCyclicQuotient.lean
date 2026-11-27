import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.DualCokernelKernel
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectFreeSectionKernel
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionIsomorphism
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.GlobalLineBundleCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundleTrivialization
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.LocalRing.Quotient

/-! Over a local base with a trivial closed fibre, a quotient of the base
ring trivializes the bundle and presents the first dual cokernel. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology GlobalTheory.MatrixKernels ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

private theorem trivial_finrank_globalSections {k : Type} [Field k] {X : Scheme.{0}}
    {g : X ⟶ Spec (.of k)} [IsIso g.appTop] {L : LB X} (hL : L.IsLB)
    (h : ∃ s : L.Gen, s.IsGen) :
    letI := sectionBaseModule g (toMod L) ⊤
    Module.finrank k Γ(toMod L, ⊤) = 1 := by
  letI := sectionAlgebra g (⊤ : X.Opens)
  letI := sectionBaseModule g (toMod L) ⊤
  letI : IsScalarTower k Γ(X, ⊤) Γ(toMod L, ⊤) := .of_algebraMap_smul fun _ _ => rfl
  obtain ⟨s, hs⟩ := LB.exists_gen_iff_exists_iso_trivial.mp h
  let e := (chartEquiv (LB.isLB_trivial X) PUnit.unit (V := ⊤) le_rfl).symm.trans
    (sectionIsoEquiv (LB.isLB_trivial X) hL hs)
  have he : Function.Bijective (algebraMap k Γ(X, ⊤)) := by
    change Function.Bijective
      (((Scheme.ΓSpecIso (.of k)).inv ≫ g.appLE ⊤ ⊤ le_top).hom)
    rw [show g.appLE ⊤ ⊤ le_top = g.appTop by
      simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.preimage_top]]
    exact ConcreteCategory.bijective_of_isIso _
  let u := (LinearEquiv.ofBijective (Algebra.linearMap k Γ(X, ⊤)) he).trans (e.restrictScalars k)
  rw [← u.finrank_eq, Module.finrank_self]

private theorem isUnit_res_coord_of_trivial {X : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    (hunit : ∀ a : Γ(X, ⊤), a ≠ 0 → IsUnit a)
    (h : ∃ t : L.Gen, t.IsGen) {s : Γ(toMod L, ⊤)} (hs : s ≠ 0)
    (i : L.ι) {V : X.Opens} (hV : V ≤ L.U i) :
    IsUnit (resG X (le_inf le_top hV) (coord s i)) := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨a, ha⟩ := section_proportional_to_gen hL (globalCoordinates s) t ht
  have hn : a ≠ 0 := by
    intro hz
    apply hs
    apply globalCoordinates.injective
    have hh (i : L.ι) : (globalCoordinates s).f i = (globalCoordinates 0).f i := by
      rw [ha i, hz, map_zero, zero_mul, globalCoordinates_apply, coord_zero, map_zero]
    generalize globalCoordinates s = u at hh ⊢
    generalize globalCoordinates (0 : Γ(toMod L, ⊤)) = v at hh ⊢
    cases u
    cases v
    cases funext hh
    rfl
  have hun : IsUnit a := hunit a hn
  rw [← resG_resG (le_inf le_top le_rfl) hV, ← globalCoordinates_apply, ha i]
  exact ((hun.map (resG X le_top)).mul (t.s i).isUnit).map _

private theorem compare_value {S T : Type} [CommRing S] [CommRing T]
    {X Y Z : Scheme.{0}} {g : Y ⟶ Spec (.of S)} {g₀ : Z ⟶ Spec (.of T)}
    {π : Y ⟶ X} {π₀ : Z ⟶ X} {j : Z ⟶ Y} (β : S →+* T)
    (h₁ : j ≫ π = π₀) (h₂ : j ≫ g = g₀ ≫ Spec.map (CommRingCat.ofHom β))
    {a : ℕ} (W : X.Opens) (u : Fin a → Γ(X, W)) (v : Fin a → S) :
    letI := sectionAlgebra g (π ⁻¹ᵁ W)
    letI := sectionAlgebra g₀ (π₀ ⁻¹ᵁ W)
    let h : π₀ ⁻¹ᵁ W ≤ j ⁻¹ᵁ (π ⁻¹ᵁ W) := by rw [← Scheme.Hom.comp_preimage, h₁]
    j.appLE _ _ h (∑ k, algebraMap S Γ(Y, π ⁻¹ᵁ W) (v k) * π.app W (u k)) =
      ∑ k, algebraMap T Γ(Z, π₀ ⁻¹ᵁ W) (β (v k)) * π₀.app W (u k) := by
  subst π₀
  letI : Algebra S T := β.toAlgebra
  letI := sectionAlgebra g (π ⁻¹ᵁ W)
  letI := sectionAlgebra g₀ ((j ≫ π) ⁻¹ᵁ W)
  let A := (j ≫ π) ⁻¹ᵁ W
  let h : A ≤ j ⁻¹ᵁ (π ⁻¹ᵁ W) := le_rfl
  change j.appLE _ _ h _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc : j.appLE _ _ h (π.app W (u k)) = (j ≫ π).app W (u k) := by
    change (π.app W ≫ j.appLE _ _ h) (u k) = _
    rw [← Scheme.Hom.comp_appLE, ← Scheme.Hom.app_eq_appLE]
  exact ((j.appLE _ _ h).hom.map_mul _ _).trans (congrArg₂ (· * ·)
    (appLE_base_algebraMap h₂ h (v k)) hc)

/-- Over a local base, lift a nonzero closed-fibre section to the cyclic
quotient furnished by the dual cokernel. Properness makes that section a
generator everywhere on the quotient. -/
theorem exists_quotient_with_generator {R : Type} [CommRing R] [IsLocalRing R]
    {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {f : X ⟶ Spec (.of R)} [UniversallyClosed f]
    {κ : Type} [LinearOrder κ] [Fintype κ] (U : κ → X.Opens)
    (hcov : ⨆ i, U i = ⊤)
    (hU : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (coverInter ⊤ U s))
    {C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : C ⟶ cech f (toMod L) U)
    (hfree : ∀ n, Module.Free R (C.X n) ∧ Module.Finite R (C.X n))
    (hφ : ∀ (S : Type) [CommRing S] [Algebra R S], QuasiIso
      (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (ComplexShape.up ℕ)).map φ))
    {X₀ : Scheme.{0}} {π₀ : X₀ ⟶ X} {f₀ : X₀ ⟶ Spec (.of (IsLocalRing.ResidueField R))}
    (H₀ : IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    [IsIso f₀.appTop] (ht : ∃ t : (L.pull π₀).Gen, t.IsGen) :
    ∃ I : Ideal R, I ≤ IsLocalRing.maximalIdeal R ∧
      Nonempty ((Module.Dual R (C.X 0) ⧸ LinearMap.range (C.d 0 1).hom.dualMap) ≃ₗ[R] (R ⧸ I)) ∧
      ∃ t : (L.pull (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))).Gen,
        t.IsGen := by
  let k := IsLocalRing.ResidueField R
  let α₀ := IsLocalRing.residue R
  haveI (n : ℕ) : Module.Free R (C.X n) := (hfree n).1
  haveI (n : ℕ) : Module.Finite R (C.X n) := (hfree n).2
  let p := Module.finBasis R (C.X 0)
  let q := Module.finBasis R (C.X 1)
  let D := LinearMap.toMatrix p q (C.d 0 1).hom
  letI := sectionBaseModule f₀ (toMod (L.pull π₀)) ⊤
  obtain ⟨e₀, he₀⟩ := exists_free_kernel_section_equiv hL U hcov hU φ p q α₀ H₀ (hφ k)
  have hrank : Module.finrank k (LinearMap.ker (D.map α₀).mulVecLin) = 1 :=
    e₀.finrank_eq.trans (trivial_finrank_globalSections (hL.pull π₀) ht)
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_quotient_equiv_of_residue_finrank_one D hrank
  refine ⟨I, hI, ⟨(dualCokernelEquiv p q (C.d 0 1).hom).trans e⟩, ?_⟩
  let S := R ⧸ I
  have hproper : I ≠ ⊤ := fun hn => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.mp (hn ▸ hI))
  letI : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hproper
  letI : IsLocalRing S := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let α := Ideal.Quotient.mk I
  let β : S →ₐ[R] k := Ideal.Quotient.factorₐ R hI
  let σ := Spec.map (CommRingCat.ofHom α)
  let ρ : Spec (.of k) ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom β.toRingHom)
  have hρ : ρ ≫ σ = Spec.map (CommRingCat.ofHom α₀) := by
    rw [← Spec.map_comp]
    rfl
  let Y := pullback f σ
  let π := pullback.fst f σ
  let g := pullback.snd f σ
  have H : IsPullback π g f σ := IsPullback.of_hasPullback _ _
  have hjw : π₀ ≫ f = (f₀ ≫ ρ) ≫ σ := H₀.w.trans
    ((congrArg (fun m : Spec (.of k) ⟶ Spec (.of R) => f₀ ≫ m) hρ.symm).trans
      (Category.assoc f₀ ρ σ).symm)
  let j := H.lift π₀ (f₀ ≫ ρ) hjw
  have h₁ : j ≫ π = π₀ := H.lift_fst _ _ _
  have h₂ : j ≫ g = f₀ ≫ ρ := H.lift_snd _ _ _
  let v := kernelEquiv D e.toLinearMap
  let v₀ := kernelEquiv D (β.toLinearMap.comp e.toLinearMap)
  have hv₀ : v₀ ≠ 0 := by
    intro hz
    have he : β.toLinearMap.comp e.toLinearMap = 0 :=
      (kernelEquiv D).injective (hz.trans (map_zero _).symm)
    obtain ⟨r, hr⟩ := e.surjective (1 : S)
    have h : β (e r) = 0 := LinearMap.congr_fun he r
    exact one_ne_zero ((map_one β).symm.trans ((congrArg β hr).symm.trans h))
  letI := sectionBaseModule g (toMod (L.pull π)) ⊤
  obtain ⟨eg, heg⟩ := exists_free_kernel_section_equiv hL U hcov hU φ p q α H (hφ S)
  let W (i : κ × L.ι) := coverInter ⊤ U {i.1} ⊓ L.U i.2
  let c (i : κ × L.ι) : (L.pull π).ι := fun _ => i.2
  let d (i : κ × L.ι) : (L.pull π₀).ι := fun _ => i.2
  let hW (i : κ × L.ι) : π ⁻¹ᵁ W i ≤ (L.pull π).U (c i) :=
    (π.preimage_mono inf_le_right).trans (pull_chart L π i.2).ge
  let hW₀ (i : κ × L.ι) : π₀ ⁻¹ᵁ W i ≤ (L.pull π₀).U (d i) :=
    (π₀.preimage_mono inf_le_right).trans (pull_chart L π₀ i.2).ge
  let a (i : κ × L.ι) := resG Y (hW i) ((globalCoordinates (eg v)).f (c i))
  let a₀ (i : κ × L.ι) := resG X₀ (hW₀ i) ((globalCoordinates (e₀ v₀)).f (d i))
  let Ω : Y.Opens := ⨆ i, Y.basicOpen (a i)
  letI : UniversallyClosed g := MorphismProperty.of_isPullback H inferInstance
  have hc : IsClosed (g '' (Ω : Set Y)ᶜ) := g.isClosedMap _ Ω.isOpen.isClosed_compl
  let z : PrimeSpectrum k := IsLocalRing.closedPoint k
  have hz : ρ z = IsLocalRing.closedPoint S := by
    have hβ : Function.Surjective β.toRingHom := Ideal.Quotient.factor_surjective hI
    apply PrimeSpectrum.ext
    change (IsLocalRing.maximalIdeal k).comap β.toRingHom = IsLocalRing.maximalIdeal S
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact IsLocalRing.ker_eq_maximalIdeal β.toRingHom hβ
  have hy (y : Y) (hy : y ∉ Ω) (hf : g y = ρ z) : False := by
    have P₀ : IsPullback π₀ f₀ f (ρ ≫ σ) := hρ.symm ▸ H₀
    have P : IsPullback j f₀ g ρ := IsPullback.of_right (h₁.symm ▸ P₀) h₂ H
    obtain ⟨y₀, hyy, -⟩ := Scheme.exists_preimage_of_isPullback P y z hf
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ (π₀ y₀)))
    obtain ⟨l, hl⟩ := Opens.mem_iSup.mp (hL.cover.ge (Set.mem_univ (π₀ y₀)))
    let u := (i, l)
    have hu : y₀ ∈ π₀ ⁻¹ᵁ W u :=
      ⟨mem_coverInter.mpr ⟨trivial, fun n hn => (Finset.mem_singleton.mp hn).symm ▸ hi⟩, hl⟩
    let E := ((Scheme.ΓSpecIso (.of k)).symm ≪≫ asIso f₀.appTop).commRingCatIsoToRingEquiv
    have hunit (s : Γ(X₀, ⊤)) (hs : s ≠ 0) : IsUnit s := by
      have h : E.symm s ≠ 0 := fun hz => hs (E.symm.injective (hz.trans (map_zero _).symm))
      exact E.apply_symm_apply s ▸ (Ne.isUnit h).map E.toRingHom
    have hv : e₀ v₀ ≠ 0 := fun h => hv₀ (e₀.injective (h.trans (map_zero _).symm))
    have hu₀ : IsUnit (a₀ u) := by
      dsimp only [a₀]
      rw [globalCoordinates_apply, resG_resG]
      exact isUnit_res_coord_of_trivial (hL.pull π₀) hunit ht hv _ (hW₀ u)
    have hle : π₀ ⁻¹ᵁ W u ≤ j ⁻¹ᵁ (π ⁻¹ᵁ W u) := by rw [← Scheme.Hom.comp_preimage, h₁]
    have eq : j.appLE _ _ hle (a u) = a₀ u := by
      dsimp only [a, a₀]
      rw [globalCoordinates_apply, resG_resG, globalCoordinates_apply, resG_resG, heg, he₀]
      exact compare_value β.toRingHom h₁ h₂ (W u) _ v.1
    have hm : y₀ ∈ X₀.basicOpen (j.appLE _ _ hle (a u)) := by
      rw [eq, X₀.basicOpen_of_isUnit hu₀]
      exact hu
    rw [Scheme.basicOpen_appLE] at hm
    exact hy (Opens.mem_iSup.mpr ⟨u, hyy ▸ hm.2⟩)
  have hgood (y : Y) : y ∈ Ω := by
    by_contra hbad
    have hmem := (IsLocalRing.specializes_closedPoint (R := S) (g y)).mem_closed hc ⟨y, hbad, rfl⟩
    obtain ⟨y', hy', hf'⟩ := hz.symm ▸ hmem
    exact hy y' hy' hf'
  exact exists_gen_of_nonvanishing_coordinates (eg v) (fun i => π ⁻¹ᵁ W i) c hW
    (fun y => Opens.mem_iSup.mp (hgood y))

end GlobalTheory.LineBundleSections
