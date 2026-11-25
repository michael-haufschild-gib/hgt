import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleAffineSections
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange

/-! Pullback of line-bundle sections on affine opens is scalar extension. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace TensorProduct
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {X Y : Scheme.{0}} {π : Y ⟶ X} {L : LB X} {M : LB Y}

private abbrev sectionRestriction (F : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    letI : Module Γ(X, U) Γ(F, V) := Module.compHom _ (resG X h)
    Γ(F, U) →ₗ[Γ(X, U)] Γ(F, V) :=
  letI : Module Γ(X, U) Γ(F, V) := Module.compHom _ (resG X h)
  { (F.presheaf.map (homOfLE h).op).hom with
    map_smul' := fun r x => F.map_smul (homOfLE h) r x }

private theorem isLocalizedModule_sections (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) :
    letI : Module Γ(X, U) Γ(F, X.basicOpen a) := Module.compHom _ (resG X (X.basicOpen_le a))
    IsLocalizedModule.Away a (sectionRestriction F (X.basicOpen_le a)) := by
  let W := X.basicOpen a
  let B := Γ(X, W)
  let N := Γ(F, W)
  letI := Scheme.algebra_section_section_basicOpen a
  letI : Module Γ(X, U) N := Module.compHom _ (algebraMap Γ(X, U) B)
  letI := hU.isLocalization_basicOpen a
  have h := hasBasicOpenLocalization_of_isQuasicoherent F hU a
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ (fun v => ?_) h.2
  · rw [Module.End.isUnit_iff]
    change Function.Bijective (algebraMap B (Module.End B N) (algebraMap Γ(X, U) B a))
    rw [← Module.End.isUnit_iff]
    exact (IsLocalization.Away.algebraMap_isUnit (S := B) a).map _
  · obtain ⟨n, x, hx⟩ := h.1 v
    refine ⟨n, x, ?_⟩
    change (algebraMap Γ(X, U) B (a ^ n)) • v = _
    rw [map_pow]
    exact hx

/-- Sections on the pulled-back affine open are obtained by extending scalars on sections. -/
theorem isBaseChange_pullSection (hL : L.IsLB)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V)
    (hle : V ≤ π ⁻¹ᵁ U) :
    letI : Algebra Γ(X, U) Γ(Y, V) := (π.appLE U V hle).hom.toAlgebra
    letI : Module Γ(X, U) Γ(toMod (L.pull π), V) := Module.compHom _ (algebraMap Γ(X, U) Γ(Y, V))
    letI : IsScalarTower Γ(X, U) Γ(Y, V) Γ(toMod (L.pull π), V) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    IsBaseChange Γ(Y, V)
      { pullSection (ChartPull.pull L π) hle with
        map_smul' := pullSection_smul (ChartPull.pull L π) hle } := by
  classical
  let P := ChartPull.pull L π
  let F := toMod L
  let G := toMod (L.pull π)
  letI : F.IsQuasicoherent := isQuasicoherent_toMod hL
  letI : G.IsQuasicoherent := isQuasicoherent_toMod (hL.pull π)
  let A := Γ(X, U)
  let B := Γ(Y, V)
  let MA := Γ(F, U)
  let NB := Γ(G, V)
  let ρ : A →+* B := (π.appLE U V hle).hom
  letI : Algebra A B := ρ.toAlgebra
  letI : Module A NB := Module.compHom _ ρ
  letI : IsScalarTower A B NB := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let σ : MA →ₗ[A] NB := { pullSection P hle with map_smul' := pullSection_smul P hle }
  change IsBaseChange B σ
  let Φ : B ⊗[A] MA →ₗ[B] NB := LinearMap.liftBaseChange B σ
  let s : Set A := {a | ∃ j, X.basicOpen a ≤ L.U j}
  have hs : Ideal.span s = ⊤ := hU.self_le_iSup_basicOpen_iff.mp (by
    intro x hx
    have hx' : x ∈ ⨆ j, L.U j := by rw [hL.cover]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx'
    obtain ⟨a, ha, hxa⟩ := hU.exists_basicOpen_le ⟨x, hj⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨a, j, ha⟩, hxa⟩)
  let t := ρ '' s
  have ht : Ideal.span t = ⊤ := by
    change Ideal.span (ρ '' s) = ⊤
    rw [← Ideal.map_span, hs, Ideal.map_top]
  let N (b : t) : Type := Γ(G, Y.basicOpen b.1)
  letI (b : t) : Module B (N b) := Module.compHom _ (resG Y (Y.basicOpen_le b.1))
  let resN (b : t) : NB →ₗ[B] N b := sectionRestriction G (Y.basicOpen_le b.1)
  letI (b : t) : IsLocalizedModule.Away b.1 (resN b) := isLocalizedModule_sections G hV b.1
  -- On the inverse image of a trivializing principal open, both section modules have rank one.
  haveI (b : t) : IsLocalizedModule.Away b.1 ((resN b).comp Φ) := by
    obtain ⟨a, ⟨j, hj⟩, ha⟩ := b.2
    let U' := X.basicOpen a
    let V' := Y.basicOpen b.1
    have hv : V' ≤ π ⁻¹ᵁ U' :=
      calc V' = V ⊓ π ⁻¹ᵁ U' := by
            change Y.basicOpen b.1 = _
            rw [← ha, show ρ a = π.appLE U V hle a from rfl, Scheme.basicOpen_appLE]
        _ ≤ _ := inf_le_right
    let A' := Γ(X, U')
    let B' := Γ(Y, V')
    let M' := Γ(F, U')
    let N' := N b
    letI : Algebra A A' := Scheme.algebra_section_section_basicOpen a
    letI : Algebra B B' := Scheme.algebra_section_section_basicOpen b.1
    letI : Algebra A' B' := (π.appLE U' V' hv).hom.toAlgebra
    letI : Algebra A B' := ((algebraMap B B').comp ρ).toAlgebra
    letI : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower B B' N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun r => by
      change resG Y (Y.basicOpen_le b.1) (π.appLE U V hle r) =
        π.appLE U' V' hv (resG X (X.basicOpen_le a) r)
      rw [resG_appLE, appLE_resG]
    letI : Module A M' := Module.compHom _ (algebraMap A A')
    letI : IsScalarTower A A' M' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : Module A' N' := Module.compHom _ (algebraMap A' B')
    letI : IsScalarTower A' B' N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : Module A N' := Module.compHom _ (algebraMap A B')
    letI : IsScalarTower A B' N' := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : IsScalarTower A B N' := .to₁₂₄ A B B' N'
    haveI : IsScalarTower A A' N' := .to₁₂₄ A A' B' N'
    haveI : IsLocalization.Away a A' := hU.isLocalization_basicOpen a
    haveI : IsLocalization.Away b.1 B' := hV.isLocalization_basicOpen b.1
    let rM : MA →ₗ[A] M' := sectionRestriction F (X.basicOpen_le a)
    letI : IsLocalizedModule.Away a rM := isLocalizedModule_sections F hU a
    let τ : M' →ₗ[A'] N' := { pullSection P hv with map_smul' := pullSection_smul P hv }
    have hloc : IsBaseChange B' τ := by
      let i : (L.pull π).ι := fun _ => j
      have hi : U' ≤ L.U (P.idx i) := hj
      have hj' : V' ≤ (L.pull π).U i := by
        change V' ≤ (L.pull π).U (fun _ => j)
        rw [pull_chart]
        exact hv.trans (π.preimage_mono hj)
      refine (IsBaseChange.iff_of_equiv_comm (chartEquiv hL (P.idx i) hi)
        (chartEquiv (hL.pull π) i hj') (f := τ) (f' := Algebra.linearMap A' B') ?_).mpr
        (IsBaseChange.linearMap A' B')
      exact LinearMap.ext fun v => (chartEquiv_pullSection P hL (hL.pull π) hv hi hj' v).symm
    have hbase := (IsLocalizedModule.isBaseChange (Submonoid.powers a) A' rM).comp hloc
    have e : (τ.restrictScalars A).comp rM =
        (((resN b).comp Φ).restrictScalars A).comp (TensorProduct.mk A B MA 1) := by
      apply LinearMap.ext
      intro x
      change pullSection P hv ((toMod L).presheaf.map (homOfLE (X.basicOpen_le a)).op x) =
        (resN b) (Φ (1 ⊗ₜ[A] x))
      rw [show Φ (1 ⊗ₜ[A] x) = σ x by
        change (1 : B) • σ x = σ x
        exact one_smul B _]
      exact pullSection_restrict P hle hv (X.basicOpen_le a) (Y.basicOpen_le b.1) x
    rw [e] at hbase
    exact (isLocalizedModule_iff_isBaseChange (Submonoid.powers b.1) B' _).mpr
      (IsBaseChange.of_comp (TensorProduct.isBaseChange A MA B) hbase)
  have hbij : Function.Bijective Φ := by
    refine bijective_of_isLocalized_span t ht N (fun b => (resN b).comp Φ) N resN Φ
      fun b => ?_
    have he : IsLocalizedModule.map (Submonoid.powers b.1) ((resN b).comp Φ) (resN b) Φ =
        LinearMap.id := by
      apply IsLocalizedModule.ext (Submonoid.powers b.1) ((resN b).comp Φ)
        (IsLocalizedModule.map_units (resN b))
      rw [IsLocalizedModule.map_comp, LinearMap.id_comp]
    rw [he]
    exact Function.bijective_id
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ hbij) fun x => ?_
  change (1 : B) • σ x = σ x
  exact one_smul B _

end GlobalTheory.LineBundleSections
