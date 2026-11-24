import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineFiniteEtaleTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveProductTrace
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! On each affine open the trace along a finite étale morphism is the sum
of the traces along a clopen partition of its inverse image. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

variable {K : Type} [CommRing K] {X Y : Scheme.{0}} {J : Type} [Fintype J]
  {s : X ⟶ Spec (CommRingCat.of K)} {t : Y ⟶ Spec (CommRingCat.of K)}
  {f : Y ⟶ X} [IsFinite f] [Etale f]

omit [Fintype J] in
private theorem section_partition_bijective (V : Y.Opens) (D : J → Y.Opens)
    (hD : ∀ j, D j ≤ V) (hcov : V ≤ iSup D) (hdis : ∀ i j, i ≠ j → D i ⊓ D j = ⊥) :
    Function.Bijective fun (x : Γ(Y, V)) j => Y.presheaf.map (homOfLE (hD j)).op x := by
  constructor
  · intro x y h
    exact TopCat.Sheaf.eq_of_locally_eq' Y.sheaf D V (fun j => homOfLE (hD j)) hcov x y
      fun j => congrFun h j
  · intro y
    classical
    have hy : TopCat.Presheaf.IsCompatible Y.sheaf.obj D y := by
      intro i j
      by_cases h : i = j
      · subst j
        rfl
      · have h0 : Subsingleton Γ(Y, D i ⊓ D j) := by
          rw [hdis i j h]
          infer_instance
        exact h0.elim _ _
    obtain ⟨x, hx, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf D V
      (fun j => homOfLE (hD j)) hcov y hy
    exact ⟨x, funext hx⟩

/-- The trace of a section equals the sum of the traces of its restrictions
to the members of a finite disjoint open cover. -/
theorem affineSectionTrace_eq_sum_clopen (W : J → Y.Opens)
    (hdis : ∀ i j, i ≠ j → W i ⊓ W j = ⊥) (hcov : iSup W = ⊤)
    [∀ j, IsFinite ((W j).ι ≫ f)] [∀ j, Etale ((W j).ι ≫ f)]
    {U : X.Opens} (hU : IsAffineOpen U) (x : SectionRing t (f ⁻¹ᵁ U)) :
    affineSectionTrace (f := f) s t hU x =
      ∑ j, affineSectionTrace (f := (W j).ι ≫ f) s ((W j).ι ≫ t) hU
        (((W j).ι.app (f ⁻¹ᵁ U)).hom x) := by
  let A := SectionRing s U
  let V := f ⁻¹ᵁ U
  let B := SectionRing t V
  let g (j : J) := (W j).ι ≫ f
  let C (j : J) := SectionRing ((W j).ι ≫ t) (g j ⁻¹ᵁ U)
  letI : Algebra A B := (f.app U).hom.toAlgebra
  letI (j : J) : Algebra A (C j) := ((g j).app U).hom.toAlgebra
  letI : Module.Finite A B := f.finite_app U hU
  letI (j : J) : Module.Finite A (C j) := (g j).finite_app U hU
  letI : Algebra.Etale A B := by
    have h := f.etale_appLE hU (hU.preimage f) le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at h
    exact h
  letI (j : J) : Algebra.Etale A (C j) := by
    have h := (g j).etale_appLE hU (hU.preimage (g j)) le_rfl
    rw [← Scheme.Hom.app_eq_appLE] at h
    exact h
  let r (j : J) : B →ₐ[A] C j :=
    { ((W j).ι.app V).hom with
      commutes' := fun a => by
        change ((f.app U ≫ (W j).ι.app V).hom a) = ((g j).app U).hom a
        exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_app (W j).ι f U) a).symm }
  let D (j : J) := (W j).ι ''ᵁ ((W j).ι ⁻¹ᵁ V)
  have hD (j : J) : D j = W j ⊓ V := by
    unfold D
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hle (j : J) : D j ≤ V := (hD j).le.trans inf_le_right
  have hDc : V ≤ iSup D := by
    rw [funext hD, ← iSup_inf_eq, hcov, top_inf_eq]
  have hDd (i j : J) (h : i ≠ j) : D i ⊓ D j = ⊥ := by
    rw [hD, hD, eq_bot_iff, ← hdis i j h]
    exact inf_le_inf inf_le_left inf_le_left
  have hb := section_partition_bijective V D hle hDc hDd
  have hr : Function.Bijective fun (b : B) j => r j b := by
    have h : (fun (b : B) j => r j b) =
        fun b j => Y.presheaf.map (homOfLE (hle j)).op b := by
      funext b j
      change ((W j).ι.app V).hom b = _
      rw [Scheme.Opens.ι_app]
      rfl
    rw [h]
    exact hb
  exact finiteEtaleAlgebraTrace_sum_of_coordinates r hr x

end GlobalTheory.SchemeCohomology
