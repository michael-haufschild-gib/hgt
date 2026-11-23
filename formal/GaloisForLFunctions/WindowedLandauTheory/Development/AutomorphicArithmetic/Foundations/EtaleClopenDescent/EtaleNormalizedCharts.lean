import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NormalizedFibrePullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PullbackFiniteCover

/-! Étale on schemes agrees with étale on the normalized coordinate algebras. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open GlobalTheory.PD GaloisForLFunctions.HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [Field k] {Y Z : Scheme.{0}} [IsIntegral Y] [IsIntegral Z]
  {c : Y ⟶ Z} [IsFinite c] [Etale c] [IsDominant c]
  {s : Z ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)}

/-- The induced maps on normalized chart intersections are étale. -/
theorem rBPullback_etale (hc : c ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    ∀ {F : Type} [Field F] [Algebra k F] [Algebra F Z.functionField] [Algebra F Y.functionField]
      [Algebra Z.functionField Y.functionField]
      [IsScalarTower k F Z.functionField] [IsScalarTower k F Y.functionField]
      [IsScalarTower k Z.functionField Y.functionField] [IsScalarTower F Z.functionField Y.functionField],
      algebraMap Z.functionField Y.functionField = c.functionFieldPullback.hom →
      ∀ {d : ℕ} (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens),
        IsAffCover s U (rB k Z.functionField x) →
        IsAffCover t (fun i => c ⁻¹ᵁ U i) (rB k Y.functionField x) →
        ∀ (I : Finset (Fin (d + 1))), I.Nonempty →
          (rBPullback x I : rB k Z.functionField x I →ₐ[k] rB k Y.functionField x I).toRingHom.Etale := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  intro F _ _ _ _ _ _ _ _ _ hff d x U hZ hY I hI
  let V (i : Fin (d + 1)) := c ⁻¹ᵁ U i
  let W := I.inf U
  let W' := c ⁻¹ᵁ W
  have hW : IsAffineOpen W := hZ.affine I hI
  have hW' : IsAffineOpen W' := hW.preimage c
  let pull : InfTopHom Z.Opens Y.Opens :=
    ⟨⟨fun U => c ⁻¹ᵁ U, fun _ _ => c.preimage_inf⟩, c.preimage_top⟩
  have e : I.inf V = W' := (map_finset_inf pull I U).symm
  have hη' : genericPoint Y ∈ W' := e ▸ hY.ne I
  let eZ := hZ.sectionEquiv I hI
  let eY : SectionRing t W' ≃ₐ[k] rB k Y.functionField x I := e ▸ hY.sectionEquiv I hI
  have hval (a : SectionRing t W') :
      (eY a : Y.functionField) = (Y.presheaf.germ W' _ hη').hom a := by
    have key (P : Y.Opens) (ep : I.inf V = P) (hη : genericPoint Y ∈ P) (b : SectionRing t P) :
        ((ep ▸ hY.sectionEquiv I hI : SectionRing t P ≃ₐ[k] rB k Y.functionField x I) b :
          Y.functionField) = (Y.presheaf.germ P _ hη).hom b := by
      subst P
      rfl
    exact key W' e hη' a
  let q := sectionPullback hc W
  have hcompat (a : SectionRing s W) : rBPullback x I (eZ a) = eY (q a) := by
    apply Subtype.ext
    have ha := hZ.sectionEquiv_apply_coe I hI a
    calc
      _ = algebraMap Z.functionField Y.functionField (eZ a : Z.functionField) := rfl
      _ = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ W _ (hZ.ne I)).hom a) :=
        congrArg (algebraMap Z.functionField Y.functionField) ha
      _ = (Y.presheaf.germ W' _ hη').hom (q a) :=
        (DFunLike.congr_fun hff _).trans (c.functionFieldPullback_germ W (hZ.ne I) a)
      _ = (eY (q a) : Y.functionField) := (hval _).symm
  have heq :
      (rBPullback x I : rB k Z.functionField x I →ₐ[k] rB k Y.functionField x I).toRingHom =
        eY.toRingEquiv.toRingHom.comp (q.toRingHom.comp eZ.symm.toRingEquiv.toRingHom) := by
    apply RingHom.ext
    intro b
    change rBPullback x I b = eY (q (eZ.symm b))
    rw [← hcompat, eZ.apply_symm_apply]
  have hq : q.toRingHom.Etale := by
    change (c.app W).hom.Etale
    rw [c.app_eq_appLE]
    exact c.etale_appLE hW hW' le_rfl
  rw [heq]
  exact RingHom.Etale.respectsIso.left _ eY.toRingEquiv
    (RingHom.Etale.respectsIso.right _ eZ.symm.toRingEquiv hq)

/-- An étale pullback of a normalized projective cover preserves its
reduced origin fibre. -/
theorem isReduced_originFibre_of_finiteEtalePullback [CharZero k] {d : ℕ}
    [SmoothOfRelativeDimension d t] (hc : c ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    ∀ {F : Type} [Field F] [Algebra k F] [Algebra F Z.functionField] [Algebra F Y.functionField]
      [Algebra Z.functionField Y.functionField]
      [IsScalarTower k F Z.functionField] [IsScalarTower k F Y.functionField]
      [IsScalarTower k Z.functionField Y.functionField] [IsScalarTower F Z.functionField Y.functionField],
      algebraMap Z.functionField Y.functionField = c.functionFieldPullback.hom →
      ∀ (x : Fin (d + 1) → F) (U : Fin (d + 1) → Z.Opens),
        IsFinCover k Z.functionField x → IsAffCover s U (rB k Z.functionField x) →
        IsReduced ((rB k Z.functionField x {0}) ⧸ Ideal.span (Set.range fun j : Fin d =>
          (⟨_, tco_mem k Z.functionField x j⟩ : rB k Z.functionField x {0}))) →
        IsReduced ((rB k Y.functionField x {0}) ⧸ Ideal.span (Set.range fun j : Fin d =>
          (⟨_, tco_mem k Y.functionField x j⟩ : rB k Y.functionField x {0}))) := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  intro F _ _ _ _ _ _ _ _ _ hff x U hfin hcov hred
  obtain ⟨hfin', hcov'⟩ := isFinCover_pullback hc hff x U hfin hcov
  let A := rB k Z.functionField x {0}
  let B := rB k Y.functionField x {0}
  let φ : A →ₐ[k] B := rBPullback x {0}
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra.Etale A B := rBPullback_etale hc hff x U hcov hcov' {0} (Finset.singleton_nonempty 0)
  letI := hred
  exact isReduced_normalizedOriginFibre_pullback x hfin hfin'
    (inferInstanceAs (Algebra.FormallyUnramified A B))

end GlobalTheory.SchemeCohomology
