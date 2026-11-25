import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectCochainModel

/-! A bounded flat complex descended from a Noetherian ring has a perfect model after base change. -/

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory

theorem exists_perfect_cochain_of_noetherian_model {B R : Type} [CommRing B] [CommRing R]
    [Algebra B R] [IsNoetherianRing B]
    (C₀ : CochainComplex (ModuleCat.{0} B) ℕ) (C : CochainComplex (ModuleCat.{0} R) ℕ)
    (e : (((ModuleCat.extendScalars (algebraMap B R)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C₀) ≅ C) (n : ℕ)
    (hzero : ∀ p, n < p → IsZero (C₀.X p))
    (hflat₀ : ∀ p, Module.Flat B (C₀.X p)) (hfin : ∀ p, Module.Finite B (C₀.homology p))
    (hflat : ∀ p, Module.Flat R (C.X p)) :
    ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C),
      (∀ p, n < p → IsZero (K.X p)) ∧
      (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧
      (∀ (S : Type) [CommRing S] (α : R →+* S),
        QuasiIso (((ModuleCat.extendScalars α).mapHomologicalComplex _).map φ)) := by
  obtain ⟨K₀, φ₀, hK₀, hfinK₀, _, hprojK₀, _, _, hq⟩ :=
    exists_finite_projective_complex_quasiIso C₀ n hzero hflat₀ hfin
  let T := ModuleCat.extendScalars (algebraMap B R)
  let E := T.mapHomologicalComplex (ComplexShape.up ℕ)
  let K := E.obj K₀
  let φ := E.map φ₀ ≫ e.hom
  have hK p (hp : n < p) : IsZero (K.X p) := T.map_isZero (hK₀ p hp)
  have hC p (hp : n < p) : IsZero (C.X p) :=
    (T.map_isZero (hzero p hp)).of_iso
      ((HomologicalComplex.eval _ _ p).mapIso e.symm)
  have hproj p : Module.Finite R (K.X p) ∧ Module.Projective R (K.X p) := by
    letI : Algebra B R := (algebraMap B R).toAlgebra
    letI := hfinK₀ p
    letI := hprojK₀ p
    change Module.Finite R (R ⊗[B] K₀.X p) ∧ Module.Projective R (R ⊗[B] K₀.X p)
    exact ⟨inferInstance, inferInstance⟩
  haveI : QuasiIso (E.map φ₀) := hq R
  haveI : QuasiIso φ := inferInstanceAs (QuasiIso (E.map φ₀ ≫ e.hom))
  refine ⟨K, φ, hK, hproj, fun S _ α => ?_⟩
  apply quasiIso_extendScalars_of_flat φ _ hflat n hK hC α
  intro p
  letI := (hproj p).2
  infer_instance

end GlobalTheory
