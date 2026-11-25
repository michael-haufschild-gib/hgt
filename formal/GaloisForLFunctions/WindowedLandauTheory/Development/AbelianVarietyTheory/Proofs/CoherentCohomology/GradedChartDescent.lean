import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.GradedMatrixPresentation
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.NoetherianChartMatrix

/-! Smooth projective chart modules give a graded presentation descending to a Noetherian ring. -/

open DirectSum MvPolynomial
open scoped Pointwise

namespace GlobalTheory.SmoothDescent

private theorem exists_semilinear_of_specialized_cokernel
    {S B P : Type} [CommRing S] [CommRing B] [AddCommGroup P] [Module B P]
    (π : S →+* B) {a b : ℕ} (Φ : Matrix (Fin a) (Fin b) S) (u : S)
    (e : letI := Module.compHom P π
      QuotSMulTop u ((Fin a → S) ⧸ LinearMap.range Φ.mulVecLin) ≃ₗ[S] P) :
    ∃ ε : (Fin a → S) →ₛₗ[π] P, Function.Surjective ε ∧
      ∀ y, ε y = 0 ↔ ∃ w w', y = Φ.mulVec w + u • w' := by
  letI := Module.compHom P π
  let K := LinearMap.range Φ.mulVecLin
  let J : Submodule S ((Fin a → S) ⧸ K) := u • ⊤
  let f := (e.toLinearMap ∘ₗ J.mkQ) ∘ₗ K.mkQ
  let ε : (Fin a → S) →ₛₗ[π] P :=
    { f.toAddMonoidHom with map_smul' := fun r x => f.map_smul r x }
  refine ⟨ε, (e.surjective.comp J.mkQ_surjective).comp K.mkQ_surjective, fun y => ?_⟩
  have he : ε y = 0 ↔ J.mkQ (K.mkQ y) = 0 := by
    change e (J.mkQ (K.mkQ y)) = 0 ↔ _
    exact ⟨fun h => e.injective (h.trans e.map_zero.symm), fun h => by rw [h, map_zero]⟩
  rw [he, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hy
    obtain ⟨v, _, hv⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
    obtain ⟨w', rfl⟩ := K.mkQ_surjective v
    have h : K.mkQ (y - u • w') = 0 := by rw [map_sub, map_smul, hv, sub_self]
    obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero K).1 h
    exact ⟨w, w', sub_eq_iff_eq_add.1 hw.symm⟩
  · rintro ⟨w, w', rfl⟩
    have h : K.mkQ (Φ.mulVec w) = 0 := (Submodule.Quotient.mk_eq_zero K).2 ⟨w, rfl⟩
    rw [map_add, map_smul, h, zero_add]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

/-- A graded module with smooth affine charts and finite projective chart modules
admits a homogeneous presentation that is flat on the charts over a Noetherian subalgebra. -/
theorem exists_descended_graded_presentation {ι R G : Type} [Fintype ι] [CommRing R]
    [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G] [IsScalarTower R (MvPolynomial ι R) G]
    (D : ℤ → Submodule R G) [PolyGradedSMul ι D] [Decomposition D]
    (hChart : ∀ i : ι, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B)
      (π : MvPolynomial ι R →ₐ[R] B) (P : Type) (_ : AddCommGroup P) (_ : Module B P),
      Algebra.Smooth R B ∧ Module.Finite B P ∧ Module.Projective B P ∧
        Function.Surjective π ∧ π (X i) = 1 ∧
        (letI := Module.compHom P π.toRingHom
         Nonempty (QuotSMulTop (X i - 1 : MvPolynomial ι R) G ≃ₗ[MvPolynomial ι R] P))) :
    ∃ (R₀ : Subalgebra ℤ R) (_ : IsNoetherianRing R₀) (a b : ℕ) (d : Fin a → ℤ) (e : Fin b → ℤ)
      (Φ₀ : Matrix (Fin a) (Fin b) (MvPolynomial ι R₀)),
      let Φ := Φ₀.map (MvPolynomial.map R₀.val.toRingHom)
      ∃ (ψ : ((Fin a → MvPolynomial ι R) ⧸ LinearMap.range Φ.mulVecLin) →ₗ[MvPolynomial ι R] G),
        (∀ l j, Φ₀ l j ∈ polyGrading ι R₀ (e j - d l)) ∧
        IsGradedMap (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) D ψ ∧
        ∀ i : ι,
          Module.Flat R₀ (QuotSMulTop ((X i : MvPolynomial ι ↥R₀) - 1)
            ((Fin a → MvPolynomial ι R₀) ⧸ LinearMap.range Φ₀.mulVecLin)) ∧
          (∀ y, ψ y = 0 → ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • y = 0) ∧
          (∀ z : G, ∃ k : ℕ, (X i : MvPolynomial ι R) ^ k • z ∈ LinearMap.range ψ) := by
  let S := MvPolynomial ι R
  have hG (i : ι) : Module.FinitePresentation S (QuotSMulTop (X i - 1 : S) G) := by
    obtain ⟨B, _, _, π, P, _, _, hB, hfin, hproj, hπ, _, ⟨e⟩⟩ := hChart i
    letI := hB
    letI := hfin
    letI := hproj
    letI : Algebra S B := π.toRingHom.toAlgebra
    letI : Module S P := Module.compHom P π.toRingHom
    haveI : IsScalarTower S B P := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    haveI : Module.FinitePresentation S B :=
      Module.finitePresentation_of_surjective (Algebra.linearMap S B) hπ
        (Algebra.FinitePresentation.ker_fG_of_surjective π hπ)
    haveI : Module.FinitePresentation B P := Module.finitePresentation_of_projective B P
    haveI : Module.FinitePresentation S P := Module.FinitePresentation.trans S P B
    exact Module.FinitePresentation.of_equiv e.symm
  obtain ⟨a, b, d, e, Φ, ψ, hΦ, hψ, hsat⟩ := exists_graded_presentation_saturating D hG
  haveI : Decomposition (grQuot (grFree ι R d) (LinearMap.range Φ.mulVecLin)) :=
    grQuotDecomposition (isGradedMap_mulVecLin hΦ).isHomogeneous_range
  obtain ⟨R₀, hnoeth, Φ₀, hmap, hΦ₀, hflat⟩ :=
    exists_noetherian_matrix_model d e Φ hΦ fun i => by
      obtain ⟨B, _, _, π, P, _, _, hB, _, hproj, hπ, hX, ⟨ε⟩⟩ := hChart i
      letI : Module S P := Module.compHom P π.toRingHom
      let u : S := X i - 1
      let η := LinearEquiv.ofBijective (QuotSMulTop.map u ψ)
        (bijective_specialization_of_saturating hψ i (hsat i).1 (hsat i).2)
      obtain ⟨q, hq, hker⟩ :=
        exists_semilinear_of_specialized_cokernel π.toRingHom Φ u (η.trans ε)
      exact ⟨B, inferInstance, inferInstance, π, P, inferInstance, inferInstance,
        q, hB, hproj, hπ, hX, hq, hker⟩
  subst Φ
  exact ⟨R₀, hnoeth, a, b, d, e, Φ₀, ψ, hΦ₀, hψ, fun i => ⟨hflat i, hsat i⟩⟩

end GlobalTheory.SmoothDescent
