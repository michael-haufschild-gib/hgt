import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanContinuousH2Hasse

/-!
# Residue Hasse principle for finite unramified Galois automorphisms

For a packaged finite unramified root lift, the canonical lift from residue-field Galois
automorphisms to fraction-field Galois automorphisms is bijective.  This produces a literal
isomorphism of Galois groups, a unique residue-ancestor classification, and a canonical lifted
arithmetic Frobenius whose bounded powers exhaust the generic-fibre Galois group.

This is finite unramified local-class-field infrastructure.  It does not use or assert a
comparison between continuous `H²` and the Brauer group.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

noncomputable section

namespace NonarchimedeanFiniteUnramifiedRootLift

universe u

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Residue Galois automorphisms and fraction-field Galois automorphisms are canonically
isomorphic for packaged finite unramified lift data. -/
noncomputable def residueFractionGaloisMulEquiv
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :=
  letI : IsDomain (AdjoinRoot D.polynomial) :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalRing (AdjoinRoot D.polynomial) :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] (AdjoinRoot D.polynomial)) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FaithfulSMul 𝒪[K] (AdjoinRoot D.polynomial) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (AdjoinRoot D.polynomial)).mpr ?_
    change Function.Injective <| AdjoinRoot.of D.polynomial
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible)
  letI : FaithfulSMul 𝒪[K] (FractionRing (AdjoinRoot D.polynomial)) := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K]
      (FractionRing (AdjoinRoot D.polynomial))).mpr ?_
    change Function.Injective <|
      (algebraMap (AdjoinRoot D.polynomial)
        (FractionRing (AdjoinRoot D.polynomial))).comp (AdjoinRoot.of D.polynomial)
    exact (IsFractionRing.injective (AdjoinRoot D.polynomial)
      (FractionRing (AdjoinRoot D.polynomial))).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra (FractionRing 𝒪[K]) (FractionRing (AdjoinRoot D.polynomial)) :=
    FractionRing.liftAlgebra 𝒪[K] (FractionRing (AdjoinRoot D.polynomial))
  letI : Algebra K (FractionRing (AdjoinRoot D.polynomial)) := by
    let g₀ : 𝒪[K] →+* FractionRing (AdjoinRoot D.polynomial) :=
      (algebraMap (AdjoinRoot D.polynomial)
        (FractionRing (AdjoinRoot D.polynomial))).comp (AdjoinRoot.of D.polynomial)
    have hg₀ : Function.Injective g₀ :=
      (IsFractionRing.injective (AdjoinRoot D.polynomial)
        (FractionRing (AdjoinRoot D.polynomial))).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
              D.residuePolynomial D.reduction_eq D.residueIrreducible))
    exact RingHom.toAlgebra (IsFractionRing.lift hg₀)
  MulEquiv.ofBijective
    (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom
      K D.polynomial D.monic D.residuePolynomial D.residueMonic
        D.reduction_eq D.residueIrreducible)
    ⟨nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_injective
      K D.polynomial D.monic D.residuePolynomial D.residueMonic
        D.reduction_eq D.residueIrreducible,
      nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_surjective
        K D.polynomial D.monic D.residuePolynomial D.residueMonic
          D.reduction_eq D.residueIrreducible⟩

/-- Residue-action Hasse congruence for finite unramified fraction-field automorphisms. -/
theorem residueFractionGalois_congr_hasse_iff
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let e := D.residueFractionGaloisMulEquiv
    ∀ σ τ, σ = τ ↔ e σ = e τ := by
  dsimp only
  intro σ τ
  exact D.residueFractionGaloisMulEquiv.injective.eq_iff.symm

/-- Every fraction-field Galois automorphism has a unique residue-field ancestor. -/
theorem residueFractionGalois_existsUnique_lift
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let e := D.residueFractionGaloisMulEquiv
    ∀ τ, ∃! σ, e σ = τ := by
  dsimp only
  intro τ
  exact ⟨D.residueFractionGaloisMulEquiv.symm τ,
    D.residueFractionGaloisMulEquiv.apply_symm_apply τ,
    fun σ hσ ↦ D.residueFractionGaloisMulEquiv.injective
      (hσ.trans (D.residueFractionGaloisMulEquiv.apply_symm_apply τ).symm)⟩

/-- Canonical arithmetic Frobenius lifted from residue to the unramified fraction field. -/
noncomputable def fractionGaloisFrobenius
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :=
  D.residueFractionGaloisMulEquiv
    (nonarchimedeanLocalFieldAdjoinRootResidueFrobenius
      K D.polynomial D.monic D.residuePolynomial D.residueMonic
        D.reduction_eq D.residueIrreducible)

/-- Every unramified fraction-field automorphism is a bounded power of lifted Frobenius. -/
theorem fractionGaloisFrobenius_exists_pow_eq
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let φ := D.fractionGaloisFrobenius
    ∀ τ, ∃ i < D.polynomial.natDegree, φ ^ i = τ := by
  dsimp only
  intro τ
  obtain ⟨σ, rfl⟩ := D.residueFractionGaloisMulEquiv.surjective τ
  obtain ⟨i, hi, hσ⟩ :=
    nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_exists_pow_eq
      K D.polynomial D.monic D.residuePolynomial D.residueMonic
        D.reduction_eq D.residueIrreducible σ
  refine ⟨i, hi, ?_⟩
  change (D.residueFractionGaloisMulEquiv
      (nonarchimedeanLocalFieldAdjoinRootResidueFrobenius
        K D.polynomial D.monic D.residuePolynomial D.residueMonic
          D.reduction_eq D.residueIrreducible)) ^ i =
    D.residueFractionGaloisMulEquiv σ
  rw [← map_pow, hσ]

end NonarchimedeanFiniteUnramifiedRootLift

end

end GaloisForLFunctions.HTGeometry.ABHN
