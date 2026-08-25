import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanFrobeniusHasseNormalization
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanFiniteUnramifiedRootLiftTower

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

noncomputable section

namespace NonarchimedeanFiniteUnramifiedRootLift

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Arithmetic Frobenius regarded over the original local field rather than its chosen
fraction-ring presentation. -/
noncomputable def fractionGaloisFrobeniusOverBase
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let B := AdjoinRoot D.polynomial
    let U := FractionRing B
    letI : IsDomain B :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    let hg : Function.Injective g :=
      (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
    Gal(U/K) := by
  let B := AdjoinRoot D.polynomial
  let U := FractionRing B
  letI : IsDomain B :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalRing B :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] B) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FaithfulSMul 𝒪[K] B := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] B).mpr ?_
    change Function.Injective <| AdjoinRoot.of D.polynomial
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible)
  let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
  have hg : Function.Injective g :=
    (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : FaithfulSMul 𝒪[K] U :=
    (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr hg
  letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
  letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
  let φ := D.fractionGaloisFrobenius
  let eK := FractionRing.algEquiv 𝒪[K] K
  have hcompat : (algebraMap K U).comp eK.toRingEquiv.toRingHom =
      (RingEquiv.refl U).toRingHom.comp
        (algebraMap (FractionRing 𝒪[K]) U) := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    change (algebraMap K U)
      (eK (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)) = _
    rw [eK.commutes]
    change IsFractionRing.lift hg (algebraMap 𝒪[K] K r) =
      IsFractionRing.lift hg (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)
    rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
  have hfix : ∀ x : K, φ (algebraMap K U x) = algebraMap K U x := by
    intro x
    let y := eK.symm x
    have hy := DFunLike.congr_fun hcompat y
    change algebraMap K U (eK y) = algebraMap (FractionRing 𝒪[K]) U y at hy
    calc
      φ (algebraMap K U x) = φ (algebraMap K U (eK y)) := by
        rw [eK.apply_symm_apply]
      _ = φ (algebraMap (FractionRing 𝒪[K]) U y) := by rw [hy]
      _ = algebraMap (FractionRing 𝒪[K]) U y := φ.commutes y
      _ = algebraMap K U (eK y) := hy.symm
      _ = algebraMap K U x := by rw [eK.apply_symm_apply]
  let result : U ≃ₐ[K] U := AlgEquiv.ofRingEquiv (R := K) (A₁ := U) (A₂ := U)
    (f := φ.toRingEquiv) hfix
  exact result

/-- Selected integral embedding between unramified root lifts of dividing residue degrees. -/
noncomputable def integralTowerEmbedding
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) := by
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalRing BE := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] BE) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
      E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : Algebra 𝒪[K] BD := AdjoinRoot.instAlgebra D.polynomial
  exact Classical.choice
    (nonarchimedeanFiniteUnramifiedRootLift_exists_integralAlgHom_of_dvd K D E hde)

/-- Every selected integral tower embedding is local, so it induces the canonical embedding of
residue fields. -/
theorem integralTowerEmbedding_isLocalHom
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    let BD := AdjoinRoot D.polynomial
    let BE := AdjoinRoot E.polynomial
    letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : IsLocalRing BD := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalRing BE := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : Algebra BD BE := (D.integralTowerEmbedding E hde).toRingHom.toAlgebra
    IsLocalHom (algebraMap BD BE) := by
  dsimp only
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalRing BD := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalRing BE := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  let φ := D.integralTowerEmbedding E hde
  letI : Algebra BD BE := φ.toRingHom.toAlgebra
  letI : IsScalarTower 𝒪[K] BD BE := IsScalarTower.of_algHom φ
  have hD : Ideal.map (algebraMap 𝒪[K] BD) 𝓂[K] =
      IsLocalRing.maximalIdeal BD :=
    nonarchimedeanLocalFieldAdjoinRoot_map_maximalIdeal K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  have hE : Ideal.map (algebraMap 𝒪[K] BE) 𝓂[K] =
      IsLocalRing.maximalIdeal BE :=
    nonarchimedeanLocalFieldAdjoinRoot_map_maximalIdeal K E.polynomial E.monic
      E.residuePolynomial E.reduction_eq E.residueIrreducible
  apply ((IsLocalRing.local_hom_TFAE (algebraMap BD BE)).out 2 0).mp
  rw [← hD, Ideal.map_map, ← IsScalarTower.algebraMap_eq 𝒪[K] BD BE, hE]

/-- Arithmetic Frobenius on residue fields commutes with every selected unramified tower
embedding, because both Frobenius maps are the same base-cardinality power map. -/
theorem residueFrobenius_tower_natural
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    let BD := AdjoinRoot D.polynomial
    let BE := AdjoinRoot E.polynomial
    letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : IsLocalRing BD := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalRing BE := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : IsLocalHom (algebraMap 𝒪[K] BD) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalHom (algebraMap 𝒪[K] BE) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
        E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : Algebra BD BE := (D.integralTowerEmbedding E hde).toRingHom.toAlgebra
    letI : IsScalarTower 𝒪[K] BD BE :=
      IsScalarTower.of_algHom (D.integralTowerEmbedding E hde)
    letI : IsLocalHom (algebraMap BD BE) := D.integralTowerEmbedding_isLocalHom E hde
    ∀ x : IsLocalRing.ResidueField BD,
      algebraMap (IsLocalRing.ResidueField BD) (IsLocalRing.ResidueField BE)
          (nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K
            D.polynomial D.monic D.residuePolynomial D.residueMonic
            D.reduction_eq D.residueIrreducible x) =
        nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K
          E.polynomial E.monic E.residuePolynomial E.residueMonic
          E.reduction_eq E.residueIrreducible
          (algebraMap (IsLocalRing.ResidueField BD) (IsLocalRing.ResidueField BE) x) := by
  dsimp only
  intro x
  rw [nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_apply,
    nonarchimedeanLocalFieldAdjoinRootResidueFrobenius_apply, map_pow]

/-- Integral arithmetic Frobenius commutes with the selected unramified tower embedding. Hensel
uniqueness upgrades the residue-field power-map square to the integral root algebras. -/
theorem integralFrobenius_tower_natural
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    let BD := AdjoinRoot D.polynomial
    let BE := AdjoinRoot E.polynomial
    letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : IsLocalRing BD := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalRing BE := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : IsLocalHom (algebraMap 𝒪[K] BD) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalHom (algebraMap 𝒪[K] BE) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
        E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : Algebra BD BE := (D.integralTowerEmbedding E hde).toRingHom.toAlgebra
    letI : IsScalarTower 𝒪[K] BD BE :=
      IsScalarTower.of_algHom (D.integralTowerEmbedding E hde)
    letI : IsLocalHom (algebraMap BD BE) := D.integralTowerEmbedding_isLocalHom E hde
    let σD := nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
    let σE := nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible
    let τD := nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible σD
    let τE := nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible σE
    (D.integralTowerEmbedding E hde).comp τD.toAlgHom =
      τE.toAlgHom.comp (D.integralTowerEmbedding E hde) := by
  dsimp only
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalRing BD := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalRing BE := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] BD) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] BE) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
      E.residuePolynomial E.reduction_eq E.residueIrreducible
  let φ := D.integralTowerEmbedding E hde
  letI : Algebra BD BE := φ.toRingHom.toAlgebra
  letI : IsScalarTower 𝒪[K] BD BE := IsScalarTower.of_algHom φ
  letI : IsLocalHom (algebraMap BD BE) := D.integralTowerEmbedding_isLocalHom E hde
  let σD := nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K
    D.polynomial D.monic D.residuePolynomial D.residueMonic
    D.reduction_eq D.residueIrreducible
  let σE := nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K
    E.polynomial E.monic E.residuePolynomial E.residueMonic
    E.reduction_eq E.residueIrreducible
  let τD := nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom K
    D.polynomial D.monic D.residuePolynomial D.residueMonic
    D.reduction_eq D.residueIrreducible σD
  let τE := nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom K
    E.polynomial E.monic E.residuePolynomial E.residueMonic
    E.reduction_eq E.residueIrreducible σE
  let left : BD →ₐ[𝒪[K]] BE := φ.comp τD.toAlgHom
  let right : BD →ₐ[𝒪[K]] BE := τE.toAlgHom.comp φ
  let p : Polynomial BE := D.polynomial.map (algebraMap 𝒪[K] BE)
  have hleft : p.eval (left (AdjoinRoot.root D.polynomial)) = 0 := by
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact AdjoinRoot.aeval_algHom_eq_zero D.polynomial left
  have hright : p.eval (right (AdjoinRoot.root D.polynomial)) = 0 := by
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact AdjoinRoot.aeval_algHom_eq_zero D.polynomial right
  have hres : IsLocalRing.residue BE (left (AdjoinRoot.root D.polynomial)) =
      IsLocalRing.residue BE (right (AdjoinRoot.root D.polynomial)) := by
    calc
      IsLocalRing.residue BE (φ (τD (AdjoinRoot.root D.polynomial))) =
          algebraMap (IsLocalRing.ResidueField BD) (IsLocalRing.ResidueField BE)
            (IsLocalRing.residue BD (τD (AdjoinRoot.root D.polynomial))) :=
        (IsLocalRing.ResidueField.algebraMap_residue _).symm
      _ = algebraMap (IsLocalRing.ResidueField BD) (IsLocalRing.ResidueField BE)
            (σD (IsLocalRing.residue BD (AdjoinRoot.root D.polynomial))) := by
        rw [nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom_commutes_residue]
      _ = σE (algebraMap (IsLocalRing.ResidueField BD) (IsLocalRing.ResidueField BE)
            (IsLocalRing.residue BD (AdjoinRoot.root D.polynomial))) :=
        D.residueFrobenius_tower_natural E hde _
      _ = σE (IsLocalRing.residue BE (φ (AdjoinRoot.root D.polynomial))) := by
        change σE (IsLocalRing.residue BE
          ((algebraMap BD BE) (AdjoinRoot.root D.polynomial))) = _
        rfl
      _ = IsLocalRing.residue BE (τE (φ (AdjoinRoot.root D.polynomial))) :=
        (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom_commutes_residue
          K E.polynomial E.monic E.residuePolynomial E.residueMonic
          E.reduction_eq E.residueIrreducible σE _).symm
  have hnonunit : ¬ IsUnit
      (left (AdjoinRoot.root D.polynomial) - right (AdjoinRoot.root D.polynomial)) := by
    intro hu
    have hne := (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu
    rw [map_sub, hres] at hne
    exact hne (sub_self _)
  have hderiv : IsUnit (p.derivative.eval (left (AdjoinRoot.root D.polynomial))) := by
    have hu := nonarchimedeanLocalFieldAdjoinRoot_derivative_isUnit K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
    rw [Polynomial.eval_map] at hu
    change IsUnit (Polynomial.eval₂ (algebraMap 𝒪[K] BD)
      (AdjoinRoot.root D.polynomial) D.polynomial.derivative) at hu
    have humap := hu.map left
    rw [Polynomial.algHom_eval₂_algebraMap] at humap
    simpa only [p, Polynomial.derivative_map, Polynomial.eval_map] using humap
  have hroot := IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
    hleft hright hnonunit hderiv
  change left = right
  exact AdjoinRoot.algHom_ext hroot

/-- Fraction-field extension of the selected integral tower embedding, over the original base
local field. -/
noncomputable def fractionTowerEmbedding
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) := by
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
  let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgD : Function.Injective gD :=
    (IsFractionRing.injective BD UD).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  exact Classical.choice
    (nonarchimedeanFiniteUnramifiedRootLift_exists_fractionFieldAlgHom_of_dvd K D E hde)

/-- A fraction-field tower embedding selected together with its exact restriction to the
selected integral embedding. -/
noncomputable def fractionTowerEmbeddingData
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    let BD := AdjoinRoot D.polynomial
    let BE := AdjoinRoot E.polynomial
    let UD := FractionRing BD
    let UE := FractionRing BE
    letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
    let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
    let hgD : Function.Injective gD :=
      (IsFractionRing.injective BD UD).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    let hgE : Function.Injective gE :=
      (IsFractionRing.injective BE UE).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
            E.residuePolynomial E.reduction_eq E.residueIrreducible))
    letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
    letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
    { φU : UD →ₐ[K] UE // ∀ b : BD,
      φU (algebraMap BD UD b) =
        algebraMap BE UE (D.integralTowerEmbedding E hde b) } := by
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
  let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgD : Function.Injective gD :=
    (IsFractionRing.injective BD UD).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  let φB := D.integralTowerEmbedding E hde
  let qD := D.polynomial.map (algebraMap 𝒪[K] K)
  letI : Fact (Irreducible qD) :=
    ⟨nonarchimedeanLocalFieldAdjoinRootFractionPolynomial_irreducible K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible⟩
  let i : BD →+* AdjoinRoot qD :=
    AdjoinRoot.lift
      ((AdjoinRoot.of qD).comp (algebraMap 𝒪[K] K))
      (AdjoinRoot.root qD)
      (by rw [← Polynomial.eval₂_map]
          exact AdjoinRoot.eval₂_root qD)
  have hi : Function.Injective i :=
    adjoinRootToScalarExtendedAdjoinRoot_injective 𝒪[K] K
      (IsFractionRing.injective 𝒪[K] K) D.polynomial D.monic
  let b : UE := algebraMap BE UE (φB (AdjoinRoot.root D.polynomial))
  have hφroot : D.polynomial.eval₂ (algebraMap 𝒪[K] BE)
      (φB (AdjoinRoot.root D.polynomial)) = 0 := by
    rw [← Polynomial.aeval_def]
    exact AdjoinRoot.aeval_algHom_eq_zero D.polynomial φB
  have hrootUE : D.polynomial.eval₂
      ((algebraMap BE UE).comp (algebraMap 𝒪[K] BE)) b = 0 := by
    change D.polynomial.eval₂
      ((algebraMap BE UE).comp (algebraMap 𝒪[K] BE))
      (algebraMap BE UE (φB (AdjoinRoot.root D.polynomial))) = 0
    rw [← Polynomial.hom_eval₂, hφroot, map_zero]
  have hbase : (algebraMap K UE).comp (algebraMap 𝒪[K] K) =
      (algebraMap BE UE).comp (algebraMap 𝒪[K] BE) := by
    ext r
    change IsFractionRing.lift hgE (algebraMap 𝒪[K] K r) =
      algebraMap BE UE (AdjoinRoot.of E.polynomial r)
    rw [IsFractionRing.lift_algebraMap]
    rfl
  have hqroot : qD.eval₂ (algebraMap K UE) b = 0 := by
    dsimp only [qD]
    rw [Polynomial.eval₂_map, hbase]
    exact hrootUE
  let ψ : AdjoinRoot qD →ₐ[K] UE :=
    AdjoinRoot.liftAlgHom qD (Algebra.ofId K UE) b hqroot
  let h : BD →+* UE := (algebraMap BE UE).comp φB.toRingHom
  let lhs : BD →ₐ[𝒪[K]] UE :=
    { ψ.toRingHom.comp i with
      commutes' := fun r => by
        calc
          ψ (i (algebraMap 𝒪[K] BD r)) =
              ψ (AdjoinRoot.of qD (algebraMap 𝒪[K] K r)) := by
            rw [AdjoinRoot.algebraMap_eq]
            congr 1
            exact AdjoinRoot.lift_of _
          _ = algebraMap K UE (algebraMap 𝒪[K] K r) := ψ.commutes _
          _ = algebraMap BE UE (algebraMap 𝒪[K] BE r) :=
            DFunLike.congr_fun hbase r
          _ = algebraMap 𝒪[K] UE r := rfl }
  let rhs : BD →ₐ[𝒪[K]] UE :=
    { h with
      commutes' := fun r => by
        change algebraMap BE UE (φB (AdjoinRoot.of D.polynomial r)) =
          algebraMap BE UE (AdjoinRoot.of E.polynomial r)
        rw [show φB (AdjoinRoot.of D.polynomial r) =
            AdjoinRoot.of E.polynomial r by
          change φB (algebraMap 𝒪[K] BD r) = algebraMap 𝒪[K] BE r
          exact φB.commutes r] }
  have hfactor : ψ.toRingHom.comp i = h := by
    have halg : lhs = rhs := by
      apply AdjoinRoot.algHom_ext
      dsimp only [lhs, rhs]
      change ψ (i (AdjoinRoot.root D.polynomial)) =
        algebraMap BE UE (φB (AdjoinRoot.root D.polynomial))
      rw [show i (AdjoinRoot.root D.polynomial) = AdjoinRoot.root qD by
        exact AdjoinRoot.lift_root _]
      exact AdjoinRoot.liftAlgHom_root qD (Algebra.ofId K UE) b hqroot
    change lhs.toRingHom = rhs.toRingHom
    exact congrArg AlgHom.toRingHom halg
  have hh : Function.Injective h := by
    rw [← hfactor]
    exact ψ.injective.comp hi
  let ΦRing : UD →+* UE := IsFractionRing.lift hh
  have hΦK : ΦRing.comp (algebraMap K UD) = algebraMap K UE := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    change IsFractionRing.lift hh (IsFractionRing.lift hgD
        (algebraMap 𝒪[K] K r)) = algebraMap K UE (algebraMap 𝒪[K] K r)
    rw [IsFractionRing.lift_algebraMap]
    change IsFractionRing.lift hh
        (algebraMap BD UD (AdjoinRoot.of D.polynomial r)) = _
    rw [IsFractionRing.lift_algebraMap]
    change algebraMap BE UE (φB (AdjoinRoot.of D.polynomial r)) = _
    rw [show φB (AdjoinRoot.of D.polynomial r) =
        AdjoinRoot.of E.polynomial r by
      change φB (algebraMap 𝒪[K] BD r) = algebraMap 𝒪[K] BE r
      exact φB.commutes r]
    exact (DFunLike.congr_fun hbase r).symm
  let Φ : UD →ₐ[K] UE :=
    { ΦRing with commutes' := fun x => DFunLike.congr_fun hΦK x }
  refine ⟨Φ, ?_⟩
  intro x
  exact IsFractionRing.lift_algebraMap hh x

/-- Changing the displayed base from `FractionRing 𝒪[K]` to `K` does not change the
underlying arithmetic Frobenius automorphism. -/
theorem fractionGaloisFrobeniusOverBase_apply
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let B := AdjoinRoot D.polynomial
    let U := FractionRing B
    letI : IsDomain B :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    let hg : Function.Injective g :=
      (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
    ∀ x : U, D.fractionGaloisFrobeniusOverBase x = D.fractionGaloisFrobenius x := by
  dsimp only
  intro x
  rfl

/-- Canonical identification of the two displayed Galois groups obtained by replacing
`FractionRing 𝒪[K]` with the canonically equivalent original local field `K`. -/
noncomputable def fractionGaloisBaseChangeMulEquiv
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let B := AdjoinRoot D.polynomial
    let U := FractionRing B
    letI : IsDomain B :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalRing B :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalHom (algebraMap 𝒪[K] B) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : FaithfulSMul 𝒪[K] U := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
      change Function.Injective <|
        (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
      exact (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
    let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    let hg : Function.Injective g :=
      (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
    Gal(U / FractionRing 𝒪[K]) ≃* Gal(U / K) := by
  let B := AdjoinRoot D.polynomial
  let U := FractionRing B
  letI : IsDomain B :=
    nonarchimedeanLocalFieldAdjoinRoot_isDomain K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalRing B :=
    nonarchimedeanLocalFieldAdjoinRootIsLocalRing K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] B) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FaithfulSMul 𝒪[K] U := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
    change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    exact (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
  let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
  have hg : Function.Injective g :=
    (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
  let eK := FractionRing.algEquiv 𝒪[K] K
  have hforward :
      (algebraMap K U).comp eK.toRingEquiv.toRingHom =
        (RingEquiv.refl U).toRingHom.comp
          (algebraMap (FractionRing 𝒪[K]) U) := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    change (algebraMap K U)
      (eK (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)) = _
    rw [eK.commutes]
    change IsFractionRing.lift hg (algebraMap 𝒪[K] K r) =
      IsFractionRing.lift hg (algebraMap 𝒪[K] (FractionRing 𝒪[K]) r)
    rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
  exact
    { toFun := fun σ ↦
        { σ.toRingEquiv with
          commutes' := fun x ↦ by
            have hx := DFunLike.congr_fun hforward (eK.symm x)
            calc
              σ (algebraMap K U x) =
                  σ (algebraMap (FractionRing 𝒪[K]) U (eK.symm x)) := by
                    simpa using congrArg σ hx
              _ = algebraMap (FractionRing 𝒪[K]) U (eK.symm x) := σ.commutes _
              _ = algebraMap K U x := by simpa using hx.symm }
      invFun := fun τ ↦
        { τ.toRingEquiv with
          commutes' := fun y ↦ by
            have hy := DFunLike.congr_fun hforward y
            calc
              τ (algebraMap (FractionRing 𝒪[K]) U y) =
                  τ (algebraMap K U (eK y)) := by
                    simpa using congrArg τ hy.symm
              _ = algebraMap K U (eK y) := τ.commutes _
              _ = algebraMap (FractionRing 𝒪[K]) U y := by simpa using hy }
      left_inv := fun σ ↦ by ext; rfl
      right_inv := fun τ ↦ by ext; rfl
      map_mul' := fun σ τ ↦ by ext; rfl }

@[simp] theorem fractionGaloisBaseChangeMulEquiv_frobenius
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let B := AdjoinRoot D.polynomial
    let U := FractionRing B
    letI : IsDomain B :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalRing B :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalHom (algebraMap 𝒪[K] B) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : FaithfulSMul 𝒪[K] U := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
      change Function.Injective <|
        (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
      exact (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
    let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    let hg : Function.Injective g :=
      (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
    D.fractionGaloisBaseChangeMulEquiv D.fractionGaloisFrobenius =
      D.fractionGaloisFrobeniusOverBase := by
  dsimp only
  rfl

/-- Arithmetic Frobenius generates the displayed Galois group over the original local field. -/
theorem fractionGaloisFrobeniusOverBase_exists_pow_eq
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let B := AdjoinRoot D.polynomial
    let U := FractionRing B
    letI : IsDomain B :=
      nonarchimedeanLocalFieldAdjoinRoot_isDomain K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalRing B :=
      nonarchimedeanLocalFieldAdjoinRootIsLocalRing K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsLocalHom (algebraMap 𝒪[K] B) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : FaithfulSMul 𝒪[K] U := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
      change Function.Injective <|
        (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
      exact (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
    let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    let hg : Function.Injective g :=
      (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
    ∀ τ : Gal(U/K), ∃ i < D.polynomial.natDegree,
      D.fractionGaloisFrobeniusOverBase ^ i = τ := by
  dsimp only
  intro τ
  let e := D.fractionGaloisBaseChangeMulEquiv
  obtain ⟨σ, rfl⟩ := e.surjective τ
  obtain ⟨i, hi, hσ⟩ := D.fractionGaloisFrobenius_exists_pow_eq σ
  refine ⟨i, hi, ?_⟩
  rw [← D.fractionGaloisBaseChangeMulEquiv_frobenius, ← map_pow, hσ]

/-- Coordinate of arithmetic Frobenius relative to mathlib's selected cyclic generator over the
original local field. -/
noncomputable def fractionGaloisFrobeniusCoordinateOverBase
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    ZMod D.polynomial.natDegree := by
  let B := AdjoinRoot D.polynomial
  let U := FractionRing B
  letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
  have hg : Function.Injective g :=
    (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
  letI : FiniteDimensional K U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsGalois K U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(U/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  have hdegree : Module.finrank K U = D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  have hcard : Nat.card Gal(U/K) = D.polynomial.natDegree :=
    (IsGalois.card_aut_eq_finrank K U).trans hdegree
  let e : Multiplicative (ZMod D.polynomial.natDegree) ≃* Gal(U/K) :=
    zmodMulEquivOfGenerator (cyclicGaloisGenerator_spec K U) hcard
  exact Multiplicative.toAdd (e.symm D.fractionGaloisFrobeniusOverBase)

theorem fractionGaloisFrobeniusOverBase_eq_generator_pow_coordinate
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    let B := AdjoinRoot D.polynomial
    let U := FractionRing B
    letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    let hg : Function.Injective g :=
      (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
    letI : FiniteDimensional K U :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
        D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsGalois K U :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
        D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
    letI : IsCyclic Gal(U/K) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
        D.polynomial D.monic D.residuePolynomial D.residueMonic
        D.reduction_eq D.residueIrreducible
    D.fractionGaloisFrobeniusOverBase = cyclicGaloisGenerator K U ^
      D.fractionGaloisFrobeniusCoordinateOverBase.val := by
  dsimp only
  let B := AdjoinRoot D.polynomial
  let U := FractionRing B
  letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
  have hg : Function.Injective g :=
    (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
  letI : FiniteDimensional K U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsGalois K U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(U/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  have hdegree : Module.finrank K U = D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  have hcard : Nat.card Gal(U/K) = D.polynomial.natDegree :=
    (IsGalois.card_aut_eq_finrank K U).trans hdegree
  let e : Multiplicative (ZMod D.polynomial.natDegree) ≃* Gal(U/K) :=
    zmodMulEquivOfGenerator (cyclicGaloisGenerator_spec K U) hcard
  have h := e.apply_symm_apply D.fractionGaloisFrobeniusOverBase
  change e (Multiplicative.ofAdd D.fractionGaloisFrobeniusCoordinateOverBase) = _ at h
  calc
    D.fractionGaloisFrobeniusOverBase =
        e (Multiplicative.ofAdd D.fractionGaloisFrobeniusCoordinateOverBase) := h.symm
    _ = e (Multiplicative.ofAdd
        (((D.fractionGaloisFrobeniusCoordinateOverBase).val : ℤ) : ZMod _)) := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    _ = cyclicGaloisGenerator K U ^
        ((D.fractionGaloisFrobeniusCoordinateOverBase).val : ℤ) := by
      exact zmodMulEquivOfGenerator_apply_ofAdd_intCast
        (cyclicGaloisGenerator_spec K U) hcard _
    _ = _ := by rw [zpow_natCast]

theorem fractionGaloisFrobeniusCoordinateOverBase_isUnit
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    IsUnit D.fractionGaloisFrobeniusCoordinateOverBase := by
  let B := AdjoinRoot D.polynomial
  let U := FractionRing B
  letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalRing B := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] B) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FaithfulSMul 𝒪[K] U := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
    change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    exact (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
  let g : 𝒪[K] →+* U := (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
  have hg : Function.Injective g :=
    (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra K U := RingHom.toAlgebra (IsFractionRing.lift hg)
  letI : FiniteDimensional K U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsGalois K U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(U/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  have hdegree : Module.finrank K U = D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  have htop : Subgroup.zpowers D.fractionGaloisFrobeniusOverBase = ⊤ := by
    apply top_unique
    intro τ _
    obtain ⟨i, -, hi⟩ := D.fractionGaloisFrobeniusOverBase_exists_pow_eq τ
    rw [← hi]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have horder : orderOf D.fractionGaloisFrobeniusOverBase =
      D.polynomial.natDegree := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ((Subgroup.eq_top_iff' _).1 htop)]
    exact (IsGalois.card_aut_eq_finrank K U).trans hdegree
  rw [D.fractionGaloisFrobeniusOverBase_eq_generator_pow_coordinate,
    orderOf_pow, cyclicGaloisGenerator_orderOf, hdegree] at horder
  have hgcd : Nat.gcd D.polynomial.natDegree
      D.fractionGaloisFrobeniusCoordinateOverBase.val = 1 := by
    rw [Nat.div_eq_self] at horder
    rcases horder with hzero | hgcd
    · exact (D.natDegree_ne_zero hzero).elim
    · exact hgcd
  rw [← ZMod.natCast_zmod_val D.fractionGaloisFrobeniusCoordinateOverBase,
    ZMod.isUnit_iff_coprime, Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
  exact hgcd

noncomputable def fractionGaloisFrobeniusCoordinateOverBaseUnit
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    (ZMod D.polynomial.natDegree)ˣ :=
  D.fractionGaloisFrobeniusCoordinateOverBase_isUnit.unit

@[simp] theorem coe_fractionGaloisFrobeniusCoordinateOverBaseUnit
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    (D.fractionGaloisFrobeniusCoordinateOverBaseUnit :
      ZMod D.polynomial.natDegree) =
        D.fractionGaloisFrobeniusCoordinateOverBase :=
  D.fractionGaloisFrobeniusCoordinateOverBase_isUnit.unit_spec

/-- Arithmetic Frobenius commutes with the compatible fraction-field embedding throughout the
unramified divisibility tower. -/
theorem fractionTowerEmbeddingData_commutes_frobenius
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    let BD := AdjoinRoot D.polynomial
    let BE := AdjoinRoot E.polynomial
    let UD := FractionRing BD
    let UE := FractionRing BE
    letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
    let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
    let hgD : Function.Injective gD :=
      (IsFractionRing.injective BD UD).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    let hgE : Function.Injective gE :=
      (IsFractionRing.injective BE UE).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
            E.residuePolynomial E.reduction_eq E.residueIrreducible))
    letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
    letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
    let Φ := (D.fractionTowerEmbeddingData E hde).1
    Φ.comp D.fractionGaloisFrobeniusOverBase.toAlgHom =
      E.fractionGaloisFrobeniusOverBase.toAlgHom.comp Φ := by
  dsimp only
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalRing BD := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalRing BE := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] BD) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K D.polynomial D.monic
      D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] BE) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
      E.residuePolynomial E.reduction_eq E.residueIrreducible
  let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
  let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgD : Function.Injective gD :=
    (IsFractionRing.injective BD UD).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : FaithfulSMul 𝒪[K] UD :=
    (faithfulSMul_iff_algebraMap_injective 𝒪[K] UD).mpr hgD
  letI : FaithfulSMul 𝒪[K] UE :=
    (faithfulSMul_iff_algebraMap_injective 𝒪[K] UE).mpr hgE
  letI : Algebra (FractionRing 𝒪[K]) UD := FractionRing.liftAlgebra 𝒪[K] UD
  letI : Algebra (FractionRing 𝒪[K]) UE := FractionRing.liftAlgebra 𝒪[K] UE
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  let Φ := (D.fractionTowerEmbeddingData E hde).1
  let φB := D.integralTowerEmbedding E hde
  let σD := nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K
    D.polynomial D.monic D.residuePolynomial D.residueMonic
    D.reduction_eq D.residueIrreducible
  let σE := nonarchimedeanLocalFieldAdjoinRootResidueFrobenius K
    E.polynomial E.monic E.residuePolynomial E.residueMonic
    E.reduction_eq E.residueIrreducible
  let τD := nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom K
    D.polynomial D.monic D.residuePolynomial D.residueMonic
    D.reduction_eq D.residueIrreducible σD
  let τE := nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalAlgEquivHom K
    E.polynomial E.monic E.residuePolynomial E.residueMonic
    E.reduction_eq E.residueIrreducible σE
  apply AlgHom.ext
  intro z
  have hmap :
      (Φ.comp D.fractionGaloisFrobeniusOverBase.toAlgHom).toRingHom =
        (E.fractionGaloisFrobeniusOverBase.toAlgHom.comp Φ).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := BD)
    intro x
    change Φ (D.fractionGaloisFrobeniusOverBase (algebraMap BD UD x)) =
      E.fractionGaloisFrobeniusOverBase (Φ (algebraMap BD UD x))
    rw [D.fractionGaloisFrobeniusOverBase_apply,
      E.fractionGaloisFrobeniusOverBase_apply]
    change Φ
        (nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom K
          D.polynomial D.monic D.residuePolynomial D.residueMonic
          D.reduction_eq D.residueIrreducible σD (algebraMap BD UD x)) =
      nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom K
        E.polynomial E.monic E.residuePolynomial E.residueMonic
        E.reduction_eq E.residueIrreducible σE (Φ (algebraMap BD UD x))
    rw [nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_algebraMap,
      (D.fractionTowerEmbeddingData E hde).2,
      (D.fractionTowerEmbeddingData E hde).2,
      nonarchimedeanLocalFieldAdjoinRoot_liftResidueGalFractionFieldHom_algebraMap]
    exact congrArg (algebraMap BE UE)
      (DFunLike.congr_fun (D.integralFrobenius_tower_natural E hde) x)
  exact DFunLike.congr_fun hmap z

/-- Galois restriction along the selected unramified tower sends upper arithmetic Frobenius to
lower arithmetic Frobenius. -/
theorem restrict_fractionGaloisFrobeniusOverBase
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    let BD := AdjoinRoot D.polynomial
    let BE := AdjoinRoot E.polynomial
    let UD := FractionRing BD
    let UE := FractionRing BE
    letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
    let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
    let hgD : Function.Injective gD :=
      (IsFractionRing.injective BD UD).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    let hgE : Function.Injective gE :=
      (IsFractionRing.injective BE UE).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
            E.residuePolynomial E.reduction_eq E.residueIrreducible))
    letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
    letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
    let Φ := (D.fractionTowerEmbeddingData E hde).1
    letI : Algebra UD UE := Φ.toRingHom.toAlgebra
    letI : IsScalarTower K UD UE := IsScalarTower.of_algHom Φ
    letI : FiniteDimensional K UD :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
        D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : FiniteDimensional K UE :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
        E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : FiniteDimensional UD UE := FiniteDimensional.right K UD UE
    letI : IsGalois K UD :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
        D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
    letI : IsGalois K UE :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K E.polynomial E.monic
        E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
    AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
        E.fractionGaloisFrobeniusOverBase =
      D.fractionGaloisFrobeniusOverBase := by
  dsimp only
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
  let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgD : Function.Injective gD :=
    (IsFractionRing.injective BD UD).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  let Φ := (D.fractionTowerEmbeddingData E hde).1
  letI : Algebra UD UE := Φ.toRingHom.toAlgebra
  letI : IsScalarTower K UD UE := IsScalarTower.of_algHom Φ
  letI : FiniteDimensional K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FiniteDimensional K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : FiniteDimensional UD UE := FiniteDimensional.right K UD UE
  letI : IsGalois K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : IsGalois K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K E.polynomial E.monic
      E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
  apply AlgEquiv.ext
  intro x
  apply Φ.injective
  change algebraMap UD UE
      ((E.fractionGaloisFrobeniusOverBase.restrictNormal UD) x) =
    Φ (D.fractionGaloisFrobeniusOverBase x)
  rw [AlgEquiv.restrictNormal_commutes]
  exact (DFunLike.congr_fun
    (D.fractionTowerEmbeddingData_commutes_frobenius E hde) x).symm

/-- Coordinate of any automorphism relative to the selected generator of a finite cyclic Galois
extension. This isolates the choice-dependent coordinate used by periodic cyclic resolutions. -/
noncomputable def cyclicAutomorphismCoordinate
    (F L : Type) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] [IsCyclic Gal(L/F)]
    (sigma : Gal(L/F)) : ZMod (Module.finrank F L) := by
  letI : NeZero (Module.finrank F L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := F) (M := L))⟩
  let e : Multiplicative (ZMod (Module.finrank F L)) ≃* Gal(L/F) :=
    zmodMulEquivOfGenerator (cyclicGaloisGenerator_spec F L)
      (IsGalois.card_aut_eq_finrank F L)
  exact Multiplicative.toAdd (e.symm sigma)

theorem cyclicAutomorphismCoordinate_spec
    (F L : Type) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] [IsCyclic Gal(L/F)]
    (sigma : Gal(L/F)) :
    sigma = cyclicGaloisGenerator F L ^
      (cyclicAutomorphismCoordinate F L sigma).val := by
  letI : NeZero (Module.finrank F L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := F) (M := L))⟩
  let e : Multiplicative (ZMod (Module.finrank F L)) ≃* Gal(L/F) :=
    zmodMulEquivOfGenerator (cyclicGaloisGenerator_spec F L)
      (IsGalois.card_aut_eq_finrank F L)
  have h := e.apply_symm_apply sigma
  change e (Multiplicative.ofAdd (cyclicAutomorphismCoordinate F L sigma)) = sigma at h
  calc
    sigma = e (Multiplicative.ofAdd (cyclicAutomorphismCoordinate F L sigma)) := h.symm
    _ = e (Multiplicative.ofAdd
        ((((cyclicAutomorphismCoordinate F L sigma).val : ℕ) : ℤ) :
          ZMod (Module.finrank F L))) := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    _ = cyclicGaloisGenerator F L ^
        ((cyclicAutomorphismCoordinate F L sigma).val : ℤ) := by
      exact zmodMulEquivOfGenerator_apply_ofAdd_intCast
        (cyclicGaloisGenerator_spec F L)
        (IsGalois.card_aut_eq_finrank F L) _
    _ = _ := by rw [zpow_natCast]

/-- Coordinates of an upper automorphism and its restriction differ by exactly the generator
restriction orientation. -/
theorem cyclicAutomorphismCoordinate_restrict
    (F L M : Type) [Field F] [Field L] [Field M]
    [Algebra F L] [Algebra L M] [Algebra F M] [IsScalarTower F L M]
    [FiniteDimensional F L] [FiniteDimensional L M] [FiniteDimensional F M]
    [IsGalois F L] [IsGalois F M]
    [IsCyclic Gal(L/F)] [IsCyclic Gal(M/F)] (sigma : Gal(M/F)) :
    cyclicAutomorphismCoordinate F L
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L sigma) =
      cyclicGaloisRestrictionOrientation F L M *
        ZMod.castHom (cyclicGaloisFinrank_dvd F L M)
          (ZMod (Module.finrank F L))
          (cyclicAutomorphismCoordinate F M sigma) := by
  letI : NeZero (Module.finrank F L) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := F) (M := L))⟩
  letI : NeZero (Module.finrank F M) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := F) (M := M))⟩
  let eL : Multiplicative (ZMod (Module.finrank F L)) ≃* Gal(L/F) :=
    zmodMulEquivOfGenerator (cyclicGaloisGenerator_spec F L)
      (IsGalois.card_aut_eq_finrank F L)
  apply Multiplicative.ofAdd.injective
  apply eL.injective
  rw [show eL (Multiplicative.ofAdd (cyclicAutomorphismCoordinate F L
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L sigma))) =
      AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L sigma by
        exact eL.apply_symm_apply _]
  let q := cyclicGaloisRestrictionOrientation F L M
  let c := cyclicAutomorphismCoordinate F M sigma
  have hcast :
      ZMod.castHom (cyclicGaloisFinrank_dvd F L M)
          (ZMod (Module.finrank F L)) c =
        (c.val : ZMod (Module.finrank F L)) := by
    calc
      _ = ZMod.castHom (cyclicGaloisFinrank_dvd F L M)
          (ZMod (Module.finrank F L)) (c.val : ZMod (Module.finrank F M)) := by
        rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [map_natCast]
  have hproduct :
      q * ZMod.castHom (cyclicGaloisFinrank_dvd F L M)
          (ZMod (Module.finrank F L)) c =
        (((q.val * c.val : ℕ) : ℤ) : ZMod (Module.finrank F L)) := by
    calc
      _ = q * (c.val : ZMod (Module.finrank F L)) := by rw [hcast]
      _ = (q.val : ZMod (Module.finrank F L)) *
          (c.val : ZMod (Module.finrank F L)) := by rw [ZMod.natCast_zmod_val]
      _ = ((q.val * c.val : ℕ) : ZMod (Module.finrank F L)) := by
        rw [Nat.cast_mul]
      _ = _ := by rw [Int.cast_natCast]
  have hsigma := cyclicAutomorphismCoordinate_spec F M sigma
  calc
    AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L sigma =
        AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L
          (cyclicGaloisGenerator F M ^ c.val) := by rw [hsigma]
    _ = (AlgEquiv.restrictNormalHom (F := F) (K₁ := M) L
          (cyclicGaloisGenerator F M)) ^ c.val := by rw [map_pow]
    _ = (cyclicGaloisGenerator F L ^ q.val) ^ c.val := by
      rw [cyclicGaloisRestrictionOrientation_spec F L M]
    _ = cyclicGaloisGenerator F L ^ (q.val * c.val) := by rw [pow_mul]
    _ = eL (Multiplicative.ofAdd
        (q * ZMod.castHom (cyclicGaloisFinrank_dvd F L M)
          (ZMod (Module.finrank F L)) c)) := by
      rw [hproduct]
      symm
      calc
        eL (Multiplicative.ofAdd
            ((((q.val * c.val : ℕ) : ℤ)) : ZMod (Module.finrank F L))) =
            cyclicGaloisGenerator F L ^ (((q.val * c.val : ℕ) : ℤ)) :=
          zmodMulEquivOfGenerator_apply_ofAdd_intCast
            (cyclicGaloisGenerator_spec F L) (IsGalois.card_aut_eq_finrank F L) _
        _ = cyclicGaloisGenerator F L ^ (q.val * c.val) := by rw [zpow_natCast]

/-- Generator-restriction orientation for the concrete unramified root-lift tower, transported
from the abstract finrank modulus to the defining residue degree. -/
noncomputable def fractionGaloisRestrictionOrientationOverBase
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    ZMod D.polynomial.natDegree := by
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
  let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgD : Function.Injective gD :=
    (IsFractionRing.injective BD UD).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  let Φ := (D.fractionTowerEmbeddingData E hde).1
  letI : Algebra UD UE := Φ.toRingHom.toAlgebra
  letI : IsScalarTower K UD UE := IsScalarTower.of_algHom Φ
  letI : FiniteDimensional K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FiniteDimensional K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : FiniteDimensional UD UE := FiniteDimensional.right K UD UE
  letI : IsGalois K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : IsGalois K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K E.polynomial E.monic
      E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
  letI : IsCyclic Gal(UD/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(UE/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible
  have hdegreeD : Module.finrank K UD = D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  have hcardD : Nat.card Gal(UD/K) = D.polynomial.natDegree :=
    (IsGalois.card_aut_eq_finrank K UD).trans hdegreeD
  let eD : Multiplicative (ZMod D.polynomial.natDegree) ≃* Gal(UD/K) :=
    zmodMulEquivOfGenerator (cyclicGaloisGenerator_spec K UD) hcardD
  exact Multiplicative.toAdd (eD.symm
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
      (cyclicGaloisGenerator K UE)))

/-- Frobenius coordinates satisfy the exact restriction law throughout the concrete unramified
tower. This is the cancellation identity needed for canonical Hasse gluing. -/
theorem fractionGaloisFrobeniusCoordinateOverBase_tower
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    D.fractionGaloisFrobeniusCoordinateOverBase =
      D.fractionGaloisRestrictionOrientationOverBase E hde *
        ZMod.castHom hde (ZMod D.polynomial.natDegree)
          E.fractionGaloisFrobeniusCoordinateOverBase := by
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
  let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgD : Function.Injective gD :=
    (IsFractionRing.injective BD UD).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  let Φ := (D.fractionTowerEmbeddingData E hde).1
  letI : Algebra UD UE := Φ.toRingHom.toAlgebra
  letI : IsScalarTower K UD UE := IsScalarTower.of_algHom Φ
  letI : FiniteDimensional K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FiniteDimensional K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : FiniteDimensional UD UE := FiniteDimensional.right K UD UE
  letI : IsGalois K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : IsGalois K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K E.polynomial E.monic
      E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
  letI : IsCyclic Gal(UD/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(UE/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible
  have hdegreeD : Module.finrank K UD = D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  have hdegreeE : Module.finrank K UE = E.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  letI : NeZero E.polynomial.natDegree := ⟨E.natDegree_ne_zero⟩
  have hcardD : Nat.card Gal(UD/K) = D.polynomial.natDegree :=
    (IsGalois.card_aut_eq_finrank K UD).trans hdegreeD
  have hcardE : Nat.card Gal(UE/K) = E.polynomial.natDegree :=
    (IsGalois.card_aut_eq_finrank K UE).trans hdegreeE
  let eD : Multiplicative (ZMod D.polynomial.natDegree) ≃* Gal(UD/K) :=
    zmodMulEquivOfGenerator (cyclicGaloisGenerator_spec K UD) hcardD
  let q := D.fractionGaloisRestrictionOrientationOverBase E hde
  let cD := D.fractionGaloisFrobeniusCoordinateOverBase
  let cE := E.fractionGaloisFrobeniusCoordinateOverBase
  have hqspec :
      AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
          (cyclicGaloisGenerator K UE) =
        cyclicGaloisGenerator K UD ^ q.val := by
    have hq := eD.apply_symm_apply
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
        (cyclicGaloisGenerator K UE))
    change eD (Multiplicative.ofAdd q) = _ at hq
    calc
      _ = eD (Multiplicative.ofAdd q) := hq.symm
      _ = eD (Multiplicative.ofAdd (((q.val : ℕ) : ℤ) :
          ZMod D.polynomial.natDegree)) := by
        rw [Int.cast_natCast, ZMod.natCast_zmod_val]
      _ = cyclicGaloisGenerator K UD ^ (q.val : ℤ) := by
        exact zmodMulEquivOfGenerator_apply_ofAdd_intCast
          (cyclicGaloisGenerator_spec K UD) hcardD _
      _ = _ := by rw [zpow_natCast]
  have hcast :
      ZMod.castHom hde (ZMod D.polynomial.natDegree) cE =
        (cE.val : ZMod D.polynomial.natDegree) := by
    calc
      _ = ZMod.castHom hde (ZMod D.polynomial.natDegree)
          (cE.val : ZMod E.polynomial.natDegree) := by
        rw [ZMod.natCast_zmod_val]
      _ = _ := by rw [map_natCast]
  have hproduct :
      q * ZMod.castHom hde (ZMod D.polynomial.natDegree) cE =
        (((q.val * cE.val : ℕ) : ℤ) : ZMod D.polynomial.natDegree) := by
    calc
      _ = q * (cE.val : ZMod D.polynomial.natDegree) := by rw [hcast]
      _ = (q.val : ZMod D.polynomial.natDegree) *
          (cE.val : ZMod D.polynomial.natDegree) := by rw [ZMod.natCast_zmod_val]
      _ = ((q.val * cE.val : ℕ) : ZMod D.polynomial.natDegree) := by
        rw [Nat.cast_mul]
      _ = _ := by rw [Int.cast_natCast]
  apply Multiplicative.ofAdd.injective
  apply eD.injective
  rw [show eD (Multiplicative.ofAdd cD) =
      D.fractionGaloisFrobeniusOverBase by
    exact eD.apply_symm_apply _]
  calc
    D.fractionGaloisFrobeniusOverBase =
        AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
          E.fractionGaloisFrobeniusOverBase :=
      (D.restrict_fractionGaloisFrobeniusOverBase E hde).symm
    _ = AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
          (cyclicGaloisGenerator K UE ^ cE.val) := by
      rw [E.fractionGaloisFrobeniusOverBase_eq_generator_pow_coordinate]
    _ = (AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
          (cyclicGaloisGenerator K UE)) ^ cE.val := by rw [map_pow]
    _ = (cyclicGaloisGenerator K UD ^ q.val) ^ cE.val := by rw [hqspec]
    _ = cyclicGaloisGenerator K UD ^ (q.val * cE.val) := by rw [pow_mul]
    _ = eD (Multiplicative.ofAdd
        (q * ZMod.castHom hde (ZMod D.polynomial.natDegree) cE)) := by
      rw [hproduct]
      symm
      calc
        eD (Multiplicative.ofAdd
            ((((q.val * cE.val : ℕ) : ℤ)) : ZMod D.polynomial.natDegree)) =
            cyclicGaloisGenerator K UD ^ (((q.val * cE.val : ℕ) : ℤ)) :=
          zmodMulEquivOfGenerator_apply_ofAdd_intCast
            (cyclicGaloisGenerator_spec K UD) hcardD _
        _ = cyclicGaloisGenerator K UD ^ (q.val * cE.val) := by rw [zpow_natCast]

/-! ## Equality with the abstract restriction orientation -/

/-- The restriction coordinate defined using abstract extension degree has the same canonical
representative as the concrete root-lift coordinate. -/
theorem cyclicGaloisRestrictionOrientation_val_eq_fractionGaloisRestrictionOrientationOverBase_val
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    let BD := AdjoinRoot D.polynomial
    let BE := AdjoinRoot E.polynomial
    let UD := FractionRing BD
    let UE := FractionRing BE
    letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
    let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
    let hgD : Function.Injective gD :=
      (IsFractionRing.injective BD UD).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    let hgE : Function.Injective gE :=
      (IsFractionRing.injective BE UE).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
            E.residuePolynomial E.reduction_eq E.residueIrreducible))
    letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
    letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
    let Φ := (D.fractionTowerEmbeddingData E hde).1
    letI : Algebra UD UE := Φ.toRingHom.toAlgebra
    letI : IsScalarTower K UD UE := IsScalarTower.of_algHom Φ
    letI : FiniteDimensional K UD :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
        D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : FiniteDimensional K UE :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
        E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : FiniteDimensional UD UE := FiniteDimensional.right K UD UE
    letI : IsGalois K UD :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
        D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
    letI : IsGalois K UE :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K E.polynomial E.monic
        E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
    letI : IsCyclic Gal(UD/K) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
        D.polynomial D.monic D.residuePolynomial D.residueMonic
        D.reduction_eq D.residueIrreducible
    letI : IsCyclic Gal(UE/K) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
        E.polynomial E.monic E.residuePolynomial E.residueMonic
        E.reduction_eq E.residueIrreducible
    (cyclicGaloisRestrictionOrientation K UD UE).val =
      (D.fractionGaloisRestrictionOrientationOverBase E hde).val := by
  dsimp only
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
  let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgD : Function.Injective gD :=
    (IsFractionRing.injective BD UD).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  let Φ := (D.fractionTowerEmbeddingData E hde).1
  letI : Algebra UD UE := Φ.toRingHom.toAlgebra
  letI : IsScalarTower K UD UE := IsScalarTower.of_algHom Φ
  letI : FiniteDimensional K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FiniteDimensional K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : FiniteDimensional UD UE := FiniteDimensional.right K UD UE
  letI : IsGalois K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : IsGalois K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K E.polynomial E.monic
      E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
  letI : IsCyclic Gal(UD/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(UE/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible
  have hdegreeD : Module.finrank K UD = D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrankOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  let qN := cyclicGaloisRestrictionOrientation K UD UE
  let qR := D.fractionGaloisRestrictionOrientationOverBase E hde
  letI : NeZero (Module.finrank K UD) :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := UD))⟩
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  have hcardD : Nat.card Gal(UD/K) = D.polynomial.natDegree :=
    (IsGalois.card_aut_eq_finrank K UD).trans hdegreeD
  let eD : Multiplicative (ZMod D.polynomial.natDegree) ≃* Gal(UD/K) :=
    zmodMulEquivOfGenerator (cyclicGaloisGenerator_spec K UD) hcardD
  have hroot : eD (Multiplicative.ofAdd qR) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
        (cyclicGaloisGenerator K UE) := by
    have h := eD.apply_symm_apply
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
        (cyclicGaloisGenerator K UE))
    change eD (Multiplicative.ofAdd qR) = _ at h
    exact h
  have hnative : eD (Multiplicative.ofAdd
      (qN.val : ZMod D.polynomial.natDegree)) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
        (cyclicGaloisGenerator K UE) := by
    calc
      eD (Multiplicative.ofAdd (qN.val : ZMod D.polynomial.natDegree)) =
          cyclicGaloisGenerator K UD ^ (qN.val : ℤ) := by
        rw [show (qN.val : ZMod D.polynomial.natDegree) =
            ((qN.val : ℤ) : ZMod D.polynomial.natDegree) by
          rw [Int.cast_natCast]]
        change (zmodMulEquivOfGenerator (cyclicGaloisGenerator_spec K UD) hcardD)
          (Multiplicative.ofAdd ((qN.val : ℤ) : ZMod D.polynomial.natDegree)) = _
        exact zmodMulEquivOfGenerator_apply_ofAdd_intCast
          (cyclicGaloisGenerator_spec K UD) hcardD qN.val
      _ = cyclicGaloisGenerator K UD ^ qN.val := by rw [zpow_natCast]
      _ = AlgEquiv.restrictNormalHom (F := K) (K₁ := UE) UD
          (cyclicGaloisGenerator K UE) :=
        (cyclicGaloisRestrictionOrientation_spec K UD UE).symm
  have hq : (qN.val : ZMod D.polynomial.natDegree) = qR := by
    apply Multiplicative.ofAdd.injective
    apply eD.injective
    rw [hroot, hnative]
  have hnlt : qN.val < D.polynomial.natDegree := by
    rw [← hdegreeD]
    exact qN.val_lt
  calc
    qN.val = ((qN.val : ZMod D.polynomial.natDegree)).val :=
      (ZMod.val_natCast_of_lt hnlt).symm
    _ = qR.val := congrArg ZMod.val hq

end NonarchimedeanFiniteUnramifiedRootLift
end
end GaloisForLFunctions.HTGeometry.ABHN
