import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanFrobeniusTower
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalBrauerInvariant

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

set_option maxRecDepth 4000
set_option maxHeartbeats 800000

theorem cyclicGaloisH2AddEquivOfEquivEquiv_baseProjection
    (K K' L L' : Type) [Field K] [Field K'] [Field L] [Field L']
    [Algebra K L] [Algebra K' L'] [FiniteDimensional K L] [FiniteDimensional K' L']
    [IsGalois K L] [IsGalois K' L'] [IsCyclic Gal(L/K)] [IsCyclic Gal(L'/K')]
    (eK : K ≃+* K') (eL : L ≃+* L')
    (he : (algebraMap K' L').comp eK.toRingHom =
      eL.toRingHom.comp (algebraMap K L)) (a : Additive Kˣ) :
    cyclicGaloisH2AddEquivOfEquivEquiv K K' L L' eK eL he
        (cyclicGaloisH2BaseProjection K L a) =
      cyclicGaloisH2BaseProjection K' L'
        (additiveUnitsAddEquivOfRingEquiv eK a) := by
  change ((cyclicGaloisH2BaseNormQuotientEquiv K L).symm.trans
    ((cyclicGaloisH2BaseNormQuotientAddEquivOfEquivEquiv K K' L L' eK eL he).trans
      (cyclicGaloisH2BaseNormQuotientEquiv K' L')))
        (cyclicGaloisH2BaseProjection K L a) = _
  change (cyclicGaloisH2BaseNormQuotientEquiv K' L')
      ((cyclicGaloisH2BaseNormQuotientAddEquivOfEquivEquiv K K' L L' eK eL he)
        ((cyclicGaloisH2BaseNormQuotientEquiv K L).symm
          (cyclicGaloisH2BaseProjection K L a))) = _
  rw [show (cyclicGaloisH2BaseNormQuotientEquiv K L).symm
      (cyclicGaloisH2BaseProjection K L a) = QuotientAddGroup.mk a by
    apply (cyclicGaloisH2BaseNormQuotientEquiv K L).injective
    rw [AddEquiv.apply_symm_apply]
    rfl]
  rw [show (cyclicGaloisH2BaseNormQuotientAddEquivOfEquivEquiv
      K K' L L' eK eL he) (QuotientAddGroup.mk a) =
        QuotientAddGroup.mk (additiveUnitsAddEquivOfRingEquiv eK a) by rfl]
  rfl

theorem cyclicGaloisH2AddEquivOfEquivEquiv_normQuotientTransition
    (K K' L M : Type) [Field K] [Field K'] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra K' L] [Algebra K' M]
    [Algebra L M] [IsScalarTower K L M] [IsScalarTower K' L M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [FiniteDimensional K' L] [FiniteDimensional K' M] [FiniteDimensional L M]
    [IsGalois K L] [IsGalois K M] [IsGalois K' L] [IsGalois K' M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    [IsCyclic Gal(L/K')] [IsCyclic Gal(M/K')]
    (eK : K ≃+* K')
    (heL : (algebraMap K' L).comp eK.toRingHom =
      (RingEquiv.refl L).toRingHom.comp (algebraMap K L))
    (heM : (algebraMap K' M).comp eK.toRingHom =
      (RingEquiv.refl M).toRingHom.comp (algebraMap K M))
    (z : cyclicGaloisH2 K L) :
    cyclicGaloisH2AddEquivOfEquivEquiv K K' M M eK (RingEquiv.refl M) heM
        (cyclicGaloisH2NormQuotientTransition K L M z) =
      cyclicGaloisH2NormQuotientTransition K' L M
        (cyclicGaloisH2AddEquivOfEquivEquiv K K' L L eK
          (RingEquiv.refl L) heL z) := by
  obtain ⟨a, rfl⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  rw [cyclicGaloisH2NormQuotientTransition_baseProjection,
    cyclicGaloisH2AddEquivOfEquivEquiv_baseProjection,
    cyclicGaloisH2AddEquivOfEquivEquiv_baseProjection,
    cyclicGaloisH2NormQuotientTransition_baseProjection, map_nsmul]

theorem cyclicGaloisH2SplitValuationEquiv_transition_of_finrank_eq
    (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]
    [IsGalois K L] [IsGalois K M]
    [IsCyclic Gal(L/K)] [IsCyclic Gal(M/K)]
    (vK : Valuation K (WithZero (Multiplicative ℤ)))
    (vL : Valuation L (WithZero (Multiplicative ℤ)))
    (vM : Valuation M (WithZero (Multiplicative ℤ)))
    (nL nM : ℕ) (hnL : nL ≠ 0) (hnM : nM ≠ 0)
    (hfinL : Module.finrank K L = nL) (hfinM : Module.finrank K M = nM)
    (hdiv : nL ∣ nM) (u : Kˣ)
    (hu : Multiplicative.toAdd (tameValHom vK u) = 1)
    (hvalL : ∀ x : Lˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vL x) ^ nL)
    (hzeroL : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Lˣ, Units.map (Algebra.norm K) b = a)
    (hvalM : ∀ x : Mˣ,
      tameValHom vK (Units.map (Algebra.norm K) x) = (tameValHom vM x) ^ nM)
    (hzeroM : ∀ a : Kˣ, tameValHom vK a = 1 →
      ∃ b : Mˣ, Units.map (Algebra.norm K) b = a) :
    (cyclicGaloisH2SplitValuationEquiv K M vK vM nM u hu hfinM hvalM hzeroM).toAddMonoidHom.comp
        (cyclicGaloisH2NormQuotientTransition K L M) =
      (zmodRatModIntTransition hnL hnM hdiv).comp
        (cyclicGaloisH2SplitValuationEquiv K L vK vL nL u hu hfinL hvalL hzeroL).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := cyclicGaloisH2BaseProjection_surjective K L z
  rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
    cyclicGaloisH2NormQuotientTransition_baseProjection]
  rw [← DFunLike.congr_fun (cyclicGaloisH2TameInvariant_eq_splitValuationEquiv
      K M vK vM nM u hu hfinM hvalM hzeroM)
    (cyclicGaloisH2BaseProjection K M (Module.finrank L M • a))]
  rw [cyclicGaloisH2TameInvariant_baseProjection]
  rw [← DFunLike.congr_fun (cyclicGaloisH2TameInvariant_eq_splitValuationEquiv
      K L vK vL nL u hu hfinL hvalL hzeroL)
    (cyclicGaloisH2BaseProjection K L a)]
  rw [cyclicGaloisH2TameInvariant_baseProjection, map_nsmul]
  have hmul : nL * Module.finrank L M = nM := by
    rw [← hfinL, ← hfinM]
    exact Module.finrank_mul_finrank K L M
  change Module.finrank L M •
      (((Multiplicative.toAdd (tameValHom vK (Additive.toMul a)) : ℤ)) : ZMod nM) =
    zmodRatModIntTransition hnL hnM hdiv
      (((Multiplicative.toAdd (tameValHom vK (Additive.toMul a)) : ℤ)) : ZMod nL)
  rw [show hdiv = ⟨Module.finrank L M, hmul.symm⟩ by rfl]
  rw [zmodRatModIntTransition_intCast hnL hnM hmul]
  simp [nsmul_eq_mul]

/-- Multiplying finite cyclic coordinates by Frobenius units cancels the restriction
orientation in the canonical torsion transition. -/
theorem zmodRatModIntTransition_frobenius_cancellation
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m ∣ n) (q : ZMod m) (c : ZMod n) (d x : ZMod m)
    (hcoord : d = q * ZMod.castHom hmn (ZMod m) c) :
    c * (q.val • zmodRatModIntTransition hm hn hmn x) =
      zmodRatModIntTransition hm hn hmn (d * x) := by
  obtain ⟨r, rfl⟩ := hmn
  have hmr : m * r = m * r := rfl
  have hn' : m * r ≠ 0 := hn
  letI : NeZero m := ⟨hm⟩
  letI : NeZero (m * r) := ⟨hn'⟩
  let qv := q.val
  let cv := c.val
  let xv := x.val
  have hq : q = (qv : ZMod m) := (ZMod.natCast_zmod_val q).symm
  have hc : c = (cv : ZMod (m * r)) := (ZMod.natCast_zmod_val c).symm
  have hx : x = (xv : ZMod m) := (ZMod.natCast_zmod_val x).symm
  have hcdown : ZMod.castHom (⟨r, rfl⟩ : m ∣ m * r) (ZMod m) c =
      (cv : ZMod m) := by
    calc
      _ = ZMod.castHom (⟨r, rfl⟩ : m ∣ m * r) (ZMod m)
          (cv : ZMod (m * r)) := by rw [← hc]
      _ = _ := by rw [map_natCast]
  have hd : d = ((qv * cv : ℕ) : ZMod m) := by
    calc
      d = q * ZMod.castHom (⟨r, rfl⟩ : m ∣ m * r) (ZMod m) c := hcoord
      _ = (qv : ZMod m) * (cv : ZMod m) := by rw [hq, hcdown]
      _ = ((qv * cv : ℕ) : ZMod m) := by rw [Nat.cast_mul]
  rw [hd, hx, hc]
  rw [show (xv : ZMod m) = ((xv : ℤ) : ZMod m) by rw [Int.cast_natCast]]
  rw [show (cv : ZMod (m * r)) = ((cv : ℤ) : ZMod (m * r)) by
    rw [Int.cast_natCast]]
  rw [zmodRatModIntTransition_intCast hm hn' hmr]
  rw [show (((qv * cv : ℕ) : ZMod m) * ((xv : ℤ) : ZMod m)) =
      (((qv * cv * xv : ℕ) : ℤ) : ZMod m) by
    push_cast
    rfl]
  rw [zmodRatModIntTransition_intCast hm hn' hmr]
  simp only [nsmul_eq_mul]
  push_cast
  ring

theorem addEquiv_symm_trans_apply_self {A B C : Type*}
    [AddGroup A] [AddGroup B] [AddGroup C]
    (e : A ≃+ B) (f : A ≃+ C) (x : A) :
    e.symm.trans f (e x) = f x := by
  rw [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]

namespace NonarchimedeanFiniteUnramifiedRootLift

open scoped ValuativeRel WithZero WithZeroMulInt

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Finite unramified `H²` coordinate normalized by arithmetic Frobenius, rather than by
mathlib's selected generator. -/
noncomputable def cyclicGaloisH2FrobeniusInvariantOverBase
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
    cyclicGaloisH2 K U ≃+ ZMod D.polynomial.natDegree := by
  dsimp only
  exact (nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2InvariantOverBase K
    D.polynomial D.monic D.residuePolynomial D.residueMonic
    D.reduction_eq D.residueIrreducible).trans
      (zmodUnitMulAddEquiv D.fractionGaloisFrobeniusCoordinateOverBaseUnit)

/-- Frobenius-normalized coordinate on the finite cyclic Brauer subgroup split by a concrete
unramified root lift. -/
noncomputable def cyclicBrauerFrobeniusInvariantOverBase
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    nonarchimedeanFiniteUnramifiedRootLiftCyclicBrauerSubgroup K D ≃+
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
  change cyclicGaloisBrauerSubgroup K U ≃+ ZMod D.polynomial.natDegree
  exact (cyclicGaloisH2BrauerSubgroupAddEquiv K U).symm.trans
    D.cyclicGaloisH2FrobeniusInvariantOverBase

/-- Concrete inclusion between unramified cyclic Brauer slices along residue-degree divisibility. -/
noncomputable def cyclicBrauerRootLiftInclusion
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    nonarchimedeanFiniteUnramifiedRootLiftCyclicBrauerSubgroup K D →+
      nonarchimedeanFiniteUnramifiedRootLiftCyclicBrauerSubgroup K E :=
  AddSubgroup.inclusion
    (nonarchimedeanFiniteUnramifiedRootLift_cyclicGaloisBrauerSubgroup_le_of_dvd
      K D E hde)

theorem cyclicBrauerFrobeniusInvariantOverBase_h2
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
    ∀ z : cyclicGaloisH2 K U,
      D.cyclicBrauerFrobeniusInvariantOverBase
          (cyclicGaloisH2BrauerSubgroupAddEquiv K U z) =
        D.cyclicGaloisH2FrobeniusInvariantOverBase z := by
  dsimp only
  intro z
  unfold cyclicBrauerFrobeniusInvariantOverBase
    cyclicGaloisH2FrobeniusInvariantOverBase
  dsimp only
  simp only [id_eq]
  exact addEquiv_symm_trans_apply_self _ _ z

theorem cyclicGaloisH2SelectedInvariantOverBase_normTransition
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
    let sD :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2InvariantOverBase K
        D.polynomial D.monic D.residuePolynomial D.residueMonic
        D.reduction_eq D.residueIrreducible
    let sE :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2InvariantOverBase K
        E.polynomial E.monic E.residuePolynomial E.residueMonic
        E.reduction_eq E.residueIrreducible
    sE.toAddMonoidHom.comp (cyclicGaloisH2NormQuotientTransition K UD UE) =
      (zmodRatModIntTransition D.natDegree_ne_zero E.natDegree_ne_zero hde).comp
        sD.toAddMonoidHom := by
  dsimp only
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  let F0 := FractionRing 𝒪[K]
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
  letI : IsDiscreteValuationRing BD :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : IsDiscreteValuationRing BE :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K E.polynomial E.monic
      E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
  letI : FaithfulSMul 𝒪[K] BD := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] BD).mpr ?_
    change Function.Injective <| AdjoinRoot.of D.polynomial
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible)
  letI : FaithfulSMul 𝒪[K] BE := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] BE).mpr ?_
    change Function.Injective <| AdjoinRoot.of E.polynomial
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
        E.residuePolynomial E.reduction_eq E.residueIrreducible)
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
  letI : Algebra F0 UD := FractionRing.liftAlgebra 𝒪[K] UD
  letI : Algebra F0 UE := FractionRing.liftAlgebra 𝒪[K] UE
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  let Φ := (D.fractionTowerEmbeddingData E hde).1
  letI : Algebra UD UE := Φ.toRingHom.toAlgebra
  letI : IsScalarTower K UD UE := IsScalarTower.of_algHom Φ
  have hscalar0 : ∀ x : F0,
      algebraMap F0 UE x = algebraMap UD UE (algebraMap F0 UD x) := by
    intro x
    have hmaps : (algebraMap F0 UE) =
        (algebraMap UD UE).comp (algebraMap F0 UD) := by
      apply IsFractionRing.ringHom_ext (A := 𝒪[K])
      intro r
      have hlhs : algebraMap F0 UE (algebraMap 𝒪[K] F0 r) =
          algebraMap 𝒪[K] UE r := by
        rw [FractionRing.algebraMap_liftAlgebra,
          IsFractionRing.lift_algebraMap]
      have hinner : algebraMap F0 UD (algebraMap 𝒪[K] F0 r) =
          algebraMap 𝒪[K] UD r := by
        rw [FractionRing.algebraMap_liftAlgebra,
          IsFractionRing.lift_algebraMap]
      rw [RingHom.comp_apply, hlhs, hinner]
      change algebraMap BE UE (AdjoinRoot.of E.polynomial r) =
        Φ (algebraMap BD UD (AdjoinRoot.of D.polynomial r))
      rw [(D.fractionTowerEmbeddingData E hde).2]
      exact congrArg (algebraMap BE UE) (by
        change AdjoinRoot.of E.polynomial r =
          D.integralTowerEmbedding E hde (AdjoinRoot.of D.polynomial r)
        symm
        change D.integralTowerEmbedding E hde (algebraMap 𝒪[K] BD r) =
          algebraMap 𝒪[K] BE r
        exact (D.integralTowerEmbedding E hde).commutes r)
    exact DFunLike.congr_fun hmaps x
  letI : IsScalarTower F0 UD UE := IsScalarTower.of_algebraMap_eq hscalar0
  letI : FiniteDimensional F0 UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FiniteDimensional F0 UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : FiniteDimensional K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FiniteDimensional K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : FiniteDimensional UD UE := FiniteDimensional.right K UD UE
  letI : IsGalois F0 UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsGalois F0 UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible
  letI : IsGalois K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : IsGalois K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois K E.polynomial E.monic
      E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
  letI : IsCyclic Gal(UD/F0) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(UE/F0) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible
  letI : IsCyclic Gal(UD/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(UE/K) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible
  let eK := FractionRing.algEquiv 𝒪[K] K
  have hcompatD : (algebraMap K UD).comp eK.toRingEquiv.toRingHom =
      (RingEquiv.refl UD).toRingHom.comp (algebraMap F0 UD) := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    change (algebraMap K UD) (eK (algebraMap 𝒪[K] F0 r)) = _
    rw [eK.commutes]
    change IsFractionRing.lift hgD (algebraMap 𝒪[K] K r) =
      IsFractionRing.lift hgD (algebraMap 𝒪[K] F0 r)
    rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
  have hcompatE : (algebraMap K UE).comp eK.toRingEquiv.toRingHom =
      (RingEquiv.refl UE).toRingHom.comp (algebraMap F0 UE) := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    change (algebraMap K UE) (eK (algebraMap 𝒪[K] F0 r)) = _
    rw [eK.commutes]
    change IsFractionRing.lift hgE (algebraMap 𝒪[K] K r) =
      IsFractionRing.lift hgE (algebraMap 𝒪[K] F0 r)
    rw [IsFractionRing.lift_algebraMap, IsFractionRing.lift_algebraMap]
  let cD := cyclicGaloisH2AddEquivOfEquivEquiv F0 K UD UD
    eK.toRingEquiv (RingEquiv.refl UD) hcompatD
  let cE := cyclicGaloisH2AddEquivOfEquivEquiv F0 K UE UE
    eK.toRingEquiv (RingEquiv.refl UE) hcompatE
  let oldD := nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2Invariant K
    D.polynomial D.monic D.residuePolynomial D.residueMonic
    D.reduction_eq D.residueIrreducible
  let oldE := nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2Invariant K
    E.polynomial E.monic E.residuePolynomial E.residueMonic
    E.reduction_eq E.residueIrreducible
  let π : 𝒪[K] := (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose
  have hπ : Irreducible π :=
    (IsDiscreteValuationRing.exists_irreducible 𝒪[K]).choose_spec
  have hπF : algebraMap 𝒪[K] F0 π ≠ 0 := by
    intro hz
    apply hπ.ne_zero
    exact (IsFractionRing.injective 𝒪[K] F0) (by simpa using hz)
  let u : F0ˣ := Units.mk0 (algebraMap 𝒪[K] F0 π) hπF
  let v0 := (IsDiscreteValuationRing.maximalIdeal 𝒪[K]).valuation F0
  let vD := (IsDiscreteValuationRing.maximalIdeal BD).valuation UD
  let vE := (IsDiscreteValuationRing.maximalIdeal BE).valuation UE
  have hu : Multiplicative.toAdd (tameValHom v0 u) = 1 :=
    discreteValuationRingFractionField_irreducible_tameVal 𝒪[K] F0 hπ
  have hselected0 := cyclicGaloisH2SplitValuationEquiv_transition_of_finrank_eq
    F0 UD UE v0 vD vE
    D.polynomial.natDegree E.polynomial.natDegree D.natDegree_ne_zero
    E.natDegree_ne_zero
    (nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible)
    (nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible)
    hde u hu
    (nonarchimedeanLocalFieldAdjoinRootFractionField_tameValHom_norm K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible)
    (by
      intro a ha
      have ha' : a ∈ (tameValHom v0).ker := by simpa only [MonoidHom.mem_ker] using ha
      obtain ⟨b, hb⟩ :=
        nonarchimedeanLocalFieldAdjoinRoot_fractionField_norm_surjective_on_tameValKer
          K D.polynomial D.monic D.residuePolynomial D.residueMonic
          D.reduction_eq D.residueIrreducible a ha'
      exact ⟨Units.map (algebraMap BD UD) b, by
        apply Units.ext
        exact hb⟩)
    (nonarchimedeanLocalFieldAdjoinRootFractionField_tameValHom_norm K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible)
    (by
      intro a ha
      have ha' : a ∈ (tameValHom v0).ker := by simpa only [MonoidHom.mem_ker] using ha
      obtain ⟨b, hb⟩ :=
        nonarchimedeanLocalFieldAdjoinRoot_fractionField_norm_surjective_on_tameValKer
          K E.polynomial E.monic E.residuePolynomial E.residueMonic
          E.reduction_eq E.residueIrreducible a ha'
      exact ⟨Units.map (algebraMap BE UE) b, by
        apply Units.ext
        exact hb⟩)
  apply AddMonoidHom.ext
  intro z
  let w := cD.symm z
  have hbase := cyclicGaloisH2AddEquivOfEquivEquiv_normQuotientTransition
    F0 K UD UE eK.toRingEquiv hcompatD hcompatE w
  have hnorm : cE.symm (cyclicGaloisH2NormQuotientTransition K UD UE z) =
      cyclicGaloisH2NormQuotientTransition F0 UD UE w := by
    apply cE.injective
    rw [cE.apply_symm_apply]
    rw [show z = cD w by exact (cD.apply_symm_apply z).symm]
    exact hbase.symm
  have hold := DFunLike.congr_fun hselected0 w
  change oldE (cE.symm (cyclicGaloisH2NormQuotientTransition K UD UE z)) =
    zmodRatModIntTransition D.natDegree_ne_zero E.natDegree_ne_zero hde
      (oldD (cD.symm z))
  rw [hnorm]
  exact hold

/-- Arithmetic-Frobenius normalization converts oriented Galois inflation into the canonical
inclusion between finite torsion layers. -/
theorem cyclicGaloisH2FrobeniusInvariantOverBase_orientedTransition
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
    E.cyclicGaloisH2FrobeniusInvariantOverBase.toAddMonoidHom.comp
        (cyclicGaloisH2OrientedNormQuotientTransition K UD UE) =
      (zmodRatModIntTransition D.natDegree_ne_zero E.natDegree_ne_zero hde).comp
        D.cyclicGaloisH2FrobeniusInvariantOverBase.toAddMonoidHom := by
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
  let sD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2InvariantOverBase K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  let sE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2InvariantOverBase K
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible
  let cD := D.fractionGaloisFrobeniusCoordinateOverBase
  let cE := E.fractionGaloisFrobeniusCoordinateOverBase
  let q := D.fractionGaloisRestrictionOrientationOverBase E hde
  apply AddMonoidHom.ext
  intro z
  have hselected := DFunLike.congr_fun
    (D.cyclicGaloisH2SelectedInvariantOverBase_normTransition E hde) z
  have hqval :=
    D.cyclicGaloisRestrictionOrientation_val_eq_fractionGaloisRestrictionOrientationOverBase_val
      E hde
  have hcoord := D.fractionGaloisFrobeniusCoordinateOverBase_tower E hde
  change sE (cyclicGaloisH2NormQuotientTransition K UD UE z) =
    zmodRatModIntTransition D.natDegree_ne_zero E.natDegree_ne_zero hde (sD z)
    at hselected
  dsimp only at hqval
  change cE * sE (cyclicGaloisH2OrientedNormQuotientTransition K UD UE z) =
    zmodRatModIntTransition D.natDegree_ne_zero E.natDegree_ne_zero hde (cD * sD z)
  rw [cyclicGaloisH2OrientedNormQuotientTransition_apply, map_nsmul, hqval]
  rw [hselected]
  exact zmodRatModIntTransition_frobenius_cancellation
    D.natDegree_ne_zero E.natDegree_ne_zero hde q cE cD (sD z) hcoord

/-- Frobenius-normalized finite Brauer coordinates commute with concrete root-lift inclusion. -/
theorem cyclicBrauerFrobeniusInvariantOverBase_inclusion
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    E.cyclicBrauerFrobeniusInvariantOverBase.toAddMonoidHom.comp
        (cyclicBrauerRootLiftInclusion D E hde) =
      (zmodRatModIntTransition D.natDegree_ne_zero E.natDegree_ne_zero hde).comp
        D.cyclicBrauerFrobeniusInvariantOverBase.toAddMonoidHom := by
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
  apply AddMonoidHom.ext
  intro x
  let bD := cyclicGaloisH2BrauerSubgroupAddEquiv K UD
  let z := bD.symm x
  have hx : bD z = x := bD.apply_symm_apply x
  rw [← hx]
  simp only [AddMonoidHom.comp_apply]
  have hinclusion : cyclicBrauerRootLiftInclusion D E hde
      (cyclicGaloisH2BrauerSubgroupAddEquiv K UD z) =
        cyclicGaloisH2BrauerSubgroupAddEquiv K UE
          (cyclicGaloisH2OrientedNormQuotientTransition K UD UE z) := by
    apply Subtype.ext
    exact (cyclicGaloisH2BrauerMap_orientedNormQuotientTransition K UD UE z).symm
  rw [hinclusion]
  have hE := E.cyclicBrauerFrobeniusInvariantOverBase_h2
    (cyclicGaloisH2OrientedNormQuotientTransition K UD UE z)
  have hD := D.cyclicBrauerFrobeniusInvariantOverBase_h2 z
  have htransition := DFunLike.congr_fun
    (D.cyclicGaloisH2FrobeniusInvariantOverBase_orientedTransition E hde) z
  calc
    _ = E.cyclicGaloisH2FrobeniusInvariantOverBase
        (cyclicGaloisH2OrientedNormQuotientTransition K UD UE z) := hE
    _ = zmodRatModIntTransition D.natDegree_ne_zero E.natDegree_ne_zero hde
        (D.cyclicGaloisH2FrobeniusInvariantOverBase z) := by
      simpa only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom] using htransition
    _ = _ := congrArg
      (zmodRatModIntTransition D.natDegree_ne_zero E.natDegree_ne_zero hde) hD.symm

end NonarchimedeanFiniteUnramifiedRootLift

open scoped NormedField ValuativeRel Valued

/-- Frobenius-normalized coordinate on the factorial unramified Brauer slice. -/
noncomputable def localBrauerFactorialFrobeniusAddEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    localBrauerFactorialSlice K n ≃+ ZMod (localBrauerFactorialDegree n) := by
  rw [← localBrauerFactorialRootLift_natDegree K n]
  exact (localBrauerFactorialRootLift K n).cyclicBrauerFrobeniusInvariantOverBase

noncomputable def localBrauerFactorialFrobeniusInvariant
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    localBrauerFactorialSlice K n →+ RatModInt :=
  let D := localBrauerFactorialRootLift K n
  (zmodRatModIntAddHom D.polynomial.natDegree D.natDegree_ne_zero).comp
    D.cyclicBrauerFrobeniusInvariantOverBase.toAddMonoidHom

theorem localBrauerFactorialFrobeniusInvariant_inclusion
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {m n : ℕ} (hmn : m ≤ n)
    (x : localBrauerFactorialSlice K m) :
    localBrauerFactorialFrobeniusInvariant K n
        (localBrauerFactorialInclusion K hmn x) =
      localBrauerFactorialFrobeniusInvariant K m x := by
  let D := localBrauerFactorialRootLift K m
  let E := localBrauerFactorialRootLift K n
  let hde := localBrauerFactorialRootLift_degree_dvd_of_le K hmn
  have hfinite := DFunLike.congr_fun
    (D.cyclicBrauerFrobeniusInvariantOverBase_inclusion E hde) x
  change zmodRatModIntAddHom E.polynomial.natDegree E.natDegree_ne_zero
      (E.cyclicBrauerFrobeniusInvariantOverBase
        (localBrauerFactorialInclusion K hmn x)) =
    zmodRatModIntAddHom D.polynomial.natDegree D.natDegree_ne_zero
      (D.cyclicBrauerFrobeniusInvariantOverBase x)
  rw [← zmodRatModIntAddHom_transition D.natDegree_ne_zero E.natDegree_ne_zero
    hde (D.cyclicBrauerFrobeniusInvariantOverBase x)]
  congr 1

theorem localBrauerFactorialFrobeniusInvariants_agree
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (m n : ℕ) (x : BrauerGroup K)
    (hxm : x ∈ localBrauerFactorialSlice K m)
    (hxn : x ∈ localBrauerFactorialSlice K n) :
    localBrauerFactorialFrobeniusInvariant K m ⟨x, hxm⟩ =
      localBrauerFactorialFrobeniusInvariant K n ⟨x, hxn⟩ := by
  let k := max m n
  calc
    localBrauerFactorialFrobeniusInvariant K m ⟨x, hxm⟩ =
        localBrauerFactorialFrobeniusInvariant K k
          (localBrauerFactorialInclusion K (Nat.le_max_left m n) ⟨x, hxm⟩) :=
      (localBrauerFactorialFrobeniusInvariant_inclusion K
        (Nat.le_max_left m n) ⟨x, hxm⟩).symm
    _ = localBrauerFactorialFrobeniusInvariant K k
          (localBrauerFactorialInclusion K (Nat.le_max_right m n) ⟨x, hxn⟩) := by
      rfl
    _ = localBrauerFactorialFrobeniusInvariant K n ⟨x, hxn⟩ :=
      localBrauerFactorialFrobeniusInvariant_inclusion K
        (Nat.le_max_right m n) ⟨x, hxn⟩


end
end GaloisForLFunctions.HTGeometry.ABHN
