/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanFiniteUnramifiedRootLiftTower
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldCyclicGaloisH2InvariantOverBase
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionLocalUnramifiedCyclicExhaustion

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped NormedField ValuativeRel Valued

theorem nonarchimedeanFiniteUnramifiedRootLift_exists_natDegree
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) [NeZero n] :
    ∃ D : NonarchimedeanFiniteUnramifiedRootLift K,
      D.polynomial.natDegree = n := by
  obtain ⟨f, g, hf, hgmonic, hg, hfg, hdegree, _⟩ :=
    nonarchimedeanLocalField_exists_finiteUnramifiedDVRLift_of_natDegree K n
  exact ⟨{
    polynomial := f
    residuePolynomial := g
    monic := hf
    residueMonic := hgmonic
    reduction_eq := hfg
    residueIrreducible := hg
  }, hdegree⟩

def localBrauerFactorialDegree (n : ℕ) : ℕ := (n + 1).factorial

theorem localBrauerFactorialDegree_ne_zero (n : ℕ) :
    localBrauerFactorialDegree n ≠ 0 :=
  Nat.factorial_ne_zero _

theorem localBrauerFactorialDegree_dvd_of_le {m n : ℕ} (hmn : m ≤ n) :
    localBrauerFactorialDegree m ∣ localBrauerFactorialDegree n :=
  Nat.factorial_dvd_factorial (Nat.add_le_add_right hmn 1)

noncomputable def localBrauerFactorialRootLift
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    NonarchimedeanFiniteUnramifiedRootLift K := by
  letI : NeZero (localBrauerFactorialDegree n) :=
    ⟨localBrauerFactorialDegree_ne_zero n⟩
  exact Classical.choose
    (nonarchimedeanFiniteUnramifiedRootLift_exists_natDegree K
      (localBrauerFactorialDegree n))

theorem localBrauerFactorialRootLift_natDegree
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    (localBrauerFactorialRootLift K n).polynomial.natDegree =
      localBrauerFactorialDegree n := by
  letI : NeZero (localBrauerFactorialDegree n) :=
    ⟨localBrauerFactorialDegree_ne_zero n⟩
  exact Classical.choose_spec
    (nonarchimedeanFiniteUnramifiedRootLift_exists_natDegree K
      (localBrauerFactorialDegree n))

theorem localBrauerFactorialRootLift_degree_dvd_of_le
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {m n : ℕ} (hmn : m ≤ n) :
    (localBrauerFactorialRootLift K m).polynomial.natDegree ∣
      (localBrauerFactorialRootLift K n).polynomial.natDegree := by
  rw [localBrauerFactorialRootLift_natDegree,
    localBrauerFactorialRootLift_natDegree]
  exact localBrauerFactorialDegree_dvd_of_le hmn

noncomputable def nonarchimedeanFiniteUnramifiedRootLiftCyclicBrauerSubgroup
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    AddSubgroup (BrauerGroup K) := by
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
  exact cyclicGaloisBrauerSubgroup K U

theorem nonarchimedeanFiniteUnramifiedRootLiftCyclicBrauerSubgroup_addEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    Nonempty (ZMod D.polynomial.natDegree ≃+
      nonarchimedeanFiniteUnramifiedRootLiftCyclicBrauerSubgroup K D) := by
  let B := AdjoinRoot D.polynomial
  let U := FractionRing B
  letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FaithfulSMul 𝒪[K] B := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] B).mpr ?_
    change Function.Injective <| AdjoinRoot.of D.polynomial
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible)
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
  let hInv : cyclicGaloisH2 K U ≃+ ZMod D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2InvariantOverBase K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  change Nonempty (ZMod D.polynomial.natDegree ≃+ cyclicGaloisBrauerSubgroup K U)
  exact ⟨hInv.symm.trans (cyclicGaloisH2BrauerSubgroupAddEquiv K U)⟩

noncomputable def localBrauerFactorialSlice
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) : AddSubgroup (BrauerGroup K) :=
  nonarchimedeanFiniteUnramifiedRootLiftCyclicBrauerSubgroup K
    (localBrauerFactorialRootLift K n)

theorem localBrauerFactorialSlice_addEquiv
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ) :
    Nonempty (ZMod (localBrauerFactorialDegree n) ≃+ localBrauerFactorialSlice K n) := by
  rw [← localBrauerFactorialRootLift_natDegree K n]
  exact nonarchimedeanFiniteUnramifiedRootLiftCyclicBrauerSubgroup_addEquiv K
    (localBrauerFactorialRootLift K n)

theorem localBrauerFactorialSlice_mono
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {m n : ℕ} (hmn : m ≤ n) :
    localBrauerFactorialSlice K m ≤ localBrauerFactorialSlice K n := by
  exact nonarchimedeanFiniteUnramifiedRootLift_cyclicGaloisBrauerSubgroup_le_of_dvd
    K (localBrauerFactorialRootLift K m) (localBrauerFactorialRootLift K n)
      (localBrauerFactorialRootLift_degree_dvd_of_le K hmn)

theorem iSup_localBrauerFactorialSlice_eq_top
    (F : Type) [NontriviallyNormedField F] [CompleteSpace F]
    [IsUltrametricDist F] [LocallyCompactSpace F] :
    letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
    letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
      change (NormedField.valuation (K := F)).IsNontrivial
      exact Valuation.RankOne.toIsNontrivial
    letI : IsNonarchimedeanLocalField F :=
      isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
    ⨆ n : ℕ, localBrauerFactorialSlice F n = ⊤ := by
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
    change (NormedField.valuation (K := F)).IsNontrivial
    exact Valuation.RankOne.toIsNontrivial
  letI : IsNonarchimedeanLocalField F :=
    isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
  apply top_unique
  intro x _
  obtain ⟨T, hT, aFT, finT, galoisT, cyclicT, a, hx, R, hRdegree,
      ⟨eUT⟩, _, _⟩ :=
    nonarchimedeanLocal_brauerGroup_exists_unramifiedRootLiftCyclicRepresentative x
  letI : Field T := hT
  letI : Algebra F T := aFT
  letI : FiniteDimensional F T := finT
  letI : IsGalois F T := galoisT
  letI : IsCyclic Gal(T/F) := cyclicT
  have hxT : x ∈ cyclicGaloisBrauerSubgroup F T := by
    rw [hx]
    exact cyclicGaloisAlgebra_brauerClass_mem_cyclicGaloisBrauerSubgroup F T (a⁻¹)
  let E := localBrauerFactorialRootLift F R.polynomial.natDegree
  have hdiv : R.polynomial.natDegree ∣ E.polynomial.natDegree := by
    rw [show E.polynomial.natDegree =
      localBrauerFactorialDegree R.polynomial.natDegree by
        exact localBrauerFactorialRootLift_natDegree F R.polynomial.natDegree]
    change R.polynomial.natDegree ∣ (R.polynomial.natDegree + 1).factorial
    exact Nat.dvd_factorial (Nat.pos_of_ne_zero R.natDegree_ne_zero)
      (Nat.le_add_right _ 1)
  let B := AdjoinRoot R.polynomial
  let U := FractionRing B
  let BE := AdjoinRoot E.polynomial
  let UE := FractionRing BE
  letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain F
    R.polynomial R.monic R.residuePolynomial R.reduction_eq R.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain F
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  let gR : (ValuativeRel.valuation F).integer →+* U :=
    (algebraMap B U).comp (AdjoinRoot.of R.polynomial)
  have hgR : Function.Injective gR :=
    (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero F R.polynomial R.monic
          R.residuePolynomial R.reduction_eq R.residueIrreducible))
  let gE : (ValuativeRel.valuation F).integer →+* UE :=
    (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero F E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : Algebra F U := RingHom.toAlgebra (IsFractionRing.lift hgR)
  letI : Algebra F UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  letI : FiniteDimensional F UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase F
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsGalois F UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGalois F E.polynomial E.monic
      E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
  letI : IsCyclic Gal(UE/F) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic_over_base F
      E.polynomial E.monic E.residuePolynomial E.residueMonic
      E.reduction_eq E.residueIrreducible
  obtain ⟨φU⟩ :=
    nonarchimedeanFiniteUnramifiedRootLift_exists_fractionFieldAlgHom_of_dvd F R E hdiv
  let φ : T →ₐ[F] UE := φU.comp eUT.symm.toAlgHom
  letI : Algebra T UE := φ.toRingHom.toAlgebra
  letI : IsScalarTower F T UE := IsScalarTower.of_algHom φ
  letI : FiniteDimensional T UE := FiniteDimensional.right F T UE
  have hxUE : x ∈ cyclicGaloisBrauerSubgroup F UE :=
    cyclicGaloisBrauerSubgroup_le_of_isScalarTower F T UE hxT
  apply (le_iSup (fun n : ℕ => localBrauerFactorialSlice F n)
    R.polynomial.natDegree)
  change x ∈ nonarchimedeanFiniteUnramifiedRootLiftCyclicBrauerSubgroup F E
  exact hxUE

end


end GaloisForLFunctions.HTGeometry.ABHN

