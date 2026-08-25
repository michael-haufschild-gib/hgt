/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanContinuousH2Hasse
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionUnramifiedMaximalSubfieldGalois
import GaloisForLFunctions.HTGeometry.ABHN.CyclicGaloisBrauerSubgroupTower

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped ValuativeRel

theorem adjoinRootToScalarExtendedAdjoinRoot_injective
    (R K : Type) [CommRing R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K))
    (p : Polynomial R) (hp : p.Monic) :
    Function.Injective
      (AdjoinRoot.lift
        ((AdjoinRoot.of (p.map (algebraMap R K))).comp (algebraMap R K))
        (AdjoinRoot.root (p.map (algebraMap R K)))
        (by rw [← Polynomial.eval₂_map]
            exact AdjoinRoot.eval₂_root (p.map (algebraMap R K)))) := by
  letI : Module.Free R (AdjoinRoot p) := hp.free_adjoinRoot
  letI : Module.Flat R (AdjoinRoot p) := inferInstance
  let e := adjoinRootScalarExtensionEquivOfMapEq R K p
    (p.map (algebraMap R K)) rfl
  let t : AdjoinRoot p →+* AdjoinRoot (p.map (algebraMap R K)) :=
    e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        AdjoinRoot p →ₐ[R] TensorProduct R K (AdjoinRoot p)).toRingHom
  have ht : Function.Injective t :=
    e.injective.comp (Algebra.TensorProduct.includeRight_injective hinj)
  let i : AdjoinRoot p →+* AdjoinRoot (p.map (algebraMap R K)) :=
    AdjoinRoot.lift
      ((AdjoinRoot.of (p.map (algebraMap R K))).comp (algebraMap R K))
      (AdjoinRoot.root (p.map (algebraMap R K)))
      (by rw [← Polynomial.eval₂_map]
          exact AdjoinRoot.eval₂_root (p.map (algebraMap R K)))
  have hti : t = i := by
    apply AdjoinRoot.ringHom_ext
    · ext r
      change t (AdjoinRoot.of p r) = i (AdjoinRoot.of p r)
      rw [show t (AdjoinRoot.of p r) =
          e (Algebra.TensorProduct.includeRight (AdjoinRoot.of p r)) by rfl]
      rw [show Algebra.TensorProduct.includeRight (AdjoinRoot.of p r) =
          algebraMap K (TensorProduct R K (AdjoinRoot p)) (algebraMap R K r) by
        rw [Algebra.TensorProduct.includeRight_apply]
        change 1 ⊗ₜ[R] algebraMap R (AdjoinRoot p) r = _
        rw [← Algebra.TensorProduct.algebraMap_apply']
        exact IsScalarTower.algebraMap_apply R K
          (TensorProduct R K (AdjoinRoot p)) r]
      rw [e.commutes]
      exact (AdjoinRoot.lift_of (i :=
        (AdjoinRoot.of (p.map (algebraMap R K))).comp (algebraMap R K))
        (a := AdjoinRoot.root (p.map (algebraMap R K))) _).symm
    · rw [show t (AdjoinRoot.root p) =
          e ((1 : K) ⊗ₜ[R] AdjoinRoot.root p) by rfl]
      rw [show i (AdjoinRoot.root p) =
          AdjoinRoot.root (p.map (algebraMap R K)) by
        exact AdjoinRoot.lift_root _]
      exact adjoinRootScalarExtensionEquivOfMapEq_tmul_one_root
        R K p (p.map (algebraMap R K)) rfl
  exact show Function.Injective i from hti ▸ ht


theorem nonarchimedeanFiniteUnramifiedRootLift_exists_residueAlgHom_of_dvd
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    let B := AdjoinRoot E.polynomial
    letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : IsLocalRing B := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : IsLocalHom (algebraMap 𝒪[K] B) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
        E.residuePolynomial E.reduction_eq E.residueIrreducible
    Nonempty (AdjoinRoot D.residuePolynomial →ₐ[𝓀[K]] IsLocalRing.ResidueField B) := by
  let B := AdjoinRoot E.polynomial
  letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalRing B := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] B) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
      E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : Fact (Irreducible D.residuePolynomial) := ⟨D.residueIrreducible⟩
  letI : Algebra 𝓀[K] (AdjoinRoot D.residuePolynomial) :=
    AdjoinRoot.instAlgebra D.residuePolynomial
  letI : Module.Finite 𝓀[K] (AdjoinRoot D.residuePolynomial) :=
    D.residueMonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot D.residuePolynomial) := Module.finite_of_finite 𝓀[K]
  letI : Finite (IsLocalRing.ResidueField B) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K E.polynomial E.monic
      E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField B) :=
    Module.Finite.of_finite
  exact FiniteField.nonempty_algHom_of_finrank_dvd
    (F := 𝓀[K]) (K := AdjoinRoot D.residuePolynomial)
    (L := IsLocalRing.ResidueField B) (by
  calc
    Module.finrank 𝓀[K] (AdjoinRoot D.residuePolynomial) =
        D.residuePolynomial.natDegree :=
      (AdjoinRoot.isAdjoinRootMonic D.residuePolynomial D.residueMonic).finrank
    _ = D.polynomial.natDegree := by
      rw [← D.reduction_eq]
      exact D.monic.natDegree_map _
    _ ∣ E.polynomial.natDegree := hde
    _ = Module.finrank 𝓀[K] (IsLocalRing.ResidueField B) :=
      (nonarchimedeanLocalFieldAdjoinRootResidueField_finrank K E.polynomial E.monic
        E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible).symm)

theorem nonarchimedeanFiniteUnramifiedRootLift_exists_integralAlgHom_of_dvd
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D E : NonarchimedeanFiniteUnramifiedRootLift K)
    (hde : D.polynomial.natDegree ∣ E.polynomial.natDegree) :
    let B := AdjoinRoot E.polynomial
    letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : IsLocalRing B := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : IsLocalHom (algebraMap 𝒪[K] B) :=
      nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
        E.residuePolynomial E.reduction_eq E.residueIrreducible
    letI : Algebra 𝒪[K] (AdjoinRoot D.polynomial) :=
      AdjoinRoot.instAlgebra D.polynomial
    Nonempty (AdjoinRoot D.polynomial →ₐ[𝒪[K]] B) := by
  let B := AdjoinRoot E.polynomial
  letI : IsDomain B := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalRing B := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] B) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
      E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : Algebra 𝒪[K] (AdjoinRoot D.polynomial) :=
    AdjoinRoot.instAlgebra D.polynomial
  letI : Fact (Irreducible D.residuePolynomial) := ⟨D.residueIrreducible⟩
  letI : Algebra 𝓀[K] (AdjoinRoot D.residuePolynomial) :=
    AdjoinRoot.instAlgebra D.residuePolynomial
  letI : Module.Finite 𝓀[K] (AdjoinRoot D.residuePolynomial) :=
    D.residueMonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot D.residuePolynomial) := Module.finite_of_finite 𝓀[K]
  letI : Finite (IsLocalRing.ResidueField B) :=
    nonarchimedeanLocalFieldAdjoinRootResidueField_finite K E.polynomial E.monic
      E.residuePolynomial E.residueMonic E.reduction_eq E.residueIrreducible
  letI : Module.Finite 𝓀[K] (IsLocalRing.ResidueField B) := Module.Finite.of_finite
  obtain ⟨φ⟩ :=
    nonarchimedeanFiniteUnramifiedRootLift_exists_residueAlgHom_of_dvd K D E hde
  let a₀ : IsLocalRing.ResidueField B := φ (AdjoinRoot.root D.residuePolynomial)
  obtain ⟨aLift, haLift⟩ := IsLocalRing.residue_surjective (R := B) a₀
  let p : Polynomial B := D.polynomial.map (algebraMap 𝒪[K] B)
  have hp : p.Monic := D.monic.map _
  have hcoeff : (IsLocalRing.residue B).comp (algebraMap 𝒪[K] B) =
      (algebraMap 𝓀[K] (IsLocalRing.ResidueField B)).comp
        (IsLocalRing.residue 𝒪[K]) := by
    ext c
    exact (IsLocalRing.ResidueField.algebraMap_residue c).symm
  have hreduce : p.map (IsLocalRing.residue B) =
      D.residuePolynomial.map (algebraMap 𝓀[K] (IsLocalRing.ResidueField B)) := by
    calc
      p.map (IsLocalRing.residue B) =
          D.polynomial.map ((IsLocalRing.residue B).comp (algebraMap 𝒪[K] B)) := by
        simp only [p, Polynomial.map_map]
      _ = D.polynomial.map ((algebraMap 𝓀[K] (IsLocalRing.ResidueField B)).comp
          (IsLocalRing.residue 𝒪[K])) := by rw [hcoeff]
      _ = (D.polynomial.map (IsLocalRing.residue 𝒪[K])).map
          (algebraMap 𝓀[K] (IsLocalRing.ResidueField B)) := by
        rw [Polynomial.map_map]
      _ = D.residuePolynomial.map
          (algebraMap 𝓀[K] (IsLocalRing.ResidueField B)) := by
        change (D.polynomial.map (Ideal.Quotient.mk 𝓂[K])).map _ = _
        exact congrArg (fun q => q.map
          (algebraMap 𝓀[K] (IsLocalRing.ResidueField B))) D.reduction_eq
  have hrootResidue : (p.map (IsLocalRing.residue B)).eval a₀ = 0 := by
    rw [hreduce]
    rw [Polynomial.eval_map]
    exact AdjoinRoot.aeval_algHom_eq_zero D.residuePolynomial φ
  letI : PerfectField 𝓀[K] := inferInstance
  have hsep : D.residuePolynomial.Separable :=
    PerfectField.separable_of_irreducible D.residueIrreducible
  have hsepMap : (p.map (IsLocalRing.residue B)).Separable := by
    rw [hreduce]
    exact (Polynomial.separable_map _).mpr hsep
  have hderivResidue :
      (p.map (IsLocalRing.residue B)).derivative.eval a₀ ≠ 0 := by
    apply hsepMap.eval₂_derivative_ne_zero (RingHom.id (IsLocalRing.ResidueField B))
    simpa only [Polynomial.eval₂_id] using hrootResidue
  have hrootLift : Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) (p.eval aLift) = 0 := by
    change IsLocalRing.residue B (p.eval aLift) = 0
    calc
      IsLocalRing.residue B (p.eval aLift) =
          Polynomial.eval₂ (IsLocalRing.residue B)
            (IsLocalRing.residue B aLift) p :=
        (Polynomial.eval₂_at_apply (IsLocalRing.residue B) aLift).symm
      _ = (p.map (IsLocalRing.residue B)).eval
          (IsLocalRing.residue B aLift) :=
        (Polynomial.eval_map (IsLocalRing.residue B) _).symm
      _ = 0 := by rw [haLift]; exact hrootResidue
  have hderivLift :
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal B) (p.derivative.eval aLift) ≠ 0 := by
    change IsLocalRing.residue B (p.derivative.eval aLift) ≠ 0
    calc
      IsLocalRing.residue B (p.derivative.eval aLift) =
          Polynomial.eval₂ (IsLocalRing.residue B)
            (IsLocalRing.residue B aLift) p.derivative :=
        (Polynomial.eval₂_at_apply (IsLocalRing.residue B) aLift).symm
      _ = (p.derivative.map (IsLocalRing.residue B)).eval
          (IsLocalRing.residue B aLift) :=
        (Polynomial.eval_map (IsLocalRing.residue B) _).symm
      _ = (p.map (IsLocalRing.residue B)).derivative.eval a₀ := by
        rw [haLift]
        exact congrArg (fun q : Polynomial (IsLocalRing.ResidueField B) => q.eval a₀)
          (Polynomial.derivative_map p (IsLocalRing.residue B)).symm
      _ ≠ 0 := hderivResidue
  obtain ⟨a, ha, _⟩ :=
    nonarchimedeanLocalFieldAdjoinRoot_hensel_lift K E.polynomial E.monic
      E.residuePolynomial E.reduction_eq E.residueIrreducible
      p hp aLift hrootLift hderivLift
  have hEval : Polynomial.eval₂ (algebraMap 𝒪[K] B) a D.polynomial = 0 := by
    have ha' : (D.polynomial.map (algebraMap 𝒪[K] B)).eval a = 0 := ha
    rw [Polynomial.eval_map] at ha'
    exact ha'
  let liftRingHom : AdjoinRoot D.polynomial →+* B :=
    AdjoinRoot.lift (algebraMap 𝒪[K] B) a hEval
  refine ⟨{ liftRingHom with commutes' := ?_ }⟩
  intro r
  change (AdjoinRoot.lift (algebraMap 𝒪[K] B) a hEval)
      (AdjoinRoot.of D.polynomial r) = AdjoinRoot.of E.polynomial r
  rw [AdjoinRoot.lift_of hEval]
  rfl

theorem nonarchimedeanFiniteUnramifiedRootLift_exists_fractionFieldAlgHom_of_dvd
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
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
    letI : Algebra K UD := by
      let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
      have hgD : Function.Injective gD :=
        (IsFractionRing.injective BD UD).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
              D.residuePolynomial D.reduction_eq D.residueIrreducible))
      exact RingHom.toAlgebra (IsFractionRing.lift hgD)
    letI : Algebra K UE := by
      let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
      have hgE : Function.Injective gE :=
        (IsFractionRing.injective BE UE).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
              E.residuePolynomial E.reduction_eq E.residueIrreducible))
      exact RingHom.toAlgebra (IsFractionRing.lift hgE)
    Nonempty (UD →ₐ[K] UE) := by
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalRing BE := nonarchimedeanLocalFieldAdjoinRootIsLocalRing K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : IsLocalHom (algebraMap 𝒪[K] BE) :=
    nonarchimedeanLocalFieldAdjoinRoot_isLocalHom K E.polynomial E.monic
      E.residuePolynomial E.reduction_eq E.residueIrreducible
  letI : Algebra 𝒪[K] BD := AdjoinRoot.instAlgebra D.polynomial
  let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
  have hgD : Function.Injective gD :=
    (IsFractionRing.injective BD UD).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  obtain ⟨φB⟩ :=
    nonarchimedeanFiniteUnramifiedRootLift_exists_integralAlgHom_of_dvd K D E hde
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
  let j : UD →+* AdjoinRoot qD := IsFractionRing.lift hi
  have hjcomm : j.comp (algebraMap K UD) = algebraMap K (AdjoinRoot qD) := by
    apply IsFractionRing.ringHom_ext (A := 𝒪[K])
    intro r
    simp only [RingHom.comp_apply]
    change IsFractionRing.lift hi (IsFractionRing.lift hgD
        (algebraMap 𝒪[K] K r)) =
      AdjoinRoot.of qD (algebraMap 𝒪[K] K r)
    rw [IsFractionRing.lift_algebraMap]
    change IsFractionRing.lift hi
        (algebraMap BD UD (AdjoinRoot.of D.polynomial r)) = _
    rw [IsFractionRing.lift_algebraMap]
    exact AdjoinRoot.lift_of _
  let jAlg : UD →ₐ[K] AdjoinRoot qD :=
    { j with commutes' := fun x => DFunLike.congr_fun hjcomm x }
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
    rw [Polynomial.eval₂_map]
    rw [hbase]
    exact hrootUE
  let ψ : AdjoinRoot qD →ₐ[K] UE :=
    AdjoinRoot.liftAlgHom qD (Algebra.ofId K UE) b hqroot
  exact ⟨ψ.comp jAlg⟩

/-- Unramified cyclic Brauer slices are directed by divisibility of residue degrees. -/
theorem nonarchimedeanFiniteUnramifiedRootLift_cyclicGaloisBrauerSubgroup_le_of_dvd
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
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
    letI : Algebra K UD := by
      let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
      have hgD : Function.Injective gD :=
        (IsFractionRing.injective BD UD).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
              D.residuePolynomial D.reduction_eq D.residueIrreducible))
      exact RingHom.toAlgebra (IsFractionRing.lift hgD)
    letI : Algebra K UE := by
      let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
      have hgE : Function.Injective gE :=
        (IsFractionRing.injective BE UE).comp
          (AdjoinRoot.of.injective_of_degree_ne_zero
            (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
              E.residuePolynomial E.reduction_eq E.residueIrreducible))
      exact RingHom.toAlgebra (IsFractionRing.lift hgE)
    letI : FiniteDimensional K UD :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
        D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : FiniteDimensional K UE :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
        E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
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
    cyclicGaloisBrauerSubgroup K UD ≤ cyclicGaloisBrauerSubgroup K UE := by
  let BD := AdjoinRoot D.polynomial
  let BE := AdjoinRoot E.polynomial
  let UD := FractionRing BD
  let UE := FractionRing BE
  letI : IsDomain BD := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsDomain BE := nonarchimedeanLocalFieldAdjoinRoot_isDomain K
    E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
  let gD : 𝒪[K] →+* UD := (algebraMap BD UD).comp (AdjoinRoot.of D.polynomial)
  have hgD : Function.Injective gD :=
    (IsFractionRing.injective BD UD).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  let gE : 𝒪[K] →+* UE := (algebraMap BE UE).comp (AdjoinRoot.of E.polynomial)
  have hgE : Function.Injective gE :=
    (IsFractionRing.injective BE UE).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K E.polynomial E.monic
          E.residuePolynomial E.reduction_eq E.residueIrreducible))
  letI : Algebra K UD := RingHom.toAlgebra (IsFractionRing.lift hgD)
  letI : Algebra K UE := RingHom.toAlgebra (IsFractionRing.lift hgE)
  letI : FiniteDimensional K UD :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : FiniteDimensional K UE :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensionalOverBase K
      E.polynomial E.monic E.residuePolynomial E.reduction_eq E.residueIrreducible
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
  obtain ⟨φ⟩ :=
    nonarchimedeanFiniteUnramifiedRootLift_exists_fractionFieldAlgHom_of_dvd K D E hde
  letI : Algebra UD UE := φ.toRingHom.toAlgebra
  letI : IsScalarTower K UD UE := IsScalarTower.of_algHom φ
  letI : FiniteDimensional UD UE := FiniteDimensional.right K UD UE
  exact cyclicGaloisBrauerSubgroup_le_of_isScalarTower K UD UE

end

end GaloisForLFunctions.HTGeometry.ABHN

