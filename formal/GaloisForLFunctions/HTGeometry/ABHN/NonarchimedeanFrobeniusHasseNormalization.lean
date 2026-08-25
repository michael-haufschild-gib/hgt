/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanUnramifiedGaloisHasse
import GaloisForLFunctions.HTGeometry.ABHN.CyclicSubgroupCompatibleCoordinates
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldCyclicGaloisH2Invariant
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldCyclicBrauerInvariant

/-!
# Frobenius/Hasse normalization of finite unramified local invariants

The valuation coordinate on cyclic `H²` uses mathlib's internally selected cyclic Galois
generator. Canonical local class field theory instead evaluates the corresponding character on
arithmetic Frobenius. This module computes arithmetic Frobenius's coordinate relative to the
selected generator, proves that coordinate is a unit, and multiplies the finite local invariant
by precisely that unit.

Thus the correction is explicit and axiom-free. It also records why an arbitrary compatible
`Br(K) ≃ ℚ/ℤ` coordinate cannot be declared Frobenius-normalized without this comparison.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped ValuativeRel WithZero WithZeroMulInt

noncomputable section

namespace NonarchimedeanFiniteUnramifiedRootLift

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

noncomputable def fractionGaloisFrobeniusCoordinate
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    ZMod D.polynomial.natDegree := by
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
  letI : FaithfulSMul 𝒪[K] U := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
    change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    exact (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
  letI : FiniteDimensional (FractionRing 𝒪[K]) U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsGalois (FractionRing 𝒪[K]) U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(U / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  have hdegree : Module.finrank (FractionRing 𝒪[K]) U =
      D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  have hcard : Nat.card Gal(U / FractionRing 𝒪[K]) = D.polynomial.natDegree :=
    (IsGalois.card_aut_eq_finrank (FractionRing 𝒪[K]) U).trans hdegree
  let e : Multiplicative (ZMod D.polynomial.natDegree) ≃* Gal(U / FractionRing 𝒪[K]) :=
    zmodMulEquivOfGenerator
      (cyclicGaloisGenerator_spec (FractionRing 𝒪[K]) U) hcard
  exact Multiplicative.toAdd
    (e.symm D.fractionGaloisFrobenius)

theorem fractionGaloisFrobenius_eq_generator_pow_coordinate
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
    letI : FaithfulSMul 𝒪[K] B := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] B).mpr ?_
      change Function.Injective <| AdjoinRoot.of D.polynomial
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible)
    letI : FaithfulSMul 𝒪[K] U := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
      change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
      exact (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
    letI : FiniteDimensional (FractionRing 𝒪[K]) U :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
        D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    letI : IsGalois (FractionRing 𝒪[K]) U :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K
        D.polynomial D.monic D.residuePolynomial D.residueMonic
        D.reduction_eq D.residueIrreducible
    letI : IsCyclic Gal(U / FractionRing 𝒪[K]) :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K
        D.polynomial D.monic D.residuePolynomial D.residueMonic
        D.reduction_eq D.residueIrreducible
    D.fractionGaloisFrobenius =
      cyclicGaloisGenerator (FractionRing 𝒪[K]) U ^
        (D.fractionGaloisFrobeniusCoordinate).val := by
  dsimp only
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
  letI : FaithfulSMul 𝒪[K] U := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
    change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    exact (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
  letI : FiniteDimensional (FractionRing 𝒪[K]) U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsGalois (FractionRing 𝒪[K]) U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(U / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  have hdegree : Module.finrank (FractionRing 𝒪[K]) U =
      D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  have hcard : Nat.card Gal(U / FractionRing 𝒪[K]) = D.polynomial.natDegree :=
    (IsGalois.card_aut_eq_finrank (FractionRing 𝒪[K]) U).trans hdegree
  let e : Multiplicative (ZMod D.polynomial.natDegree) ≃* Gal(U / FractionRing 𝒪[K]) :=
    zmodMulEquivOfGenerator
      (cyclicGaloisGenerator_spec (FractionRing 𝒪[K]) U) hcard
  have h := e.apply_symm_apply D.fractionGaloisFrobenius
  change e (Multiplicative.ofAdd D.fractionGaloisFrobeniusCoordinate) = _ at h
  calc
    D.fractionGaloisFrobenius = e (Multiplicative.ofAdd D.fractionGaloisFrobeniusCoordinate) := h.symm
    _ = e (Multiplicative.ofAdd
        (((D.fractionGaloisFrobeniusCoordinate).val : ℤ) : ZMod _)) := by
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    _ = cyclicGaloisGenerator (FractionRing 𝒪[K]) U ^
        ((D.fractionGaloisFrobeniusCoordinate).val : ℤ) := by
      exact zmodMulEquivOfGenerator_apply_ofAdd_intCast
        (cyclicGaloisGenerator_spec (FractionRing 𝒪[K]) U) hcard _
    _ = _ := by rw [zpow_natCast]

/-- Arithmetic Frobenius differs from the internally selected cyclic generator by a unit
coordinate. This unit is the exact finite-level Hasse-normalization correction. -/
theorem fractionGaloisFrobeniusCoordinate_isUnit
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    IsUnit D.fractionGaloisFrobeniusCoordinate := by
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
  letI : FaithfulSMul 𝒪[K] U := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
    change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    exact (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
  letI : FiniteDimensional (FractionRing 𝒪[K]) U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsGalois (FractionRing 𝒪[K]) U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(U / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : NeZero D.polynomial.natDegree := ⟨D.natDegree_ne_zero⟩
  have hdegree : Module.finrank (FractionRing 𝒪[K]) U =
      D.polynomial.natDegree :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finrank K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  have htop : Subgroup.zpowers D.fractionGaloisFrobenius = ⊤ := by
    apply top_unique
    intro τ _
    obtain ⟨i, -, hi⟩ := D.fractionGaloisFrobenius_exists_pow_eq τ
    rw [← hi]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have horder : orderOf D.fractionGaloisFrobenius = D.polynomial.natDegree := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ((Subgroup.eq_top_iff' _).1 htop)]
    exact (IsGalois.card_aut_eq_finrank (FractionRing 𝒪[K]) U).trans hdegree
  rw [D.fractionGaloisFrobenius_eq_generator_pow_coordinate,
    orderOf_pow, cyclicGaloisGenerator_orderOf, hdegree] at horder
  have hgcd : Nat.gcd D.polynomial.natDegree
      D.fractionGaloisFrobeniusCoordinate.val = 1 := by
    rw [Nat.div_eq_self] at horder
    rcases horder with hzero | hgcd
    · exact (D.natDegree_ne_zero hzero).elim
    · exact hgcd
  rw [← ZMod.natCast_zmod_val D.fractionGaloisFrobeniusCoordinate,
    ZMod.isUnit_iff_coprime, Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
  exact hgcd

/-- Unit packaging of arithmetic Frobenius's coordinate relative to the internal cyclic
generator. -/
noncomputable def fractionGaloisFrobeniusCoordinateUnit
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    (ZMod D.polynomial.natDegree)ˣ :=
  D.fractionGaloisFrobeniusCoordinate_isUnit.unit

@[simp] theorem coe_fractionGaloisFrobeniusCoordinateUnit
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    (D.fractionGaloisFrobeniusCoordinateUnit : ZMod D.polynomial.natDegree) =
      D.fractionGaloisFrobeniusCoordinate :=
  D.fractionGaloisFrobeniusCoordinate_isUnit.unit_spec

/-- Frobenius/Hasse-normalized finite local invariant. The existing valuation invariant uses
the internally selected cyclic generator; multiplication by the coordinate of arithmetic
Frobenius changes evaluation from that generator to Frobenius, exactly as in the canonical
definition `χ ↦ χ(Frob)`. -/
noncomputable def cyclicGaloisH2FrobeniusInvariant
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
    letI : IsDiscreteValuationRing B :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K D.polynomial D.monic
        D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
    letI : FaithfulSMul 𝒪[K] B := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] B).mpr ?_
      change Function.Injective <| AdjoinRoot.of D.polynomial
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible)
    letI : FaithfulSMul 𝒪[K] U := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
      change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
      exact (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
    letI : FiniteDimensional (FractionRing 𝒪[K]) U :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
        D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    cyclicGaloisH2 (FractionRing 𝒪[K]) U ≃+ ZMod D.polynomial.natDegree :=
  (nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2Invariant K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible).trans
    (zmodUnitMulAddEquiv D.fractionGaloisFrobeniusCoordinateUnit)

/-- Exact comparison: canonical Frobenius evaluation is the old selected-generator coordinate
multiplied by the unique finite orientation unit taking that generator to arithmetic Frobenius. -/
@[simp] theorem cyclicGaloisH2FrobeniusInvariant_apply
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
    letI : IsDiscreteValuationRing B :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K D.polynomial D.monic
        D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
    letI : FaithfulSMul 𝒪[K] B := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] B).mpr ?_
      change Function.Injective <| AdjoinRoot.of D.polynomial
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible)
    letI : FaithfulSMul 𝒪[K] U := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
      change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
      exact (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
    letI : FiniteDimensional (FractionRing 𝒪[K]) U :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
        D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    ∀ x : cyclicGaloisH2 (FractionRing 𝒪[K]) U,
      D.cyclicGaloisH2FrobeniusInvariant x =
        D.fractionGaloisFrobeniusCoordinate *
          nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2Invariant K
            D.polynomial D.monic D.residuePolynomial D.residueMonic
            D.reduction_eq D.residueIrreducible x := by
  dsimp only
  intro x
  simp [cyclicGaloisH2FrobeniusInvariant]

/-- The old selected-generator invariant is literally the canonical Frobenius invariant exactly
when the Frobenius orientation correction is one. This is the precise equality criterion that
the choice-based full local invariant had not established. -/
theorem cyclicGaloisH2FrobeniusInvariant_eq_selected_iff
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
    letI : IsDiscreteValuationRing B :=
      nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K D.polynomial D.monic
        D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
    letI : FaithfulSMul 𝒪[K] B := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] B).mpr ?_
      change Function.Injective <| AdjoinRoot.of D.polynomial
      exact AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible)
    letI : FaithfulSMul 𝒪[K] U := by
      refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
      change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
      exact (IsFractionRing.injective B U).comp
        (AdjoinRoot.of.injective_of_degree_ne_zero
          (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
            D.residuePolynomial D.reduction_eq D.residueIrreducible))
    letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
    letI : FiniteDimensional (FractionRing 𝒪[K]) U :=
      nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
        D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
    D.cyclicGaloisH2FrobeniusInvariant =
        nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2Invariant K
          D.polynomial D.monic D.residuePolynomial D.residueMonic
          D.reduction_eq D.residueIrreducible ↔
      D.fractionGaloisFrobeniusCoordinate = 1 := by
  dsimp only
  let old :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicGaloisH2Invariant K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  constructor
  · intro h
    have hx := DFunLike.congr_fun h (old.symm 1)
    rw [D.cyclicGaloisH2FrobeniusInvariant_apply, old.apply_symm_apply, mul_one] at hx
    exact hx
  · intro h
    apply AddEquiv.ext
    intro x
    rw [D.cyclicGaloisH2FrobeniusInvariant_apply, h, one_mul]

/-- The existing selected-generator coordinate on the finite cyclic relative Brauer subgroup. This
wrapper exposes a stable type independent of the local instances used to construct the subgroup
equivalence. -/
noncomputable def cyclicBrauerSelectedInvariant
    (D : NonarchimedeanFiniteUnramifiedRootLift K) := by
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
  letI : IsDiscreteValuationRing B :=
    nonarchimedeanLocalFieldAdjoinRoot_isDiscreteValuationRing K D.polynomial D.monic
      D.residuePolynomial D.residueMonic D.reduction_eq D.residueIrreducible
  letI : FaithfulSMul 𝒪[K] B := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] B).mpr ?_
    change Function.Injective <| AdjoinRoot.of D.polynomial
    exact AdjoinRoot.of.injective_of_degree_ne_zero
      (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
        D.residuePolynomial D.reduction_eq D.residueIrreducible)
  letI : FaithfulSMul 𝒪[K] U := by
    refine (faithfulSMul_iff_algebraMap_injective 𝒪[K] U).mpr ?_
    change Function.Injective <| (algebraMap B U).comp (AdjoinRoot.of D.polynomial)
    exact (IsFractionRing.injective B U).comp
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (nonarchimedeanLocalFieldAdjoinRoot_degree_ne_zero K D.polynomial D.monic
          D.residuePolynomial D.reduction_eq D.residueIrreducible))
  letI : Algebra (FractionRing 𝒪[K]) U := FractionRing.liftAlgebra 𝒪[K] U
  letI : FiniteDimensional (FractionRing 𝒪[K]) U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_finiteDimensional K
      D.polynomial D.monic D.residuePolynomial D.reduction_eq D.residueIrreducible
  letI : IsGalois (FractionRing 𝒪[K]) U :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_isGaloisOverFractionRing K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  letI : IsCyclic Gal(U / FractionRing 𝒪[K]) :=
    nonarchimedeanLocalFieldAdjoinRootFractionField_gal_isCyclic K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible
  exact
    (nonarchimedeanLocalFieldAdjoinRootFractionField_cyclicBrauerInvariant K
      D.polynomial D.monic D.residuePolynomial D.residueMonic
      D.reduction_eq D.residueIrreducible).symm

/-- Frobenius/Hasse-normalized coordinate on the actual finite cyclic relative Brauer subgroup. -/
noncomputable def cyclicBrauerFrobeniusInvariant
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :=
  D.cyclicBrauerSelectedInvariant.trans
    (zmodUnitMulAddEquiv D.fractionGaloisFrobeniusCoordinateUnit)

/-- On actual finite Brauer classes, canonical Frobenius normalization is multiplication of the
selected coordinate by the arithmetic-Frobenius orientation unit. -/
@[simp] theorem cyclicBrauerFrobeniusInvariant_apply
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    ∀ x, D.cyclicBrauerFrobeniusInvariant x =
      D.fractionGaloisFrobeniusCoordinate * D.cyclicBrauerSelectedInvariant x := by
  intro x
  simp [cyclicBrauerFrobeniusInvariant]

/-- The current finite cyclic Brauer coordinate equals canonical Frobenius/Hasse normalization
exactly when its orientation unit is one. -/
theorem cyclicBrauerFrobeniusInvariant_eq_selected_iff
    (D : NonarchimedeanFiniteUnramifiedRootLift K) :
    D.cyclicBrauerFrobeniusInvariant = D.cyclicBrauerSelectedInvariant ↔
      D.fractionGaloisFrobeniusCoordinate = 1 := by
  constructor
  · intro h
    have hx := DFunLike.congr_fun h (D.cyclicBrauerSelectedInvariant.symm 1)
    rw [D.cyclicBrauerFrobeniusInvariant_apply,
      D.cyclicBrauerSelectedInvariant.apply_symm_apply, mul_one] at hx
    exact hx
  · intro h
    apply AddEquiv.ext
    intro x
    rw [D.cyclicBrauerFrobeniusInvariant_apply, h, one_mul]

end NonarchimedeanFiniteUnramifiedRootLift

end

end GaloisForLFunctions.HTGeometry.ABHN
