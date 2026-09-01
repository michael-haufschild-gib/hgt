import GaloisForLFunctions.HTGeometry.DifferentialScalarExtensionSpecialization
import GaloisForLFunctions.HTGeometry.DifferentialChevalleyFinite
import GaloisForLFunctions.HTGeometry.DifferentialPrincipalIdeal
import GaloisForLFunctions.HTGeometry.SigmaStableIdealFixedGeneration

/-!
# No new difference constants over a difference-field extension

This is the domain case of Hardouin--Singer Proposition 6.14.  A differentially finitely
generated `σ`-`δ`-simple domain over a difference field acquires no new `σ`-constants when the
fixed field is differentially closed.  Marked scalar specialization and differential Chevalley
extension discharge the fact that finite differential generation is over the larger difference
field rather than directly over its constants.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions
open scoped Differential

noncomputable section

attribute [local instance] differentialPolynomialOverDifferential

universe u

variable {C K R : Type u}
  [Field C] [Algebra ℚ C] [Differential C] [IsDifferentiallyClosed C]
  [Field K] [CharZero K] [Algebra C K] [Differential K] [DifferentialAlgebra C K]
  [CommRing R] [IsDomain R] [Algebra K R] [Differential R] [DifferentialAlgebra K R]
  [Algebra C R] [IsScalarTower C K R]

omit [CharZero K] [IsDomain R] [DifferentialAlgebra K R] in
/-- Finite differential generation survives enlargement of the coefficient ring inside the
target. -/
theorem differentialPolynomialEvalOver_coeffExtension_surjective
    {A : Type u} [CommRing A] [Algebra K A] [Differential A]
    [DifferentialAlgebra K A] [Algebra A R] [IsScalarTower K A R]
    [DifferentialAlgebra A R]
    {k : ℕ} (y : Fin k → R)
    (hy : Function.Surjective
      (differentialPolynomialEvalOver (K := K) (L := R) y)) :
    Function.Surjective
      (differentialPolynomialEvalOver (K := A) (L := R) y) := by
  intro r
  obtain ⟨Q, hQ⟩ := hy r
  refine ⟨MvPolynomial.map (algebraMap K A) Q, ?_⟩
  change differentialPolynomialEvalOver (K := A) y
      (differentialCoeffExtend (F := K) (L := A) Q) = r
  rw [differentialPolynomialEvalOver_differentialCoeffExtend]
  exact hQ

/-- **Hardouin--Singer no-new-constants theorem, domain case.**  A fixed element of a
differentially finitely generated `σ`-`δ`-simple domain over `K` already belongs to the
differentially closed fixed field `C`. -/
theorem exists_eq_algebraMap_of_isSigmaDeltaSimple_of_diffFG_fieldExtension
    (σK : K ≃+* K) (σR : R ≃+* R)
    (hσδ : CommutesDeriv σR)
    (hcompat : ∀ a : K,
      σR (algebraMap K R a) = algebraMap K R (σK a))
    (hσC : ∀ c : C, σK (algebraMap C K c) = algebraMap C K c)
    (hfix : ∀ a : K, σK a = a → ∃ c : C, algebraMap C K c = a)
    (hsimple : IsSigmaDeltaSimple σR)
    {k : ℕ} (y : Fin k → R)
    (hy : Function.Surjective
      (differentialPolynomialEvalOver (K := K) (L := R) y))
    {x : R} (hx : σR x = x) :
    ∃ c : C, x = algebraMap C R c := by
  classical
  let xFamily : Fin 1 → R := fun _ => x
  let A := differentialGeneratorSubalgebra (A := K) xFamily
  let xA : Fin 1 → A := fun i => differentialGeneratorIn (A := K) xFamily i
  letI : Algebra ℚ A := ((algebraMap K A).comp (algebraMap ℚ K)).toAlgebra
  letI : CharZero A := ⟨fun m n hmn => by
    apply CharZero.cast_injective (R := K)
    apply (algebraMap K A).injective
    simpa using hmn⟩
  letI : DifferentialAlgebra A R := ⟨fun a => by
    exact (differentialGeneratorSubalgebra_deriv_coe xFamily a).symm⟩
  have hyA : Function.Surjective
      (differentialPolynomialEvalOver (K := A) (L := R) y) :=
    differentialPolynomialEvalOver_coeffExtension_surjective y hy
  have hAR : Function.Injective (algebraMap A R) := by
    intro a b hab
    exact Subtype.ext hab
  obtain ⟨g, hg, hguard⟩ :=
    exists_differentialChevalley_extension_fin
      (A := A) (B := R) (K := K) k y hyA hAR
  have hxAsurj : Function.Surjective
      (differentialPolynomialEvalOver (K := K) xA) :=
    differentialPolynomialEvalOver_generatorIn_surjective xFamily
  obtain ⟨H, hHg⟩ := hxAsurj g
  have hHambient :
      differentialPolynomialEvalOver (K := K) xFamily H = (g : R) :=
    (differentialPolynomialEvalOver_generatorIn_coe xFamily H).symm.trans
      (congrArg Subtype.val hHg)
  let J : Ideal (DifferentialPolynomial (Fin 1) K) :=
    differentialRelationIdealOver (K := K) xFamily
  have hHnotJ : H ∉ J := by
    intro hHJ
    apply hg
    apply Subtype.ext
    have hzero : differentialPolynomialEvalOver (K := K) xFamily H = 0 := by
      simpa [J] using hHJ
    exact hHambient.symm.trans hzero
  let φ : DifferentialPolynomial (Fin 1) C →+*
      DifferentialPolynomial (Fin 1) K :=
    differentialCoeffExtend (F := C) (L := K)
  let I : Ideal (DifferentialPolynomial (Fin 1) C) := Ideal.comap φ J
  have hJI : Ideal.map φ I = J := by
    simpa [φ, I, J, xFamily] using
      (differentialRelationIdealOver_eq_map_fixedDescent
        (C := C) σK σR hcompat hσδ hfix xFamily (fun _ => hx))
  have hJprime : J.IsPrime := by
    simpa [J, differentialRelationIdealOver] using
      (RingHom.ker_isPrime
        (differentialPolynomialEvalOver (K := K) xFamily).toRingHom)
  have hIprime : I.IsPrime := by
    exact hJprime.comap φ
  have hIderiv : ∀ P ∈ I, Differential.deriv P ∈ I := by
    intro P hPI
    change φ (Differential.deriv P) ∈ J
    change φ (differentialPolynomialOverDerivation (Fin 1) C P) ∈ J
    rw [show φ (differentialPolynomialOverDerivation (Fin 1) C P) =
        differentialPolynomialOverDerivation (Fin 1) K (φ P) by
      exact differentialCoeffExtend_deriv
        (fun c => DifferentialAlgebra.deriv_algebraMap c) P]
    exact differentialPolynomialOverDerivation_mem_relationIdeal xFamily hPI
  have hHnotMap : H ∉ Ideal.map φ I := by
    rw [hJI]
    exact hHnotJ
  obtain ⟨c, hcI, hcH⟩ :=
    exists_point_avoiding_scalarExtended_primeDifferentialIdeal
      I hIprime hIderiv H hHnotMap
  let cK : Fin 1 → K := fun i => algebraMap C K (c i)
  let ψ : DifferentialPolynomial (Fin 1) K →+* K :=
    (differentialPolynomialEvalOver (K := K) cK).toRingHom
  have hψδ : ∀ Q, ψ (differentialPolynomialOverDerivation (Fin 1) K Q) =
      Differential.deriv (ψ Q) := by
    intro Q
    exact differentialPolynomialEvalOver_derivation cK Q
  have hevalExtend (Q : DifferentialPolynomial (Fin 1) C) :
      ψ (φ Q) = algebraMap C K
        (differentialPolynomialEvalOver (K := C) c Q) := by
    change differentialPolynomialEvalOver (K := K) cK
        (differentialCoeffExtend (F := C) (L := K) Q) = _
    rw [differentialPolynomialEvalOver_differentialCoeffExtend]
    symm
    exact map_differentialPolynomialEvalOver
      (algebraMap C K) (fun z => (DifferentialAlgebra.deriv_algebraMap z).symm)
      (fun _ => rfl) c Q
  have hmapkill : Ideal.map φ I ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQI
    change ψ (φ Q) = 0
    rw [hevalExtend, hcI Q hQI, map_zero]
  have hmapId (Q : DifferentialPolynomial (Fin 1) K) :
      MvPolynomial.map (RingHom.id K) Q = Q := by
    ext m
    rw [MvPolynomial.coeff_map]
    rfl
  have hrel : ∀ Q ∈ differentialRelationIdealOver (K := K) xA,
      ψ (MvPolynomial.map (RingHom.id K) Q) = 0 := by
    intro Q hQ
    have hQAzero : differentialPolynomialEvalOver (K := K) xA Q = 0 := by
      simpa using hQ
    have hQJ : Q ∈ J := by
      rw [show J = differentialRelationIdealOver (K := K) xFamily by rfl,
        mem_differentialRelationIdealOver_iff]
      rw [← differentialPolynomialEvalOver_generatorIn_coe xFamily Q]
      exact congrArg Subtype.val hQAzero
    have hQmap : Q ∈ Ideal.map φ I := by
      rw [hJI]
      exact hQJ
    rw [hmapId]
    exact hmapkill hQmap
  obtain ⟨κ, F, hκδ, hFδ, hbaseF, hFeval⟩ :=
    exists_differentialRingHom_of_surjective_eval
      (A := K) (B := A) (K := K) (L := K) (ι := Fin 1)
      xA hxAsurj (RingHom.id K) (fun _ => rfl) ψ hψδ hrel
  have hFg : F g ≠ 0 := by
    rw [← hHg, hFeval, hmapId]
    exact hcH
  obtain ⟨L, instLField, instLDifferential, κL, E,
      hκLδ, hEδ, hbaseE⟩ := hguard F hFδ hFg
  let xA0 : A := xA 0
  have hFxA0 : F xA0 = algebraMap C K (c 0) := by
    have h := hFeval (MvPolynomial.X (0, 0))
    simpa [xA0, xA, xFamily, ψ, cK] using h
  have hFcoeff (a : K) : F (algebraMap K A a) = a := by
    have h := hFeval (MvPolynomial.C a)
    simpa [ψ] using h
  let pA : A := xA0 - algebraMap K A (algebraMap C K (c 0))
  have hFpA : F pA = 0 := by
    rw [map_sub, hFxA0, hFcoeff, sub_self]
  let p : R := x - algebraMap C R (c 0)
  have hp_eq : p = algebraMap A R pA := by
    simp [p, pA, xA0, xA, xFamily, IsScalarTower.algebraMap_apply C K R]
  have hEp : E p = 0 := by
    rw [hp_eq, hbaseE, hFpA, map_zero]
  have hpσ : σR p = p := by
    have hcσ : σR (algebraMap C R (c 0)) = algebraMap C R (c 0) := by
      calc
        σR (algebraMap C R (c 0)) =
            σR (algebraMap K R (algebraMap C K (c 0))) := by
              rw [IsScalarTower.algebraMap_apply C K R]
        _ = algebraMap K R (σK (algebraMap C K (c 0))) := hcompat _
        _ = algebraMap K R (algebraMap C K (c 0)) := by rw [hσC]
        _ = algebraMap C R (c 0) :=
          (IsScalarTower.algebraMap_apply C K R (c 0)).symm
    simp [p, hx, hcσ]
  have hproper : derivationIterateIdeal p ≠ ⊤ :=
    derivationIterateIdeal_ne_top_of_ringHom E hEδ hEp
  have hsd : IsSigmaDeltaIdeal σR (derivationIterateIdeal p) :=
    isSigmaDeltaIdeal_derivationIterateIdeal_of_fixed hσδ hpσ
  have hbot : derivationIterateIdeal p = ⊥ :=
    (hsimple (derivationIterateIdeal p) hsd).resolve_right hproper
  have hpzero : p = 0 := by
    rw [← Ideal.mem_bot, ← hbot]
    exact iterate_deriv_mem_derivationIterateIdeal p 0
  exact ⟨c 0, sub_eq_zero.mp hpzero⟩

end

end GaloisForLFunctions.HTGeometry
