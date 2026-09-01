import GaloisForLFunctions.RHTower.DeningerQ8ActualQuadraticSourceHigherRamification
import AlgebraicNumberTheory.Completion.AdicCompletionComparison
import AlgebraicNumberTheory.Ramification.Splitting.FinitePlaceIdeal
import AlgebraicNumberTheory.RayClass.Rational

/-!
# Literal dyadic completion of the Q8 quadratic source

Every dyadic prime of `S = ℚ(√41)` has relative ramification index and
residue degree one over `ℚ`.  This leaf carries those arithmetic equalities
through the ideal stabilizer, absolute-value decomposition group, algebraic
localization, metric completion, and concrete adic-completion comparisons.
It proves that the canonical completion map at the literal rational prime
`2` is an algebra equivalence.  No abstract replacement field is chosen.
-/

namespace RHTower

noncomputable section

open scoped NumberField Pointwise ValuativeRel NNReal
open IsDedekindDomain AlgebraicNumberTheory.Valuations HilbertRamification

local notation "K1" => deningerQ8RootNumberNegOneFirstQuadraticField
local notation "K2" => deningerQ8RootNumberNegOneSecondQuadraticField
local notation "K3" => deningerQ8RootNumberNegOneTopField
local notation "S" => q8BiquadQuadraticSourceField

local instance : CharZero K2 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K2).injective
local instance : CharZero K3 :=
  charZero_of_injective_algebraMap (algebraMap ℚ K3).injective
noncomputable local instance : FiniteDimensional ℚ K1 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadUBasis
noncomputable local instance : FiniteDimensional K1 K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadVBasis
noncomputable local instance : FiniteDimensional ℚ K2 :=
  Module.Basis.finiteDimensional_of_finite q8BiquadIntegralBasis
noncomputable local instance : FiniteDimensional S K2 := by infer_instance
noncomputable local instance : NumberField S := NumberField.mk

noncomputable local instance : Algebra.IsQuadraticExtension ℚ S where
  finrank_eq_two' := q8BiquadQuadraticSourceField_finrank

noncomputable local instance : IsGalois ℚ S := by
  rw [isGalois_iff]
  constructor <;> infer_instance

noncomputable local instance q8BaseFieldAction :
    MulSemiringAction Gal(S/ℚ) S := inferInstance
noncomputable local instance q8BaseIsGaloisGroup :
    IsGaloisGroup Gal(S/ℚ) ℚ S := IsGaloisGroup.of_isGalois ℚ S
noncomputable local instance q8BaseIntegralAction :
    MulSemiringAction Gal(S/ℚ) (𝓞 S) := inferInstance

/-- A dyadic source prime has trivial ideal decomposition group over `ℚ`. -/
theorem q8QuadraticSource_dyadic_idealStabilizer_eq_bot
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    MulAction.stabilizer Gal(S/ℚ) v.asIdeal = ⊥ := by
  let p := v.asIdeal.under ℤ
  letI : v.asIdeal.LiesOver p := ⟨rfl⟩
  have hcard := Ideal.card_stabilizer_eq
    (G := Gal(S/ℚ)) p v.asIdeal
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p v.asIdeal Gal(S/ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg p v.asIdeal Gal(S/ℚ),
    q8QuadraticSource_dyadic_ramificationIdx_eq_one v hv,
    q8QuadraticSource_dyadic_inertiaDeg_eq_one v hv,
    one_mul] at hcard
  exact (MulAction.stabilizer Gal(S/ℚ) v.asIdeal).eq_bot_iff_card.mpr hcard

/-- The corresponding absolute-value decomposition group is trivial. -/
theorem q8QuadraticSource_dyadic_absoluteValueDecompositionGroup_eq_bot
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let q := finitePlaceBelow (K := ℚ) v
    let W : {W : HeightOneSpectrum (𝓞 S) //
        finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
    let a := (finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q).symm W
    absoluteValueDecompositionGroup ℚ a.1 = ⊥ := by
  dsimp only
  let q := finitePlaceBelow (K := ℚ) v
  let W : {W : HeightOneSpectrum (𝓞 S) //
      finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
  let a := (finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q).symm W
  have hcentre : finitePlaceExtensionCentre (K := ℚ) (L := S) q a = v := by
    have h := (finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q).apply_symm_apply W
    exact congrArg Subtype.val h
  letI := finitePlaceMulAction ℚ S
  rw [absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
    (K := ℚ) (L := S) q a]
  apply le_bot_iff.mp
  intro g hg
  rw [Subgroup.mem_bot]
  have hfix : finitePlaceEquiv ℚ S g v = v := by
    rw [MulAction.mem_stabilizer_iff] at hg
    rw [hcentre] at hg
    exact hg
  have hgIdeal : g ∈ MulAction.stabilizer Gal(S/ℚ) v.asIdeal := by
    rw [MulAction.mem_stabilizer_iff]
    have hideal := congrArg HeightOneSpectrum.asIdeal hfix
    rw [finitePlaceEquiv_asIdeal] at hideal
    convert hideal using 1
    ext x
    rfl
  have hbot := q8QuadraticSource_dyadic_idealStabilizer_eq_bot v hv
  rw [hbot, Subgroup.mem_bot] at hgIdeal
  exact hgIdeal

set_option maxHeartbeats 800000 in
/-- Trivial decomposition makes the exact metric completion degree one. -/
theorem q8QuadraticSource_dyadic_exactCompletion_finrank_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let q := finitePlaceBelow (K := ℚ) v
    let W : {W : HeightOneSpectrum (𝓞 S) //
        finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
    let a := (finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q).symm W
    let vQ := NumberField.HeightOneSpectrum.adicAbv ℚ q
    letI : Algebra vQ.Completion a.1.Completion :=
      AbsoluteValue.completionAlgebra vQ a.1 a.2
    Module.finrank vQ.Completion a.1.Completion = 1 := by
  dsimp only
  let q := finitePlaceBelow (K := ℚ) v
  let W : {W : HeightOneSpectrum (𝓞 S) //
      finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
  let a := (finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q).symm W
  let vQ := NumberField.HeightOneSpectrum.adicAbv ℚ q
  let hvQ : vQ.IsNontrivial := RayClass.adicAbv_isNontrivial q
  letI hQ := AbsoluteValue.extensionCompletionAlgebra (K := ℚ) a.1
  letI : SMul ℚ a.1.Completion := hQ.toSMul
  letI : Algebra vQ.Completion a.1.Completion :=
    AbsoluteValue.completionAlgebra vQ a.1 a.2
  let E := LocalizedCompletion vQ a
  letI : FiniteDimensional vQ.Completion E :=
    localizedCompletionModuleFinite vQ hvQ a
  letI : IsGalois vQ.Completion E :=
    HilbertRamification.algebraicLocalization_isGalois vQ a
  let e : E ≃ₐ[vQ.Completion] a.1.Completion :=
    localizedCompletionEquivCompletion vQ hvQ a
  have hloc : Module.finrank vQ.Completion E = 1 := by
    calc
      Module.finrank vQ.Completion E = Nat.card Gal(E/vQ.Completion) :=
        (IsGalois.card_aut_eq_finrank vQ.Completion E).symm
      _ = Nat.card (absoluteValueDecompositionGroup ℚ a.1) :=
        Nat.card_congr
          (decompositionGroupEquivAlgebraicLocalizationAut vQ hvQ a).symm.toEquiv
      _ = 1 := by
        rw [q8QuadraticSource_dyadic_absoluteValueDecompositionGroup_eq_bot v hv]
        exact Nat.card_unique
  rw [← LinearEquiv.finrank_eq e.toLinearEquiv]
  exact hloc

set_option maxHeartbeats 800000 in
/-- The concrete adic completion at the chosen centre also has degree one. -/
theorem q8QuadraticSource_dyadic_centreAdicCompletion_finrank_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let q := finitePlaceBelow (K := ℚ) v
    let W : {W : HeightOneSpectrum (𝓞 S) //
        finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
    let a := (finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q).symm W
    let Wa := finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q a
    letI : Algebra (q.adicCompletion ℚ) (Wa.1.adicCompletion S) :=
      (finitePlaceAdicCompletionMap ℚ S q Wa).toAlgebra
    Module.finrank (q.adicCompletion ℚ) (Wa.1.adicCompletion S) = 1 := by
  dsimp only
  let q := finitePlaceBelow (K := ℚ) v
  let W : {W : HeightOneSpectrum (𝓞 S) //
      finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
  let a := (finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q).symm W
  let Wa := finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q a
  letI : Algebra (q.adicCompletion ℚ) (Wa.1.adicCompletion S) :=
    (finitePlaceAdicCompletionMap ℚ S q Wa).toAlgebra
  let vQ := NumberField.HeightOneSpectrum.adicAbv ℚ q
  letI : Algebra (q.adicCompletion ℚ) vQ.Completion :=
    (relativeFinitePlaceCompletionAlgEquiv q).symm.toRingHom.toAlgebra
  letI : Algebra vQ.Completion a.1.Completion :=
    AbsoluteValue.completionAlgebra vQ a.1 a.2
  letI : Algebra (q.adicCompletion ℚ) a.1.Completion :=
    ((algebraMap vQ.Completion a.1.Completion).comp
      (relativeFinitePlaceCompletionAlgEquiv q).symm.toRingHom).toAlgebra
  let e : a.1.Completion ≃ₐ[q.adicCompletion ℚ] Wa.1.adicCompletion S :=
    { __ := finitePlaceExtensionAdicCompletionRingEquiv
        (K := ℚ) (L := S) q a
      commutes' := fun x => by
        change finitePlaceExtensionAdicCompletionMap ℚ S q a x =
          finitePlaceAdicCompletionMap ℚ S q Wa x
        exact finitePlaceExtensionAdicCompletionMap_eq_finitePlaceAdicCompletionMap
          ℚ S q a x }
  have hexact := q8QuadraticSource_dyadic_exactCompletion_finrank_eq_one v hv
  have hbase : Module.finrank vQ.Completion a.1.Completion =
      Module.finrank (q.adicCompletion ℚ) a.1.Completion := by
    apply Algebra.finrank_eq_of_equiv_equiv
      (relativeFinitePlaceCompletionAlgEquiv q).toRingEquiv
      (RingEquiv.refl a.1.Completion)
    ext x
    change algebraMap vQ.Completion a.1.Completion
        ((relativeFinitePlaceCompletionAlgEquiv q).symm
          ((relativeFinitePlaceCompletionAlgEquiv q) x)) =
      algebraMap vQ.Completion a.1.Completion x
    rw [AlgEquiv.symm_apply_apply]
  rw [← LinearEquiv.finrank_eq e.toLinearEquiv]
  rw [← hbase]
  exact hexact

set_option maxHeartbeats 800000 in
/-- The actual source adic completion has degree one over its prime below. -/
theorem q8QuadraticSource_dyadic_adicCompletion_finrank_eq_one
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let q := finitePlaceBelow (K := ℚ) v
    let W : {W : HeightOneSpectrum (𝓞 S) //
        finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
    letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion S) :=
      (finitePlaceAdicCompletionMap ℚ S q W).toAlgebra
    Module.finrank (q.adicCompletion ℚ) (v.adicCompletion S) = 1 := by
  dsimp only
  let q := finitePlaceBelow (K := ℚ) v
  let W : {W : HeightOneSpectrum (𝓞 S) //
      finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
  letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion S) :=
    (finitePlaceAdicCompletionMap ℚ S q W).toAlgebra
  let a := (finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q).symm W
  have hWa : finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q a = W :=
    (finitePlaceExtensionEquivAbove (K := ℚ) (L := S) q).apply_symm_apply W
  have h := q8QuadraticSource_dyadic_centreAdicCompletion_finrank_eq_one v hv
  dsimp only at h
  rw [hWa] at h
  exact h

/-- The canonical finite-place completion map is an algebra equivalence. -/
noncomputable def q8QuadraticSource_dyadic_adicCompletionAlgEquiv
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    let q := finitePlaceBelow (K := ℚ) v
    let W : {W : HeightOneSpectrum (𝓞 S) //
        finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
    letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion S) :=
      (finitePlaceAdicCompletionMap ℚ S q W).toAlgebra
    q.adicCompletion ℚ ≃ₐ[q.adicCompletion ℚ] v.adicCompletion S := by
  dsimp only
  let q := finitePlaceBelow (K := ℚ) v
  let W : {W : HeightOneSpectrum (𝓞 S) //
      finitePlaceBelow (K := ℚ) W = q} := ⟨v, rfl⟩
  letI : Algebra (q.adicCompletion ℚ) (v.adicCompletion S) :=
    (finitePlaceAdicCompletionMap ℚ S q W).toAlgebra
  letI : Module.Finite (q.adicCompletion ℚ) (v.adicCompletion S) :=
    finitePlaceAdicCompletionMap_moduleFinite ℚ S q W
  exact AlgEquiv.ofBijective
    (Algebra.ofId (q.adicCompletion ℚ) (v.adicCompletion S))
    ((Algebra.finrank_eq_one_iff_bijective_algebraMap).mp
      (q8QuadraticSource_dyadic_adicCompletion_finrank_eq_one v hv))

/-- The rational prime below every dyadic source prime is literally `(2)`. -/
theorem q8QuadraticSource_dyadic_below_eq_rationalPrime_two
    (v : HeightOneSpectrum (𝓞 S))
    (hv : (2 : 𝓞 S) ∈ v.asIdeal) :
    finitePlaceBelow (K := ℚ) v =
      RayClass.rationalPrime (⟨2, by norm_num⟩ : Nat.Primes) := by
  let q := finitePlaceBelow (K := ℚ) v
  apply RayClass.rational_natGenerator_injective
  rw [RayClass.natGenerator_rationalPrime]
  have hqmem : (2 : 𝓞 ℚ) ∈ q.asIdeal := by
    rw [finitePlaceBelow_asIdeal]
    change algebraMap (𝓞 ℚ) (𝓞 S) (2 : 𝓞 ℚ) ∈ v.asIdeal
    have hmap : algebraMap (𝓞 ℚ) (𝓞 S) (2 : 𝓞 ℚ) = (2 : 𝓞 S) := by
      exact map_ofNat (algebraMap (𝓞 ℚ) (𝓞 S)) 2
    rw [hmap]
    exact hv
  have hmapmem : (2 : ℤ) ∈
      Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) q.asIdeal := by
    have h := Ideal.mem_map_of_mem
      (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hqmem
    convert h using 1
    exact (map_ofNat (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) 2).symm
  rw [← Rat.HeightOneSpectrum.span_natGenerator q] at hmapmem
  have hdivInt : (Rat.HeightOneSpectrum.natGenerator q : ℤ) ∣ (2 : ℤ) :=
    Ideal.mem_span_singleton.mp hmapmem
  have hdiv : Rat.HeightOneSpectrum.natGenerator q ∣ 2 := by
    exact_mod_cast hdivInt
  have hle : Rat.HeightOneSpectrum.natGenerator q ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hdiv
  have htwo : 2 ≤ Rat.HeightOneSpectrum.natGenerator q :=
    (Rat.HeightOneSpectrum.prime_natGenerator q).two_le
  exact Nat.le_antisymm hle htwo

end

end RHTower
