import GaloisForLFunctions.HTGeometry.SplittingFieldBaseEquiv
import GaloisForLFunctions.HTGeometry.AlgebraicPrimitiveDescent

/-!
# Normal-closure automorphism cardinality under field equivalence

Compatible equivalences of base fields and finite separable source extensions transport primitive
generators and their minimal polynomials.  Splitting-field uniqueness then identifies the two
normal-closure automorphism groups, even though their base and ambient field types differ.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

/-- A compatible equivalence of base and extension fields transports a primitive generator. -/
theorem adjoin_singleton_eq_top_of_ringEquiv
    {F A S T : Type*} [Field F] [Field A] [Field S] [Field T]
    [Algebra F S] [Algebra A T]
    (eF : F ≃+* A) (eS : S ≃+* T)
    (hcomp : (algebraMap A T).comp eF.toRingHom =
      eS.toRingHom.comp (algebraMap F S))
    {alpha : S} (halpha : IntermediateField.adjoin F {alpha} = ⊤) :
    IntermediateField.adjoin A {eS alpha} = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := eS.surjective y
  have hx : x ∈ IntermediateField.adjoin F {alpha} := by
    rw [halpha]
    trivial
  let p : ∀ z, z ∈ IntermediateField.adjoin F {alpha} → Prop :=
    fun z _ => eS z ∈ IntermediateField.adjoin A {eS alpha}
  change p x hx
  refine IntermediateField.adjoin_induction F (p := p) ?_ ?_ ?_ ?_ ?_ hx
  · intro z hz
    change eS z ∈ IntermediateField.adjoin A {eS alpha}
    have hz' : z = alpha := Set.mem_singleton_iff.mp hz
    subst z
    apply IntermediateField.subset_adjoin A
    exact Set.mem_singleton _
  · intro c
    change eS (algebraMap F S c) ∈ IntermediateField.adjoin A {eS alpha}
    have hc := DFunLike.congr_fun hcomp c
    rw [RingHom.comp_apply, RingHom.comp_apply] at hc
    have hc' : eS (algebraMap F S c) = algebraMap A T (eF c) := by
      simpa using hc.symm
    rw [hc']
    exact IntermediateField.algebraMap_mem _ (eF c)
  · intro x y hx hy hx' hy'
    change eS (x + y) ∈ IntermediateField.adjoin A {eS alpha}
    rw [map_add]
    exact (IntermediateField.adjoin A {eS alpha}).add_mem hx' hy'
  · intro x hx hx'
    change eS x⁻¹ ∈ IntermediateField.adjoin A {eS alpha}
    rw [map_inv₀]
    exact (IntermediateField.adjoin A {eS alpha}).inv_mem hx'
  · intro x y hx hy hx' hy'
    change eS (x * y) ∈ IntermediateField.adjoin A {eS alpha}
    rw [map_mul]
    exact (IntermediateField.adjoin A {eS alpha}).mul_mem hx' hy'

/-- Conjugation by an algebra equivalence identifies the two automorphism groups. -/
noncomputable def autMulEquivOfAlgEquiv
    {A L M : Type*} [Field A] [Field L] [Field M]
    [Algebra A L] [Algebra A M] (e : L ≃ₐ[A] M) :
    (L ≃ₐ[A] L) ≃* (M ≃ₐ[A] M) where
  toFun sigma := e.symm.trans (sigma.trans e)
  invFun tau := e.trans (tau.trans e.symm)
  left_inv sigma := by ext x; simp
  right_inv tau := by ext x; simp
  map_mul' sigma tau := by ext x; simp

/-- Compatible equivalences of finite separable source extensions preserve the cardinality of
their normal-closure automorphism groups. -/
theorem natCard_aut_normalClosure_eq_of_ringEquiv
    {F A S T L M : Type*}
    [Field F] [Field A] [Field S] [Field T] [Field L] [Field M]
    [Algebra F S] [Algebra F L] [Algebra A T] [Algebra A M]
    [FiniteDimensional F S] [FiniteDimensional A T]
    [Algebra.IsSeparable F S]
    [Algebra.IsAlgebraic F L] [Algebra.IsAlgebraic A M]
    [IsNormalClosure F S L] [IsNormalClosure A T M]
    (eF : F ≃+* A) (eS : S ≃+* T)
    (hcomp : (algebraMap A T).comp eF.toRingHom =
      eS.toRingHom.comp (algebraMap F S)) :
    Nat.card (L ≃ₐ[F] L) = Nat.card (M ≃ₐ[A] M) := by
  obtain ⟨alpha, halpha⟩ := Field.exists_primitive_element F S
  let beta : T := eS alpha
  have hbeta : IntermediateField.adjoin A {beta} = ⊤ :=
    adjoin_singleton_eq_top_of_ringEquiv eF eS hcomp halpha
  have halphaInt : IsIntegral F alpha := Algebra.IsIntegral.isIntegral alpha
  have hbetaInt : IsIntegral A beta := Algebra.IsIntegral.isIntegral beta
  let p : Polynomial F := minpoly F alpha
  let q : Polynomial A := minpoly A beta
  have hpq : p.map eF.toRingHom = q := by
    exact GaloisForLFunctions.minpoly_map_eq_of_ringEquiv_of_isIntegral
      hcomp halphaInt
  letI : Polynomial.IsSplittingField F L p :=
    isSplittingField_minpoly_of_isNormalClosure_of_adjoin_singleton_eq_top
      alpha halphaInt halpha
  letI : Polynomial.IsSplittingField A M q :=
    isSplittingField_minpoly_of_isNormalClosure_of_adjoin_singleton_eq_top
      beta hbetaInt hbeta
  letI : Algebra A L :=
    ((algebraMap F L).comp eF.symm.toRingHom).toAlgebra
  have hAlgForward : algebraMap F L =
      (algebraMap A L).comp eF.toRingHom := by
    ext x
    change algebraMap F L x = algebraMap F L (eF.symm (eF x))
    rw [eF.symm_apply_apply]
  have hAlgBackward : algebraMap A L =
      (algebraMap F L).comp eF.symm.toRingHom := rfl
  have hback : q.map eF.symm.toRingHom = p := by
    rw [← hpq, Polynomial.map_map]
    simp
  letI : Polynomial.IsSplittingField F L (q.map eF.symm.toRingHom) := by
    rw [hback]
    infer_instance
  letI : Polynomial.IsSplittingField A L q :=
    isSplittingField_map_algEquiv_of_algebraMap_eq
      eF.symm hAlgBackward q
  let u : L ≃ₐ[A] M :=
    (Polynomial.IsSplittingField.algEquiv L q).trans
      (Polynomial.IsSplittingField.algEquiv M q).symm
  calc
    Nat.card (L ≃ₐ[F] L) = Nat.card (L ≃ₐ[A] L) :=
      Nat.card_congr (autEquivOfBaseEquiv eF hAlgForward).toEquiv
    _ = Nat.card (M ≃ₐ[A] M) :=
      Nat.card_congr (autMulEquivOfAlgEquiv u).toEquiv

end

end GaloisForLFunctions.HTGeometry
