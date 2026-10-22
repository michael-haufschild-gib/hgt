import GaloisForLFunctions.HTGeometry.CriticalConstantExtensionCompatibility
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.ConstantFieldNormalClosureBaseChange
import GaloisForLFunctions.HTGeometry.NormalClosureEquivCardinality

/-!
# Critical normal closure under extension of algebraically closed constants

The critical normal-closure Galois group has constant cardinality under every extension between
algebraically closed characteristic-zero coefficient fields.  The proof transports the actual
normal closure, not an abstract substitute.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

variable {k K : Type*} [Field k] [IsAlgClosed k] [CharZero k]
  [Field K] [IsAlgClosed K] [CharZero K] [Algebra k K]

/-- Extension of algebraically closed characteristic-zero constants preserves the cardinality of
the actual critical normal-closure Galois group. -/
theorem natCard_criticalNormalClosureAut_eq_of_constantExtension
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalNormalClosure k m n ≃ₐ[criticalObservationField k m n]
        criticalNormalClosure k m n) =
      Nat.card (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n) := by
  let F := criticalObservationField k m n
  let S := criticalSourceField k m n
  let L := criticalNormalClosure k m n
  let A := criticalObservationField K m n
  let T := criticalSourceField K m n
  let M := criticalNormalClosure K m n
  let B := constantScalarBase k F K
  let S' := constantScalarExtension k F S K
  let L' := constantScalarExtension k F L K
  letI : FiniteDimensional F S :=
    criticalSourceField_finiteDimensional_criticalObservationField k hm hn
  letI : FiniteDimensional F L :=
    criticalNormalClosure_finiteDimensional k hm hn
  letI : IsGalois F L := by infer_instance
  letI : Algebra k L :=
    ((algebraMap F L).comp (algebraMap k F)).toAlgebra
  letI : IsScalarTower k F L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let i : S →ₐ[F] L := by
    let j : S →ₐ[F] criticalSourceAlgebraicClosure k m n :=
      { toRingHom := algebraMap S (criticalSourceAlgebraicClosure k m n)
        commutes' := fun _ => rfl }
    exact (normalClosure.algHomEquiv F S
      (criticalSourceAlgebraicClosure k m n)).symm j
  letI : IsNormalClosure B S' L' :=
    constantScalarExtension_isNormalClosure (k := k) (K := K) i
  letI : CharZero B :=
    charZero_of_injective_algebraMap (algebraMap k B).injective
  letI : Algebra.IsSeparable B S' := inferInstance
  letI : FiniteDimensional A T :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  have hbase : Nat.card (L ≃ₐ[F] L) = Nat.card (L' ≃ₐ[B] L') :=
    Nat.card_congr
      (constantGaloisBaseChangeEquiv
        (k := k) (F := F) (E := L) (K := K)).toEquiv
  have hnormal : Nat.card (L' ≃ₐ[B] L') = Nat.card (M ≃ₐ[A] M) :=
    natCard_aut_normalClosure_eq_of_ringEquiv
      (F := B) (A := A) (S := S') (T := T) (L := L') (M := M)
      (criticalObservationConstantBaseChange k K hm hn).toRingEquiv
      (criticalSourceConstantScalarExtensionRingEquiv
        (k := k) (K := K) hm hn)
      (criticalConstantScalarExtensionRingEquiv_compat
        (k := k) (K := K) hm hn)
  exact hbase.trans hnormal

end

end GaloisForLFunctions.HTGeometry
