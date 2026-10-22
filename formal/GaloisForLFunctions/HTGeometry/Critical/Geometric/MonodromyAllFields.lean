import GaloisForLFunctions.HTGeometry.Critical.Normal.ClosureConstantExtension
import GaloisForLFunctions.HTGeometry.Critical.Geometric.NormalClosureTower
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyFull
import GaloisForLFunctions.HTGeometry.Critical.Geometric.MonodromyFaithful
import GaloisForLFunctions.HTGeometry.Critical.Geometric.DegreeExact
import GaloisForLFunctions.HTGeometry.RankOneCriticalMonodromy
import GaloisForLFunctions.HTGeometry.CoRankOneCriticalMonodromy

/-!
# Full critical geometric monodromy over all algebraically closed characteristic-zero fields

Normal-closure automorphism cardinality is transported from algebraic constants to an arbitrary
coefficient field, then compared with the already-proved complex monodromy.  Faithfulness and the
field-independent sheet count force the actual monodromy subgroup to be the full symmetric group.
Rank-one results complete every positive pair of horizon depths.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000

/-- Faithfulness identifies the critical normal-closure Galois group with its concrete monodromy
image. -/
theorem natCard_criticalGeometricMonodromy_eq_aut
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalGeometricMonodromy K m n) =
      Nat.card (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n) := by
  exact Nat.card_congr
    (Equiv.ofInjective (criticalNormalClosureAction K m n)
      (criticalNormalClosureAction_injective K hm hn)).symm

/-- The critical normal-closure Galois group over any algebraically closed characteristic-zero
field has the same cardinality as the one over `ℂ`. -/
theorem natCard_criticalNormalClosureAut_eq_complex
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
        criticalNormalClosure K m n) =
      Nat.card (criticalNormalClosure ℂ m n ≃ₐ[criticalObservationField ℂ m n]
        criticalNormalClosure ℂ m n) := by
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  let iK : AlgebraicClosure ℚ →ₐ[ℚ] K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) K := iK.toRingHom.toAlgebra
  have hK := natCard_criticalNormalClosureAut_eq_of_constantExtension
    (k := AlgebraicClosure ℚ) (K := K) hm hn
  let iC : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) ℂ := iC.toRingHom.toAlgebra
  have hC := natCard_criticalNormalClosureAut_eq_of_constantExtension
    (k := AlgebraicClosure ℚ) (K := ℂ) hm hn
  exact hK.symm.trans hC

/-- The full permutation groups on critical sheets have field-independent cardinality. -/
theorem natCard_perm_criticalGeometricSheet_eq_complex
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    Nat.card (Equiv.Perm (criticalGeometricSheet K m n)) =
      Nat.card (Equiv.Perm (criticalGeometricSheet ℂ m n)) := by
  letI : Finite (criticalGeometricSheet K m n) :=
    finite_criticalGeometricSheet K hm hn
  letI : Finite (criticalGeometricSheet ℂ m n) :=
    finite_criticalGeometricSheet ℂ hm hn
  rw [Nat.card_perm, Nat.card_perm,
    natCard_criticalGeometricSheet_eq_criticalHorizonMultiplicity K hm hn,
    natCard_criticalGeometricSheet_eq_criticalHorizonMultiplicity ℂ hm hn]

/-- Every algebraically closed characteristic-zero realization has monodromy of the same order as
its full symmetric group. -/
theorem natCard_criticalGeometricMonodromy_eq_perm
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    Nat.card (criticalGeometricMonodromy K m n) =
      Nat.card (Equiv.Perm (criticalGeometricSheet K m n)) := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  letI : Fact (0 < m) := ⟨hm0⟩
  letI : Fact (0 < n) := ⟨hn0⟩
  letI : Fact (1 < m) := ⟨hm⟩
  letI : Fact (1 < n) := ⟨hn⟩
  have hcomplex :
      Nat.card (criticalGeometricMonodromy ℂ m n) =
        Nat.card (Equiv.Perm (criticalGeometricSheet ℂ m n)) := by
    rw [criticalGeometricMonodromy_eq_top]
    exact Nat.card_congr (Equiv.Set.univ _)
  calc
    Nat.card (criticalGeometricMonodromy K m n) =
        Nat.card (criticalNormalClosure K m n ≃ₐ[criticalObservationField K m n]
          criticalNormalClosure K m n) :=
      natCard_criticalGeometricMonodromy_eq_aut K hm0 hn0
    _ = Nat.card (criticalNormalClosure ℂ m n ≃ₐ[criticalObservationField ℂ m n]
          criticalNormalClosure ℂ m n) :=
      natCard_criticalNormalClosureAut_eq_complex K hm0 hn0
    _ = Nat.card (criticalGeometricMonodromy ℂ m n) :=
      (natCard_criticalGeometricMonodromy_eq_aut ℂ hm0 hn0).symm
    _ = Nat.card (Equiv.Perm (criticalGeometricSheet ℂ m n)) := hcomplex
    _ = Nat.card (Equiv.Perm (criticalGeometricSheet K m n)) :=
      (natCard_perm_criticalGeometricSheet_eq_complex K hm0 hn0).symm

/-- Full symmetric critical geometric monodromy over every algebraically closed
characteristic-zero field in the genuinely two-sided range. -/
theorem criticalGeometricMonodromy_eq_top_allFields
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n) :
    criticalGeometricMonodromy K m n = ⊤ := by
  let hm0 : 0 < m := by omega
  let hn0 : 0 < n := by omega
  letI : Finite (criticalGeometricSheet K m n) :=
    finite_criticalGeometricSheet K hm0 hn0
  letI : Fintype (Equiv.Perm (criticalGeometricSheet K m n)) :=
    Fintype.ofFinite _
  letI : Fintype (criticalGeometricMonodromy K m n) :=
    Fintype.ofFinite _
  let inclusion : criticalGeometricMonodromy K m n →
      Equiv.Perm (criticalGeometricSheet K m n) := fun g => g
  have hcard : Fintype.card (criticalGeometricMonodromy K m n) =
      Fintype.card (Equiv.Perm (criticalGeometricSheet K m n)) := by
    simpa only [Fintype.card_eq_nat_card] using
      natCard_criticalGeometricMonodromy_eq_perm K hm hn
  have hsurj : Function.Surjective inclusion :=
    ((Fintype.bijective_iff_injective_and_card inclusion).2
      ⟨Subtype.val_injective, hcard⟩).2
  apply top_unique
  intro g _
  obtain ⟨h, rfl⟩ := hsurj g
  exact h.property

/-- Every positive critical projective horizon over an algebraically closed characteristic-zero
field has full symmetric geometric monodromy. -/
theorem criticalGeometricMonodromy_eq_top_charZero
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    criticalGeometricMonodromy K m n = ⊤ := by
  by_cases hm1 : m = 1
  · subst m
    exact criticalGeometricMonodromy_one_left_eq_top (K := K) hn
  by_cases hn1 : n = 1
  · subst n
    exact criticalGeometricMonodromy_one_right_eq_top (K := K) hm
  exact criticalGeometricMonodromy_eq_top_allFields K (by omega) (by omega)

end

end GaloisForLFunctions.HTGeometry
