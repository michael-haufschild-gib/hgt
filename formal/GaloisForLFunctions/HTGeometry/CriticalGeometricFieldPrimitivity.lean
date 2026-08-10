import GaloisForLFunctions.HTGeometry.CriticalGeometricDegreeExact
import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromyFaithful
import GaloisForLFunctions.HTGeometry.CriticalNormalClosureSchurValuation
import GaloisForLFunctions.HTGeometry.CoatomFixedField

/-!
# Actual critical source field as a maximal point-stabilizer field

The chosen source embedding into the actual normal closure identifies its field range with the
fixed field of the stabilizer of that geometric sheet.  Consequently, full actual geometric
monodromy makes this fixing subgroup maximal.  This is the literal field-primitivity bridge needed
by one-step postcritical rigidity; it uses neither an abstract cover nor occupation-state proxies.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

/-- The fixing subgroup of the actual embedded source field is exactly the inverse image of its
sheet stabilizer under the actual normal-closure permutation action. -/
theorem criticalSourceNormalClosureFieldRange_fixingSubgroup_eq_actionStabilizer
    (K : Type*) [Field K]
    (m n : ℕ) :
    (criticalSourceNormalClosureEmbedding K m n).fieldRange.fixingSubgroup =
      (MulAction.stabilizer
        (Equiv.Perm (criticalGeometricSheet K m n))
        (criticalSourceNormalClosureEmbedding K m n)).comap
          (criticalNormalClosureAction K m n) := by
  ext τ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hfix
    change criticalNormalClosureAction K m n τ
      (criticalSourceNormalClosureEmbedding K m n) =
        criticalSourceNormalClosureEmbedding K m n
    apply AlgHom.ext
    intro x
    exact hfix _ ⟨x, rfl⟩
  · intro hstab y hy
    obtain ⟨x, rfl⟩ := hy
    change criticalNormalClosureAction K m n τ
      (criticalSourceNormalClosureEmbedding K m n) =
        criticalSourceNormalClosureEmbedding K m n at hstab
    exact DFunLike.congr_fun hstab x

/-- Positive depths make the actual critical sheet set nontrivial. -/
theorem one_lt_natCard_criticalGeometricSheet
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    1 < Nat.card (criticalGeometricSheet K m n) := by
  rw [natCard_criticalGeometricSheet_eq_criticalHorizonMultiplicity K hm hn,
    criticalHorizonMultiplicity]
  have hpos : 0 < (m + n).choose m := Nat.choose_pos (by omega)
  have hne : (m + n).choose m ≠ 1 := by
    intro heq
    rcases Nat.choose_eq_one_iff.mp heq with hm0 | hmn
    · omega
    · omega
  omega

/-- **Actual critical field-primitivity from full monodromy.**  If actual geometric monodromy is
the full permutation group, the fixing subgroup of the actual embedded source field is maximal in
the actual normal-closure Galois group. -/
theorem criticalSourceNormalClosureFieldRange_fixingSubgroup_isCoatom_of_full_monodromy
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hfull : criticalGeometricMonodromy K m n = ⊤) :
    IsCoatom
      (criticalSourceNormalClosureEmbedding K m n).fieldRange.fixingSubgroup := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : Nontrivial (criticalGeometricSheet K m n) :=
    Finite.one_lt_card_iff_nontrivial.mp
      (one_lt_natCard_criticalGeometricSheet K hm hn)
  have hsurj : Function.Surjective (criticalNormalClosureAction K m n) := by
    intro σ
    have hmem : σ ∈ criticalGeometricMonodromy K m n := by rw [hfull]; trivial
    exact hmem
  rw [criticalSourceNormalClosureFieldRange_fixingSubgroup_eq_actionStabilizer]
  exact Subgroup.isCoatom_comap_of_surjective hsurj
    (isCoatom_stabilizer_perm (criticalSourceNormalClosureEmbedding K m n))

/-- **No intermediate fields below the actual critical source field.**  Full actual geometric
monodromy makes every intermediate field contained in the chosen embedded source field either the
observation field or the entire embedded source field. -/
theorem eq_bot_or_eq_criticalSourceNormalClosureFieldRange_of_full_monodromy
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hfull : criticalGeometricMonodromy K m n = ⊤)
    (M : IntermediateField (criticalObservationField K m n)
      (criticalNormalClosure K m n))
    (hM : M ≤ (criticalSourceNormalClosureEmbedding K m n).fieldRange) :
    M = ⊥ ∨ M = (criticalSourceNormalClosureEmbedding K m n).fieldRange := by
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    criticalNormalClosure_finiteDimensional K hm hn
  letI : FiniteDimensional (criticalObservationField K m n)
      (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  letI : Algebra.IsSeparable (criticalObservationField K m n)
      (criticalSourceField K m n) := inferInstance
  letI : IsScalarTower (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n) :=
    AlgebraicClosure.instIsScalarTower (criticalSourceField K m n)
  letI : Algebra.IsAlgebraic (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    Algebra.IsAlgebraic.trans (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  letI : Normal (criticalObservationField K m n)
      (criticalSourceAlgebraicClosure K m n) :=
    { splits' _ := IsAlgClosed.splits _ }
  letI : Normal (criticalObservationField K m n)
      (criticalNormalClosure K m n) :=
    normalClosure.normal (criticalObservationField K m n)
      (criticalSourceField K m n) (criticalSourceAlgebraicClosure K m n)
  letI : IsGalois (criticalObservationField K m n)
      (criticalNormalClosure K m n) := inferInstance
  exact eq_bot_or_eq_of_isCoatom_fixingSubgroup
    (criticalSourceNormalClosureFieldRange_fixingSubgroup_isCoatom_of_full_monodromy
      K hm hn hfull) hM

end

end GaloisForLFunctions.HTGeometry
