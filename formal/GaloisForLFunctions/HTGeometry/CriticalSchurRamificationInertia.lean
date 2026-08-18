import GaloisForLFunctions.HTGeometry.CriticalSchurIdealInertiaTransport
import GaloisForLFunctions.HTGeometry.CriticalGeometricMonodromyJordan

/-!
# Ramification at the Schur place, and the packaged endgame criterion

The tree already proves that the cardinality of ideal-theoretic Schur inertia is the ramification
index (`natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn`) and that ideal inertia embeds
in valuation-theoretic inertia (`criticalSchurIdealInertiaToInertia_injective`).  Chaining them
turns the analytic statement "the Schur place ramifies" into the group-theoretic hypothesis the
transposition criterion consumes:

```text
nontrivial_criticalSchurInertiaGroup_of_ramificationIdx :
    2 ≤ ramificationIdxIn ...  →  Nontrivial (criticalSchurInertiaGroup K hm hn)
exists_criticalGeometricMonodromy_isSwap_of_ramification_of_degree
criticalGeometricMonodromy_eq_top_of_ramification_of_degree_of_isPreprimitive
    ** ramification + the reduction-degree count + primitivity  ⟹  criticalGeometricMonodromy = ⊤ **
```

The last statement is exactly `(4)` of the projective-horizon card, reduced to three named geometric
inputs.  Transitivity is already unconditional, and `SCE_k` — the hard input to primitivity — is
`AffineSpaceEtaleRankOne.rank_eq_one_of_isUnit_discr_mvPolynomial`.
-/

namespace GaloisForLFunctions.HTGeometry

set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1600000

noncomputable local instance sheetDecEqEndgame (K : Type*) [Field K] (m n : ℕ) :
    DecidableEq (criticalGeometricSheet K m n) := Classical.decEq _

/-- A group receiving an injective homomorphism from a nontrivial group is nontrivial. -/
theorem nontrivial_of_injective_monoidHom {G H : Type*} [Group G] [Group H] [Nontrivial G]
    (f : G →* H) (hf : Function.Injective f) : Nontrivial H := by
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  refine ⟨⟨f g, 1, ?_⟩⟩
  intro hcon
  apply hg
  apply hf
  rw [hcon, map_one]

/-- **Ramification at the Schur place makes the actual Schur inertia group nontrivial.** -/
theorem nontrivial_criticalSchurInertiaGroup_of_ramificationIdx
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hram : 2 ≤ Ideal.ramificationIdxIn
      (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K hm hn))
      (CriticalSchurNormalIntegralClosure K hm hn)) :
    Nontrivial (criticalSchurInertiaGroup K hm hn) := by
  have hcard := natCard_criticalSchurIdealInertiaGroup_eq_ramificationIdxIn K hm hn
  haveI : Finite (criticalSchurIdealInertiaGroup K hm hn) :=
    Nat.finite_of_card_ne_zero (by omega)
  haveI : Nontrivial (criticalSchurIdealInertiaGroup K hm hn) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  exact nontrivial_of_injective_monoidHom (criticalSchurIdealInertiaToInertia K hm hn)
    (criticalSchurIdealInertiaToInertia_injective K hm hn)


/-- **Ramification plus the reduction-degree count give the transposition.** -/
theorem exists_criticalGeometricMonodromy_isSwap_of_ramification_of_degree
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (hram : 2 ≤ Ideal.ramificationIdxIn
      (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
      (CriticalSchurNormalIntegralClosure K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
    (hdeg : Nat.card (criticalGeometricSheet K m n)
      ≤ (Set.range (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard + 1) :
    ∃ τ : Equiv.Perm (criticalGeometricSheet K m n),
      τ.IsSwap ∧ τ ∈ criticalGeometricMonodromy K m n := by
  haveI := nontrivial_criticalSchurInertiaGroup_of_ramificationIdx K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) hram
  haveI := finite_criticalGeometricSheet K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  exact exists_criticalGeometricMonodromy_isSwap_of_reducedFibre_degree K hm hn hdeg

/-- **The endgame, packaged.**  Ramification at the Schur place, the reduction-degree count and
primitivity give full symmetric monodromy — statement `(4)` of the card. -/
theorem criticalGeometricMonodromy_eq_top_of_ramification_of_degree_of_isPreprimitive
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (hram : 2 ≤ Ideal.ramificationIdxIn
      (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
      (CriticalSchurNormalIntegralClosure K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
    (hdeg : Nat.card (criticalGeometricSheet K m n)
      ≤ (Set.range (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard + 1)
    (hprim : MulAction.IsPreprimitive (criticalGeometricMonodromy K m n)
      (criticalGeometricSheet K m n)) :
    criticalGeometricMonodromy K m n = ⊤ := by
  obtain ⟨τ, hτswap, hτmem⟩ :=
    exists_criticalGeometricMonodromy_isSwap_of_ramification_of_degree K hm hn hram hdeg
  exact criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_isSwap K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) hprim τ hτswap hτmem

/-- **The endgame in collision form.**  Ramification at the Schur place, at most two colliding
sheets, and primitivity give full symmetric monodromy. -/
theorem criticalGeometricMonodromy_eq_top_of_ramification_of_collision_of_isPreprimitive
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    (hram : 2 ≤ Ideal.ramificationIdxIn
      (IsLocalRing.maximalIdeal (CriticalSchurNormalBaseRing K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
      (CriticalSchurNormalIntegralClosure K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)))
    (hcollision :
      (collisionSupport (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard ≤ 2)
    (hprim : MulAction.IsPreprimitive (criticalGeometricMonodromy K m n)
      (criticalGeometricSheet K m n)) :
    criticalGeometricMonodromy K m n = ⊤ := by
  haveI := nontrivial_criticalSchurInertiaGroup_of_ramificationIdx K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) hram
  obtain ⟨τ, hτswap, hτmem⟩ :=
    exists_criticalGeometricMonodromy_isSwap_of_collisionSupport_ncard_le_two K hm hn hcollision
  exact criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_isSwap K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) hprim τ hτswap hτmem

end GaloisForLFunctions.HTGeometry
