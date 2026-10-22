import GaloisForLFunctions.HTGeometry.Critical.Schur.CollisionDegree
import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Jordan's criterion on the actual geometric sheets

`CriticalMonodromyJordan` states Jordan's theorem for the abstract occupation states.  The critical
monodromy group of this card acts on the *actual* geometric sheets — the observation-field
embeddings of the critical source field — so the criterion is restated there, together with the
finiteness of the sheet set (the source field is finite dimensional over the observation field, so
its algebra homomorphisms into the normal closure form a finite set).

```text
criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_isSwap
criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_reducedFibre_degree
    ** primitivity + the Schur reduction-degree bound  ⟹  criticalGeometricMonodromy = ⊤ **
```

The second form is the exact shape of the endgame: transitivity is already unconditional, the
transposition is delivered by the degree count of `CriticalSchurCollisionDegree`, and primitivity is
what the torus/`SCE_k` chain supplies.
-/

namespace GaloisForLFunctions.HTGeometry

set_option synthInstance.maxHeartbeats 400000

noncomputable local instance sheetDecEq (K : Type*) [Field K] (m n : ℕ) :
    DecidableEq (criticalGeometricSheet K m n) := Classical.decEq _

/-- The critical geometric sheets form a finite set. -/
theorem finite_criticalGeometricSheet (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : Finite (criticalGeometricSheet K m n) := by
  letI : FiniteDimensional (criticalObservationField K m n) (criticalSourceField K m n) :=
    criticalSourceField_finiteDimensional_criticalObservationField K hm hn
  infer_instance

/-- **Jordan on the actual geometric sheets.**  A primitive monodromy group containing a
transposition is the full symmetric group. -/
theorem criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_isSwap
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hprim : MulAction.IsPreprimitive (criticalGeometricMonodromy K m n)
      (criticalGeometricSheet K m n))
    (g : Equiv.Perm (criticalGeometricSheet K m n)) (hswap : g.IsSwap)
    (hg : g ∈ criticalGeometricMonodromy K m n) :
    criticalGeometricMonodromy K m n = ⊤ := by
  haveI := finite_criticalGeometricSheet K hm hn
  exact Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hprim g hswap hg


/-- **The final criterion for `(4)`.**  Primitivity of the monodromy action together with the
Schur reduction-degree bound gives full symmetric monodromy. -/
theorem criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_reducedFibre_degree
    (K : Type*) [Field K] [CharZero K] [IsAlgClosed K] {m n : ℕ} (hm : 1 < m) (hn : 1 < n)
    [Nontrivial ↥(criticalSchurInertiaGroup K (m := m) (n := n)
      (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn))]
    (hdeg : Nat.card (criticalGeometricSheet K m n)
      ≤ (Set.range (criticalGeometricSheetToSchurReducedFibre K hm hn)).ncard + 1)
    (hprim : MulAction.IsPreprimitive (criticalGeometricMonodromy K m n)
      (criticalGeometricSheet K m n)) :
    criticalGeometricMonodromy K m n = ⊤ := by
  haveI := finite_criticalGeometricSheet K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
  obtain ⟨τ, hτswap, hτmem⟩ :=
    exists_criticalGeometricMonodromy_isSwap_of_reducedFibre_degree K hm hn hdeg
  exact criticalGeometricMonodromy_eq_top_of_isPreprimitive_of_isSwap K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) hprim τ hτswap hτmem

end GaloisForLFunctions.HTGeometry
