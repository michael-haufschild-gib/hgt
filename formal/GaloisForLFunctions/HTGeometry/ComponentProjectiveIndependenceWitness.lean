import GaloisForLFunctions.Core
import GaloisForLFunctions.HTGeometry.ComponentReplicaCollisionLaw

/-!
# Component projective independence is attained by prime logarithms

Mutual projective independence of a family of component energies is the standing hypothesis of the
component-histogram and replica-factorization laws.  It follows from ordinary integer linear
independence of the joint energy family — the balanced-relation condition is then not even needed —
and it is attained: labelling the joint index set by distinct primes and taking logarithms gives an
energy family that is projectively independent for every finite component structure.

So the hypothesis is a genuine transversality condition, satisfiable on every finite label set, and
the arithmetic source of the corpus already supplies a witness.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Integer linear independence of the joint energy family implies component projective
independence. -/
theorem componentProjectivelyIndependent_of_linearIndependent
    {C : Type*} [Fintype C] {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (hind : LinearIndependent ℤ (fun ci : Σ c, I c => energy ci.1 ci.2)) :
    ComponentProjectivelyIndependent energy := by
  intro k _ hsum c
  funext i
  have hzero : ∀ ci : Σ c, I c, k ci.1 ci.2 = 0 := by
    refine Fintype.linearIndependent_iff.mp hind (fun ci => k ci.1 ci.2) ?_
    rw [Fintype.sum_sigma]
    simpa [zsmul_eq_mul] using hsum
  exact hzero ⟨c, i⟩

/-- Distinct prime logarithms give a projectively independent component energy family. -/
theorem componentProjectivelyIndependent_primeLog
    {C : Type*} [Fintype C] {I : C → Type*} [∀ c, Fintype (I c)]
    (idx : (Σ c, I c) ↪ Nat.Primes) :
    ComponentProjectivelyIndependent
      (fun c i => Real.log ((idx ⟨c, i⟩ : Nat.Primes) : ℕ)) := by
  refine componentProjectivelyIndependent_of_linearIndependent _ ?_
  have hbase : LinearIndependent ℤ (fun p : Nat.Primes => Real.log (p : ℕ)) :=
    logPrime_linearIndependent_int
  have h := hbase.comp idx idx.injective
  simpa [Function.comp_def] using h

/-- **The interface is attained on every finite component structure.**  For every finite family of
finite component label sets there is a projectively independent energy family. -/
theorem exists_componentProjectivelyIndependent
    {C : Type*} [Fintype C] {I : C → Type*} [∀ c, Fintype (I c)] :
    ∃ energy : ∀ c, I c → ℝ, ComponentProjectivelyIndependent energy := by
  classical
  let f : ((c : C) × I c) ↪ ℕ :=
    (Fintype.equivFin ((c : C) × I c)).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩
  exact ⟨_, componentProjectivelyIndependent_primeLog
    (f.trans (Infinite.natEmbedding Nat.Primes))⟩

end

end GaloisForLFunctions.HTGeometry
