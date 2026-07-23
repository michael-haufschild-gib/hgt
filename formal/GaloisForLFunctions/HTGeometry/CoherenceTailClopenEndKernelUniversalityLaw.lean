import GaloisForLFunctions.HTGeometry.CoherenceEndClopen
import GaloisForLFunctions.HTGeometry.CoherenceTailQuotient

/-!
# Coherence-tail/clopen-end kernel universality

Finite-defect edge coherence forgets exactly finite-boundary orientation walls.  Independently,
finite-boundary vertex sets modulo finite changes present the Boolean algebra of clopen graph-end
sectors.  Their closure identifies the genuinely nontrivial part of the coherence kernel with
proper nonempty clopen sectors at infinity.
-/

namespace GaloisForLFunctions.HTGeometry

open Set
open scoped symmDiff

variable {V : Type}

/-- A Boolean orientation is projectively trivial exactly when its negative domain is finite or
cofinite. -/
theorem booleanProjectiveFiniteTailClass_eq_allPositive_iff
    (ε : V → Bool) :
    booleanProjectiveFiniteTailClass ε =
        booleanProjectiveFiniteTailClass (fun _ => false) ↔
      {v | ε v = true}.Finite ∨ ({v | ε v = true}ᶜ).Finite := by
  constructor
  · intro h
    have heq : BooleanProjectiveFiniteEquivalent ε (fun _ => false) := Quotient.exact h
    rcases heq with hdiff | hagree
    · left
      have hset : {v | ε v ≠ false} = {v | ε v = true} := by
        ext v
        cases ε v <;> simp
      simpa only [hset] using hdiff
    · right
      have hset : {v | ε v = false} = {v | ε v = true}ᶜ := by
        ext v
        cases ε v <;> simp
      simpa only [hset] using hagree
  · rintro (hfinite | hcofinite)
    · apply Quotient.sound
      left
      have hset : {v | ε v ≠ false} = {v | ε v = true} := by
        ext v
        cases ε v <;> simp
      simpa only [hset] using hfinite
    · apply Quotient.sound
      right
      have hset : {v | ε v = false} = {v | ε v = true}ᶜ := by
        ext v
        cases ε v <;> simp
      simpa only [hset] using hcofinite

/-- A finite-boundary set determines the empty end sector exactly when it is finite. -/
theorem finiteBoundaryEndClopen_eq_bot_iff_finite
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected]
    (A : FiniteBoundarySet G) :
    finiteBoundaryEndClopen G A = ⊥ ↔ (A.1).Finite := by
  rw [← finiteBoundaryEndClopen_empty G,
    finiteBoundaryEndClopen_eq_iff_symmDiff_finite]
  change ((A.1) ∆ (∅ : Set V)).Finite ↔ (A.1).Finite
  have hset : (A.1) ∆ (∅ : Set V) = A.1 := by
    ext v
    simp [Set.mem_symmDiff]
  rw [hset]

/-- A finite-boundary set determines the full end sector exactly when it is cofinite. -/
theorem finiteBoundaryEndClopen_eq_top_iff_compl_finite
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected]
    (A : FiniteBoundarySet G) :
    finiteBoundaryEndClopen G A = ⊤ ↔ ((A.1)ᶜ).Finite := by
  rw [← finiteBoundaryEndClopen_univ G,
    finiteBoundaryEndClopen_eq_iff_symmDiff_finite]
  change ((A.1) ∆ (Set.univ : Set V)).Finite ↔ ((A.1)ᶜ).Finite
  have hset : (A.1) ∆ (Set.univ : Set V) = (A.1)ᶜ := by
    ext v
    simp [Set.mem_symmDiff]
  rw [hset]

/-- **Coherence-tail/clopen-end kernel universality.** Within the finite-boundary kernel, a
projective orientation remains genuinely nontrivial exactly when its end sector is proper and
nonempty. -/
theorem coherenceTailMap_nontrivialKernel_iff_properClopenEndSector
    (G : SimpleGraph V) [Infinite V] [G.LocallyFinite] [Fact G.Preconnected]
    (ε : V → Bool) (hboundary : (edgeBoundary G {v | ε v = true}).Finite) :
    let A : FiniteBoundarySet G := ⟨{v | ε v = true}, hboundary⟩
    (coherenceTailMap G (booleanProjectiveFiniteTailClass ε) =
          coherenceTailMap G (booleanProjectiveFiniteTailClass (fun _ => false)) ∧
        booleanProjectiveFiniteTailClass ε ≠
          booleanProjectiveFiniteTailClass (fun _ => false)) ↔
      finiteBoundaryEndClopen G A ≠ ⊥ ∧
        finiteBoundaryEndClopen G A ≠ ⊤ := by
  dsimp only
  have hmap : coherenceTailMap G (booleanProjectiveFiniteTailClass ε) =
      coherenceTailMap G (booleanProjectiveFiniteTailClass (fun _ => false)) :=
    (coherenceTailMap_eq_allPositive_iff_negativeDomain_finiteBoundary G ε).2 hboundary
  constructor
  · rintro ⟨_hmap, hnontrivial⟩
    refine ⟨?_, ?_⟩
    · intro hbot
      apply hnontrivial
      apply (booleanProjectiveFiniteTailClass_eq_allPositive_iff ε).2
      left
      exact (finiteBoundaryEndClopen_eq_bot_iff_finite G
        (⟨{v | ε v = true}, hboundary⟩ : FiniteBoundarySet G)).1 hbot
    · intro htop
      apply hnontrivial
      apply (booleanProjectiveFiniteTailClass_eq_allPositive_iff ε).2
      right
      exact (finiteBoundaryEndClopen_eq_top_iff_compl_finite G
        (⟨{v | ε v = true}, hboundary⟩ : FiniteBoundarySet G)).1 htop
  · rintro ⟨hnotBot, hnotTop⟩
    refine ⟨hmap, ?_⟩
    intro htrivial
    rcases (booleanProjectiveFiniteTailClass_eq_allPositive_iff ε).1 htrivial with
      hfinite | hcofinite
    · exact hnotBot ((finiteBoundaryEndClopen_eq_bot_iff_finite G
        (⟨{v | ε v = true}, hboundary⟩ : FiniteBoundarySet G)).2 hfinite)
    · exact hnotTop ((finiteBoundaryEndClopen_eq_top_iff_compl_finite G
        (⟨{v | ε v = true}, hboundary⟩ : FiniteBoundarySet G)).2 hcofinite)

end GaloisForLFunctions.HTGeometry
