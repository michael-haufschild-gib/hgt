import GaloisForLFunctions.HTGeometry.JetRelationIndependence

/-!
# Hypertranscendence in terms of jet relations

Hypertranscendence over a differential base field is defined as the failure of differential
algebraicity, which unfolds to algebraic independence of the jet family indexed by `Unit × ℕ`.  The
relation statements produced by the finite phase law are indexed by `ℕ`.  The two indexings differ by
an equivalence, so the predicates agree; with that identification, hypertranscendence is exactly the
absence of a jet relation, and it is invariant under inversion.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {F K : Type*} [Field F] [Field K] [Differential K] [Algebra F K]

/-- Differential independence of a single element is algebraic independence of its jets. -/
theorem differentialIndependent_unit_iff_algebraicIndependent_jets (x : K) :
    DifferentialIndependent F (fun _ : Unit => x) ↔
      AlgebraicIndependent F (fun i : ℕ => differentialJet i x) := by
  constructor
  · intro h
    have h' : AlgebraicIndependent F (fun p : Unit × ℕ => differentialJet p.2 x) := h
    exact h'.comp (fun i : ℕ => (((), i) : Unit × ℕ)) (fun a b hab => congrArg Prod.snd hab)
  · intro h
    show AlgebraicIndependent F (fun p : Unit × ℕ => differentialJet p.2 x)
    exact h.comp (fun p : Unit × ℕ => p.2)
      (fun a b hab => Prod.ext (Subsingleton.elim _ _) hab)

/-- **Hypertranscendence is the absence of an algebraic relation among the jets.** -/
theorem hypertranscendentalOver_iff_algebraicIndependent_jets (x : K) :
    HypertranscendentalOver F x ↔ AlgebraicIndependent F (fun i : ℕ => differentialJet i x) :=
  (hypertranscendentalOver_iff_differentialIndependent_singleton F x).trans
    (differentialIndependent_unit_iff_algebraicIndependent_jets x)

/-- A hypertranscendental element is not algebraic over the base, in particular not a base
element. -/
theorem not_mem_range_algebraMap_of_algebraicIndependent_jets {x : K}
    (h : AlgebraicIndependent F (fun i : ℕ => differentialJet i x)) :
    x ∉ Set.range (algebraMap F K) := by
  rintro ⟨c, rfl⟩
  have h0 := h.transcendental 0
  rw [differentialJet_zero] at h0
  exact h0 (isAlgebraic_algebraMap c)

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
  [Algebra F K] [DifferentialAlgebra F K]

omit [Differential F] [DifferentialAlgebra F K] in
/-- **Hypertranscendence from the absence of a jet relation.**  This is the form the finite phase law
produces: a sum of jet monomials with distinct exponent vectors and nonzero coefficients never
vanishes. -/
theorem hypertranscendentalOver_of_no_jet_relation {u : K}
    (H : ∀ (n N : ℕ), 0 < N → ∀ e : Fin N → Fin (n + 1) → ℕ, Function.Injective e →
      ∀ c : Fin N → F, (∀ α, c α ≠ 0) →
        ∑ α : Fin N, algebraMap F K (c α)
          * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) u) ^ (e α i) ≠ 0) :
    HypertranscendentalOver F u :=
  (hypertranscendentalOver_iff_algebraicIndependent_jets u).mpr
    (algebraicIndependent_of_no_jet_relation H)

/-- **Hypertranscendence is invariant under inversion.** -/
theorem hypertranscendentalOver_inv {u : K} (hu : u ≠ 0) (h : HypertranscendentalOver F u) :
    HypertranscendentalOver F u⁻¹ :=
  (hypertranscendentalOver_iff_algebraicIndependent_jets u⁻¹).mpr
    (algebraicIndependent_jets_inv hu
      ((hypertranscendentalOver_iff_algebraicIndependent_jets u).mp h))

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {F K : Type*} [Field F] [Field K] [Differential K] [Algebra F K]

/-- **A jet relation exists whenever the jets are dependent.**  This is the converse direction of
`algebraicIndependent_of_no_jet_relation`, in the explicit shape the finite phase law consumes:
distinct exponent vectors, nonzero base-field coefficients, and a vanishing sum. -/
theorem exists_jet_relation_of_not_algebraicIndependent {u : K}
    (h : ¬ AlgebraicIndependent F (fun i : ℕ => differentialJet i u)) :
    ∃ (n N : ℕ) (e : Fin N → Fin (n + 1) → ℕ) (c : Fin N → F),
      0 < N ∧ Function.Injective e ∧ (∀ α, c α ≠ 0) ∧
        ∑ α : Fin N, algebraMap F K (c α)
          * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) u) ^ (e α i) = 0 := by
  by_contra hcon
  refine h (algebraicIndependent_of_no_jet_relation ?_)
  intro n N hN e he c hc hrel
  exact hcon ⟨n, N, e, c, hN, he, hc, hrel⟩

/-- The same, from differential algebraicity over the base. -/
theorem exists_jet_relation_of_differentialAlgebraic {u : K}
    (h : DifferentialAlgebraicOver F u) :
    ∃ (n N : ℕ) (e : Fin N → Fin (n + 1) → ℕ) (c : Fin N → F),
      0 < N ∧ Function.Injective e ∧ (∀ α, c α ≠ 0) ∧
        ∑ α : Fin N, algebraMap F K (c α)
          * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) u) ^ (e α i) = 0 :=
  exists_jet_relation_of_not_algebraicIndependent
    (fun hind => h ((differentialIndependent_unit_iff_algebraicIndependent_jets u).mpr hind))

end GaloisForLFunctions.HTGeometry
