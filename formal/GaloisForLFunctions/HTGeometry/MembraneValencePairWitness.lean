import GaloisForLFunctions.HTGeometry.MembraneLocalityWitnesses

/-!
# Membrane locality together with a valence bound

The holographic locality layer consumes `MembraneLocalPrincipalBrackets symbol support` together
with `MembraneValenceAtMost support Δ`.  Locality has realizations in the corpus and the valence
bound appears only as an anonymous `by simp` inside the three-scale certificate, so the pair is
nowhere on record — and the two premises pull against each other, since locality wants large
membranes and the valence bound wants small ones.

Both ends of that trade-off are realized here:

* total membranes make locality free, at valence exactly the ambient cardinality
  (`membraneLocality_and_valence_univ`);
* a symbol with vanishing principal brackets is local for *every* support, so locality costs nothing
  at valence `0` (`membraneLocality_and_valence_zero`).

So the pair is jointly satisfiable at both extremes of the valence scale, and the layer's content is
what happens in between.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I H : Type*} [Fintype I] [Fintype H]
variable {K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M] [LinearOrder I]

omit [Fintype H] [CharZero K] [Module K M] [LinearOrder I] in
/-- Total membranes have valence the ambient cardinality. -/
theorem membraneValenceAtMost_univ :
    MembraneValenceAtMost (fun _ : H => (Finset.univ : Finset I)) (Fintype.card I) :=
  fun _ => le_of_eq Finset.card_univ

omit [Fintype I] [Fintype H] [CharZero K] [Module K M] [LinearOrder I] in
/-- The empty membranes have valence zero. -/
theorem membraneValenceAtMost_empty :
    MembraneValenceAtMost (fun _ : H => (∅ : Finset I)) 0 := by
  intro h
  simp

omit [Fintype H] in
/-- **The large end.**  Total membranes cover every law pair, so locality is free, and their valence
is exactly the ambient cardinality. -/
theorem membraneLocality_and_valence_univ [Nonempty H]
    (symbol : (I → K) →ₗ[K] Module.End K M) :
    MembraneLocalPrincipalBrackets symbol (fun _ : H => (Finset.univ : Finset I)) ∧
      MembraneValenceAtMost (fun _ : H => (Finset.univ : Finset I)) (Fintype.card I) :=
  ⟨membraneLocalPrincipalBrackets_univ_support symbol, membraneValenceAtMost_univ⟩

omit [Fintype H] in
/-- **The small end.**  A symbol with vanishing principal brackets is local for every support, so
the pair holds at valence zero. -/
theorem membraneLocality_and_valence_zero :
    MembraneLocalPrincipalBrackets (0 : (I → K) →ₗ[K] Module.End K M)
        (fun _ : H => (∅ : Finset I)) ∧
      MembraneValenceAtMost (fun _ : H => (∅ : Finset I)) 0 :=
  ⟨membraneLocalPrincipalBrackets_zero _, membraneValenceAtMost_empty⟩

end

end GaloisForLFunctions.HTGeometry
