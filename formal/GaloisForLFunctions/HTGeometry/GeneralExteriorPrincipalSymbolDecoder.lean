import GaloisForLFunctions.HTGeometry.QuantumTorusPrincipalSymbol

/-!
# General exterior principal-symbol decoder

No quantum commutation law is needed once the commutators of coordinate generators are known to
be linearly independent.  This module constructs an explicit left inverse from that minimal
hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u v

variable {K : Type u} {M : Type v} {ι : Type*}
  [Field K] [CharZero K]
  [AddCommGroup M] [Module K M]
  [Fintype ι] [LinearOrder ι]

/-- Coordinate commutator attached to an increasing law pair. -/
def principalBracketPair
    (symbol : (ι → K) →ₗ[K] Module.End K M) (p : QuantumLawPair ι) :
    Module.End K M :=
  symbol (Pi.basisFun K ι p.lower) * symbol (Pi.basisFun K ι p.upper) -
    symbol (Pi.basisFun K ι p.upper) * symbol (Pi.basisFun K ι p.lower)

/-- Decode coordinate commutators on their linear span. -/
def principalBracketSpanDecoder
    (symbol : (ι → K) →ₗ[K] Module.End K M)
    (hLI : LinearIndependent K (principalBracketPair symbol)) :
    Submodule.span K (Set.range (principalBracketPair symbol)) →ₗ[K]
      ⋀[K]^(2 : ℕ) (ι → K) :=
  (Finsupp.linearCombination K fun p : QuantumLawPair ι ↦
    quantumPairWedge (K := K) p).comp hLI.repr

/-- Extend the bracket decoder to the whole endomorphism space. -/
def principalBracketDecoder
    (symbol : (ι → K) →ₗ[K] Module.End K M)
    (hLI : LinearIndependent K (principalBracketPair symbol)) :
    Module.End K M →ₗ[K] ⋀[K]^(2 : ℕ) (ι → K) :=
  Classical.choose (LinearMap.exists_extend (principalBracketSpanDecoder symbol hLI))

omit [CharZero K] in
theorem principalBracketDecoder_apply
    (symbol : (ι → K) →ₗ[K] Module.End K M)
    (hLI : LinearIndependent K (principalBracketPair symbol))
    (p : QuantumLawPair ι) :
    principalBracketDecoder symbol hLI (principalBracketPair symbol p) =
      quantumPairWedge (K := K) p := by
  have hp : principalBracketPair symbol p ∈
      Submodule.span K (Set.range (principalBracketPair symbol)) :=
    Submodule.subset_span (Set.mem_range_self p)
  have hext := LinearMap.congr_fun
    (Classical.choose_spec (LinearMap.exists_extend (principalBracketSpanDecoder symbol hLI)))
    ⟨principalBracketPair symbol p, hp⟩
  rw [LinearMap.comp_apply] at hext
  have hrepr := hLI.repr_eq_single p ⟨principalBracketPair symbol p, hp⟩ rfl
  calc
    principalBracketDecoder symbol hLI (principalBracketPair symbol p) =
        principalBracketSpanDecoder symbol hLI
          ⟨principalBracketPair symbol p, hp⟩ := by
      simpa [principalBracketDecoder] using hext
    _ = quantumPairWedge (K := K) p := by
      unfold principalBracketSpanDecoder
      rw [LinearMap.comp_apply, hrepr]
      simp

/-- Decoder composed with the exterior commutator symbol. -/
def decodedPrincipalBracketMap
    (symbol : (ι → K) →ₗ[K] Module.End K M)
    (hLI : LinearIndependent K (principalBracketPair symbol)) :
    (⋀[K]^(2 : ℕ) (ι → K)) →ₗ[K] ⋀[K]^(2 : ℕ) (ι → K) :=
  (principalBracketDecoder symbol hLI).comp (endomorphismCommutatorMap symbol)

omit [CharZero K] in
/-- Independent coordinate commutators give a literal left inverse on the full exterior square. -/
theorem decodedPrincipalBracketMap_eq_id
    (symbol : (ι → K) →ₗ[K] Module.End K M)
    (hLI : LinearIndependent K (principalBracketPair symbol)) :
    decodedPrincipalBracketMap symbol hLI = LinearMap.id := by
  apply ((Pi.basisFun K ι).exteriorPower 2).ext
  intro s
  rw [exteriorPower.basis_apply]
  let e : Fin 2 ↪o ι := Set.powersetCard.ofFinEmbEquiv.symm s
  have he : e 0 < e 1 := e.strictMono Fin.zero_lt_one
  let p : QuantumLawPair ι := ⟨e 0, e 1, he⟩
  change principalBracketDecoder symbol hLI
      (endomorphismCommutatorMap symbol
        (exteriorPower.ιMulti K 2
          ![Pi.basisFun K ι (e 0), Pi.basisFun K ι (e 1)])) =
    exteriorPower.ιMulti K 2
      ![Pi.basisFun K ι (e 0), Pi.basisFun K ι (e 1)]
  rw [endomorphismCommutatorMap_wedge]
  rw [LieRing.of_associative_ring_bracket]
  simpa [principalBracketPair, quantumPairWedge, p] using
    (principalBracketDecoder_apply symbol hLI p)

omit [CharZero K] in
/-- **General principal-symbol theorem.**  Linear independence of the coordinate commutators is
exactly sufficient for injectivity of the full exterior commutator map. -/
theorem endomorphismCommutatorMap_injective_of_principalBracketPair_linearIndependent
    (symbol : (ι → K) →ₗ[K] Module.End K M)
    (hLI : LinearIndependent K (principalBracketPair symbol)) :
    Function.Injective (endomorphismCommutatorMap symbol) := by
  intro z z' hzz'
  have hdecoded := congrArg (principalBracketDecoder symbol hLI) hzz'
  have hleft := LinearMap.congr_fun (decodedPrincipalBracketMap_eq_id symbol hLI)
  calc
    z = decodedPrincipalBracketMap symbol hLI z := (hleft z).symm
    _ = decodedPrincipalBracketMap symbol hLI z' := hdecoded
    _ = z' := hleft z'

end

end GaloisForLFunctions.HTGeometry
