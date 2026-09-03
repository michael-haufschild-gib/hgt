import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLatticeRelativeLength
import GaloisForLFunctions.HTGeometry.NoncommutativeSubmoduleQuotientLength

/-!
# Additivity of completed lattice quotient lengths

For a chain of included completed lattices, the middle carrier identifies with the intermediate
submodule inside the largest carrier.  The generic noncommutative quotient exact sequence then
makes both module length and its canonical natural Cartan-coordinate value additive.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*}

/-- The carrier of an included lattice is equivalent to its image inside the larger carrier. -/
def completedPseudoDiffOpIncludedLatticeCarrierEquiv
    (M N : CompletedPseudoDiffOpLattice K ι) (hMN : M.carrier ≤ N.carrier) :
    M.carrier ≃ₗ[CompletedPseudoDiffOpInteger (K := K)]
      completedPseudoDiffOpLatticeSubmoduleOf M N hMN where
  toFun x := ⟨⟨x.1, hMN x.2⟩, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨y.1.1, y.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Carrier inclusion identifies an inner lattice with the corresponding nested submodule. -/
theorem map_completedPseudoDiffOpLatticeSubmoduleOf_eq_nestedInside
    (L M N : CompletedPseudoDiffOpLattice K ι)
    (hLM : L.carrier ≤ M.carrier) (hMN : M.carrier ≤ N.carrier) :
    Submodule.map (completedPseudoDiffOpIncludedLatticeCarrierEquiv M N hMN).toLinearMap
        (completedPseudoDiffOpLatticeSubmoduleOf L M hLM) =
      nestedSubmoduleInside
        (completedPseudoDiffOpLatticeSubmoduleOf L N (hLM.trans hMN))
        (completedPseudoDiffOpLatticeSubmoduleOf M N hMN) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨⟨y.1.1, y.2⟩, hy, ?_⟩
    rfl

/-- Relative quotient length is additive along chains of included completed lattices. -/
theorem completedPseudoDiffOpLatticeQuotient_length_add
    (L M N : CompletedPseudoDiffOpLattice K ι)
    (hLM : L.carrier ≤ M.carrier) (hMN : M.carrier ≤ N.carrier) :
    Module.length (CompletedPseudoDiffOpInteger (K := K))
        (N.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L N (hLM.trans hMN)) =
      Module.length (CompletedPseudoDiffOpInteger (K := K))
          (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L M hLM) +
        Module.length (CompletedPseudoDiffOpInteger (K := K))
          (N.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf M N hMN) := by
  let P := completedPseudoDiffOpLatticeSubmoduleOf L N (hLM.trans hMN)
  let Q := completedPseudoDiffOpLatticeSubmoduleOf M N hMN
  have hPQ : P ≤ Q := by
    intro x hx
    exact hLM hx
  have hlen := nestedSubmoduleQuotient_length_add P Q hPQ
  have hlayer := nestedSubmoduleLayerQuotient_length_eq
    (completedPseudoDiffOpLatticeSubmoduleOf L M hLM) P Q
    (completedPseudoDiffOpIncludedLatticeCarrierEquiv M N hMN)
    (map_completedPseudoDiffOpLatticeSubmoduleOf_eq_nestedInside L M N hLM hMN)
  change Module.length (CompletedPseudoDiffOpInteger (K := K)) (N.carrier ⧸ P) =
    Module.length (CompletedPseudoDiffOpInteger (K := K))
      (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L M hLM) +
      Module.length (CompletedPseudoDiffOpInteger (K := K)) (N.carrier ⧸ Q)
  rw [hlen]
  rw [hlayer]

variable {r : ℕ}

/-- Natural-valued quotient length, expressed by canonical reverse Cartan coordinates. -/
def completedPseudoDiffOpLatticeQuotientNatLength
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) : ℕ :=
  ∑ i, Int.toNat (completedPseudoDiffOpDominantRelativePosition M L i)

/-- Actual module length equals the natural Cartan-coordinate quotient length. -/
theorem completedPseudoDiffOpLatticeQuotient_length_eq_natLength
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) (h : L.carrier ≤ M.carrier) :
    Module.length (CompletedPseudoDiffOpInteger (K := K)) (M.carrier ⧸ completedPseudoDiffOpLatticeSubmoduleOf L M h) =
      completedPseudoDiffOpLatticeQuotientNatLength L M :=
  completedPseudoDiffOpLatticeQuotient_length_eq_sum_relativePosition L M h

/-- Natural quotient length is additive along every included lattice chain. -/
theorem completedPseudoDiffOpLatticeQuotientNatLength_add
    (L M N : CompletedPseudoDiffOpLattice K (Fin r))
    (hLM : L.carrier ≤ M.carrier) (hMN : M.carrier ≤ N.carrier) :
    completedPseudoDiffOpLatticeQuotientNatLength L N =
      completedPseudoDiffOpLatticeQuotientNatLength L M + completedPseudoDiffOpLatticeQuotientNatLength M N := by
  have hlen := completedPseudoDiffOpLatticeQuotient_length_add L M N hLM hMN
  rw [completedPseudoDiffOpLatticeQuotient_length_eq_natLength L N (hLM.trans hMN),
    completedPseudoDiffOpLatticeQuotient_length_eq_natLength L M hLM,
    completedPseudoDiffOpLatticeQuotient_length_eq_natLength M N hMN] at hlen
  exact ENat.coe_inj.mp hlen

end

end GaloisForLFunctions.HTGeometry.DiffOp
