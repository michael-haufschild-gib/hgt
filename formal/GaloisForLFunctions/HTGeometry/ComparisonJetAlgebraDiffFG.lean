import GaloisForLFunctions.HTGeometry.GaloisMonoidDichotomyDiffFG

/-!
# The comparison constants algebra is differentially finitely generated

The comparison matrix has four entries and the inverse determinant is one more element; every other
generator of the constants algebra is a jet of one of those five.  So the algebra is the jet adjoin
of a five-element family, which is exactly the hypothesis the endgame dichotomy needs in place of
algebraic finite type.

* `comparisonJetGeneratorsTwo`;
* `adjoin_comparisonJetGeneratorsTwo`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

/-- The five differential generators of the constants algebra of a rank-two comparison matrix. -/
def comparisonJetGeneratorsTwo (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (w : R ⊗[K] R) :
    Fin 5 → R ⊗[K] R :=
  ![Z 0 0, Z 0 1, Z 1 0, Z 1 1, w]

/-- Every jet of the inverse determinant lies in the comparison-jet algebra. -/
theorem tensorJet_w_mem_comparisonJetAlgebra {n : ℕ}
    (Z : Matrix (Fin n) (Fin n) (R ⊗[K] R)) {w : R ⊗[K] R} (hw : Z.det * w = 1) :
    ∀ m : ℕ, tensorJet (K := K) m w ∈ comparisonJetAlgebra (C := C) Z w
  | 0 => mem_comparisonJetAlgebra_w Z w
  | (m + 1) => comparisonJetAlgebra_deriv_stable Z hw
      (tensorJet_w_mem_comparisonJetAlgebra Z hw m)

/-- **The comparison constants algebra is the jet adjoin of five elements.** -/
theorem adjoin_comparisonJetGeneratorsTwo
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) {w : R ⊗[K] R} (hw : Z.det * w = 1) :
    Algebra.adjoin C (Set.range fun p : Fin 5 × ℕ =>
        tensorJet (K := K) p.2 (comparisonJetGeneratorsTwo Z w p.1))
      = comparisonJetAlgebra (C := C) Z w := by
  classical
  refine le_antisymm (Algebra.adjoin_le ?_) ?_
  · rintro _ ⟨⟨i, m⟩, rfl⟩
    have hZmem : ∀ a b : Fin 2,
        tensorJet (K := K) m (Z a b) ∈ comparisonJetAlgebra (C := C) Z w := fun a b =>
      Algebra.subset_adjoin (Set.mem_union_left _ (mem_comparisonJetGens Z m a b))
    fin_cases i
    · exact hZmem 0 0
    · exact hZmem 0 1
    · exact hZmem 1 0
    · exact hZmem 1 1
    · exact tensorJet_w_mem_comparisonJetAlgebra Z hw m
  · refine Algebra.adjoin_le ?_
    rintro x (hx | hx)
    · obtain ⟨_, ⟨m, rfl⟩, ⟨⟨a, b⟩, rfl⟩⟩ := hx
      refine Algebra.subset_adjoin ?_
      have hex : ∃ i : Fin 5, comparisonJetGeneratorsTwo Z w i = Z a b := by
        fin_cases a <;> fin_cases b
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨3, rfl⟩
      obtain ⟨i, hi⟩ := hex
      refine ⟨(i, m), ?_⟩
      show tensorJet (K := K) m (comparisonJetGeneratorsTwo Z w i)
        = tensorJet (K := K) m (Z a b)
      rw [hi]
    · rw [Set.mem_singleton_iff] at hx
      refine Algebra.subset_adjoin ⟨(4, 0), ?_⟩
      rw [hx]
      rfl

end

end GaloisForLFunctions.HTGeometry
