import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedAffineCover

/-! Ordered inclusions of the two halves of a joined affine cover. -/

namespace GlobalTheory.WH

variable {ι κ : Type} [Preorder ι] [Preorder κ]

/-- The left half of the lexicographically ordered sum. -/
def joinedLeft : ι ↪o ι ⊕ₗ κ where
  toEmbedding := Function.Embedding.inl.trans (toLex : ι ⊕ κ ≃ ι ⊕ₗ κ).toEmbedding
  map_rel_iff' := Sum.Lex.inl_le_inl_iff

/-- The right half of the lexicographically ordered sum. -/
def joinedRight : κ ↪o ι ⊕ₗ κ where
  toEmbedding := Function.Embedding.inr.trans (toLex : ι ⊕ κ ≃ ι ⊕ₗ κ).toEmbedding
  map_rel_iff' := Sum.Lex.inr_le_inr_iff

@[simp] theorem map_joinedLeft (I : Finset ι) :
    I.map (joinedLeft (κ := κ)).toEmbedding = uni I ∅ := by
  rw [uni, Finset.disjSum_empty, Finset.map_map]
  rfl

@[simp] theorem map_joinedRight (I : Finset κ) :
    I.map (joinedRight (ι := ι)).toEmbedding = uni ∅ I := by
  rw [uni, Finset.empty_disjSum, Finset.map_map]
  rfl

end GlobalTheory.WH
