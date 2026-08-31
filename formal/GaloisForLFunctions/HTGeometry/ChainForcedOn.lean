import GaloisForLFunctions.HTGeometry.ChainForcedFamily

/-!
# The chain complex on an available vertex set

The recursion descends on a pair `(A, V)`: the vertices `A` forced into every face, and the vertices
`V` still available.  The complex is

```text
Δ_r^{A,V} = { S ⊆ V : S ∪ A contains no (r+1)-chain } .
```

```text
chainForcedOn N r A V          the complex
chainForcedOn_univ             Δ_r^{A,univ} = Δ_r^A
isFaceFamily_chainForcedOn     it is downward closed
faceDeletion_chainForcedOn     ** del v = Δ_r^{A, V \ {v}} **
faceLink_chainForcedOn         ** lk v  = Δ_r^{A ∪ {v}, V \ {v}} **   (for v ∈ V)
```

Both operations shrink `V` by one vertex, so the recursion of `StarReduction.lean` — which needs
only the deletion and the link — is well founded on `V.card`.  What is left is the dimension
bookkeeping: that the deletion keeps the largest face size and the link drops it by one, for the
least available vertex.
-/

namespace GaloisForLFunctions.HTGeometry

open RHTower

/-- The chain complex with forced vertices `A`, restricted to the available vertices `V`. -/
noncomputable def chainForcedOn (N r : ℕ) (A V : Finset (Fin N)) : Finset (Finset (Fin N)) := by
  classical
  exact Finset.univ.filter (fun S => S ⊆ V ∧ IsChainFace N r (S ∪ A))

theorem mem_chainForcedOn {N r : ℕ} {A V S : Finset (Fin N)} :
    S ∈ chainForcedOn N r A V ↔ S ⊆ V ∧ IsChainFace N r (S ∪ A) := by
  classical
  simp [chainForcedOn]

theorem isFaceFamily_chainForcedOn (N r : ℕ) (A V : Finset (Fin N)) :
    IsFaceFamily (chainForcedOn N r A V) := by
  intro S T hT hST
  rw [mem_chainForcedOn] at hT ⊢
  exact ⟨hST.trans hT.1,
    hT.2.subset (Finset.union_subset_union hST (subset_refl A))⟩

theorem chainForcedOn_univ (N r : ℕ) (A : Finset (Fin N)) :
    chainForcedOn N r A Finset.univ = chainForcedFamily N r A := by
  classical
  ext S
  rw [mem_chainForcedOn, mem_chainForcedFamily]
  exact ⟨fun h => h.2, fun h => ⟨Finset.subset_univ S, h⟩⟩

/-- **Deletion shrinks the available set.** -/
theorem faceDeletion_chainForcedOn (N r : ℕ) (A V : Finset (Fin N)) (v : Fin N) :
    faceDeletion (chainForcedOn N r A V) v = chainForcedOn N r A (V.erase v) := by
  classical
  ext S
  rw [mem_faceDeletion, mem_chainForcedOn, mem_chainForcedOn]
  constructor
  · rintro ⟨⟨hSV, hface⟩, hv⟩
    exact ⟨Finset.subset_erase.mpr ⟨hSV, hv⟩, hface⟩
  · rintro ⟨hSV, hface⟩
    obtain ⟨hS, hv⟩ := Finset.subset_erase.mp hSV
    exact ⟨⟨hS, hface⟩, hv⟩

/-- **The link shrinks the available set and grows the forced set.** -/
theorem faceLink_chainForcedOn (N r : ℕ) (A V : Finset (Fin N)) {v : Fin N} (hv : v ∈ V) :
    faceLink (chainForcedOn N r A V) v = chainForcedOn N r (insert v A) (V.erase v) := by
  classical
  ext S
  rw [mem_faceLink, mem_chainForcedOn, mem_chainForcedOn, mem_chainForcedOn]
  have hins : insert v S ∪ A = S ∪ insert v A := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  constructor
  · rintro ⟨⟨hSV, -⟩, hvS, ⟨-, hface⟩⟩
    rw [hins] at hface
    exact ⟨Finset.subset_erase.mpr ⟨hSV, hvS⟩, hface⟩
  · rintro ⟨hSV, hface⟩
    obtain ⟨hS, hvS⟩ := Finset.subset_erase.mp hSV
    refine ⟨⟨hS, ?_⟩, hvS, ⟨?_, ?_⟩⟩
    · exact hface.subset (Finset.union_subset_union (subset_refl S) (Finset.subset_insert v A))
    · exact Finset.insert_subset hv hS
    · rw [hins]
      exact hface

end GaloisForLFunctions.HTGeometry
