import GaloisForLFunctions.HTGeometry.HankelChainStanleyReisner
import GaloisForLFunctions.HTGeometry.StanleyReisnerMayerVietoris

/-!
# The chain complex with forced vertices

The Cohen–Macaulay recursion does not close on the family `{Δ_r}`: the link of a vertex is `Δ_r`
with that vertex *forced into every face*.  The class that is closed under both deletion and link is

```text
Δ_r^A = { S : S ∪ A contains no (r+1)-chain }
```

with `A` a set of forced vertices.

```text
chainForcedFamily N r A            the complex Δ_r^A
chainForcedFamily_empty            Δ_r^∅ = Δ_r
isFaceFamily_chainForcedFamily     it is downward closed
faceLink_chainForcedFamily
    ** lk (Δ_r^A) v = del (Δ_r^{A ∪ {v}}) v — the class is closed under links **
card_add_card_le_of_mem_chainForcedFamily
    a face disjoint from the forced set has at most 2r − |A| vertices
```

Deletion needs no lemma: `del (Δ_r^A) v` is `Δ_r^A` with the faces avoiding `v`, by definition.  The
link identity is the substantive one, and with it the recursion of `ConeRegularSequence.lean` and
`SheddingRegularSequence.lean` can run on the pair `(A, remaining vertices)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

/-- The chain complex with a set `A` of vertices forced into every face:
`Δ_r^A = {S : S ∪ A contains no (r+1)-chain}`. -/
noncomputable def chainForcedFamily (N r : ℕ) (A : Finset (Fin N)) :
    Finset (Finset (Fin N)) := by
  classical
  exact Finset.univ.filter (fun S => IsChainFace N r (S ∪ A))

theorem mem_chainForcedFamily {N r : ℕ} {A S : Finset (Fin N)} :
    S ∈ chainForcedFamily N r A ↔ IsChainFace N r (S ∪ A) := by
  classical
  simp [chainForcedFamily]

theorem chainForcedFamily_empty (N r : ℕ) : chainForcedFamily N r ∅ = chainFaceFinset N r := by
  classical
  ext S
  rw [mem_chainForcedFamily, mem_chainFaceFinset, Finset.union_empty]

theorem isFaceFamily_chainForcedFamily (N r : ℕ) (A : Finset (Fin N)) :
    IsFaceFamily (chainForcedFamily N r A) := by
  intro S T hT hST
  rw [mem_chainForcedFamily] at hT ⊢
  exact hT.subset (Finset.union_subset_union hST (subset_refl A))

/-- **The link of a vertex forces it.**  `lk (Δ_r^A) v` is the deletion of `v` from
`Δ_r^{A ∪ {v}}`, so the family `{Δ_r^A}` is closed under links and deletions. -/
theorem faceLink_chainForcedFamily (N r : ℕ) (A : Finset (Fin N)) (v : Fin N) :
    faceLink (chainForcedFamily N r A) v
      = faceDeletion (chainForcedFamily N r (insert v A)) v := by
  classical
  ext S
  rw [mem_faceLink, mem_faceDeletion, mem_chainForcedFamily, mem_chainForcedFamily,
    mem_chainForcedFamily]
  have hins : insert v S ∪ A = S ∪ insert v A := by
    ext w
    simp only [Finset.mem_union, Finset.mem_insert]
    tauto
  constructor
  · rintro ⟨-, hv, hface⟩
    rw [hins] at hface
    exact ⟨hface, hv⟩
  · rintro ⟨hface, hv⟩
    refine ⟨?_, hv, ?_⟩
    · exact hface.subset (Finset.union_subset_union (subset_refl S) (Finset.subset_insert v A))
    · rw [hins]
      exact hface

/-- **The face-size bound for the forced family.**  A face disjoint from the forced set has at most
`2r - |A|` vertices. -/
theorem card_add_card_le_of_mem_chainForcedFamily {N r : ℕ} {A S : Finset (Fin N)}
    (hdisj : Disjoint S A) (hS : S ∈ chainForcedFamily N r A) :
    S.card + A.card ≤ 2 * r := by
  classical
  rw [mem_chainForcedFamily] at hS
  have hcard := card_le_two_mul_of_isChainFace hS
  rwa [Finset.card_union_of_disjoint hdisj] at hcard

/-- The forced set is itself a face-size obstruction: `|A| ≤ 2r` for a nonempty family. -/
theorem card_le_two_mul_of_mem_chainForcedFamily {N r : ℕ} {A : Finset (Fin N)}
    (hA : ∅ ∈ chainForcedFamily N r A) : A.card ≤ 2 * r := by
  classical
  have := card_add_card_le_of_mem_chainForcedFamily (S := (∅ : Finset (Fin N))) (by simp) hA
  simpa using this


end GaloisForLFunctions.HTGeometry
