import GaloisForLFunctions.HTGeometry.SimplicialCochainComplex

/-!
# The cone contraction of the full simplex, in the cochain model

Coordinate-facet descent splits by monomial, and the block belonging to a monomial is the reduced
simplicial cochain complex of the *full* simplex on the facets containing its support.  This module
supplies the contraction of that block in the concrete cochain model of
`SimplicialCochainComplex`: a base vertex gives an explicit cone homotopy

```text
(K f)(τ) = if i₀ ∈ τ then 0 else faceSign (τ ∪ {i₀}) i₀ · f (τ ∪ {i₀}),
```

which satisfies `δ ∘ K + K ∘ δ = id` in every degree at once, over any commutative ring.  Hence
every cocycle on a nonempty full simplex is a coboundary, with a primitive of the same support and
one degree lower: the reduced cohomology of a nonempty full simplex vanishes everywhere, including
in the augmentation slot.

The homotopy identity rests on the same incidence-sign antisymmetry that gives `δ² = 0`.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] {F : Type*} [CommRing F]

/-- The cone homotopy at a base vertex: adjoin `i₀` and evaluate, with the sign of `i₀`. -/
def simplicialCone (F : Type*) [CommRing F] (i₀ : α) (f : Finset α → F) : Finset α → F :=
  fun τ => if i₀ ∈ τ then 0 else faceSign F (insert i₀ τ) i₀ * f (insert i₀ τ)

theorem simplicialCone_of_mem {i₀ : α} (f : Finset α → F) {τ : Finset α} (h : i₀ ∈ τ) :
    simplicialCone F i₀ f τ = 0 := if_pos h

theorem simplicialCone_of_notMem {i₀ : α} (f : Finset α → F) {τ : Finset α} (h : i₀ ∉ τ) :
    simplicialCone F i₀ f τ = faceSign F (insert i₀ τ) i₀ * f (insert i₀ τ) := if_neg h

/-- The sign identity behind the cone homotopy: for a vertex `v` of `σ` and a base vertex `i₀`
outside `σ`, the coefficient contributed by `δ ∘ K` cancels the one contributed by `K ∘ δ`. -/
theorem faceSign_cone_cancel {i₀ : α} {σ : Finset α} (hi₀ : i₀ ∉ σ) {v : α} (hv : v ∈ σ) :
    faceSign F σ v * faceSign F ((insert i₀ σ).erase v) i₀
      + faceSign F (insert i₀ σ) i₀ * faceSign F (insert i₀ σ) v = 0 := by
  have hvi : i₀ ≠ v := fun h => hi₀ (h ▸ hv)
  have hmem₀ : i₀ ∈ insert i₀ σ := Finset.mem_insert_self i₀ σ
  have hmemv : v ∈ insert i₀ σ := Finset.mem_insert_of_mem hv
  have herase : (insert i₀ σ).erase i₀ = σ := Finset.erase_insert hi₀
  have h1 := faceSign_mul_faceSign_erase_antisymm (F := F) hmem₀ hmemv hvi
  rw [herase] at h1
  have hp : faceSign F σ v * faceSign F σ v = 1 := faceSign_mul_self σ v
  have ht : faceSign F (insert i₀ σ) v * faceSign F (insert i₀ σ) v = 1 :=
    faceSign_mul_self (insert i₀ σ) v
  linear_combination (faceSign F σ v * faceSign F (insert i₀ σ) v) * h1
    - (faceSign F σ v * faceSign F ((insert i₀ σ).erase v) i₀) * ht
    - (faceSign F (insert i₀ σ) i₀ * faceSign F (insert i₀ σ) v) * hp

/-- **The cone homotopy identity.**  `δ ∘ K + K ∘ δ = id` on every cochain and in every degree. -/
theorem simplicialCoboundary_simplicialCone_add (i₀ : α) (f : Finset α → F) (σ : Finset α) :
    simplicialCoboundary F (simplicialCone F i₀ f) σ
      + simplicialCone F i₀ (simplicialCoboundary F f) σ = f σ := by
  by_cases hi₀ : i₀ ∈ σ
  · rw [simplicialCone_of_mem _ hi₀, add_zero]
    show ∑ v ∈ σ, faceSign F σ v * simplicialCone F i₀ f (σ.erase v) = f σ
    rw [Finset.sum_eq_single i₀]
    · have hne : i₀ ∉ σ.erase i₀ := Finset.notMem_erase i₀ σ
      rw [simplicialCone_of_notMem _ hne, Finset.insert_erase hi₀, ← mul_assoc,
        faceSign_mul_self, one_mul]
    · intro v _ hv
      have hmem : i₀ ∈ σ.erase v := Finset.mem_erase.mpr ⟨fun h => hv h.symm, hi₀⟩
      rw [simplicialCone_of_mem _ hmem, mul_zero]
    · intro h
      exact absurd hi₀ h
  · have hins : ∀ v ∈ σ, insert i₀ (σ.erase v) = (insert i₀ σ).erase v := by
      intro v hv
      have hvi : v ≠ i₀ := fun h => hi₀ (h ▸ hv)
      rw [Finset.erase_insert_of_ne (Ne.symm hvi)]
    have hleft : simplicialCoboundary F (simplicialCone F i₀ f) σ
        = ∑ v ∈ σ, faceSign F σ v
            * (faceSign F ((insert i₀ σ).erase v) i₀ * f ((insert i₀ σ).erase v)) := by
      refine Finset.sum_congr rfl (fun v hv => ?_)
      have hne : i₀ ∉ σ.erase v := fun h => hi₀ (Finset.mem_of_mem_erase h)
      rw [simplicialCone_of_notMem _ hne, hins v hv]
    have hright : simplicialCone F i₀ (simplicialCoboundary F f) σ
        = faceSign F (insert i₀ σ) i₀
          * ∑ v ∈ insert i₀ σ, faceSign F (insert i₀ σ) v * f ((insert i₀ σ).erase v) := by
      rw [simplicialCone_of_notMem _ hi₀]
      rfl
    have hzero : ∀ v ∈ σ,
        faceSign F σ v * (faceSign F ((insert i₀ σ).erase v) i₀ * f ((insert i₀ σ).erase v))
          + faceSign F (insert i₀ σ) i₀
            * (faceSign F (insert i₀ σ) v * f ((insert i₀ σ).erase v)) = 0 := by
      intro v hv
      have hs := faceSign_cone_cancel (F := F) hi₀ hv
      linear_combination f ((insert i₀ σ).erase v) * hs
    have hsum : (∑ v ∈ σ, faceSign F σ v
          * (faceSign F ((insert i₀ σ).erase v) i₀ * f ((insert i₀ σ).erase v)))
        + ∑ v ∈ σ, faceSign F (insert i₀ σ) i₀
            * (faceSign F (insert i₀ σ) v * f ((insert i₀ σ).erase v)) = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero hzero
    rw [hleft, hright, Finset.sum_insert hi₀, Finset.erase_insert hi₀, mul_add, ← mul_assoc,
      faceSign_mul_self, one_mul, Finset.mul_sum]
    linear_combination hsum

/-- **Every cocycle on the full simplex is a coboundary.**  The cone homotopy at any base vertex
produces an explicit primitive. -/
theorem simplicialCoboundary_simplicialCone (i₀ : α) {f : Finset α → F}
    (hf : simplicialCoboundary F f = 0) :
    simplicialCoboundary F (simplicialCone F i₀ f) = f := by
  funext σ
  have h := simplicialCoboundary_simplicialCone_add (F := F) i₀ f σ
  rw [hf] at h
  have hzero : simplicialCone F i₀ (0 : Finset α → F) σ = 0 := by
    by_cases hi₀ : i₀ ∈ σ
    · exact simplicialCone_of_mem _ hi₀
    · rw [simplicialCone_of_notMem _ hi₀]
      exact mul_zero _
  rwa [hzero, add_zero] at h

/-- The cone homotopy lowers the cardinality degree by one. -/
theorem simplicialCone_mem_cardCochains {i₀ : α} {c : ℕ} {f : Finset α → F}
    (hf : f ∈ cardCochains F (c + 1)) : simplicialCone F i₀ f ∈ cardCochains F c := by
  intro σ hσ
  by_cases hi₀ : i₀ ∈ σ
  · exact simplicialCone_of_mem _ hi₀
  · rw [simplicialCone_of_notMem _ hi₀]
    have hcard : (insert i₀ σ).card ≠ c + 1 := by
      rw [Finset.card_insert_of_notMem hi₀]
      omega
    rw [hf _ hcard, mul_zero]

/-- The cone homotopy keeps the support inside a vertex set containing the base vertex. -/
theorem simplicialCone_support {i₀ : α} {A : Finset α} {f : Finset α → F}
    (hf : ∀ τ : Finset α, ¬ τ ⊆ A → f τ = 0) :
    ∀ τ : Finset α, ¬ τ ⊆ A → simplicialCone F i₀ f τ = 0 := by
  intro τ hτ
  by_cases hi : i₀ ∈ τ
  · exact simplicialCone_of_mem _ hi
  · rw [simplicialCone_of_notMem _ hi]
    have hsub : ¬ insert i₀ τ ⊆ A := by
      intro hcon
      exact hτ (fun x hx => hcon (Finset.mem_insert_of_mem hx))
    rw [hf _ hsub, mul_zero]

/-- **The monomial block contraction.**  On a nonempty vertex set `A`, every cocycle supported on
the `c+1`-subsets of `A` is the coboundary of a cochain supported on the `c`-subsets of `A`.  This
is the exactness of one full-simplex block of coordinate-facet descent, in every degree, including
the augmentation slot `c = 0`. -/
theorem fullSimplex_exact {A : Finset α} (hA : A.Nonempty) (c : ℕ) {f : Finset α → F}
    (hcard : f ∈ cardCochains F (c + 1)) (hsupp : ∀ τ : Finset α, ¬ τ ⊆ A → f τ = 0)
    (hf : simplicialCoboundary F f = 0) :
    ∃ h : Finset α → F, h ∈ cardCochains F c ∧ (∀ τ : Finset α, ¬ τ ⊆ A → h τ = 0)
      ∧ simplicialCoboundary F h = f := by
  obtain ⟨i₀, _⟩ := hA
  exact ⟨simplicialCone F i₀ f, simplicialCone_mem_cardCochains hcard,
    simplicialCone_support hsupp, simplicialCoboundary_simplicialCone i₀ hf⟩

/-- **The cone primitive works on the subsets of a prescribed vertex set.**  A cochain that is a
cocycle only on the subsets of `A` -- which is all the block differential sees -- is still the
coboundary of its cone primitive at any base vertex of `A`, on those subsets. -/
theorem simplicialCoboundary_simplicialCone_of_subset {A : Finset α} {i₀ : α} (hi₀ : i₀ ∈ A)
    {f : Finset α → F} (hf : ∀ σ : Finset α, σ ⊆ A → simplicialCoboundary F f σ = 0)
    {σ : Finset α} (hσ : σ ⊆ A) :
    simplicialCoboundary F (simplicialCone F i₀ f) σ = f σ := by
  have hid := simplicialCoboundary_simplicialCone_add (F := F) i₀ f σ
  by_cases hmem : i₀ ∈ σ
  · rwa [simplicialCone_of_mem _ hmem, add_zero] at hid
  · rw [simplicialCone_of_notMem _ hmem] at hid
    have hins : insert i₀ σ ⊆ A := Finset.insert_subset hi₀ hσ
    rw [hf _ hins, mul_zero, add_zero] at hid
    exact hid

/-- **The block contraction on a prescribed vertex set.**  A cochain that is a cocycle only on the
subsets of `A` -- which is all the coboundary of the block complex sees -- is still the coboundary
of its cone primitive on those subsets.  This is the form the monomial blocks of coordinate-facet
descent occur in, because the block differential is the ambient one restricted to subsets of `A`. -/
theorem fullSimplex_exact_on {A : Finset α} (hA : A.Nonempty) (c : ℕ) {f : Finset α → F}
    (hcard : f ∈ cardCochains F (c + 1)) (hsupp : ∀ τ : Finset α, ¬ τ ⊆ A → f τ = 0)
    (hf : ∀ σ : Finset α, σ ⊆ A → simplicialCoboundary F f σ = 0) :
    ∃ h : Finset α → F, h ∈ cardCochains F c ∧ (∀ τ : Finset α, ¬ τ ⊆ A → h τ = 0)
      ∧ ∀ σ : Finset α, σ ⊆ A → simplicialCoboundary F h σ = f σ := by
  obtain ⟨i₀, hi₀⟩ := hA
  exact ⟨simplicialCone F i₀ f, simplicialCone_mem_cardCochains hcard,
    simplicialCone_support hsupp,
    fun σ hσ => simplicialCoboundary_simplicialCone_of_subset hi₀ hf hσ⟩

end

end GaloisForLFunctions.HTGeometry
