import GaloisForLFunctions.HTGeometry.RegularSequenceBridge
import GaloisForLFunctions.HTGeometry.DepthLemma
import Mathlib.RingTheory.Depth.Rees

/-!
# Depth by `Ext`-vanishing, in the corpus's vocabulary

Mathlib's Rees theorem `ModuleCat.exists_isRegular_tfae` equates, for a Noetherian ring, an ideal
`I` and a finitely generated `M` with `I • ⊤ < ⊤`, the vanishing of `Ext^i(R/I, M)` for `i < n` with
the existence of an `M`-regular sequence of length `n` inside `I`.  Specialised to `M = R` and
translated through `isRingRegularSeq_iff_isRegular`:

```text
exists_isRegular_of_ext, ext_subsingleton_of_isRegular      the two directions, for modules
smul_top_lt_top_of_ne_top                                   the hypothesis for M = R
exists_isRingRegularSeq_of_ext
    ** Ext-vanishing ⟹ a ring-regular sequence of length n inside I **
ext_subsingleton_of_isRingRegularSeq
    ** and back **
```

This is step 2 of the route recorded on the Hankel card.  Together with `DepthLemma.lean` (step 3)
and `MayerVietorisShortExact.lean` (step 1), the chain

```text
regular sequences on K[del(v)] and K[lk(v)]
  → Ext-vanishing                       (this file)
  → Ext-vanishing for K[Δ]              (the depth lemma, along the Mayer–Vietoris sequence)
  → a regular sequence on K[Δ]          (this file, back again)
```

is complete as a chain of available theorems.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory CategoryTheory.Abelian ModuleCat

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- **Rees, in the direction that produces a regular sequence.** -/
theorem exists_isRegular_of_ext (I : Ideal R) (n : ℕ) (M : ModuleCat.{u} R) [Module.Finite R M]
    (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (h : ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{u} (R ⧸ I))) M i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs :=
  ((ModuleCat.exists_isRegular_tfae I n M smul_lt).out 1 3).mp h

/-- **Rees, in the direction that produces `Ext`-vanishing.** -/
theorem ext_subsingleton_of_isRegular (I : Ideal R) (n : ℕ) (M : ModuleCat.{u} R)
    [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (h : ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs) :
    ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{u} (R ⧸ I))) M i) :=
  ((ModuleCat.exists_isRegular_tfae I n M smul_lt).out 3 1).mp h

omit [IsNoetherianRing R] in
theorem smul_top_lt_top_of_ne_top {I : Ideal R} (hI : I ≠ ⊤) :
    I • (⊤ : Submodule R (ModuleCat.of R R)) < ⊤ := by
  have hEq : I • (⊤ : Submodule R R) = I := by simp
  refine lt_of_le_of_ne le_top ?_
  intro hcon
  exact hI (by rw [← hEq, hcon])

/-- **Step 2 in the corpus's own vocabulary.**  `Ext`-vanishing produces a ring-regular sequence
inside the ideal. -/
theorem exists_isRingRegularSeq_of_ext (I : Ideal R) (n : ℕ) (hI : I ≠ ⊤)
    (h : ∀ i < n,
      Subsingleton (Ext (ModuleCat.of R (Shrink.{u} (R ⧸ I))) (ModuleCat.of R R) i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRingRegularSeq rs := by
  obtain ⟨rs, hlen, hmem, hreg⟩ :=
    exists_isRegular_of_ext I n (ModuleCat.of R R) (smul_top_lt_top_of_ne_top hI) h
  exact ⟨rs, hlen, hmem, (isRingRegularSeq_iff_isRegular rs).mpr hreg⟩

/-- And back. -/
theorem ext_subsingleton_of_isRingRegularSeq (I : Ideal R) (n : ℕ) (hI : I ≠ ⊤)
    (h : ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRingRegularSeq rs) :
    ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{u} (R ⧸ I))) (ModuleCat.of R R) i) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h
  exact ext_subsingleton_of_isRegular I n (ModuleCat.of R R) (smul_top_lt_top_of_ne_top hI)
    ⟨rs, hlen, hmem, (isRingRegularSeq_iff_isRegular rs).mp hreg⟩


end GaloisForLFunctions.HTGeometry
