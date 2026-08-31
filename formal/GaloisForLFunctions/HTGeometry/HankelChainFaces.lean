import GaloisForLFunctions.HTGeometry.HankelStandardMonomials

/-!
# The faces of the Hankel chain complex have exactly `2r` vertices

The standard monomials of the Hankel secant degeneration are the chain-reduced exponents, and the
chain-reduced supports are the faces of the simplicial complex

```text
Δ_r = { S : S contains no r+1 elements pairwise at distance at least two } .
```

Both bounds on the face size are proved here.

```text
card_support_le_two_mul_of_chainReduced          |S| ≤ 2r, from the r-colouring: each colour class
                                                 lies on two consecutive indices
card_support_le_two_mul_of_finiteChainReduced    the same for finitely many variables
card_le_of_pairwise_chainAdj                     halving is injective on a 2-separated set
finiteHankelChainReduced_initialSegment          ** {0, …, 2r-1} is a face **
card_support_initialSegmentExponent              and it has 2r vertices
```

So `dim Δ_r = 2r - 1` and the Stanley–Reisner ring of the degeneration has Krull dimension `2r` —
the card's dimension count `(11)`, on the monomial side.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

/-- **A chain-reduced exponent has at most `2r` variables.**  A proper `r`-coloring of its support
splits it into `r` pieces, each supported on two consecutive indices. -/
theorem card_support_le_two_mul_of_chainReduced {r : ℕ} {e : ℕ →₀ ℕ}
    (hred : HankelChainReduced r e) : e.support.card ≤ 2 * r := by
  classical
  let D := hankelAdjacentDecompositionOfReduced hred
  have hpart : ∀ j : Fin r, (D.part j).support.card ≤ 2 := by
    intro j
    obtain ⟨q, hq⟩ := D.supported_adjacent j
    have hsub : (D.part j).support ⊆ ({q, q + 1} : Finset ℕ) := by
      intro i hi
      have := hq i (Finsupp.mem_support_iff.mp hi)
      simpa using this
    exact le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_insert_le _ _) (by simp))
  have hsub : e.support ⊆ Finset.biUnion Finset.univ (fun j : Fin r => (D.part j).support) := by
    intro i hi
    rw [Finset.mem_biUnion]
    by_contra hcon
    push Not at hcon
    have hzero : e i = 0 := by
      rw [← D.sum_part, Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := hcon j (Finset.mem_univ j)
      simpa [Finsupp.mem_support_iff] using this
    exact (Finsupp.mem_support_iff.mp hi) hzero
  calc e.support.card
      ≤ (Finset.biUnion Finset.univ (fun j : Fin r => (D.part j).support)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ j : Fin r, (D.part j).support.card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin r, 2 := Finset.sum_le_sum fun j _ => hpart j
    _ = 2 * r := by simp [mul_comm]

theorem card_support_le_two_mul_of_finiteChainReduced {N r : ℕ} {e : Fin N →₀ ℕ}
    (hred : FiniteHankelChainReduced N r e) : e.support.card ≤ 2 * r := by
  classical
  have hcard : (Finsupp.mapDomain Fin.val e).support.card = e.support.card := by
    rw [Finsupp.mapDomain_support_of_injective Fin.val_injective,
      Finset.card_image_of_injective _ Fin.val_injective]
  rw [← hcard]
  exact card_support_le_two_mul_of_chainReduced hred

/-- **A `2`-separated subset of an initial segment is small.**  Halving is injective on a set whose
elements are pairwise at distance at least two. -/
theorem card_le_of_pairwise_chainAdj {J : Finset ℕ} {M : ℕ}
    (hJ : (↑J : Set ℕ).Pairwise hankelChainGraph.Adj)
    (hbound : ∀ i ∈ J, i < 2 * M) : J.card ≤ M := by
  classical
  have h1 : J.card ≤ (Finset.range M).card := by
    refine Finset.card_le_card_of_injOn (fun i => i / 2) ?_ ?_
    · intro i hi
      have hi2 := hbound i hi
      have : i / 2 < M := by omega
      simpa using Finset.mem_range.mpr this
    · intro a ha b hb hab
      simp only at hab
      by_contra hne
      have hadj := hJ ha hb hne
      change a + 1 < b ∨ b + 1 < a at hadj
      omega
  rwa [Finset.card_range] at h1

/-- The squarefree exponent supported on the first `k` variables. -/
noncomputable def initialSegmentExponent (N k : ℕ) : Fin N →₀ ℕ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), Finsupp.single i 1

@[simp] theorem initialSegmentExponent_apply (N k : ℕ) (i : Fin N) :
    initialSegmentExponent N k i = if (i : ℕ) < k then 1 else 0 := by
  classical
  rw [initialSegmentExponent, Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply, Finset.sum_ite_eq']

theorem support_initialSegmentExponent (N k : ℕ) :
    (initialSegmentExponent N k).support
      = Finset.univ.filter (fun i : Fin N => (i : ℕ) < k) := by
  classical
  ext i
  simp [Finsupp.mem_support_iff]

/-- **The first `2r` variables form a face**: their squarefree monomial is chain-reduced.  With
`card_support_le_two_mul_of_finiteChainReduced` this pins the maximal face size at `2r`, which is
the card's dimension count `(11)`. -/
theorem finiteHankelChainReduced_initialSegment (N r : ℕ) :
    FiniteHankelChainReduced N r (initialSegmentExponent N (2 * r)) := by
  classical
  rintro ⟨J, hcard, hpair, hsub⟩
  have hb : ∀ i ∈ J, i < 2 * r := by
    intro i hi
    have hmem := hsub hi
    rw [Finsupp.mapDomain_support_of_injective Fin.val_injective] at hmem
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hmem
    rw [support_initialSegmentExponent, Finset.mem_filter] at hi'
    exact hi'.2
  have := card_le_of_pairwise_chainAdj hpair hb
  omega

theorem card_support_initialSegmentExponent (N r : ℕ) (h : 2 * r ≤ N) :
    (initialSegmentExponent N (2 * r)).support.card = 2 * r := by
  classical
  rw [support_initialSegmentExponent]
  have himg : Finset.univ.filter (fun i : Fin N => (i : ℕ) < 2 * r)
      = Finset.image (Fin.castLE h) Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨i, hi⟩, by ext; simp⟩
    · rintro ⟨j, rfl⟩
      simp
  rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective h), Finset.card_univ,
    Fintype.card_fin]

end GaloisForLFunctions.HTGeometry
