import GaloisForLFunctions.HTGeometry.ChainForcedOn

/-!
# Intervals are the maximal faces of the chain complex

An interval of length `L` has `⌈L/2⌉` pairwise `2`-separated elements, so it is a face of `Δ_r`
exactly when `L ≤ 2r`.  Since the largest face has `2r` vertices
(`card_le_two_mul_of_isChainFace`), the interval of length `2r` is a maximal face — and being an
interval it starts at whatever vertex one likes, in particular at the least available one.

```text
card_le_of_pairwise_chainAdj_interval   a 2-separated subset of an interval of length 2M has ≤ M
                                        elements (halving after shifting to the origin)
intervalFinset N a L                    the interval [a, a+L) of variables
isChainFace_intervalFinset              ** an interval of length ≤ 2r is a face **
card_intervalFinset                     it has L vertices
mem_chainForcedOn_intervalFinset        and it is a face of the complex on itself
```

This is the dimension input the shedding condition needs: the maximum face can be taken to be an
*initial* interval of the available vertices, so it contains the least available vertex — which the
naive exchange argument could not deliver.
-/

namespace GaloisForLFunctions.HTGeometry

open RHTower

/-- **A `2`-separated subset of an interval of length `2M` has at most `M` elements.**  Halving,
after shifting to the origin, is injective on such a set. -/
theorem card_le_of_pairwise_chainAdj_interval {J : Finset ℕ} {a M : ℕ}
    (hJ : (↑J : Set ℕ).Pairwise hankelChainGraph.Adj)
    (hlo : ∀ i ∈ J, a ≤ i) (hhi : ∀ i ∈ J, i < a + 2 * M) : J.card ≤ M := by
  classical
  have h1 : J.card ≤ (Finset.range M).card := by
    refine Finset.card_le_card_of_injOn (fun i => (i - a) / 2) ?_ ?_
    · intro i hi
      have h2 := hlo i hi
      have h3 := hhi i hi
      have : (i - a) / 2 < M := by omega
      simpa using Finset.mem_range.mpr this
    · intro x hx y hy hxy
      simp only at hxy
      have hx1 := hlo x hx
      have hy1 := hlo y hy
      by_contra hne
      have hadj := hJ hx hy hne
      change x + 1 < y ∨ y + 1 < x at hadj
      omega
  rwa [Finset.card_range] at h1

/-- The interval `[a, a+L)` of variables. -/
noncomputable def intervalFinset (N a L : ℕ) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun i : Fin N => a ≤ (i : ℕ) ∧ (i : ℕ) < a + L)

theorem mem_intervalFinset {N a L : ℕ} {i : Fin N} :
    i ∈ intervalFinset N a L ↔ a ≤ (i : ℕ) ∧ (i : ℕ) < a + L := by
  classical
  simp [intervalFinset]

/-- **An interval of length at most `2r` is a face of the chain complex.** -/
theorem isChainFace_intervalFinset (N r a L : ℕ) (hL : L ≤ 2 * r) :
    IsChainFace N r (intervalFinset N a L) := by
  classical
  rintro ⟨J, hcard, hpair, hsub⟩
  have hlo : ∀ i ∈ J, a ≤ i := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hsub hi)
    exact (mem_intervalFinset.mp hj).1
  have hhi : ∀ i ∈ J, i < a + 2 * r := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hsub hi)
    have := (mem_intervalFinset.mp hj).2
    omega
  have := card_le_of_pairwise_chainAdj_interval hpair hlo hhi
  omega

theorem card_intervalFinset {N a L : ℕ} (h : a + L ≤ N) :
    (intervalFinset N a L).card = L := by
  classical
  have hbij : intervalFinset N a L
      = Finset.image (fun j : Fin L => (⟨a + (j : ℕ), by have := j.isLt; omega⟩ : Fin N))
        Finset.univ := by
    ext i
    rw [mem_intervalFinset, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨(i : ℕ) - a, by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp only
      omega
    · rintro ⟨j, -, rfl⟩
      have := j.isLt
      simp only
      omega
  rw [hbij, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro x y hxy
  apply Fin.ext
  have := congrArg Fin.val hxy
  simpa using this

/-- **The initial interval of length `min (N) (2r)` is a face of the plain chain complex.** -/
theorem mem_chainForcedOn_intervalFinset (N r a L : ℕ) (hL : L ≤ 2 * r) :
    intervalFinset N a L ∈ chainForcedOn N r ∅ (intervalFinset N a L) := by
  rw [mem_chainForcedOn]
  refine ⟨subset_refl _, ?_⟩
  rw [Finset.union_empty]
  exact isChainFace_intervalFinset N r a L hL


end GaloisForLFunctions.HTGeometry
