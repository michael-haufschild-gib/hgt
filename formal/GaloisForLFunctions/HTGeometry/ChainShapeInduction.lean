import GaloisForLFunctions.HTGeometry.QuotientRegularSequence
import GaloisForLFunctions.HTGeometry.StarReduction
import GaloisForLFunctions.HTGeometry.ChainSimplexBase
import GaloisForLFunctions.HTGeometry.ChainGreedySucc
import GaloisForLFunctions.HTGeometry.ChainGreedyLeft
import GaloisForLFunctions.HTGeometry.ChainGreedyAdditive
import GaloisForLFunctions.HTGeometry.ChainInterval
import GaloisForLFunctions.HTGeometry.IrrelevantSideCondition

/-!
# The chain complex carries a regular sequence of its own dimension

Write `γ(A)` for the size of the greedy selection of `A`.  For a forced set `A` lying strictly to
the left of an interval `[k, N)` and separated from it, the complex of subsets `S ⊆ [k, N)` with
`γ(S ∪ A) ≤ r` carries a regular sequence, inside the irrelevant ideal, of length

```text
min (N − k) (2 (r − γ(A))).
```

The proof is a strong induction on `N − k` in which the recursion visits two shapes.  When the
interval is short — `N − k ≤ 2(r − γ(A))` — additivity of the greedy selection makes every subset a
face, the complex is a simplex, and its own variables are the sequence.  Otherwise shedding at `k`
replaces the complex by its deletion and its link:

```text
deletion :  the same forced set on [k+1, N)      shape I,  length min (N−k−1) (2d)   = 2d
link     :  forced set A ∪ {k} on [k+1, N)       shape II, length 1 + (2d − 2)       = 2d − 1
```

with `d = r − γ(A)`, and these are exactly the two lengths `exists_isRegular_shedding` consumes.
Shape II needs no shedding of its own: the vertex `k+1` sits one step past the greedy end of the
forced set, so it is a cone point and `exists_isRegular_cone` reduces it to shape I on `[k+2, N)`.

```text
HasRegSeq                    a regular sequence of a given length inside the irrelevant ideal
hasRegSeq_base               the short interval: a simplex, with its variables
hasRegSeq_zero               the empty sequence, when the budget is exhausted
isConePoint_chainForcedOn    a vertex one past the greedy end of the forced set is a cone point
hasRegSeq_shapeI             ** the induction **
```
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u v
variable {K : Type u} [Field K]

theorem X_mem_irrelevantIdeal (K : Type u) [Field K] {σ : Type v} (v : σ) :
    (X v : MvPolynomial σ K) ∈ irrelevantIdeal K σ :=
  Ideal.subset_span ⟨v, rfl⟩

theorem chainGreedy_singleton (k : ℕ) : chainGreedy {k} = {k} := by
  classical
  have hne : ({k} : Finset ℕ).Nonempty := ⟨k, Finset.mem_singleton_self k⟩
  rw [chainGreedy_eq_insert hne]
  have hmin : ({k} : Finset ℕ).min' hne = k := by
    simp [Finset.min'_eq_sorted_zero]
  rw [hmin]
  have hfil : ({k} : Finset ℕ).filter (fun y => k + 2 ≤ y) = ∅ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨rfl, h⟩
    omega
  rw [hfil, chainGreedy_empty]
  simp

theorem erase_intervalFinset {N k : ℕ} (hk : k < N) :
    (intervalFinset N k (N - k)).erase ⟨k, hk⟩ = intervalFinset N (k + 1) (N - (k + 1)) := by
  classical
  ext i
  rw [Finset.mem_erase, mem_intervalFinset, mem_intervalFinset]
  constructor
  · rintro ⟨hne, hlo, hhi⟩
    have hik : (i : ℕ) ≠ k := by
      intro h
      exact hne (Fin.ext h)
    have := i.isLt
    omega
  · rintro ⟨hlo, hhi⟩
    have := i.isLt
    refine ⟨?_, by omega, by omega⟩
    intro hcon
    rw [hcon] at hlo
    simp at hlo

theorem nonempty_chainForcedOn {N r : ℕ} {A V : Finset (Fin N)} (hA : IsChainFace N r A) :
    (chainForcedOn N r A V).Nonempty := by
  refine ⟨∅, ?_⟩
  rw [mem_chainForcedOn]
  exact ⟨Finset.empty_subset _, by rwa [Finset.empty_union]⟩

theorem image_insert_val {N : ℕ} (A : Finset (Fin N)) (v : Fin N) :
    (insert v A).image Fin.val = A.image Fin.val ∪ {(v : ℕ)} := by
  classical
  rw [Finset.image_insert]
  ext y
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  tauto

theorem chainGreedy_insert_of_sep {N : ℕ} {A : Finset (Fin N)} {v : Fin N}
    (hlt : ∀ a ∈ A, (a : ℕ) < (v : ℕ))
    (hsep : ∀ x ∈ chainGreedy (A.image Fin.val), x + 2 ≤ (v : ℕ)) :
    chainGreedy ((insert v A).image Fin.val)
      = chainGreedy (A.image Fin.val) ∪ {(v : ℕ)} := by
  classical
  rw [image_insert_val]
  rw [chainGreedy_union_of_sep _ _ ?_ ?_, chainGreedy_singleton]
  · intro a ha s hs
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    rw [Finset.mem_singleton] at hs
    subst hs
    exact hlt b hb
  · intro x hx s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    exact hsep x hx

theorem card_chainGreedy_insert_sep {N : ℕ} {A : Finset (Fin N)} {v : Fin N}
    (hlt : ∀ a ∈ A, (a : ℕ) < (v : ℕ))
    (hsep : ∀ x ∈ chainGreedy (A.image Fin.val), x + 2 ≤ (v : ℕ)) :
    (chainGreedy ((insert v A).image Fin.val)).card
      = (chainGreedy (A.image Fin.val)).card + 1 := by
  classical
  have hnot : (v : ℕ) ∉ chainGreedy (A.image Fin.val) := by
    intro hmem
    have := hsep _ hmem
    omega
  rw [chainGreedy_insert_of_sep hlt hsep, Finset.union_comm, Finset.singleton_union,
    Finset.card_insert_of_notMem hnot]

theorem mem_chainGreedy_insert {N : ℕ} {A : Finset (Fin N)} {v : Fin N}
    (hlt : ∀ a ∈ A, (a : ℕ) < (v : ℕ))
    (hsep : ∀ x ∈ chainGreedy (A.image Fin.val), x + 2 ≤ (v : ℕ)) :
    (v : ℕ) ∈ chainGreedy ((insert v A).image Fin.val) := by
  rw [chainGreedy_insert_of_sep hlt hsep]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- A vertex one step past the greedy end of the forced set is a cone point. -/
theorem isConePoint_chainForcedOn {N r : ℕ} {A V : Finset (Fin N)} {v : Fin N} {x : ℕ}
    (hvV : v ∈ V) (hxv : (v : ℕ) = x + 1) (hx : x ∈ chainGreedy (A.image Fin.val))
    (hAV : ∀ a ∈ A, ∀ s ∈ V, (a : ℕ) < (s : ℕ)) :
    IsConePoint (chainForcedOn N r A V) v := by
  classical
  intro S hS
  rw [mem_chainForcedOn] at hS ⊢
  refine ⟨Finset.insert_subset hvV hS.1, isChainFace_insert_succ hxv ?_ hS.2⟩
  have himg : (S ∪ A).image Fin.val = A.image Fin.val ∪ S.image Fin.val := by
    rw [Finset.image_union, Finset.union_comm]
  rw [himg]
  refine mem_chainGreedy_union_of_lt ?_ hx
  intro a ha s hs
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  exact hAV b hb t (hS.1 ht)

/-- A regular sequence of length `n`, inside the irrelevant ideal, on a Stanley–Reisner ring. -/
abbrev HasRegSeq (K : Type u) [Field K] {N : ℕ} (F : Finset (Finset (Fin N))) (n : ℕ) : Prop :=
  ∃ rs : List (MvPolynomial (Fin N) K), rs.length = n ∧
    (∀ x ∈ rs, x ∈ irrelevantIdeal K (Fin N)) ∧
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin N) K ⧸ faceFamilyIdeal K F) rs

/-- **The base case.**  When the remaining interval is short enough that every subset is a face, the
complex is a simplex and its own variables are the regular sequence. -/
theorem hasRegSeq_base {N r k : ℕ} {A : Finset (Fin N)} (hk : k ≤ N)
    (hlt : ∀ a ∈ A, (a : ℕ) < k)
    (hsep : ∀ x ∈ chainGreedy (A.image Fin.val), x + 2 ≤ k)
    (hshort : N - k ≤ 2 * (r - (chainGreedy (A.image Fin.val)).card))
    (hbudget : (chainGreedy (A.image Fin.val)).card ≤ r) :
    HasRegSeq K (chainForcedOn N r A (intervalFinset N k (N - k))) (N - k) := by
  classical
  have hlt' : ∀ a ∈ A, ∀ s ∈ (intervalFinset N k (N - k)), (a : ℕ) < (s : ℕ) := by
    intro a ha s hs
    have := (mem_intervalFinset.mp hs).1
    have := hlt a ha
    omega
  have hsep' : ∀ x ∈ chainGreedy (A.image Fin.val), ∀ s ∈ (intervalFinset N k (N - k)),
      x + 2 ≤ (s : ℕ) := by
    intro x hx s hs
    have := (mem_intervalFinset.mp hs).1
    have := hsep x hx
    omega
  rw [chainForcedOn_eq_powerset_of_short hlt' hsep' hshort hbudget]
  refine ⟨(intervalFinset N k (N - k)).toList.map X, ?_, ?_, isRegular_powerset _⟩
  · rw [List.length_map, Finset.length_toList, card_intervalFinset (by omega)]
  · intro x hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx
    exact X_mem_irrelevantIdeal K v

theorem hasRegSeq_zero {N : ℕ} {F : Finset (Finset (Fin N))} (hne : F.Nonempty) :
    HasRegSeq K F 0 := by
  refine ⟨[], rfl, by simp, ⟨⟨fun i hi => absurd hi (by simp)⟩, ?_⟩⟩
  intro htop
  have hlt := smul_top_lt_top_faceFamily (σ := Fin N) K hne
  rw [show (Ideal.ofList ([] : List (MvPolynomial (Fin N) K))) = ⊥ by simp [Ideal.ofList],
    Submodule.bot_smul] at htop
  exact absurd (le_antisymm le_top (htop.le.trans bot_le)) (ne_of_lt hlt)

/-- **Shape I of the Cohen–Macaulay recursion.**  On the chain complex forced by `A` and restricted
to the interval `[k, N)`, there is a regular sequence inside the irrelevant ideal of length
`min (N − k) (2 (r − γ(A)))`.  The proof is a strong induction on `N − k`: when the interval is
short every subset is a face and the variables themselves are the sequence; otherwise shedding at
`k` reduces to the deletion (shape I on `[k+1, N)`, one longer) and the link (shape II on
`[k+1, N)`, one shorter), and shape II is a cone over shape I on `[k+2, N)`. -/
theorem hasRegSeq_shapeI (K : Type u) [Field K] {N r : ℕ} :
    ∀ m k : ℕ, N - k = m → k ≤ N → ∀ A : Finset (Fin N),
      (∀ a ∈ A, (a : ℕ) < k) →
      (∀ x ∈ chainGreedy (A.image Fin.val), x + 2 ≤ k) →
      (chainGreedy (A.image Fin.val)).card ≤ r →
      HasRegSeq K (chainForcedOn N r A (intervalFinset N k (N - k)))
        (min (N - k) (2 * (r - (chainGreedy (A.image Fin.val)).card))) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro k hm hk A hlt hsep hbudget
    classical
    by_cases hshort : N - k ≤ 2 * (r - (chainGreedy (A.image Fin.val)).card)
    · rw [min_eq_left hshort]
      exact hasRegSeq_base hk hlt hsep hshort hbudget
    rw [not_le] at hshort
    rw [min_eq_right hshort.le]
    have hAface : IsChainFace N r A := (isChainFace_iff_card_chainGreedy A).mpr hbudget
    by_cases hd : r - (chainGreedy (A.image Fin.val)).card = 0
    · rw [hd, Nat.mul_zero]
      exact hasRegSeq_zero (nonempty_chainForcedOn hAface)
    have hge : 1 ≤ r - (chainGreedy (A.image Fin.val)).card := Nat.one_le_iff_ne_zero.mpr hd
    have hkN : k < N := by omega
    have hk1N : k + 1 < N := by omega
    have hvV : (⟨k, hkN⟩ : Fin N) ∈ intervalFinset N k (N - k) := by
      rw [mem_intervalFinset]
      exact ⟨le_rfl, by simp; omega⟩
    have hltv : ∀ a ∈ A, (a : ℕ) < ((⟨k, hkN⟩ : Fin N) : ℕ) := hlt
    have hsepv : ∀ x ∈ chainGreedy (A.image Fin.val), x + 2 ≤ ((⟨k, hkN⟩ : Fin N) : ℕ) := hsep
    have hA'card : (chainGreedy ((insert (⟨k, hkN⟩ : Fin N) A).image Fin.val)).card
        = (chainGreedy (A.image Fin.val)).card + 1 := card_chainGreedy_insert_sep hltv hsepv
    have hA'face : IsChainFace N r (insert (⟨k, hkN⟩ : Fin N) A) :=
      (isChainFace_iff_card_chainGreedy _).mpr (by rw [hA'card]; omega)
    have hsub : r - ((chainGreedy (A.image Fin.val)).card + 1)
        = r - (chainGreedy (A.image Fin.val)).card - 1 := by rw [Nat.sub_sub]
    have hdel_eq : faceDeletion (chainForcedOn N r A (intervalFinset N k (N - k)))
          (⟨k, hkN⟩ : Fin N)
        = chainForcedOn N r A (intervalFinset N (k + 1) (N - (k + 1))) := by
      rw [faceDeletion_chainForcedOn, erase_intervalFinset hkN]
    have hlk_eq : faceLink (chainForcedOn N r A (intervalFinset N k (N - k))) (⟨k, hkN⟩ : Fin N)
        = chainForcedOn N r (insert (⟨k, hkN⟩ : Fin N) A)
            (intervalFinset N (k + 1) (N - (k + 1))) := by
      rw [faceLink_chainForcedOn N r A _ hvV, erase_intervalFinset hkN]
    -- the deletion: shape I one step to the right, of the full length
    have hDel : HasRegSeq K (chainForcedOn N r A (intervalFinset N (k + 1) (N - (k + 1))))
        (2 * (r - (chainGreedy (A.image Fin.val)).card)) := by
      have h := ih (N - (k + 1)) (by omega) (k + 1) rfl (by omega) A
        (fun a ha => by have := hlt a ha; omega)
        (fun x hx => by have := hsep x hx; omega) hbudget
      rwa [min_eq_right (by omega :
        2 * (r - (chainGreedy (A.image Fin.val)).card) ≤ N - (k + 1))] at h
    -- the link: shape II one step to the right, a cone over shape I two steps to the right
    have hLink : HasRegSeq K (chainForcedOn N r (insert (⟨k, hkN⟩ : Fin N) A)
          (intervalFinset N (k + 1) (N - (k + 1))))
        (2 * (r - (chainGreedy (A.image Fin.val)).card) - 1) := by
      have hInner := ih (N - (k + 1 + 1)) (by omega) (k + 1 + 1) rfl (by omega)
        (insert (⟨k, hkN⟩ : Fin N) A)
        (fun a ha => by
          rcases Finset.mem_insert.mp ha with rfl | ha'
          · simp
          · have := hlt a ha'; omega)
        (fun x hx => by
          rw [chainGreedy_insert_of_sep hltv hsepv] at hx
          rcases Finset.mem_union.mp hx with hx' | hx'
          · have := hsep x hx'; omega
          · rw [Finset.mem_singleton] at hx'; subst hx'; simp)
        (by rw [hA'card]; omega)
      rw [hA'card] at hInner
      rw [min_eq_right (by rw [hsub]; omega :
        2 * (r - ((chainGreedy (A.image Fin.val)).card + 1)) ≤ N - (k + 1 + 1))] at hInner
      have hcp : IsConePoint (chainForcedOn N r (insert (⟨k, hkN⟩ : Fin N) A)
          (intervalFinset N (k + 1) (N - (k + 1)))) (⟨k + 1, hk1N⟩ : Fin N) :=
        isConePoint_chainForcedOn (r := r) (x := k)
          (by rw [mem_intervalFinset]; exact ⟨le_rfl, by simp; omega⟩) rfl
          (mem_chainGreedy_insert hltv hsepv)
          (fun a ha s hs => by
            rw [mem_intervalFinset] at hs
            rcases Finset.mem_insert.mp ha with rfl | ha'
            · simp only []; omega
            · have := hlt a ha'; omega)
      have hdel2 : HasRegSeq K (faceDeletion (chainForcedOn N r (insert (⟨k, hkN⟩ : Fin N) A)
            (intervalFinset N (k + 1) (N - (k + 1)))) (⟨k + 1, hk1N⟩ : Fin N))
          (2 * (r - ((chainGreedy (A.image Fin.val)).card + 1))) := by
        rw [faceDeletion_chainForcedOn, erase_intervalFinset hk1N]
        exact hInner
      have hcone := exists_isRegular_cone K
        (isFaceFamily_chainForcedOn N r (insert (⟨k, hkN⟩ : Fin N) A)
          (intervalFinset N (k + 1) (N - (k + 1))))
        hcp (irrelevantIdeal K (Fin N))
        (X_mem_irrelevantIdeal K (⟨k + 1, hk1N⟩ : Fin N)) hdel2
      obtain ⟨rs, hlen, hmem, hreg⟩ := hcone
      exact ⟨rs, by rw [hsub] at hlen; omega, hmem, hreg⟩
    -- shedding at k
    have hStarNe : (faceStar (chainForcedOn N r A (intervalFinset N k (N - k)))
        (⟨k, hkN⟩ : Fin N)).Nonempty := by
      refine ⟨∅, ?_⟩
      rw [mem_faceStar]
      constructor
      · rw [mem_chainForcedOn]
        exact ⟨Finset.empty_subset _, by rwa [Finset.empty_union]⟩
      · rw [mem_chainForcedOn]
        refine ⟨by simpa using hvV, ?_⟩
        rw [Finset.insert_union, Finset.empty_union]
        exact hA'face
    have hshed := exists_isRegular_shedding K
      (isFaceFamily_chainForcedOn N r A (intervalFinset N k (N - k))) (⟨k, hkN⟩ : Fin N)
      (irrelevantIdeal K (Fin N)) (X_mem_irrelevantIdeal K (⟨k, hkN⟩ : Fin N))
      (n₀ := 2 * (r - (chainGreedy (A.image Fin.val)).card) - 1)
      (by rw [hdel_eq]; exact smul_top_lt_top_faceFamily K (nonempty_chainForcedOn hAface))
      (smul_top_lt_top_faceFamily K hStarNe)
      (by rw [hlk_eq]; exact smul_top_lt_top_faceFamily K (nonempty_chainForcedOn hA'face))
      (smul_top_lt_top_faceFamily K (nonempty_chainForcedOn hAface))
      (by
        rw [hdel_eq]
        obtain ⟨rs, hlen, hmem, hreg⟩ := hDel
        exact ⟨rs, by omega, hmem, hreg⟩)
      (by
        rw [hlk_eq]
        exact hLink)
    obtain ⟨rs, hlen, hmem, hreg⟩ := hshed
    exact ⟨rs, by omega, hmem, hreg⟩

end GaloisForLFunctions.HTGeometry
