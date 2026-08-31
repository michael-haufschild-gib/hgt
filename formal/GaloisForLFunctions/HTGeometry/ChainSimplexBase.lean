import GaloisForLFunctions.HTGeometry.ChainGreedyAdditive
import GaloisForLFunctions.HTGeometry.IrrelevantSideCondition

/-!
# The base case of the recursion: the complex is a simplex

When the remaining budget covers the whole available interval, every subset of it is a face —
additivity of the greedy count gives `γ(S ∪ A) = γ(A) + γ(S) ≤ γ(A) + ⌈|S|/2⌉ ≤ r` — so the complex
is the full simplex there and its coordinate ring is a polynomial ring on the available variables.

```text
faceFamilyIdeal_powerset            ** the ideal of a simplex is the coordinate ideal of the
                                       complement **
isFaceFamily_powerset               a powerset is a face family
chainForcedOn_eq_powerset           the criterion
chainForcedOn_eq_powerset_of_short  ** N − k ≤ 2(r − γ(A)) ⟹ the complex is a simplex **
ringKrullDim_faceFamilyIdeal_powerset   its dimension is the number of vertices
```

With `quotientSpanXImageEquiv` the quotient is `MvPolynomial (available) K`, and the regular
sequence of the base case is the available variables themselves.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

/-- **The Stanley–Reisner ideal of a full simplex is the coordinate ideal of the complement.** -/
theorem faceFamilyIdeal_powerset (K : Type u) [Field K] (V : Finset σ) :
    faceFamilyIdeal K V.powerset = Ideal.span (X '' (↑(Vᶜ) : Set σ)) := by
  classical
  refine le_antisymm ?_ ?_
  · exact Finset.inf_le (Finset.mem_powerset.mpr (subset_refl V))
  · refine Finset.le_inf ?_
    intro S hS
    refine Ideal.span_mono (Set.image_mono ?_)
    intro x hx
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hx ⊢
    exact fun hxS => hx (Finset.mem_powerset.mp hS hxS)

omit [Fintype σ] [DecidableEq σ] in
theorem isFaceFamily_powerset (V : Finset σ) : IsFaceFamily V.powerset := by
  intro S T hT hST
  rw [Finset.mem_powerset] at hT ⊢
  exact hST.trans hT

/-- When every subset of the available set is a face, the complex is the full simplex on it. -/
theorem chainForcedOn_eq_powerset {N r : ℕ} {A V : Finset (Fin N)}
    (h : ∀ S ⊆ V, IsChainFace N r (S ∪ A)) :
    chainForcedOn N r A V = V.powerset := by
  classical
  ext S
  rw [mem_chainForcedOn, Finset.mem_powerset]
  exact ⟨fun hS => hS.1, fun hS => ⟨hS, h S hS⟩⟩

/-- The dimension of a full simplex is its number of vertices. -/
theorem ringKrullDim_faceFamilyIdeal_powerset (K : Type u) [Field K] (V : Finset σ) :
    ringKrullDim (MvPolynomial σ K ⧸ faceFamilyIdeal K V.powerset) = ((V.card : ℕ) : ℕ∞) := by
  classical
  refine ringKrullDim_faceFamilyIdeal K (D := V.card) ?_ ?_ rfl
  · intro S hS
    exact Finset.card_le_card (Finset.mem_powerset.mp hS)
  · exact Finset.mem_powerset.mpr (subset_refl V)

/-- **The base case of the recursion.**  When the remaining budget covers the whole available
interval, every subset is a face — additivity of the greedy count makes
`γ(S ∪ A) = γ(A) + γ(S) ≤ γ(A) + ⌈|S|/2⌉ ≤ r` — so the complex is a simplex and its coordinate ring
is a polynomial ring on the available variables. -/
theorem chainForcedOn_eq_powerset_of_short {N r k : ℕ} {A : Finset (Fin N)}
    (hlt : ∀ a ∈ A, ∀ s ∈ (intervalFinset N k (N - k)), (a : ℕ) < (s : ℕ))
    (hsep : ∀ x ∈ chainGreedy (A.image Fin.val), ∀ s ∈ (intervalFinset N k (N - k)),
      x + 2 ≤ (s : ℕ))
    (hshort : N - k ≤ 2 * (r - (chainGreedy (A.image Fin.val)).card))
    (hbudget : (chainGreedy (A.image Fin.val)).card ≤ r) :
    chainForcedOn N r A (intervalFinset N k (N - k))
      = (intervalFinset N k (N - k)).powerset := by
  classical
  refine chainForcedOn_eq_powerset ?_
  intro S hS
  rw [isChainFace_iff_card_chainGreedy]
  have himg : (S ∪ A).image Fin.val = A.image Fin.val ∪ S.image Fin.val := by
    rw [Finset.image_union]
    exact Finset.union_comm _ _
  rw [himg, card_chainGreedy_union_of_sep ?_ ?_]
  · have hSint : ∀ i ∈ S, k ≤ (i : ℕ) ∧ (i : ℕ) < N := by
      intro i hi
      have := mem_intervalFinset.mp (hS hi)
      have hlt := i.isLt
      exact ⟨this.1, hlt⟩
    have hbound : (chainGreedy (S.image Fin.val)).card
        ≤ r - (chainGreedy (A.image Fin.val)).card := by
      refine card_le_of_pairwise_chainAdj_interval (a := k)
        (M := r - (chainGreedy (A.image Fin.val)).card) (chainGreedy_pairwise _) ?_ ?_
      · intro i hi
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp (chainGreedy_subset _ hi)
        exact (hSint i' hi').1
      · intro i hi
        obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp (chainGreedy_subset _ hi)
        have := (hSint i' hi').2
        omega
    omega
  · intro a ha s hs
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    exact hlt a' ha' s' (hS hs')
  · intro x hx s hs
    obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
    exact hsep x hx s' (hS hs')


end GaloisForLFunctions.HTGeometry
