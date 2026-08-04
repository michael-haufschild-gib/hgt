import GaloisForLFunctions.RHTower.DeningerHornCocycleWitness

/-!
# All edges of a horn of a large simplex

A simplex with at least four vertices has, for any two of its vertices, a third avoiding them and the
horn index, so every edge lies in the horn.  The element assigned to a degenerate edge is trivial,
because the cocycle identity applied to one vertex three times says it is its own square.

* `deningerEdgeOf_mem_horn_of_three` : every edge lies in the horn.
* `deningerHornEdgeElt_refl` : a degenerate edge carries the identity.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

variable {G : Type u} [Group G] {m : ℕ} {i : Fin (m + 1)}

/-- **Every edge lies in the horn** when the simplex has at least four vertices. -/
theorem deningerEdgeOf_mem_horn_of_three (hm : 3 ≤ m) (i : Fin (m + 1)) {a b : Fin (m + 1)}
    (h : a ≤ b) : deningerStdEdgeOf.{u} h ∈ (horn.{u} m i).obj (op (mk 1)) := by
  obtain ⟨t, ht, hti, hta, htb⟩ :
      ∃ t : ℕ, t < m + 1 ∧ t ≠ (i : ℕ) ∧ t ≠ (a : ℕ) ∧ t ≠ (b : ℕ) := by
    by_contra hcon
    push Not at hcon
    have h0 := hcon 0 (by omega)
    have h1 := hcon 1 (by omega)
    have h2 := hcon 2 (by omega)
    have h3 := hcon 3 (by omega)
    omega
  exact deningerEdgeOf_mem_horn i h ⟨t, ht⟩ (fun hc => hti (congrArg Fin.val hc))
    (fun hc => hta (congrArg Fin.val hc)) (fun hc => htb (congrArg Fin.val hc))

/-- **A degenerate edge carries the identity.** -/
theorem deningerHornEdgeElt_refl (hm : 2 ≤ m) (u : (horn.{u} m i).toSSet ⟶ deningerClassifying G)
    (a : Fin (m + 1)) (ma : deningerStdEdgeOf.{u} (le_refl a) ∈ (horn.{u} m i).obj (op (mk 1))) :
    deningerEdgeElt u ⟨deningerStdEdgeOf (le_refl a), ma⟩ = 1 := by
  obtain ⟨t, ht, hti, hta⟩ : ∃ t : ℕ, t < m + 1 ∧ t ≠ (i : ℕ) ∧ t ≠ (a : ℕ) := by
    by_contra hcon
    push Not at hcon
    have h0 := hcon 0 (by omega)
    have h1 := hcon 1 (by omega)
    have h2 := hcon 2 (by omega)
    omega
  have hcyc := deningerHornEdgeElt_comp u (le_refl a) (le_refl a) ⟨t, ht⟩
    (fun hc => hti (congrArg Fin.val hc)) (fun hc => hta (congrArg Fin.val hc))
    (fun hc => hta (congrArg Fin.val hc)) (fun hc => hta (congrArg Fin.val hc))
  have hself : deningerEdgeElt u ⟨deningerStdEdgeOf (le_refl a), ma⟩ =
      deningerEdgeElt u ⟨deningerStdEdgeOf (le_refl a), ma⟩ *
        deningerEdgeElt u ⟨deningerStdEdgeOf (le_refl a), ma⟩ := hcyc
  exact right_eq_mul.mp hself

end RHTower
