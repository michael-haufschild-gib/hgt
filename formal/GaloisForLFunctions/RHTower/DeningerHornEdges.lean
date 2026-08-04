import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# Edges of a horn

A simplex of the standard simplex lies in the `i`-th horn exactly when some vertex avoids both its
image and `i`.  For the edge joining consecutive vertices `k` and `k+1` that is a condition on three
vertices, so every edge of the spine lies in the horn as soon as the simplex has at least four
vertices, and for three vertices as soon as the horn is inner.

* `deningerEdge_mem_horn` : the membership criterion for a spine edge.
* `deningerEdge_mem_horn_of_four`, `deningerEdge_mem_horn_of_inner` : the two cases.
-/

namespace RHTower

open CategoryTheory SSet SimplexCategory Opposite

universe u

/-- The `k`-th edge of the standard simplex. -/
def deningerStdEdge {m : ℕ} (k : Fin m) :
    (stdSimplex.{u}.obj (mk m)).obj (op (mk 1)) :=
  stdSimplex.objEquiv.symm (mkOfSucc k)

/-- **A spine edge lies in the horn** as soon as some vertex avoids its two endpoints and the horn
index. -/
theorem deningerEdge_mem_horn {m : ℕ} (i : Fin (m + 1)) (k : Fin m) (j : Fin (m + 1))
    (hji : (j : ℕ) ≠ (i : ℕ)) (hj0 : (j : ℕ) ≠ (k : ℕ)) (hj1 : (j : ℕ) ≠ (k : ℕ) + 1) :
    deningerStdEdge.{u} k ∈ (horn.{u} m i).obj (op (mk 1)) := by
  rw [mem_horn_iff]
  intro hcon
  have hj : j ∈ Set.range (stdSimplex.asOrderHom (deningerStdEdge.{u} k)) ∪ {i} := by
    rw [hcon]
    trivial
  rcases hj with ⟨a, ha⟩ | hj
  · have hval := congrArg Fin.val ha
    fin_cases a
    · exact hj0 hval.symm
    · exact hj1 hval.symm
  · exact hji (congrArg Fin.val hj)

/-- **Every spine edge lies in the horn** when there are at least four vertices. -/
theorem deningerEdge_mem_horn_of_four {m : ℕ} (hm : 3 ≤ m) (i : Fin (m + 1)) (k : Fin m) :
    deningerStdEdge.{u} k ∈ (horn.{u} m i).obj (op (mk 1)) := by
  obtain ⟨t, ht, hti, htk, htk1⟩ :
      ∃ t : ℕ, t < m + 1 ∧ t ≠ (i : ℕ) ∧ t ≠ (k : ℕ) ∧ t ≠ (k : ℕ) + 1 := by
    by_contra hcon
    push Not at hcon
    have h0 := hcon 0 (by omega)
    have h1 := hcon 1 (by omega)
    have h2 := hcon 2 (by omega)
    have h3 := hcon 3 (by omega)
    omega
  exact deningerEdge_mem_horn i k ⟨t, ht⟩ hti htk htk1

/-- **Every spine edge lies in an inner horn** when there are at least three vertices. -/
theorem deningerEdge_mem_horn_of_inner {m : ℕ} (i : Fin (m + 1)) (hi0 : 0 < (i : ℕ))
    (hilast : (i : ℕ) < m) (k : Fin m) :
    deningerStdEdge.{u} k ∈ (horn.{u} m i).obj (op (mk 1)) := by
  have hk : (k : ℕ) < m := k.2
  rcases Nat.eq_zero_or_pos (k : ℕ) with hk0 | hk0
  · have hm2 : 2 ≤ m := by omega
    refine deningerEdge_mem_horn i k ⟨m, by omega⟩ ?_ ?_ ?_
    · show m ≠ (i : ℕ)
      omega
    · show m ≠ (k : ℕ)
      omega
    · show m ≠ (k : ℕ) + 1
      omega
  · refine deningerEdge_mem_horn i k ⟨0, by omega⟩ ?_ ?_ ?_
    · show 0 ≠ (i : ℕ)
      omega
    · show 0 ≠ (k : ℕ)
      omega
    · show 0 ≠ (k : ℕ) + 1
      omega

end RHTower
