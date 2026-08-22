import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Intersecting a monotone chain of internally disjoint sums

Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*
(arXiv:math/0203120), proves Prop. 4.6 -- the density of `⋃_{b>a} K_b` in the Sonine space `K_a` --
from the following purely lattice-theoretic observation:

> Generally speaking `⋂_{b>a}(A_b + B_b) = (⋂_{b>a} A_b) + (⋂_{b>a} B_b)` when we have vector
> spaces indexed by `b > a` with `A_{b₁} ⊂ A_{b₂}` and `B_{b₁} ⊂ B_{b₂}` for `b₁ < b₂` and
> `A_b ∩ B_b = {0}` for `b > a`.

The point is that internal disjointness forces the decomposition `x = a_b + b_b` to be *independent
of `b`*: for `b₁ ≤ b₂` the difference `a_{b₁} - a_{b₂} = b_{b₂} - b_{b₁}` lies in
`A_{b₂} ∩ B_{b₂} = 0`.

This file proves the lattice identity for submodules over an arbitrary ring, indexed by an
arbitrary nonempty linear order, and derives the Hilbert-space corollary that Burnol actually uses:
if each `A i ⊔ B i` is closed, then the closed span of the increasing family of orthogonal
complements `(A i ⊔ B i)ᗮ` is exactly `((⨅ i, A i) ⊔ (⨅ i, B i))ᗮ`.

## Main results

* `iInf_sup_eq_of_monotone_of_disjoint`
* `topologicalClosure_iSup_orthogonal_sup_eq`
-/

namespace GaloisForLFunctions.HTGeometry

variable {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [LinearOrder ι] [Nonempty ι]

/-- **Burnol's lattice identity (proof of Prop. 4.6).**  For two monotone families of submodules
indexed by a nonempty linear order, whose members are pairwise internally disjoint, intersection
commutes with the sum. -/
theorem iInf_sup_eq_of_monotone_of_disjoint (A B : ι → Submodule R M)
    (hA : Monotone A) (hB : Monotone B) (hdisj : ∀ i, A i ⊓ B i = ⊥) :
    (⨅ i, A i ⊔ B i) = (⨅ i, A i) ⊔ (⨅ i, B i) := by
  classical
  refine le_antisymm ?_ ?_
  · intro x hx
    simp only [Submodule.mem_iInf] at hx
    have hchoice : ∀ i : ι, ∃ p : M × M, p.1 ∈ A i ∧ p.2 ∈ B i ∧ p.1 + p.2 = x := by
      intro i
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hx i)
      exact ⟨(y, z), hy, hz, hyz⟩
    choose p hp1 hp2 hp3 using hchoice
    have hconst : ∀ i j : ι, (p i).1 = (p j).1 := by
      have hmono : ∀ i j : ι, i ≤ j → (p i).1 = (p j).1 := by
        intro i j hij
        have hsum : (p i).1 + (p i).2 = (p j).1 + (p j).2 := by rw [hp3 i, hp3 j]
        have hkey : (p i).1 - (p j).1 = (p j).2 - (p i).2 := by
          rw [sub_eq_sub_iff_add_eq_add, hsum]
          exact add_comm _ _
        have hmemA : (p i).1 - (p j).1 ∈ A j :=
          Submodule.sub_mem _ (hA hij (hp1 i)) (hp1 j)
        have hmemB : (p i).1 - (p j).1 ∈ B j := by
          rw [hkey]; exact Submodule.sub_mem _ (hp2 j) (hB hij (hp2 i))
        have : (p i).1 - (p j).1 ∈ A j ⊓ B j := ⟨hmemA, hmemB⟩
        rw [hdisj j, Submodule.mem_bot] at this
        exact sub_eq_zero.1 this
      intro i j
      rcases le_total i j with h | h
      · exact hmono i j h
      · exact (hmono j i h).symm
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    refine Submodule.mem_sup.2 ⟨(p i₀).1, ?_, (p i₀).2, ?_, hp3 i₀⟩
    · simp only [Submodule.mem_iInf]
      intro i
      rw [hconst i₀ i]
      exact hp1 i
    · simp only [Submodule.mem_iInf]
      intro i
      have h2 : (p i₀).2 = (p i).2 := by
        have hsum : (p i₀).1 + (p i₀).2 = (p i).1 + (p i).2 := by rw [hp3 i₀, hp3 i]
        rw [hconst i₀ i] at hsum
        exact add_left_cancel hsum
      rw [h2]
      exact hp2 i
  · refine sup_le ?_ ?_
    · exact le_iInf fun i => le_trans (iInf_le A i) le_sup_left
    · exact le_iInf fun i => le_trans (iInf_le B i) le_sup_right

section Hilbert

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] [LinearOrder ι] [Nonempty ι]

/-- **Burnol's Prop. 4.6, in the exact shape used for the Sonine chain.**  If `A` and `B` are
monotone families of internally disjoint submodules with `A i ⊔ B i` closed, then the closed span
of the decreasing family of Sonine-type spaces `(A i ⊔ B i)ᗮ` is `((⨅ i, A i) ⊔ (⨅ i, B i))ᗮ`. -/
theorem topologicalClosure_iSup_orthogonal_sup_eq (A B : ι → Submodule 𝕜 E)
    (hA : Monotone A) (hB : Monotone B) (hdisj : ∀ i, A i ⊓ B i = ⊥)
    (hclosed : ∀ i, IsClosed ((A i ⊔ B i : Submodule 𝕜 E) : Set E)) :
    (⨆ i, (A i ⊔ B i)ᗮ).topologicalClosure = ((⨅ i, A i) ⊔ (⨅ i, B i))ᗮ := by
  have hstep : (⨆ i, (A i ⊔ B i)ᗮ)ᗮ = ⨅ i, A i ⊔ B i := by
    rw [← Submodule.iInf_orthogonal]
    refine iInf_congr fun i => ?_
    haveI : CompleteSpace ((A i ⊔ B i : Submodule 𝕜 E)) := (hclosed i).completeSpace_coe
    haveI : (A i ⊔ B i : Submodule 𝕜 E).HasOrthogonalProjection :=
      Submodule.HasOrthogonalProjection.ofCompleteSpace _
    exact Submodule.orthogonal_orthogonal _
  have h1 : (⨆ i, (A i ⊔ B i)ᗮ).topologicalClosure = ((⨆ i, (A i ⊔ B i)ᗮ)ᗮ)ᗮ :=
    (Submodule.orthogonal_orthogonal_eq_closure _).symm
  rw [h1, hstep, iInf_sup_eq_of_monotone_of_disjoint A B hA hB hdisj]

end Hilbert

end GaloisForLFunctions.HTGeometry
