import GaloisForLFunctions.HTGeometry.DifferentialGaloisScalarZeroSet

/-!
# A finite constant span solves a nonzero linear differential operator

If finitely many elements `w 0, …, w (d-1)` of a differential field are given, the `d + 1` jet
vectors `(δ^k w 0, …, δ^k w (d-1))`, `k ≤ d`, are `d + 1` vectors in a `d`-dimensional space, hence
linearly dependent.  A nontrivial dependence is exactly a nonzero linear differential operator of
order at most `d` annihilating every `w j`, and its solution set is a module over the constants, so
it annihilates the whole constant span.

This is the step that turns "the entries of a matrix group lie in a finite-dimensional space over
the constants" into the hypothesis `hGL` of `isomonodromy_of_no_riccati_of_linearRelation`.  No
Wronskian is needed: only that `d + 1` vectors in `Cᵈ` are dependent.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]

/-- **A finite family lies in the solution set of a nonzero linear differential operator**, and
therefore so does its whole span over the constants. -/
theorem exists_nonzero_linearJet_relation_of_span {ι : Type*} [Fintype ι] (w : ι → C) :
    ∃ (d : ℕ) (L : ℕ → C) (i₀ : ℕ), i₀ ∈ Finset.range (d + 1) ∧ L i₀ ≠ 0 ∧
      ∀ x ∈ Submodule.span (differentialConstants C) (Set.range w),
        x ∈ linearJetSolutions d L := by
  classical
  set d : ℕ := Fintype.card ι with hd
  set v : Fin (d + 1) → (ι → C) := fun k j => differentialJet (k : ℕ) (w j) with hv
  have hnli : ¬ LinearIndependent C v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    rw [Module.finrank_fintype_fun_eq_card] at hcard
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨gc, hrel, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.mp hnli
  set L : ℕ → C := fun i => if h : i < d + 1 then gc ⟨i, h⟩ else 0 with hL
  have hLcoe : ∀ k : Fin (d + 1), L (k : ℕ) = gc k := by
    intro k
    rw [hL]
    simp only [dif_pos k.isLt]
  have hkill : ∀ j : ι, ∑ i ∈ Finset.range (d + 1), L i * differentialJet i (w j) = 0 := by
    intro j
    rw [← Fin.sum_univ_eq_sum_range (fun i => L i * differentialJet i (w j)) (d + 1)]
    have hpt : ∀ k : Fin (d + 1), L (k : ℕ) * differentialJet (k : ℕ) (w j)
        = (gc k • v k) j := by
      intro k
      rw [hLcoe k]
      rfl
    rw [Finset.sum_congr rfl (fun k _ => hpt k)]
    have := congrFun hrel j
    simpa using this
  refine ⟨d, L, (i₀ : ℕ), Finset.mem_range.mpr i₀.isLt, by rw [hLcoe i₀]; exact hi₀, ?_⟩
  have hsub : Set.range w ⊆ (linearJetSolutions d L : Set C) := by
    rintro x ⟨j, rfl⟩
    exact hkill j
  exact fun x hx => (Submodule.span_le.mpr hsub) hx

end

end GaloisForLFunctions.HTGeometry
