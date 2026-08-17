import GaloisForLFunctions.HTGeometry.PathShellDelayFloor

/-!
# Fixing one seed on a positive-measure part of the delay sector

The delay sector of the path-local shell has positive measure at every finite delay, because its
ninth-power floor is positive.  If finitely many seeds serve the whole sector -- each shell point
being served by at least one of them -- then one fixed seed already serves a positive-measure part
of it: a finite cover of a set of positive measure has a member of positive measure.

This is the selection step that turns a per-Hamiltonian seed choice into one seed fixed for the
whole evolution.
-/

open MeasureTheory Metric Set

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Selection

variable {n : ℕ}

theorem pathShellProb_pos_iff {A : Set (sphere (0 : PathShell n) 1)} :
    0 < pathShellProb A ↔ volume.toSphere A ≠ 0 := by
  constructor
  · intro h hzero
    rw [pathShellProb, hzero] at h
    simp at h
  · intro h
    refine div_pos ?_ toSphere_pathShell_univ_pos
    exact ENNReal.toReal_pos h (toSphere_pathShell_ne_top A)

/-- **The finite cover selection.**  If finitely many sets cover a set of positive shell measure,
one of them meets it in positive shell measure. -/
theorem exists_pos_inter_of_cover {ι : Type*} [Fintype ι] {A : Set (sphere (0 : PathShell n) 1)}
    {G : ι → Set (sphere (0 : PathShell n) 1)} (hcover : A ⊆ ⋃ j, G j)
    (hA : 0 < pathShellProb A) : ∃ j, 0 < pathShellProb (A ∩ G j) := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ j, volume.toSphere (A ∩ G j) = 0 := by
    intro j
    by_contra hj
    exact absurd (pathShellProb_pos_iff.mpr hj) (not_lt.mpr (hcon j))
  have hAeq : A ⊆ ⋃ j, A ∩ G j := by
    intro a ha
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover ha)
    exact mem_iUnion.mpr ⟨j, ⟨ha, hj⟩⟩
  have hle : volume.toSphere A ≤ ∑ j, volume.toSphere (A ∩ G j) :=
    le_trans (measure_mono hAeq) (measure_iUnion_fintype_le _ _)
  have hsum : (∑ j, volume.toSphere (A ∩ G j)) = 0 :=
    Finset.sum_eq_zero fun j _ => hzero j
  rw [hsum, le_zero_iff] at hle
  exact absurd hle (pathShellProb_pos_iff.mp hA)

/-- The delay sector has positive shell measure at every finite delay. -/
theorem pathShellProb_delayEvent_pos {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))))
    (chi ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) (hψ : ‖ψ‖ = 1)
    {eta eps : ℝ} {S : ℕ} (hmargin : eta < eps) (e : Fin (n + 1))
    (hcert : ∀ u : PathShell n, ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState (pathHamiltonianCut u e) ψ s) (wordAct act w chi) ≤ eta)
    {L : ℝ} (hL : (eps - eta) / 3 ≤ L) :
    0 < pathShellProb (delayEvent act chi ψ eps S L) := by
  obtain ⟨c, hc, hfloor⟩ := exists_delay_floor act chi ψ hψ hmargin e hcert
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith) hL
  have hpos : 0 < c / L ^ 9 := by positivity
  exact lt_of_lt_of_le hpos (hfloor L hL)

/-- **Theorem C's seed-selection step.**  If finitely many seeds serve the whole delay sector, one
fixed seed serves a positive-measure part of it. -/
theorem exists_fixed_seed_on_delay {Γ : Type*}
    (act : Γ → EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))) →
      EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))))
    (chi ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2)))) (hψ : ‖ψ‖ = 1)
    {eta eps : ℝ} {S : ℕ} (hmargin : eta < eps) (e : Fin (n + 1))
    (hcert : ∀ u : PathShell n, ∀ s : ℝ, ∃ w : List Γ, w.length ≤ S ∧
      dist (orbitState (pathHamiltonianCut u e) ψ s) (wordAct act w chi) ≤ eta)
    {L : ℝ} (hL : (eps - eta) / 3 ≤ L)
    {ι : Type*} [Fintype ι] (good : ι → Set (sphere (0 : PathShell n) 1))
    (hserve : delayEvent act chi ψ eps S L ⊆ ⋃ j, good j) :
    ∃ j : ι, 0 < pathShellProb (delayEvent act chi ψ eps S L ∩ good j) :=
  exists_pos_inter_of_cover hserve
    (pathShellProb_delayEvent_pos act chi ψ hψ hmargin e hcert hL)

end Selection

end

end GaloisForLFunctions.HTGeometry
