/-
# Isolated pieces with a moat (OP16, Question B core)

A compact totally disconnected planar set has, at every point, relatively clopen pieces of
arbitrarily small diameter; such a piece is at positive distance both from the rest of the set
and from any closed set avoiding the point.  This is the piece-selection input of the W4
reduction (task #138): a deep dyadic piece of a Cantor filled Julia set `K₁` chosen at a point
of `K₁ ∖ K₂` carries a moat separating it from `K₁ ∖ P` and from `K₂` — the loops around `P`
then wind zero mass of `K₂`'s equilibrium measure.

* `exists_isolated_piece` — the generic metric/topological statement.
* `filledJulia_not_subset_or` — the swap dichotomy from `K`-determines-`c`.
* `exists_isolated_julia_piece` — the Cantor Julia instantiation (`‖c₁‖ ≥ 4` class).

Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.CantorFilledJulia
import GaloisForLFunctions.Bottcher.BottcherDetermines

open Set Metric

namespace Bottcher

/-- **Isolated piece with a moat.**  In a compact totally disconnected `K ⊆ ℂ`, every point
`x ∉ L` (`L` closed) lies in a compact piece `P ⊆ K` of diameter `≤ δ` at distance `≥ ε > 0`
from both `K ∖ P` and `L`. -/
theorem exists_isolated_piece {K L : Set ℂ} (hKcpt : IsCompact K)
    (hKtd : IsTotallyDisconnected K) (hLcl : IsClosed L)
    {x : ℂ} (hx : x ∈ K) (hxL : x ∉ L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : Set ℂ) (ε : ℝ), 0 < ε ∧ x ∈ P ∧ P ⊆ K ∧ IsCompact P ∧
      Metric.diam P ≤ δ ∧
      (∀ z ∈ P, ∀ w ∈ K \ P, ε ≤ dist z w) ∧
      (∀ z ∈ P, ∀ w ∈ L, ε ≤ dist z w) := by
  classical
  -- a clearance radius against `L`
  obtain ⟨δL, hδL0, hδLdisj⟩ :=
    (Set.disjoint_singleton_left.mpr hxL).exists_thickenings isCompact_singleton hLcl
  have hxLfar : ∀ w ∈ L, δL ≤ dist x w := by
    intro w hw
    by_contra hcon
    rw [not_le] at hcon
    have h1 : w ∈ thickening δL ({x} : Set ℂ) := by
      rw [mem_thickening_iff]
      exact ⟨x, rfl, by rw [dist_comm]; exact hcon⟩
    have h2 : w ∈ thickening δL L := self_subset_thickening hδL0 L hw
    exact (Set.disjoint_left.mp hδLdisj h1) h2
  set r : ℝ := min (δ / 2) (δL / 2) with hrdef
  have hr0 : 0 < r := lt_min (by linarith) (by linarith)
  -- pass to the subspace, where clopens cut out the component `{x}`
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
  haveI : TotallyDisconnectedSpace K := totallyDisconnectedSpace_subtype_iff.mpr hKtd
  set x' : K := ⟨x, hx⟩ with hx'def
  have hcomp : connectedComponent x' = {x'} :=
    totallyDisconnectedSpace_iff_connectedComponent_singleton.mp ‹_› x'
  set F : Set K := {z : K | r ≤ dist (z : ℂ) x} with hFdef
  have hFcl : IsClosed F :=
    isClosed_le continuous_const (continuous_subtype_val.dist continuous_const)
  have hFcpt : IsCompact F := hFcl.isCompact
  haveI : Nonempty {s : Set K // IsClopen s ∧ x' ∈ s} :=
    ⟨⟨univ, isClopen_univ, mem_univ _⟩⟩
  have hFdisj : F ∩ ⋂ (s : {s : Set K // IsClopen s ∧ x' ∈ s}), (s : Set K) = ∅ := by
    rw [← connectedComponent_eq_iInter_isClopen x', hcomp]
    ext z
    simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and,
      hFdef, mem_setOf_eq]
    intro hzF hzx
    rw [hzx] at hzF
    simp only [hx'def] at hzF
    rw [dist_self] at hzF
    linarith
  have hdir : Directed (fun (a b : Set K) => a ⊇ b)
      (fun s : {s : Set K // IsClopen s ∧ x' ∈ s} => (s : Set K)) := by
    intro s t
    exact ⟨⟨(s : Set K) ∩ t, s.2.1.inter t.2.1, ⟨s.2.2, t.2.2⟩⟩,
      inter_subset_left, inter_subset_right⟩
  obtain ⟨s₀, hs₀⟩ := hFcpt.elim_directed_family_closed _
    (fun s => s.2.1.isClosed) hFdisj hdir
  -- the ambient piece
  set P : Set ℂ := Subtype.val '' (s₀ : Set K) with hPdef
  have hxP : x ∈ P := ⟨x', s₀.2.2, rfl⟩
  have hPK : P ⊆ K := by
    rintro z ⟨z', _, rfl⟩
    exact z'.2
  have hPcpt : IsCompact P :=
    (s₀.2.1.isClosed.isCompact).image continuous_subtype_val
  have hPball : ∀ z ∈ P, dist z x < r := by
    rintro z ⟨z', hz', rfl⟩
    by_contra hcon
    rw [not_lt] at hcon
    have h1 : z' ∈ F := hcon
    have h2 : z' ∈ F ∩ (s₀ : Set K) := ⟨h1, hz'⟩
    rw [hs₀] at h2
    exact h2
  have hdiam : Metric.diam P ≤ δ := by
    apply Metric.diam_le_of_forall_dist_le (by linarith)
    intro z hz w hw
    have h1 := hPball z hz
    have h2 := hPball w hw
    have h3 : r ≤ δ / 2 := min_le_left _ _
    calc dist z w ≤ dist z x + dist x w := dist_triangle _ _ _
      _ = dist z x + dist w x := by rw [dist_comm x w]
      _ ≤ δ := by linarith
  -- the complement piece and its moat
  set Q : Set ℂ := Subtype.val '' ((s₀ : Set K)ᶜ) with hQdef
  have hKP : K \ P = Q := by
    ext z
    constructor
    · rintro ⟨hzK, hzP⟩
      refine ⟨⟨z, hzK⟩, ?_, rfl⟩
      intro hmem
      exact hzP ⟨⟨z, hzK⟩, hmem, rfl⟩
    · rintro ⟨z', hz', rfl⟩
      refine ⟨z'.2, ?_⟩
      rintro ⟨w', hw', hww⟩
      have h1 : w' = z' := Subtype.ext hww
      rw [h1] at hw'
      exact hz' hw'
  have hQcpt : IsCompact Q :=
    ((s₀.2.1.compl).isClosed.isCompact).image continuous_subtype_val
  have hPQdisj : Disjoint P Q := by
    rw [Set.disjoint_left]
    rintro z ⟨z', hz', rfl⟩ ⟨w', hw', hww⟩
    have h1 : w' = z' := Subtype.ext hww
    rw [h1] at hw'
    exact hw' hz'
  obtain ⟨εK, hεK0, hεKdisj⟩ := hPQdisj.exists_thickenings hPcpt hQcpt.isClosed
  refine ⟨P, min εK (δL / 2), lt_min hεK0 (by linarith), hxP, hPK, hPcpt, hdiam, ?_, ?_⟩
  · intro z hz w hw
    rw [hKP] at hw
    have h1 : min εK (δL / 2) ≤ εK := min_le_left _ _
    by_contra hcon
    rw [not_le] at hcon
    have h2 : w ∈ thickening εK P := by
      rw [mem_thickening_iff]
      exact ⟨z, hz, by rw [dist_comm]; linarith [h1]⟩
    have h3 : w ∈ thickening εK Q := self_subset_thickening hεK0 Q hw
    exact (Set.disjoint_left.mp hεKdisj h2) h3
  · intro z hz w hw
    have h1 := hxLfar w hw
    have h2 := hPball z hz
    have h3 : r ≤ δL / 2 := min_le_right _ _
    have h4 : min εK (δL / 2) ≤ δL / 2 := min_le_right _ _
    calc min εK (δL / 2) ≤ δL / 2 := h4
      _ ≤ δL - r := by linarith
      _ ≤ dist x w - dist z x := by linarith
      _ ≤ dist z w := by
          have := dist_triangle x z w
          rw [dist_comm x z] at this
          linarith

/-- **Swap dichotomy from `K`-determines-`c`**: distinct parameters have mutually
non-nested filled Julia sets in at least one order. -/
theorem filledJulia_not_subset_or {c₁ c₂ : ℂ} (h : c₁ ≠ c₂) :
    ¬ (filledJulia c₁ ⊆ filledJulia c₂) ∨ ¬ (filledJulia c₂ ⊆ filledJulia c₁) := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  exact h (c_eq_of_filledJulia_eq' (Set.Subset.antisymm hcon.1 hcon.2))

/-- **Isolated Julia piece with a moat** (`‖c₁‖ ≥ 4` Cantor class).  If `K_{c₁} ⊄ K_{c₂}`,
then for every `δ > 0` there is a compact piece `P ⊆ K_{c₁}` of diameter `≤ δ` at positive
distance from both `K_{c₁} ∖ P` and `K_{c₂}` — the winding target of the OP16 reduction. -/
theorem exists_isolated_julia_piece {c₁ c₂ : ℂ} (hc₁4 : (4:ℝ) ≤ ‖c₁‖)
    (hsub : ¬ (filledJulia c₁ ⊆ filledJulia c₂)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (P : Set ℂ) (ε : ℝ), 0 < ε ∧ P.Nonempty ∧ P ⊆ filledJulia c₁ ∧ IsCompact P ∧
      Metric.diam P ≤ δ ∧
      (∀ z ∈ P, ∀ w ∈ filledJulia c₁ \ P, ε ≤ dist z w) ∧
      (∀ z ∈ P, ∀ w ∈ filledJulia c₂, ε ≤ dist z w) := by
  obtain ⟨x, hx₁, hx₂⟩ := Set.not_subset.mp hsub
  obtain ⟨P, ε, hε0, hxP, hPK, hPcpt, hdiam, hmoatK, hmoatL⟩ :=
    exists_isolated_piece (isCompact_filledJulia c₁)
      (isTotallyDisconnected_filledJulia_of_four_le hc₁4)
      (isClosed_filledJulia c₂) hx₁ hx₂ hδ
  exact ⟨P, ε, hε0, ⟨x, hxP⟩, hPK, hPcpt, hdiam, hmoatK, hmoatL⟩

end Bottcher
