/-
# The filled Julia set `K_c` is connected for `c ∈ mandelbrot`

`K_c = ⋂ n, C_n` is the decreasing intersection of the compact connected sublevel sets
`C_n = (escapeLevel c n)ᶜ` (`SublevelConnected`). A nested intersection of nonempty compact connected
sets in a Hausdorff space is connected — `isPreconnected_iInter_of_antitone`, proved here from scratch
(mathlib has the nonemptiness `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` but
not the connectedness). Assembling gives `isPreconnected_filledJulia`, the `hconn : IsPreconnected
(filledJulia c)` hypothesis consumed across `JuliaFrontierPerfect` and `RelativeRigidityCapstone`.
-/
import GaloisForLFunctions.Bottcher.SublevelConnected
import GaloisForLFunctions.Bottcher.BasinColimit

open Topology Metric

/-- **A nested intersection of nonempty compact connected sets is connected.** For a decreasing
sequence `S : ℕ → Set X` of closed sets in a Hausdorff space, with `S 0` compact, each `S n` nonempty
and preconnected, the intersection `⋂ n, S n` is preconnected. The separation argument: a splitting of
`K = ⋂ S n` by closed `t₁, t₂` gives disjoint compacts `K∩t₁, K∩t₂`, separated by disjoint opens
`U, V` (Hausdorff); the closed sets `S n \ (U∪V)` are nested compact with empty intersection
(`K ⊆ U∪V`), so some `S N ⊆ U∪V`, and `S N` meeting both disjoint opens contradicts its
connectedness. -/
theorem isPreconnected_iInter_of_antitone {X : Type*} [TopologicalSpace X] [T2Space X]
    {S : ℕ → Set X} (hanti : ∀ i, S (i + 1) ⊆ S i) (hcl : ∀ n, IsClosed (S n))
    (hcomp : IsCompact (S 0)) (hpre : ∀ n, IsPreconnected (S n)) :
    IsPreconnected (⋂ n, S n) := by
  set K : Set X := ⋂ n, S n with hK
  have hKcl : IsClosed K := isClosed_iInter hcl
  have hKcomp : IsCompact K := hcomp.of_isClosed_subset hKcl (Set.iInter_subset _ 0)
  have hKsubS : ∀ N, K ⊆ S N := fun N _ hz => Set.mem_iInter.mp hz N
  rw [isPreconnected_closed_iff]
  intro t₁ t₂ ht₁ ht₂ hcov hne1 hne2
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hE1comp : IsCompact (K ∩ t₁) := hKcomp.inter_right ht₁
  have hE2comp : IsCompact (K ∩ t₂) := hKcomp.inter_right ht₂
  have hdisj : Disjoint (K ∩ t₁) (K ∩ t₂) := by
    rw [Set.disjoint_iff_inter_eq_empty, Set.inter_inter_inter_comm, Set.inter_self]
    exact hcon
  obtain ⟨U, V, hU, hV, hE1U, hE2V, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hE1comp hE2comp hdisj
  have hKUV : K ⊆ U ∪ V := by
    intro z hzK
    rcases hcov hzK with hz1 | hz2
    · exact Or.inl (hE1U ⟨hzK, hz1⟩)
    · exact Or.inr (hE2V ⟨hzK, hz2⟩)
  set W : ℕ → Set X := fun n => S n \ (U ∪ V) with hWdef
  have hWsub : ∀ i, W (i + 1) ⊆ W i := fun i => Set.diff_subset_diff_left (hanti i)
  have hWcl : ∀ n, IsClosed (W n) := fun n => (hcl n).sdiff (hU.union hV)
  have hWcomp0 : IsCompact (W 0) := hcomp.of_isClosed_subset (hWcl 0) Set.diff_subset
  have hWempty : (⋂ n, W n) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rw [Set.mem_iInter] at hz
    have hzK : z ∈ K := Set.mem_iInter.mpr (fun n => (hz n).1)
    exact (hz 0).2 (hKUV hzK)
  have hexN : ∃ N, W N = ∅ := by
    by_contra hall
    have hallne : ∀ i, (W i).Nonempty := by
      intro i
      rw [Set.nonempty_iff_ne_empty]
      exact fun he => hall ⟨i, he⟩
    have hnonempty := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      W hWsub hallne hWcomp0 hWcl
    rw [hWempty] at hnonempty
    exact Set.not_nonempty_empty hnonempty
  obtain ⟨N, hN⟩ := hexN
  have hSNUV : S N ⊆ U ∪ V := by
    intro z hz
    by_contra hznot
    exact Set.notMem_empty z (hN ▸ (⟨hz, hznot⟩ : z ∈ W N))
  have hSNU : (S N ∩ U).Nonempty := by
    obtain ⟨z, hz⟩ := hne1; exact ⟨z, hKsubS N hz.1, hE1U hz⟩
  have hSNV : (S N ∩ V).Nonempty := by
    obtain ⟨z, hz⟩ := hne2; exact ⟨z, hKsubS N hz.1, hE2V hz⟩
  obtain ⟨z, _, hzU, hzV⟩ := hpre N U V hU hV hSNUV hSNU hSNV
  exact Set.disjoint_left.mp hUV hzU hzV

namespace Bottcher

/-- `K_c` is the decreasing intersection of the escape-level complements `C_n = (escapeLevel c n)ᶜ`. -/
theorem filledJulia_eq_iInter_escapeLevel_compl (c : ℂ) :
    filledJulia c = ⋂ n, (escapeLevel c n)ᶜ := by
  rw [← compl_compl (filledJulia c), compl_filledJulia_eq_iUnion_level, Set.compl_iUnion]

/-- **`K_c` is connected for `c ∈ mandelbrot`.** The filled Julia set of a connected parameter is the
nested intersection of the compact connected sublevel sets `C_n = (escapeLevel c n)ᶜ`
(`isPreconnected_escapeLevel_compl`), hence connected by `isPreconnected_iInter_of_antitone`. This
supplies the `hconn : IsPreconnected (filledJulia c)` hypothesis assumed across the connected-case
rigidity/transcendence chain. -/
theorem isPreconnected_filledJulia {c : ℂ} (hc : c ∈ mandelbrot) :
    IsPreconnected (filledJulia c) := by
  have hc' : ∀ n, c ∉ escapeLevel c n := criticalValue_not_mem_escapeLevels_of_mem_mandelbrot hc
  rw [filledJulia_eq_iInter_escapeLevel_compl]
  refine isPreconnected_iInter_of_antitone (S := fun n => (escapeLevel c n)ᶜ) ?_ ?_ ?_ ?_
  · exact fun i z hz hz2 => hz (escapeLevel_subset_succ c i hz2)
  · exact fun n => isClosed_compl_iff.mpr (isOpen_escapeLevel c n)
  · show IsCompact ((escapeLevel c 0)ᶜ)
    have h0 : (escapeLevel c 0)ᶜ = Metric.closedBall (0 : ℂ) (max 2 ‖c‖) := by
      rw [escapeLevel_zero]
      ext z
      simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, escapeOpen,
        Set.mem_setOf_eq, not_lt]
    rw [h0]; exact isCompact_closedBall _ _
  · exact fun n => isPreconnected_escapeLevel_compl c hc' n

end Bottcher
