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
import GaloisForLFunctions.Bottcher.ConnectedCompactIntersection

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
  have hanti' : Antitone S := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro x hx; exact hx
    | succ n _ hsub => intro x hx; exact hsub (hanti n hx)
  refine Bottcher.isPreconnected_iInter_antitone hanti' ?_ hpre
  intro n
  exact hcomp.of_isClosed_subset (hcl n) (hanti' (Nat.zero_le n))

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
