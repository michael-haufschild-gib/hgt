import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Recurrence of a relatively-compact isometric `ℝ`-action

The Bohr recurrence used in the finite-phase theorem is a special case of a purely metric fact: an
isometric additive action of `ℝ` on a metric space, with a relatively compact orbit, is *recurrent* —
its orbit returns arbitrarily close to the base point at arbitrarily large times.  Mathlib has no
such statement.  This file proves it abstractly (`isometricAction_recurrence`,
`isometricAction_return_seq`), so it can be instantiated for translation on `ℝ →ᵇ ℂ`
(`AlmostPeriodicHull`) and for vertical translation on bounded holomorphic functions on a strip.

The proof is Bochner's compactness argument: the integer-time orbit has a Cauchy subsequence, and the
isometry turns bounded index gaps into small return distances at arbitrarily large times.
-/

open Filter Topology

namespace GaloisForLFunctions

/-- An isometric additive action of `ℝ` on a metric space `M`. -/
structure IsometricRAction (M : Type*) [MetricSpace M] where
  act : ℝ → M → M
  map_add : ∀ s t x, act s (act t x) = act (s + t) x
  isometry : ∀ t, Isometry (act t)

variable {M : Type*} [MetricSpace M]

/-- **Recurrence of a relatively-compact isometric orbit.**  If the orbit `{act t x}` has compact
closure, then for every `ε > 0` and every bound `N` there is a time `t ≥ N` with
`dist (act t x) x < ε`. -/
theorem isometricAction_recurrence (A : IsometricRAction M) {x : M}
    (hcompact : IsCompact (closure (Set.range (fun t : ℝ => A.act t x))))
    {ε : ℝ} (hε : 0 < ε) (N : ℝ) :
    ∃ t : ℝ, N ≤ t ∧ dist (A.act t x) x < ε := by
  have hmem : ∀ n : ℕ, A.act (n : ℝ) x ∈ closure (Set.range (fun t : ℝ => A.act t x)) :=
    fun n => subset_closure ⟨(n : ℝ), rfl⟩
  obtain ⟨g, _, φ, hφ, hconv⟩ := hcompact.tendsto_subseq hmem
  have hcauchy := hconv.cauchySeq
  rw [Metric.cauchySeq_iff] at hcauchy
  obtain ⟨K, hK⟩ := hcauchy ε hε
  set m : ℕ := max 1 ⌈N⌉₊ with hm
  have hgap : φ K + m ≤ φ (K + m) := by
    have step : ∀ i, φ K + i ≤ φ (K + i) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
          have hlt : φ (K + i) < φ (K + i + 1) := hφ (by omega)
          have heq : K + (i + 1) = K + i + 1 := by omega
          rw [heq]; omega
    exact step m
  have hmN : N ≤ (m : ℝ) :=
    (Nat.le_ceil N).trans (by exact_mod_cast le_max_right 1 ⌈N⌉₊)
  refine ⟨(φ (K + m) : ℝ) - (φ K : ℝ), ?_, ?_⟩
  · have : (φ K : ℝ) + (m : ℝ) ≤ (φ (K + m) : ℝ) := by exact_mod_cast hgap
    linarith
  · have hiso : dist (A.act ((φ (K + m) : ℝ) - (φ K : ℝ)) x) x
        = dist (A.act ((φ (K + m) : ℕ) : ℝ) x) (A.act ((φ K : ℕ) : ℝ) x) := by
      have := (A.isometry ((φ K : ℕ) : ℝ)).dist_eq
        (A.act ((φ (K + m) : ℝ) - (φ K : ℝ)) x) x
      rw [A.map_add] at this
      rw [← this]
      congr 2
      ring
    rw [hiso]
    exact hK (K + m) (by omega) K (le_refl K)

/-- **Return sequence.**  A relatively-compact isometric orbit admits return times `T_l → +∞` with
`act (T_l) x → x`. -/
theorem isometricAction_return_seq (A : IsometricRAction M) {x : M}
    (hcompact : IsCompact (closure (Set.range (fun t : ℝ => A.act t x)))) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧ Tendsto (fun l => A.act (T l) x) atTop (nhds x) := by
  choose T hT1 hT2 using
    fun l : ℕ => isometricAction_recurrence A hcompact (by positivity : (0 : ℝ) < 1 / (l + 1)) (l : ℝ)
  refine ⟨T, Filter.tendsto_atTop_mono hT1 tendsto_natCast_atTop_atTop, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun l => dist_nonneg) (fun l => (hT2 l).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end GaloisForLFunctions
