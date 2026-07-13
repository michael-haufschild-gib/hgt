import GaloisForLFunctions.Core

/-!
# Shape-blind cycle deletion forces geometric weights

When a new label is inserted into a cycle of length `k`, let `r k` be the relative weight of that
insertion.  The total lift score of a cycle shape is `sum k*r k` over its parts.  If this score is
independent of the cycle shape and depends only on total size, then every positive-length ratio is
the same.  Consequently nonzero multiplicative cycle weights are geometric.

This is the finite coherence no-go and positive maximal-class theorem for the prime-power
cycle-index RH detour.
-/

noncomputable section

namespace RHTower

/-- Total one-label deletion lift score of an unlabelled cycle shape. -/
def cycleDeletionShapeScore (r : ℕ → ℝ) (parts : List ℕ) : ℝ :=
  (parts.map fun k : ℕ => (k : ℝ) * r k).sum

/-- Deletion lift mass is blind to cycle shape and depends only on total size. -/
def CycleDeletionShapeBlind (r : ℕ → ℝ) : Prop :=
  ∀ parts parts' : List ℕ,
    (∀ k ∈ parts, 0 < k) →
    (∀ k ∈ parts', 0 < k) →
    parts.sum = parts'.sum →
    cycleDeletionShapeScore r parts = cycleDeletionShapeScore r parts'

/-- Shape-blind deletion coherence is equivalent to one constant insertion ratio on every
positive cycle length. -/
theorem cycleDeletionShapeBlind_iff_constant_ratio (r : ℕ → ℝ) :
    CycleDeletionShapeBlind r ↔ ∀ k : ℕ, 0 < k → r k = r 1 := by
  constructor
  · intro h k hk
    have hs := h [k] (List.replicate k 1)
      (by simp [hk]) (by simp) (by simp)
    simp [cycleDeletionShapeScore] at hs
    exact hs.resolve_right hk.ne'
  · intro h parts parts' hparts hparts' hsum
    have score_eq (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
        cycleDeletionShapeScore r l = (l.sum : ℝ) * r 1 := by
      induction l with
      | nil => simp [cycleDeletionShapeScore]
      | cons k l ih =>
          have hk : 0 < k := hl k (by simp)
          have hl' : ∀ a ∈ l, 0 < a := by
            intro a ha
            exact hl a (by simp [ha])
          rw [cycleDeletionShapeScore]
          simp only [List.map_cons, List.sum_cons]
          rw [h k hk]
          have ih' := ih hl'
          rw [cycleDeletionShapeScore] at ih'
          rw [ih']
          push_cast
          ring
    rw [score_eq parts hparts, score_eq parts' hparts', hsum]

/-- A constant positive-length insertion ratio forces geometric cycle weights. -/
theorem cycleWeight_eq_geometric_of_constant_ratio
    (w : ℕ → ℝ) (c : ℝ)
    (h : ∀ k : ℕ, 0 < k → w (k + 1) = c * w k) :
    ∀ k : ℕ, 0 < k → w k = w 1 * c ^ (k - 1) := by
  intro k hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  induction n with
  | zero => simp
  | succ n ih =>
      rw [h (n + 1) (by omega), ih (by omega)]
      simp only [Nat.succ_sub_one]
      rw [pow_succ]
      ring

/-- Nonzero cycle weights with shape-blind deletion lifts are necessarily geometric. -/
theorem cycleWeight_eq_geometric_of_shapeBlind
    (w : ℕ → ℝ)
    (hw : ∀ k : ℕ, 0 < k → w k ≠ 0)
    (hblind : CycleDeletionShapeBlind (fun k => w (k + 1) / w k)) :
    ∀ k : ℕ, 0 < k →
      w k = w 1 * (w 2 / w 1) ^ (k - 1) := by
  apply cycleWeight_eq_geometric_of_constant_ratio w (w 2 / w 1)
  intro k hk
  have hr := (cycleDeletionShapeBlind_iff_constant_ratio
    (fun j => w (j + 1) / w j)).mp hblind k hk
  change w (k + 1) / w k = w 2 / w 1 at hr
  exact (div_eq_iff (hw k hk)).mp hr

end RHTower
