import Mathlib
import GaloisForLFunctions.HTGeometry.CoherenceTailQuotient

/-!
# Mechanisms extracted from supercritical sharpness

`[BRIDGE]` This module formalizes reusable deterministic cores from Diskin--Easo--
Ramanan Radhakrishnan--Sudakov--Tassion, *Supercritical sharpness of percolation*,
arXiv:2603.03257:

* the anchored edge-isoperimetric profile `Phi(W)`;
* the one-touch-at-a-time geometric lower bound;
* the deterministic threshold-or-stall content of the touch induction;
* the finite weighted-moment split used in the sprinkling lemma; and
* the doubling bootstrap used in the mass-collection theorem.

No percolation theorem is assumed here.  The finite-graph collapse theorem records why the
paper's profile must be used on an infinite graph, or replaced by a finite-volume target profile.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

open Set

universe u

section Isoperimetry

variable {V : Type u}

/-- Number of ordered graph edges crossing a finite vertex set.  The paper counts unoriented
edges; this existing corpus boundary counts both orientations, a harmless factor of two. -/
noncomputable def finiteEdgeBoundarySize (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Set.ncard (edgeBoundary G (S : Set V))

/-- Paper's anchored isoperimetric profile `Phi(W)`: minimum boundary size among finite supersets
of `W`. -/
noncomputable def anchoredIsoperimetricProfile (G : SimpleGraph V) (W : Finset V) : ℕ :=
  by
    classical
    exact Nat.find (show ∃ n : ℕ, ∃ S : Finset V,
        W ⊆ S ∧ finiteEdgeBoundarySize G S = n from
      ⟨finiteEdgeBoundarySize G W, W, Finset.Subset.rfl, rfl⟩)

/-- The anchored profile is attained by a finite superset. -/
theorem exists_superset_boundarySize_eq_anchoredIsoperimetricProfile
    (G : SimpleGraph V) (W : Finset V) :
    ∃ S : Finset V, W ⊆ S ∧
      finiteEdgeBoundarySize G S = anchoredIsoperimetricProfile G W := by
  classical
  exact Nat.find_spec (show ∃ n : ℕ, ∃ S : Finset V,
    W ⊆ S ∧ finiteEdgeBoundarySize G S = n from
      ⟨finiteEdgeBoundarySize G W, W, Finset.Subset.rfl, rfl⟩)

/-- Every particular finite superset bounds the anchored profile from above. -/
theorem anchoredIsoperimetricProfile_le_boundarySize
    (G : SimpleGraph V) {W S : Finset V} (hWS : W ⊆ S) :
    anchoredIsoperimetricProfile G W ≤ finiteEdgeBoundarySize G S := by
  classical
  unfold anchoredIsoperimetricProfile
  exact Nat.find_min' _ ⟨S, hWS, rfl⟩

/-- Enlarging the anchor can only increase its minimum boundary cost. -/
theorem anchoredIsoperimetricProfile_mono
    (G : SimpleGraph V) {W W' : Finset V} (hWW' : W ⊆ W') :
    anchoredIsoperimetricProfile G W ≤ anchoredIsoperimetricProfile G W' := by
  obtain ⟨S, hW'S, hS⟩ :=
    exists_superset_boundarySize_eq_anchoredIsoperimetricProfile G W'
  rw [← hS]
  exact anchoredIsoperimetricProfile_le_boundarySize G (hWW'.trans hW'S)

/-- Empty anchor has zero isoperimetric cost. -/
@[simp] theorem anchoredIsoperimetricProfile_empty (G : SimpleGraph V) :
    anchoredIsoperimetricProfile G ∅ = 0 := by
  have hle := anchoredIsoperimetricProfile_le_boundarySize G
    (W := (∅ : Finset V)) (S := (∅ : Finset V)) Finset.Subset.rfl
  have hboundary : finiteEdgeBoundarySize G (∅ : Finset V) = 0 := by
    unfold finiteEdgeBoundarySize
    rw [show (((∅ : Finset V) : Set V)) = ∅ by ext; simp]
    have hempty : edgeBoundary G (∅ : Set V) = ∅ := by
      ext e
      simp [edgeBoundary]
    rw [hempty]
    simp
  omega

/-- On a finite graph, the paper's infinity-anchored profile degenerates identically to zero:
the whole finite vertex set is an admissible superset with empty boundary. -/
theorem anchoredIsoperimetricProfile_eq_zero_of_finite
    [Fintype V] [DecidableEq V] (G : SimpleGraph V) (W : Finset V) :
    anchoredIsoperimetricProfile G W = 0 := by
  have hW : W ⊆ (Finset.univ : Finset V) := Finset.subset_univ W
  have hle := anchoredIsoperimetricProfile_le_boundarySize G hW
  have hboundary : finiteEdgeBoundarySize G (Finset.univ : Finset V) = 0 := by
    unfold finiteEdgeBoundarySize
    rw [show ((Finset.univ : Finset V) : Set V) = Set.univ by ext; simp]
    have huniv : edgeBoundary G (Set.univ : Set V) = ∅ := by
      ext e
      simp [edgeBoundary]
    rw [huniv]
    simp
  omega

/-! ### Finite-volume replacement -/

/-- Finite-volume analogue of the paper's anchored profile.  Admissible supersets must avoid a
designated target.  The fallback `S = W` makes the definition total when anchor and target
overlap; when they are disjoint, it adds no extra competitor. -/
noncomputable def targetAvoidingIsoperimetricProfile
    (G : SimpleGraph V) (W target : Finset V) : ℕ :=
  by
    classical
    exact Nat.find (show ∃ n : ℕ, ∃ S : Finset V,
        W ⊆ S ∧ (Disjoint S target ∨ S = W) ∧
          finiteEdgeBoundarySize G S = n from
      ⟨finiteEdgeBoundarySize G W, W, Finset.Subset.rfl, Or.inr rfl, rfl⟩)

/-- For a disjoint anchor and target, the finite-volume profile is attained by a genuinely
target-avoiding superset. -/
theorem exists_targetAvoiding_superset_boundarySize_eq_profile
    (G : SimpleGraph V) {W target : Finset V} (hWT : Disjoint W target) :
    ∃ S : Finset V, W ⊆ S ∧ Disjoint S target ∧
      finiteEdgeBoundarySize G S =
        targetAvoidingIsoperimetricProfile G W target := by
  classical
  obtain ⟨S, hWS, htarget, hboundary⟩ :=
    Nat.find_spec (show ∃ n : ℕ, ∃ S : Finset V,
      W ⊆ S ∧ (Disjoint S target ∨ S = W) ∧
        finiteEdgeBoundarySize G S = n from
      ⟨finiteEdgeBoundarySize G W, W, Finset.Subset.rfl, Or.inr rfl, rfl⟩)
  refine ⟨S, hWS, ?_, hboundary⟩
  rcases htarget with htarget | rfl
  · exact htarget
  · exact hWT

/-- Every target-avoiding finite superset bounds the finite-volume profile from above. -/
theorem targetAvoidingIsoperimetricProfile_le_boundarySize
    (G : SimpleGraph V) {W target S : Finset V}
    (hWS : W ⊆ S) (hST : Disjoint S target) :
    targetAvoidingIsoperimetricProfile G W target ≤
      finiteEdgeBoundarySize G S := by
  classical
  unfold targetAvoidingIsoperimetricProfile
  exact Nat.find_min' _ ⟨S, hWS, Or.inl hST, rfl⟩

/-- Unlike the infinity-anchored profile, the target-avoiding profile is already nontrivial on
the two-vertex path: separating vertex `0` from terminal `1` costs a positive ordered boundary. -/
theorem pathGraph_two_targetAvoidingIsoperimetricProfile_pos :
    0 < targetAvoidingIsoperimetricProfile
      (SimpleGraph.pathGraph 2)
      ({(0 : Fin 2)} : Finset (Fin 2)) ({(1 : Fin 2)} : Finset (Fin 2)) := by
  have hdisjoint : Disjoint
      ({(0 : Fin 2)} : Finset (Fin 2)) ({(1 : Fin 2)} : Finset (Fin 2)) := by
    simp
  obtain ⟨S, hanchor, htarget, hprofile⟩ :=
    exists_targetAvoiding_superset_boundarySize_eq_profile
      (SimpleGraph.pathGraph 2) hdisjoint
  rw [← hprofile]
  unfold finiteEdgeBoundarySize
  rw [Set.ncard_pos]
  refine ⟨((0 : Fin 2), (1 : Fin 2)), ?_⟩
  have hzero : (0 : Fin 2) ∈ S := hanchor (by simp)
  have hone : (1 : Fin 2) ∉ S := by
    intro hone
    exact Finset.disjoint_left.mp htarget hone (by simp)
  simp [edgeBoundary, SimpleGraph.pathGraph_adj, hzero, hone]

end Isoperimetry

section SequentialTouches

/-- A finite family of stage-retention factors, each at least `retention`, retains at least the
paper's geometric mass `retention ^ card`. -/
theorem retention_pow_le_prod
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (stageRetention : ι → ℝ) (retention : ℝ)
    (hretention : 0 ≤ retention)
    (hstage : ∀ i, retention ≤ stageRetention i) :
    retention ^ Fintype.card ι ≤ ∏ i, stageRetention i := by
  calc
    retention ^ Fintype.card ι = ∏ _i : ι, retention := by simp
    _ ≤ ∏ i, stageRetention i :=
      Finset.prod_le_prod (fun _ _ => hretention) (fun i _ => hstage i)

/-- Numeric core of the paper's one-touch-at-a-time induction: a uniform one-step retention
factor compounds geometrically. -/
theorem geometric_lower_bound_of_step
    (mass : ℕ → ℝ) (retention : ℝ) (t : ℕ)
    (hretention : 0 ≤ retention)
    (hzero : 1 ≤ mass 0)
    (hstep : ∀ i < t, retention * mass i ≤ mass (i + 1)) :
    retention ^ t ≤ mass t := by
  induction t with
  | zero => simpa using hzero
  | succ t ih =>
      have iht : retention ^ t ≤ mass t :=
        ih (fun i hi => hstep i (by omega))
      rw [pow_succ]
      calc
        retention ^ t * retention = retention * retention ^ t := mul_comm _ _
        _ ≤ mass (t + 1) :=
          (mul_le_mul_of_nonneg_left iht hretention).trans (hstep t (by omega))

/-- Deterministic content behind “many touches suffice”: a monotone integer process either gains
at least `t` units by time `t`, or one of its first `t` increments stalls. -/
theorem accumulates_touches_or_exists_stall
    (N : ℕ → ℕ) (t : ℕ) (hmono : Monotone N) :
    N 0 + t ≤ N t ∨ ∃ i < t, N (i + 1) = N i := by
  by_contra h
  push Not at h
  have hstrict : ∀ i < t, N i < N (i + 1) := by
    intro i hi
    exact (hmono (Nat.le_succ i)).lt_of_ne (Ne.symm (h.2 i hi))
  have hlinear : ∀ i ≤ t, N 0 + i ≤ N i := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hi' : i < t := by omega
        exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih (by omega)) (hstrict i hi'))
  have ht := hlinear t le_rfl
  omega

/-- Zero-based form of `accumulates_touches_or_exists_stall`. -/
theorem reaches_threshold_or_exists_stall
    (N : ℕ → ℕ) (t : ℕ) (hzero : N 0 = 0)
    (hmono : Monotone N) :
    t ≤ N t ∨ ∃ i < t, N (i + 1) = N i := by
  rcases accumulates_touches_or_exists_stall N t hmono with h | h
  · left
    simpa [hzero] using h
  · exact Or.inr h

end SequentialTouches

section Sprinkling

variable {Ω : Type*} [Fintype Ω]

/-- Square-root alternative used when FKG turns a joint-failure estimate into a product estimate:
at least one marginal failure is at most the square root of the joint scale. -/
theorem le_sqrt_or_le_sqrt_of_mul_le
    {a b δ : ℝ} (hδ : 0 ≤ δ)
    (hab : a * b ≤ δ) :
    a ≤ Real.sqrt δ ∨ b ≤ Real.sqrt δ := by
  by_contra h
  push Not at h
  have ha0 : 0 < a := lt_of_le_of_lt (Real.sqrt_nonneg _) h.1
  have hmul : Real.sqrt δ * Real.sqrt δ < a * b := by
    calc
      Real.sqrt δ * Real.sqrt δ ≤ a * Real.sqrt δ :=
        mul_le_mul_of_nonneg_right h.1.le (Real.sqrt_nonneg _)
      _ < a * b := mul_lt_mul_of_pos_left h.2 ha0
  rw [Real.mul_self_sqrt hδ] at hmul
  exact (not_lt_of_ge hab) hmul

/-- Finite weighted failure moment `E[r^T]` used in the paper's sprinkling argument. -/
def weightedFailureMoment (w : Ω → ℝ) (T : Ω → ℕ) (r : ℝ) : ℝ :=
  ∑ ω, w ω * r ^ T ω

/-- Quantitative split at threshold `t` from the paper's sprinkling lemma.  Low values of `T` are
paid for by the source moment; high values are suppressed by the sprinkled factor. -/
theorem weightedFailureMoment_le_div_add_pow
    (w : Ω → ℝ) (T : Ω → ℕ) {r s : ℝ} (t : ℕ)
    (hw : ∀ ω, 0 ≤ w ω) (hwSum : ∑ ω, w ω ≤ 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    weightedFailureMoment w T s ≤
      weightedFailureMoment w T r / r ^ t + s ^ t := by
  classical
  have hrpow : 0 < r ^ t := pow_pos hr0 _
  have hlow : (∑ ω ∈ Finset.univ.filter (fun ω => T ω ≤ t), w ω * s ^ T ω) ≤
      weightedFailureMoment w T r / r ^ t := by
    have hmass : (∑ ω ∈ Finset.univ.filter (fun ω => T ω ≤ t), w ω) * r ^ t ≤
        weightedFailureMoment w T r := by
      rw [Finset.sum_mul]
      unfold weightedFailureMoment
      calc
        ∑ ω ∈ Finset.univ.filter (fun ω => T ω ≤ t), w ω * r ^ t ≤
            ∑ ω ∈ Finset.univ.filter (fun ω => T ω ≤ t), w ω * r ^ T ω := by
          apply Finset.sum_le_sum
          intro ω hω
          have hT : T ω ≤ t := (Finset.mem_filter.mp hω).2
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one (le_of_lt hr0) hr1 hT) (hw ω)
        _ ≤ ∑ ω, w ω * r ^ T ω := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => mul_nonneg (hw _) (pow_nonneg (le_of_lt hr0) _))
    have hmassDiv : ∑ ω ∈ Finset.univ.filter (fun ω => T ω ≤ t), w ω ≤
        weightedFailureMoment w T r / r ^ t := by
      exact (le_div_iff₀ hrpow).2 hmass
    calc
      ∑ ω ∈ Finset.univ.filter (fun ω => T ω ≤ t), w ω * s ^ T ω ≤
          ∑ ω ∈ Finset.univ.filter (fun ω => T ω ≤ t), w ω := by
        apply Finset.sum_le_sum
        intro ω _
        have hspow : s ^ T ω ≤ 1 := pow_le_one₀ hs0 hs1
        nlinarith [hw ω, pow_nonneg hs0 (T ω)]
      _ ≤ weightedFailureMoment w T r / r ^ t := hmassDiv
  have hhigh :
      (∑ ω ∈ Finset.univ.filter (fun ω => ¬ T ω ≤ t), w ω * s ^ T ω) ≤ s ^ t := by
    calc
      ∑ ω ∈ Finset.univ.filter (fun ω => ¬ T ω ≤ t), w ω * s ^ T ω ≤
          ∑ ω ∈ Finset.univ.filter (fun ω => ¬ T ω ≤ t), w ω * s ^ t := by
        apply Finset.sum_le_sum
        intro ω hω
        have hnot : ¬ T ω ≤ t := (Finset.mem_filter.mp hω).2
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one hs0 hs1 (by omega)) (hw ω)
      _ = (∑ ω ∈ Finset.univ.filter (fun ω => ¬ T ω ≤ t), w ω) * s ^ t := by
        rw [Finset.sum_mul]
      _ ≤ 1 * s ^ t := by
        gcongr
        exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => hw _)).trans hwSum
      _ = s ^ t := one_mul _
  calc
    weightedFailureMoment w T s =
        (∑ ω ∈ Finset.univ.filter (fun ω => T ω ≤ t), w ω * s ^ T ω) +
          ∑ ω ∈ Finset.univ.filter (fun ω => ¬ T ω ≤ t), w ω * s ^ T ω := by
            unfold weightedFailureMoment
            rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ weightedFailureMoment w T r / r ^ t + s ^ t := add_le_add hlow hhigh

/-- Source-moment form of the sprinkling comparison. -/
theorem weightedFailureMoment_le_of_source_bound
    (w : Ω → ℝ) (T : Ω → ℕ) {r s α : ℝ} (t : ℕ)
    (hw : ∀ ω, 0 ≤ w ω) (hwSum : ∑ ω, w ω ≤ 1)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hsource : weightedFailureMoment w T r ≤ α) :
    weightedFailureMoment w T s ≤ α / r ^ t + s ^ t := by
  exact (weightedFailureMoment_le_div_add_pow w T t hw hwSum hr0 hr1 hs0 hs1).trans
    (add_le_add (div_le_div_of_nonneg_right hsource (pow_nonneg (le_of_lt hr0) _)) le_rfl)

end Sprinkling

section CollectingMass

/-- Scalar doubling bootstrap used in the paper's mass-collection theorem. -/
theorem next_le_two_mul_of_isoperimetric_step
    {v next c d phiNext : ℝ}
    (hnext : 0 ≤ next) (hc : 0 ≤ c)
    (hstep : next - v ≤ c * phiNext)
    (hisop : phiNext ≤ d * next) (hsmall : 2 * c * d ≤ 1) :
    next ≤ 2 * v := by
  have hcd : c * d ≤ 1 / 2 := by linarith
  have hinc : next - v ≤ c * d * next := by
    calc
      next - v ≤ c * phiNext := hstep
      _ ≤ c * (d * next) := mul_le_mul_of_nonneg_left hisop hc
      _ = c * d * next := by ring
  have hhalf : next - v ≤ next / 2 := by
    calc
      next - v ≤ c * d * next := hinc
      _ ≤ (1 / 2) * next := mul_le_mul_of_nonneg_right hcd hnext
      _ = next / 2 := by ring
  linarith

/-- After the doubling bootstrap, monotonicity and `phi(2x) ≤ 2 phi(x)` move the next-scale
isoperimetric cost back to the current scale. -/
theorem step_le_two_mul_current_of_doubling
    (phi : ℝ → ℝ) {v next c d : ℝ}
    (hnext : 0 ≤ next) (hc : 0 ≤ c)
    (hmono : Monotone phi) (hdouble : phi (2 * v) ≤ 2 * phi v)
    (hstep : next - v ≤ c * phi next)
    (hisop : phi next ≤ d * next) (hsmall : 2 * c * d ≤ 1) :
    next - v ≤ 2 * c * phi v := by
  have hnext2 := next_le_two_mul_of_isoperimetric_step hnext hc hstep hisop hsmall
  calc
    next - v ≤ c * phi next := hstep
    _ ≤ c * phi (2 * v) := mul_le_mul_of_nonneg_left (hmono hnext2) hc
    _ ≤ c * (2 * phi v) := mul_le_mul_of_nonneg_left hdouble hc
    _ = 2 * c * phi v := by ring

end CollectingMass

end GaloisForLFunctions.HTGeometry
