import GaloisForLFunctions.HTGeometry.InstantCalibrationSingularity

/-!
# Resolution and time do not commute for exact circuit complexity

At any positive observer resolution the reference state itself certifies zero complexity for every
state within that resolution, so an orbit leaving the reference state at bounded speed is seen as
easy on an interval whose length is the resolution over the speed.

Conversely, a state of exact complexity at least `k` is strictly outside the compact layer of
circuits of length below `k`, so every resolution below that positive layer distance still sees
complexity at least `k`.  On a compact set of times whose orbit avoids the layer, the layer
distance attains a positive minimum, which is a single resolution threshold valid on the whole set.

The two statements are the two iterated limits of the threshold history: resolution first gives
zero near time zero, time first gives one at every time of high exact complexity.
-/

open Matrix

open scoped Matrix Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

noncomputable section

section Threshold

variable {X : Type*} [MetricSpace X] {Γ : Type*}

/-- The threshold history of an observer at resolution `eps` and circuit budget `k`. -/
def ThresholdHistory (act : Γ → X → X) (chi : X) (k : ℕ) (eps : ℝ) (x : X) : Prop :=
  k ≤ approxComplexity act chi eps x

/-- **Resolution collapses complexity near the reference state.**  Every state within the
resolution has approximate complexity zero. -/
theorem approxComplexity_eq_zero_of_dist_le {act : Γ → X → X} {chi : X} {eps : ℝ} {x : X}
    (h : dist x chi ≤ eps) : approxComplexity act chi eps x = 0 := by
  have hmem : (0 : ℕ) ∈ {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps} :=
    ⟨[], le_rfl, by simpa [wordAct] using h⟩
  exact Nat.le_zero.mp (Nat.sInf_le hmem)

theorem not_thresholdHistory_of_dist_le {act : Γ → X → X} {chi : X} {k : ℕ} {eps : ℝ} {x : X}
    (hk : 0 < k) (h : dist x chi ≤ eps) : ¬ ThresholdHistory act chi k eps x := by
  rw [ThresholdHistory, approxComplexity_eq_zero_of_dist_le h]
  omega

/-- **Equation `(3)`.**  An orbit leaving the reference state at speed at most `v` is seen as easy
by every observer of resolution `eps` up to time `eps / v`. -/
theorem approxComplexity_orbit_eq_zero {act : Γ → X → X} {chi : X} {v eps : ℝ} (hv : 0 < v)
    {psi : ℝ → X} (hspeed : ∀ t : ℝ, dist (psi t) chi ≤ v * |t|) {t : ℝ}
    (ht : |t| ≤ eps / v) : approxComplexity act chi eps (psi t) = 0 := by
  refine approxComplexity_eq_zero_of_dist_le (le_trans (hspeed t) ?_)
  rw [← le_div_iff₀' hv]
  exact ht

/-- **Equation `(8)`.**  A state of exact complexity at least `k` lies at positive distance from
the compact layer of circuits of length below `k`. -/
theorem layerDist_pos_of_le_approxComplexity [TopologicalSpace Γ] [CompactSpace Γ]
    {act : Γ → X → X} (hcont : Continuous fun p : Γ × X => act p.1 p.2) (chi : X) {k : ℕ}
    (hk : 0 < k) {x : X} (h : k ≤ approxComplexity act chi 0 x) :
    0 < layerDist act chi (k - 1) x :=
  lt_layerDist_of_lt_approxComplexity hcont chi 0 x (by omega)

/-- **Equation `(4)`, circuit form.**  Below the layer distance no circuit shorter than `k` enters
the resolution ball. -/
theorem lt_dist_wordAct_of_lt_layerDist {act : Γ → X → X} {chi : X} {k : ℕ} {eps : ℝ} {x : X}
    (heps : eps < layerDist act chi (k - 1) x) {w : List Γ} (hw : w.length < k) :
    eps < dist x (wordAct act w chi) :=
  lt_of_lt_of_le heps (layerDist_le_dist (by omega))

/-- **Equation `(4)`.**  Every resolution below the layer distance still sees complexity at least
`k`. -/
theorem thresholdHistory_of_lt_layerDist {act : Γ → X → X} {chi : X} {k : ℕ} {eps : ℝ} {x : X}
    (heps : eps < layerDist act chi (k - 1) x)
    (hS : {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps}.Nonempty) :
    ThresholdHistory act chi k eps x := by
  by_contra hcon
  rw [ThresholdHistory, not_le] at hcon
  obtain ⟨w, hw, hd⟩ := Nat.sInf_mem hS
  have hlen : w.length < k := lt_of_le_of_lt hw hcon
  exact absurd hd (not_le.mpr (lt_dist_wordAct_of_lt_layerDist heps hlen))

/-- **Second iterated limit.**  At a state of exact complexity at least `k` there is a positive
resolution threshold below which every observer still sees complexity at least `k`. -/
theorem exists_pos_resolution_threshold [TopologicalSpace Γ] [CompactSpace Γ]
    {act : Γ → X → X} (hcont : Continuous fun p : Γ × X => act p.1 p.2) (chi : X) {k : ℕ}
    (hk : 0 < k) {x : X} (h : k ≤ approxComplexity act chi 0 x) :
    ∃ δ > 0, ∀ eps : ℝ, eps < δ →
      ∀ w : List Γ, w.length < k → eps < dist x (wordAct act w chi) :=
  ⟨layerDist act chi (k - 1) x, layerDist_pos_of_le_approxComplexity hcont chi hk h,
    fun _eps heps _w hw => lt_dist_wordAct_of_lt_layerDist heps hw⟩

end Threshold

section UniformWindow

variable {X : Type*} [MetricSpace X] {Γ : Type*} [TopologicalSpace Γ] [CompactSpace Γ]

theorem continuous_layerDist_comp (act : Γ → X → X) (chi : X) (s : ℕ) {psi : ℝ → X}
    (hpsi : Continuous psi) : Continuous fun t : ℝ => layerDist act chi s (psi t) :=
  (Metric.continuous_infDist_pt (reachSet act chi s)).comp hpsi

/-- **Equation `(10)`.**  On a compact set of times whose orbit has exact complexity at least `k`,
one positive resolution threshold works uniformly. -/
theorem exists_pos_uniform_resolution {act : Γ → X → X}
    (hcont : Continuous fun p : Γ × X => act p.1 p.2) (chi : X) {k : ℕ} (hk : 0 < k)
    {K : Set ℝ} (hK : IsCompact K) {psi : ℝ → X} (hpsi : Continuous psi)
    (hlow : ∀ t ∈ K, k ≤ approxComplexity act chi 0 (psi t)) :
    ∃ δ > 0, ∀ t ∈ K, ∀ eps : ℝ, eps < δ →
      ∀ w : List Γ, w.length < k → eps < dist (psi t) (wordAct act w chi) := by
  rcases Set.eq_empty_or_nonempty K with hKe | hKne
  · refine ⟨1, one_pos, ?_⟩
    intro t ht
    rw [hKe] at ht
    exact absurd ht (Set.notMem_empty t)
  · obtain ⟨t₀, ht₀, hmin⟩ :=
      hK.exists_isMinOn hKne ((continuous_layerDist_comp act chi (k - 1) hpsi).continuousOn)
    refine ⟨layerDist act chi (k - 1) (psi t₀),
      layerDist_pos_of_le_approxComplexity hcont chi hk (hlow t₀ ht₀), ?_⟩
    intro t ht eps heps w hw
    have hle : layerDist act chi (k - 1) (psi t₀) ≤ layerDist act chi (k - 1) (psi t) := hmin ht
    exact lt_dist_wordAct_of_lt_layerDist (lt_of_lt_of_le heps hle) hw

end UniformWindow


section IteratedLimits

variable {X : Type*} [MetricSpace X] {Γ : Type*}

/-- The numeric threshold history. -/
def thresholdIndicator (act : Γ → X → X) (chi : X) (k : ℕ) (eps : ℝ) (x : X) : ℝ :=
  if k ≤ approxComplexity act chi eps x then 1 else 0

/-- A state of positive exact complexity is approximable at every nonnegative resolution. -/
theorem nonempty_approxSet_of_le_approxComplexity {act : Γ → X → X} {chi : X} {k : ℕ} {x : X}
    (hk : 0 < k) (h : k ≤ approxComplexity act chi 0 x) {eps : ℝ} (heps : 0 ≤ eps) :
    {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps}.Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have h0 : {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ 0} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro s ⟨w, hw, hd⟩
    have : s ∈ {s | ∃ w : List Γ, w.length ≤ s ∧ dist x (wordAct act w chi) ≤ eps} :=
      ⟨w, hw, le_trans hd heps⟩
    rw [hcon] at this
    exact this
  rw [approxComplexity, h0, Nat.sInf_empty] at h
  omega

/-- **Equation `(4)`, complexity form.**  At a state of exact complexity at least `k`, every
resolution below the layer distance still sees complexity at least `k`. -/
theorem thresholdHistory_of_lt_layerDist_of_exact {act : Γ → X → X} {chi : X} {k : ℕ} {eps : ℝ}
    {x : X} (hk : 0 < k) (h0 : k ≤ approxComplexity act chi 0 x) (heps0 : 0 ≤ eps)
    (heps : eps < layerDist act chi (k - 1) x) : ThresholdHistory act chi k eps x :=
  thresholdHistory_of_lt_layerDist heps (nonempty_approxSet_of_le_approxComplexity hk h0 heps0)

/-- **Equation `(5)`, first iterated limit.**  At any fixed positive resolution the threshold
history vanishes near time zero. -/
theorem tendsto_thresholdIndicator_time {act : Γ → X → X} {chi : X} {k : ℕ} (hk : 0 < k)
    {v eps : ℝ} (hv : 0 < v) (heps : 0 < eps) {psi : ℝ → X}
    (hspeed : ∀ t : ℝ, dist (psi t) chi ≤ v * |t|) :
    Filter.Tendsto (fun t : ℝ => thresholdIndicator act chi k eps (psi t))
      (nhds 0) (nhds 0) := by
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)) (f := nhds (0 : ℝ)))
  have hball : Metric.ball (0 : ℝ) (eps / v) ∈ nhds (0 : ℝ) :=
    Metric.ball_mem_nhds 0 (by positivity)
  filter_upwards [hball] with t ht
  have habs : |t| ≤ eps / v := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact ht.le
  rw [thresholdIndicator, if_neg]
  rw [approxComplexity_orbit_eq_zero hv hspeed habs]
  omega

/-- **Equation `(5)`, second iterated limit.**  At a state of exact complexity at least `k` the
threshold history equals one for every small enough positive resolution. -/
theorem tendsto_thresholdIndicator_resolution [TopologicalSpace Γ] [CompactSpace Γ]
    {act : Γ → X → X} (hcont : Continuous fun p : Γ × X => act p.1 p.2) (chi : X) {k : ℕ}
    (hk : 0 < k) {x : X} (h : k ≤ approxComplexity act chi 0 x) :
    Filter.Tendsto (fun eps : ℝ => thresholdIndicator act chi k eps x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ))
    (f := nhdsWithin (0 : ℝ) (Set.Ioi 0)))
  have hδ : 0 < layerDist act chi (k - 1) x :=
    layerDist_pos_of_le_approxComplexity hcont chi hk h
  have hmem : Metric.ball (0 : ℝ) (layerDist act chi (k - 1) x) ∈ nhds (0 : ℝ) :=
    Metric.ball_mem_nhds 0 hδ
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with eps hball hpos
  have hlt : eps < layerDist act chi (k - 1) x := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hball
    exact lt_of_abs_lt hball
  rw [thresholdIndicator, if_pos]
  exact thresholdHistory_of_lt_layerDist_of_exact hk h (le_of_lt hpos) hlt

end IteratedLimits

section Schroedinger

variable {d : Type*} [Fintype d] [DecidableEq d] {Γ : Type*}

/-- **Equations `(3)` and `(6)` for a Schrödinger orbit.**  Every observer of resolution `eps` sees
the orbit of a unit seed as easy up to time `eps / ‖H‖`. -/
theorem approxComplexity_evolvedState_eq_zero {act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d}
    {H : Matrix d d ℂ} (hH : IsSelfAdjoint H) (hHpos : 0 < ‖H‖)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {eps t : ℝ} (ht : |t| ≤ eps / ‖H‖) :
    approxComplexity act ψ eps (evolvedState H t ψ) = 0 :=
  approxComplexity_orbit_eq_zero (act := act) (chi := ψ) hHpos
    (psi := fun s => evolvedState H s ψ) (fun s => dist_evolvedState_le hH s hψ) ht

/-- **Noncommuting limits.**  For a Schrödinger orbit of a unit seed, resolution taken first makes
the threshold history vanish near time zero, while at any time of exact complexity at least `k` the
threshold history is one for every small enough resolution. -/
theorem noncommuting_resolution_time [TopologicalSpace Γ] [CompactSpace Γ]
    {act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d}
    (hcont : Continuous fun p : Γ × EuclideanSpace ℂ d => act p.1 p.2)
    {H : Matrix d d ℂ} (hH : IsSelfAdjoint H) (hHpos : 0 < ‖H‖)
    {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) {k : ℕ} (hk : 0 < k) :
    (∀ eps : ℝ, 0 < eps → ∀ t : ℝ, |t| ≤ eps / ‖H‖ →
        ¬ ThresholdHistory act ψ k eps (evolvedState H t ψ)) ∧
      (∀ t : ℝ, k ≤ approxComplexity act ψ 0 (evolvedState H t ψ) →
        ∃ δ > 0, ∀ eps : ℝ, eps < δ → ∀ w : List Γ, w.length < k →
          eps < dist (evolvedState H t ψ) (wordAct act w ψ)) := by
  constructor
  · intro eps _heps t ht
    rw [ThresholdHistory, approxComplexity_evolvedState_eq_zero hH hHpos hψ ht]
    omega
  · intro t hval
    exact exists_pos_resolution_threshold hcont ψ hk hval

end Schroedinger

end

end GaloisForLFunctions.HTGeometry
