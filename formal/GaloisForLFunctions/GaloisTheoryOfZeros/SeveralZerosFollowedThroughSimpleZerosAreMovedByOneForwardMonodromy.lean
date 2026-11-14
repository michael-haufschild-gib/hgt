import GaloisForLFunctions.GaloisTheoryOfZeros.AZeroFollowedThroughSimpleZerosIsMovedByTheForwardMonodromy

/-!
# Several zeros followed through simple zeros are moved by one forward monodromy

A continuous path `γ` of forward times may pass through branch times. If finitely many zeros are
followed along `γ` through simple zeros, one forward path off the branch times, with the same
ends, transports all of them at once
(`exists_forward_transports_of_simple_lifts`). For a loop this is one element of the forward
monodromy group with prescribed values at finitely many zeros
(`exists_mem_forwardMonodromy_of_simple_lifts`).

Proof. The finitely many simple zeros over a time have charts over one disc of times, and two
times of the disc off the branch times are joined inside the disc by an arc off the branch times;
the lifts of the arc are the charts (`exists_forward_continuation_in_charts`). The property "the
times near `γ(s)` are reached from the base by one forward path that transports every `w_i(0)` to
a zero near `w_i(s)`" holds near every parameter at which it holds once.
-/

open Complex Filter Topology Set Metric
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Tracks and simple lifts -/

/-- A continuous path of forward times. It may pass through branch times. -/
structure IsForwardTrack (γ : ℝ → ℂ) : Prop where
  continuousOn : ContinuousOn γ (Icc 0 1)
  re_pos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re

theorem IsForwardPath.track {γ : ℝ → ℂ} (h : IsForwardPath γ) : IsForwardTrack γ :=
  ⟨h.continuousOn, h.re_pos⟩

theorem IsForwardTrack.join {γ₁ γ₂ : ℝ → ℂ} (h₁ : IsForwardTrack γ₁) (h₂ : IsForwardTrack γ₂)
    (h : γ₁ 1 = γ₂ 0) : IsForwardTrack (pathJoin γ₁ γ₂) := by
  refine ⟨continuousOn_pathJoin h₁.continuousOn h₂.continuousOn h, fun s hs => ?_⟩
  rcases le_or_gt s (1 / 2) with hle | hlt
  · rw [pathJoin_of_le hle]
    exact h₁.re_pos _ (mapsTo_double ⟨hs.1, hle⟩)
  · rw [pathJoin_of_lt hlt]
    exact h₂.re_pos _ (mapsTo_double_sub_one ⟨hlt.le, hs.2⟩)

theorem IsForwardTrack.reverse {γ : ℝ → ℂ} (h : IsForwardTrack γ) : IsForwardTrack (pathRev γ) :=
  ⟨continuousOn_pathRev h.continuousOn, fun _ hs => h.re_pos _ (mapsTo_one_sub hs)⟩

/-- A continuous lift of zeros along `γ` all of whose points are simple zeros. -/
structure IsSimpleLift (γ w : ℝ → ℂ) : Prop where
  lift : IsZeroLift γ 1 w
  simple : ∀ s ∈ Icc (0 : ℝ) 1, deriv (complexHeat (γ s)) (w s) ≠ 0

theorem IsSimpleLift.join {γ₁ γ₂ w₁ w₂ : ℝ → ℂ} (h₁ : IsSimpleLift γ₁ w₁)
    (h₂ : IsSimpleLift γ₂ w₂) (hw : w₁ 1 = w₂ 0) :
    IsSimpleLift (pathJoin γ₁ γ₂) (pathJoin w₁ w₂) := by
  refine ⟨⟨continuousOn_pathJoin h₁.lift.continuousOn h₂.lift.continuousOn hw, fun s hs => ?_⟩,
    fun s hs => ?_⟩
  · rcases le_or_gt s (1 / 2) with hle | hlt
    · rw [pathJoin_of_le hle, pathJoin_of_le hle]
      exact h₁.lift.zero _ (mapsTo_double ⟨hs.1, hle⟩)
    · rw [pathJoin_of_lt hlt, pathJoin_of_lt hlt]
      exact h₂.lift.zero _ (mapsTo_double_sub_one ⟨hlt.le, hs.2⟩)
  · rcases le_or_gt s (1 / 2) with hle | hlt
    · rw [pathJoin_of_le hle, pathJoin_of_le hle]
      exact h₁.simple _ (mapsTo_double ⟨hs.1, hle⟩)
    · rw [pathJoin_of_lt hlt, pathJoin_of_lt hlt]
      exact h₂.simple _ (mapsTo_double_sub_one ⟨hlt.le, hs.2⟩)

theorem IsSimpleLift.reverse {γ w : ℝ → ℂ} (h : IsSimpleLift γ w) :
    IsSimpleLift (pathRev γ) (pathRev w) :=
  ⟨⟨continuousOn_pathRev h.lift.continuousOn, fun _ hs => h.lift.zero _ (mapsTo_one_sub hs)⟩,
    fun _ hs => h.simple _ (mapsTo_one_sub hs)⟩

/-- Along a forward path off the branch times every lift is simple. -/
theorem IsForwardPath.isSimpleLift {γ w : ℝ → ℂ} (hγ : IsForwardPath γ)
    (hw : IsZeroLift γ 1 w) : IsSimpleLift γ w :=
  ⟨hw, fun s hs =>
    deriv_complexHeat_ne_zero_of_not_mem_branchTimes (hγ.simple s hs) (hw.zero s hs)⟩

/-! ## Charts of finitely many simple zeros over one disc of times -/

variable {ι : Type*} [Finite ι]

/-- **Continuation inside the charts of finitely many simple zeros.** Around simple zeros
`(τ₀, z₀ i)` over one forward time there are a disc of times, a radius and continuous families
`ζ i` of zeros such that `ζ i τ` is the only zero of `H_τ` within the radius of `z₀ i`, and any
two times of the disc off the branch times are joined by one forward path that transports every
`ζ i` at the first to `ζ i` at the second. -/
theorem exists_forward_continuation_in_charts {τ₀ : ℂ} (hτ₀ : 0 < τ₀.re) {z₀ : ι → ℂ}
    (h0 : ∀ i, complexHeat τ₀ (z₀ i) = 0) (h1 : ∀ i, deriv (complexHeat τ₀) (z₀ i) ≠ 0) :
    ∃ r > 0, ∃ ρ > 0, ∃ ζ : ι → ℂ → ℂ, (∀ i, ContinuousOn (ζ i) (ball τ₀ r)) ∧
      (∀ i, ∀ τ ∈ ball τ₀ r, ∀ z ∈ ball (z₀ i) ρ, complexHeat τ z = 0 → z = ζ i τ) ∧
      ∀ τ₁ ∈ ball τ₀ r, τ₁ ∉ branchTimes → ∀ τ' ∈ ball τ₀ r, τ' ∉ branchTimes →
        ∃ g, IsForwardPath g ∧ g 0 = τ₁ ∧ g 1 = τ' ∧
          ∀ i, Transports g (ζ i τ₁) (ζ i τ') := by
  choose W hWo hτW ρ hρ ζ hζc _ hchart using fun i => exists_simple_zero_chart (h0 i) (h1 i)
  -- one radius of places
  obtain ⟨ρ₀, hρ₀, hρ₀le⟩ : ∃ ρ₀ > 0, ∀ i, ρ₀ ≤ ρ i := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_min ρ
      exact ⟨ρ i₀, hρ i₀, hi₀⟩
  -- one disc of times
  obtain ⟨r₀, hr₀, hsub⟩ :=
    Metric.isOpen_iff.mp (isOpen_iInter_of_finite hWo) τ₀ (mem_iInter.mpr hτW)
  have hsub' : ∀ i, ball τ₀ (min r₀ (τ₀.re / 2)) ⊆ W i := fun i =>
    ((ball_subset_ball (min_le_left _ _)).trans hsub).trans (iInter_subset _ i)
  refine ⟨min r₀ (τ₀.re / 2), lt_min hr₀ (half_pos hτ₀), ρ₀, hρ₀, ζ,
    fun i => (hζc i).mono (hsub' i),
    fun i τ hτ z hz hzero =>
      (hchart i τ (hsub' i hτ)).2.2.2 z (ball_subset_ball (hρ₀le i) hz) hzero,
    fun τ₁ hτ₁ hb₁ τ' hτ' hb' => ?_⟩
  obtain ⟨g, hg, hg0, hg1, hgball⟩ :=
    exists_isForwardPath_mem_ball (min_le_right _ _) hτ₁ hτ' hb₁ hb'
  refine ⟨g, hg, hg0, hg1, fun i => ⟨fun s => ζ i (g s),
    ⟨(hζc i).comp hg.continuousOn fun s hs => hsub' i (hgball s hs),
      fun s hs => (hchart i _ (hsub' i (hgball s hs))).2.1⟩, ?_, ?_⟩⟩
  · show ζ i (g 0) = ζ i τ₁
    rw [hg0]
  · show ζ i (g 1) = ζ i τ'
    rw [hg1]

/-! ## Following several zeros through simple zeros -/

/-- The property carried along a path `γ` with lifts `w i`: the times near `γ(s)` off the branch
times are reached from `γ(0)` by one forward path that transports every `w i 0` to a zero near
`w i s`. -/
def ReachedNearAll (γ : ℝ → ℂ) (w : ι → ℝ → ℂ) (s : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ τ' in 𝓝 (γ s), τ' ∉ branchTimes →
    ∃ g, IsForwardPath g ∧ g 0 = γ 0 ∧ g 1 = τ' ∧
      ∀ i, ∃ z₁, Transports g (w i 0) z₁ ∧ dist z₁ (w i s) < ε

/-- The property holds at the start. -/
theorem reachedNearAll_zero {γ : ℝ → ℂ} {w : ι → ℝ → ℂ} (hpos : 0 < (γ 0).re)
    (h0 : ∀ i, complexHeat (γ 0) (w i 0) = 0)
    (h1 : ∀ i, deriv (complexHeat (γ 0)) (w i 0) ≠ 0) (hb : γ 0 ∉ branchTimes) :
    ReachedNearAll γ w 0 := by
  intro ε hε
  obtain ⟨r, hr, ρ, hρ, ζ, hζc, huniq, hcont⟩ := exists_forward_continuation_in_charts hpos h0 h1
  have hc : γ 0 ∈ ball (γ 0) r := mem_ball_self hr
  have hwζ : ∀ i, w i 0 = ζ i (γ 0) := fun i => huniq i _ hc _ (mem_ball_self hρ) (h0 i)
  have hclose : ∀ᶠ τ' in 𝓝 (γ 0), ∀ i, ζ i τ' ∈ ball (ζ i (γ 0)) ε :=
    eventually_all.2 fun i =>
      ((hζc i).continuousAt (isOpen_ball.mem_nhds hc)).eventually (ball_mem_nhds _ hε)
  filter_upwards [isOpen_ball.eventually_mem hc, hclose] with τ' hτ'ball hτ'close hτ'b
  obtain ⟨g, hg, hg0, hg1, hT⟩ := hcont (γ 0) hc hb τ' hτ'ball hτ'b
  refine ⟨g, hg, hg0, hg1, fun i => ⟨ζ i τ', ?_, ?_⟩⟩
  · rw [hwζ i]
    exact hT i
  · rw [hwζ i]
    exact mem_ball.mp (hτ'close i)

/-- The property spreads over a neighbourhood of every parameter. -/
theorem exists_reachedNearAll_local {γ : ℝ → ℂ} {w : ι → ℝ → ℂ} (hγ : IsForwardTrack γ)
    (hw : ∀ i, IsSimpleLift γ (w i)) {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
    ∃ δ > 0, ∀ s₁ ∈ Icc (0 : ℝ) 1, dist s₁ s₀ < δ → ∀ s ∈ Icc (0 : ℝ) 1, dist s s₀ < δ →
      ReachedNearAll γ w s₁ → ReachedNearAll γ w s := by
  have hdense : Dense (branchTimesᶜ : Set ℂ) := countable_branchTimes.dense_compl ℝ
  obtain ⟨r, hr, ρ, hρ, ζ, hζc, huniq, hcont⟩ :=
    exists_forward_continuation_in_charts (hγ.re_pos s₀ hs₀)
      (fun i => (hw i).lift.zero s₀ hs₀) (fun i => (hw i).simple s₀ hs₀)
  -- near `s₀` the time is in the disc and every lift is in its chart
  have hnear : ∀ᶠ s in 𝓝[Icc (0 : ℝ) 1] s₀, γ s ∈ ball (γ s₀) r ∧
      ∀ i, w i s ∈ ball (w i s₀) (ρ / 2) :=
    (Filter.Tendsto.eventually (hγ.continuousOn s₀ hs₀) (ball_mem_nhds _ hr)).and
      (eventually_all.2 fun i => Filter.Tendsto.eventually ((hw i).lift.continuousOn s₀ hs₀)
        (ball_mem_nhds _ (half_pos hρ)))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  refine ⟨δ, hδ, fun s₁ hs₁ hd₁ s hs hd hG₁ ε hε => ?_⟩
  obtain ⟨hγs₁, hws₁⟩ := hδsub ⟨mem_ball.mpr hd₁, hs₁⟩
  obtain ⟨hγs, hws⟩ := hδsub ⟨mem_ball.mpr hd, hs⟩
  have hwζ : ∀ i, w i s = ζ i (γ s) := fun i =>
    huniq i _ hγs _ (ball_subset_ball (half_le_self hρ.le) (hws i)) ((hw i).lift.zero s hs)
  -- a time of the disc near `γ s₁`, off the branch times, reached from the base
  have hev : ∀ᶠ τ₁ in 𝓝 (γ s₁), τ₁ ∈ ball (γ s₀) r ∧ (τ₁ ∉ branchTimes →
      ∃ g, IsForwardPath g ∧ g 0 = γ 0 ∧ g 1 = τ₁ ∧
        ∀ i, ∃ z₁, Transports g (w i 0) z₁ ∧ dist z₁ (w i s₁) < ρ / 2) :=
    (isOpen_ball.eventually_mem hγs₁).and (hG₁ (ρ / 2) (half_pos hρ))
  obtain ⟨U, hU, hUo, hUmem⟩ := _root_.eventually_nhds_iff.mp hev
  obtain ⟨τ₁, hτ₁b, hτ₁U⟩ := hdense.exists_mem_open hUo ⟨γ s₁, hUmem⟩
  obtain ⟨hτ₁ball, hτ₁G⟩ := hU τ₁ hτ₁U
  obtain ⟨g₁, hg₁, hg₁0, hg₁1, hreach⟩ := hτ₁G hτ₁b
  choose z₁ hT₁ hz₁ using hreach
  have hz₁ζ : ∀ i, z₁ i = ζ i τ₁ := by
    intro i
    refine huniq i τ₁ hτ₁ball (z₁ i) ?_ ?_
    · rw [mem_ball]
      calc dist (z₁ i) (w i s₀) ≤ dist (z₁ i) (w i s₁) + dist (w i s₁) (w i s₀) :=
            dist_triangle _ _ _
        _ < ρ / 2 + ρ / 2 := add_lt_add (hz₁ i) (mem_ball.mp (hws₁ i))
        _ = ρ := add_halves ρ
    · have := (hT₁ i).zero_right
      rwa [hg₁1] at this
  -- the continuation inside the charts
  have hclose : ∀ᶠ τ' in 𝓝 (γ s), ∀ i, ζ i τ' ∈ ball (ζ i (γ s)) ε :=
    eventually_all.2 fun i =>
      ((hζc i).continuousAt (isOpen_ball.mem_nhds hγs)).eventually (ball_mem_nhds _ hε)
  filter_upwards [isOpen_ball.eventually_mem hγs, hclose] with τ' hτ'ball hτ'close hτ'b
  obtain ⟨g₂, hg₂, hg₂0, hg₂1, hT₂⟩ := hcont τ₁ hτ₁ball hτ₁b τ' hτ'ball hτ'b
  refine ⟨pathJoin g₁ g₂, hg₁.join hg₂ (hg₁1.trans hg₂0.symm), by rw [pathJoin_zero, hg₁0],
    by rw [pathJoin_one, hg₂1], fun i => ⟨ζ i τ', ?_, ?_⟩⟩
  · have h := hT₁ i
    rw [hz₁ζ i] at h
    exact h.trans (hT₂ i)
  · rw [hwζ i]
    exact mem_ball.mp (hτ'close i)

/-- **Several zeros followed through simple zeros are transported along one forward path.** Let
`γ` be a continuous path of forward times whose ends are not branch times, and `w i` finitely
many continuous lifts of zeros through simple zeros. Then one forward path off the branch times
with the same ends transports every `w i 0` to `w i 1`. -/
theorem exists_forward_transports_of_simple_lifts {γ : ℝ → ℂ} {w : ι → ℝ → ℂ}
    (hγ : IsForwardTrack γ) (hw : ∀ i, IsSimpleLift γ (w i)) (hb : γ 0 ∉ branchTimes)
    (hb' : γ 1 ∉ branchTimes) :
    ∃ g, IsForwardPath g ∧ g 0 = γ 0 ∧ g 1 = γ 1 ∧ ∀ i, Transports g (w i 0) (w i 1) := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hG0 : ReachedNearAll γ w 0 :=
    reachedNearAll_zero (hγ.re_pos 0 h01) (fun i => (hw i).lift.zero 0 h01)
      (fun i => (hw i).simple 0 h01) hb
  -- the property holds on the whole interval
  have hsub : Icc (0 : ℝ) 1 ⊆ {s | ReachedNearAll γ w s} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ hG0 ?_
    · refine isClosed_of_closure_subset fun x hx => ?_
      have hxI : x ∈ Icc (0 : ℝ) 1 := closure_minimal inter_subset_right isClosed_Icc hx
      obtain ⟨δ, hδ, hloc⟩ := exists_reachedNearAll_local hγ hw hxI
      obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx δ hδ
      exact ⟨hloc y hy.2 (by rwa [dist_comm]) x hxI (by rw [dist_self]; exact hδ) hy.1, hxI⟩
    · rintro x ⟨hxG, hx⟩
      have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
      obtain ⟨δ, hδ, hloc⟩ := exists_reachedNearAll_local hγ hw hxI
      have hlt : x < min (x + δ) 1 := lt_min (by linarith) hx.2
      refine Filter.mem_of_superset (Ioo_mem_nhdsGT hlt) fun y hy => ?_
      have hy1 : y ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith [hx.1, hy.1], (hy.2.trans_le (min_le_right _ _)).le⟩
      refine hloc x hxI (by rw [dist_self]; exact hδ) y hy1 ?_ hxG
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2.trans_le (min_le_left (x + δ) 1)]
  -- at the end the zero near `w i 1` is `w i 1`
  obtain ⟨r, hr, ρ, hρ, ζ, -, huniq, -⟩ :=
    exists_forward_continuation_in_charts (hγ.re_pos 1 h11)
      (fun i => (hw i).lift.zero 1 h11) (fun i => (hw i).simple 1 h11)
  obtain ⟨g, hg, hg0, hg1, hT⟩ := (hsub h11 ρ hρ).self_of_nhds hb'
  refine ⟨g, hg, hg0, hg1, fun i => ?_⟩
  obtain ⟨z₁, hTi, hz₁⟩ := hT i
  have hc : γ 1 ∈ ball (γ 1) r := mem_ball_self hr
  have hzero := hTi.zero_right
  rw [hg1] at hzero
  have e1 : z₁ = ζ i (γ 1) := huniq i _ hc _ (mem_ball.mpr hz₁) hzero
  have e2 : w i 1 = ζ i (γ 1) := huniq i _ hc _ (mem_ball_self hρ) ((hw i).lift.zero 1 h11)
  rw [e1, ← e2] at hTi
  exact hTi

/-- **One forward monodromy with prescribed values at finitely many zeros.** If finitely many
zeros `p i` of `H_b` are followed through simple zeros, along one loop of forward times at `b`,
to the zeros `q i`, then some element of the forward monodromy group moves every `p i` to
`q i`. -/
theorem exists_mem_forwardMonodromy_of_simple_lifts {b : ℂ} {hb₀ : 0 < b.re}
    {hb : b ∉ branchTimes} {γ : ℝ → ℂ} {w : ι → ℝ → ℂ} (hγ : IsForwardTrack γ)
    (hw : ∀ i, IsSimpleLift γ (w i)) (h0 : γ 0 = b) (h1 : γ 1 = b)
    (p q : ι → {z : ℂ // complexHeat b z = 0}) (hp : ∀ i, w i 0 = (p i).1)
    (hq : ∀ i, w i 1 = (q i).1) :
    ∃ σ ∈ forwardMonodromy b hb₀ hb, ∀ i, σ (p i) = q i := by
  obtain ⟨g, hg, hg0, hg1, hT⟩ := exists_forward_transports_of_simple_lifts hγ hw
    (by rw [h0]; exact hb) (by rw [h1]; exact hb)
  obtain ⟨σ, hσ, hσT⟩ := hg.exists_mem_forwardMonodromy (hτ := hb₀) (hb := hb)
    (hg0.trans h0) (hg1.trans h1)
  refine ⟨σ, hσ, fun i => Subtype.ext (hg.transports_unique (hσT (p i)) ?_)⟩
  have h := hT i
  rwa [hp i, hq i] at h

end

end GaloisForLFunctions.GaloisTheoryOfZeros
