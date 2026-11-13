import GaloisForLFunctions.GaloisTheoryOfZeros.TheTransportOfAZeroDependsOnlyOnTheHomotopyClass

/-!
# A zero followed through simple zeros is moved by the forward monodromy

A path of forward times may pass through branch times and still carry a continuous family of
zeros, as long as the zeros of the family are simple: the collisions at the branch times happen
elsewhere in the fibre.

**Theorem** (`exists_forward_transports_of_simple_lift`). Let `γ` be a continuous path of forward
times whose ends are not branch times, and `w` a continuous lift of zeros along `γ` through
simple zeros. Then a forward path off the branch times, with the same ends, transports `w(0)` to
`w(1)`.

Hence the orbits of the forward monodromy group at `b` are the classes of the zeros of `H_b`
that are joined through simple zeros (`simplyJoined_iff_exists_mem_forwardMonodromy`): the group
is transitive iff the simple part of the heat cover over the forward half-plane is path connected.

Proof. Over a small disc of times around a simple zero the zeros near it form one continuous
family `ζ`, and two times of the disc off the branch times are joined inside the disc by an arc
that avoids the branch times (`exists_isForwardPath_mem_ball`); the lift of the arc is `ζ`
(`exists_forward_continuation_in_chart`). The property "times near `γ(s)` are reached from the
base by forward paths that transport `w(0)` to zeros near `w(s)`" therefore holds near every
parameter at which it holds once: it holds on `[0, 1]`.
-/

open Complex Filter Topology Set Metric
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Arcs inside a disc -/

/-- An arc between two points of a disc stays in the disc if its height is small. -/
theorem arcPath_mem_ball {c τ τ' : ℂ} {r r₁ η s : ℝ} (hτ : ‖τ - c‖ ≤ r₁) (hτ' : ‖τ' - c‖ ≤ r₁)
    (hη0 : 0 ≤ η) (hη : η * ‖τ' - τ‖ ≤ r - r₁) (hr : r₁ < r) (hs : s ∈ Icc (0 : ℝ) 1) :
    arcPath τ τ' η s ∈ ball c r := by
  have hs1 : 0 ≤ 1 - s := by linarith [hs.2]
  have hq : s * (1 - s) ≤ 1 / 4 := by nlinarith [sq_nonneg (s - 1 / 2)]
  have hq0 : 0 ≤ s * (1 - s) := mul_nonneg hs.1 hs1
  have e : arcPath τ τ' η s - c =
      ((1 - s : ℝ) : ℂ) * (τ - c) + (s : ℂ) * (τ' - c) +
        (τ' - τ) * (I * ((η * (s * (1 - s)) : ℝ) : ℂ)) := by
    unfold arcPath
    push_cast
    ring
  have h1 : ‖((1 - s : ℝ) : ℂ) * (τ - c)‖ ≤ (1 - s) * r₁ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs1]
    exact mul_le_mul_of_nonneg_left hτ hs1
  have h2 : ‖(s : ℂ) * (τ' - c)‖ ≤ s * r₁ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact mul_le_mul_of_nonneg_left hτ' hs.1
  have h3 : ‖(τ' - τ) * (I * ((η * (s * (1 - s)) : ℝ) : ℂ))‖ ≤ (r - r₁) * (1 / 4) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hη0 hq0)]
    have h4 : ‖τ' - τ‖ * (η * (s * (1 - s))) = η * ‖τ' - τ‖ * (s * (1 - s)) := by ring
    rw [h4]
    exact mul_le_mul hη hq hq0 (by linarith)
  rw [mem_ball, dist_eq_norm, e]
  have h5 := norm_add_le (((1 - s : ℝ) : ℂ) * (τ - c) + (s : ℂ) * (τ' - c))
    ((τ' - τ) * (I * ((η * (s * (1 - s)) : ℝ) : ℂ)))
  have h6 := norm_add_le (((1 - s : ℝ) : ℂ) * (τ - c)) ((s : ℂ) * (τ' - c))
  have h7 : (1 - s) * r₁ + s * r₁ = r₁ := by ring
  linarith

/-- **Two times of a disc of forward times, off the branch times, are joined inside the disc by
a forward path.** -/
theorem exists_isForwardPath_mem_ball {c τ τ' : ℂ} {r : ℝ} (hr : r ≤ c.re / 2)
    (hτ : τ ∈ ball c r) (hτ' : τ' ∈ ball c r) (hb : τ ∉ branchTimes) (hb' : τ' ∉ branchTimes) :
    ∃ g, IsForwardPath g ∧ g 0 = τ ∧ g 1 = τ' ∧ ∀ s ∈ Icc (0 : ℝ) 1, g s ∈ ball c r := by
  have hr0 : 0 < r := lt_of_le_of_lt dist_nonneg (mem_ball.mp hτ)
  have hc : 0 < c.re := by linarith
  -- the disc lies in a box of forward times
  have hbox : ∀ x ∈ ball c r, c.re / 2 ≤ x.re ∧ ‖x‖ ≤ ‖c‖ + r := by
    intro x hx
    have hx' : ‖x - c‖ < r := mem_ball_iff_norm.mp hx
    have h1 := abs_le.mp ((Complex.abs_re_le_norm (x - c)).trans hx'.le)
    rw [Complex.sub_re] at h1
    have h2 := norm_add_le (x - c) c
    rw [sub_add_cancel] at h2
    exact ⟨by linarith [h1.1], by linarith⟩
  rcases eq_or_ne τ τ' with rfl | hne
  · exact ⟨fun _ => τ, IsForwardPath.const (lt_of_lt_of_le (half_pos hc) (hbox τ hτ).1) hb, rfl,
      rfl, fun _ _ => hτ⟩
  have hr₁r : max ‖τ - c‖ ‖τ' - c‖ < r :=
    max_lt (mem_ball_iff_norm.mp hτ) (mem_ball_iff_norm.mp hτ')
  have hdn : 0 < ‖τ' - τ‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  have hη₀ : 0 < (r - max ‖τ - c‖ ‖τ' - c‖) / ‖τ' - τ‖ := div_pos (by linarith) hdn
  have hball : ∀ η ∈ Ioc (0 : ℝ) ((r - max ‖τ - c‖ ‖τ' - c‖) / ‖τ' - τ‖),
      ∀ s ∈ Icc (0 : ℝ) 1, arcPath τ τ' η s ∈ ball c r := by
    intro η hη s hs
    refine arcPath_mem_ball (le_max_left _ _) (le_max_right _ _) hη.1.le ?_ hr₁r hs
    calc η * ‖τ' - τ‖ ≤ (r - max ‖τ - c‖ ‖τ' - c‖) / ‖τ' - τ‖ * ‖τ' - τ‖ :=
          mul_le_mul_of_nonneg_right hη.2 hdn.le
      _ = r - max ‖τ - c‖ ‖τ' - c‖ := div_mul_cancel₀ _ hdn.ne'
  -- the arcs are disjoint and the box has finitely many branch times
  have hfin := finite_branchTimes_box (t₀ := c.re / 2) (‖c‖ + r) (half_pos hc)
  have hex : ∃ η ∈ Ioc (0 : ℝ) ((r - max ‖τ - c‖ ‖τ' - c‖) / ‖τ' - τ‖),
      ∀ s ∈ Icc (0 : ℝ) 1, arcPath τ τ' η s ∉ branchTimes := by
    by_contra hcon
    push Not at hcon
    choose! σ hσ using hcon
    have hmaps : MapsTo (fun η => arcPath τ τ' η (σ η))
        (Ioc (0 : ℝ) ((r - max ‖τ - c‖ ‖τ' - c‖) / ‖τ' - τ‖))
        {x : ℂ | x ∈ branchTimes ∧ c.re / 2 ≤ x.re ∧ ‖x‖ ≤ ‖c‖ + r} :=
      fun η hη => ⟨(hσ η hη).2, hbox _ (hball η hη _ (hσ η hη).1)⟩
    have hinj : InjOn (fun η => arcPath τ τ' η (σ η))
        (Ioc (0 : ℝ) ((r - max ‖τ - c‖ ‖τ' - c‖) / ‖τ' - τ‖)) := by
      intro η hη η' _ hff
      obtain ⟨hs, hc'⟩ := arcPath_inj hne hff
      rw [← hs] at hc'
      have h2 : (η - η') * (σ η * (1 - σ η)) = 0 := by linear_combination hc'
      rcases mul_eq_zero.1 h2 with h | h
      · linarith
      · exfalso
        have hmem := (hσ η hη).2
        rcases mul_eq_zero.1 h with h0 | h1
        · rw [h0, arcPath_zero] at hmem
          exact hb hmem
        · rw [show σ η = 1 by linarith, arcPath_one] at hmem
          exact hb' hmem
    exact Set.infinite_of_injOn_mapsTo hinj hmaps (Ioc_infinite hη₀) hfin
  obtain ⟨η, hη, hgood⟩ := hex
  exact ⟨arcPath τ τ' η, ⟨(continuous_arcPath τ τ' η).continuousOn,
    fun s hs => lt_of_lt_of_le (half_pos hc) (hbox _ (hball η hη s hs)).1, hgood⟩,
    arcPath_zero τ τ' η, arcPath_one τ τ' η, hball η hη⟩

/-! ## Continuation inside the chart of a simple zero -/

/-- **Continuation inside a chart.** Around a simple zero `(τ₀, z₀)` over a forward time there
are a disc of times, a disc of places and a continuous family `ζ` of zeros such that `ζ(τ)` is
the only zero of `H_τ` in the disc of places, and any two times of the disc off the branch times
are joined by a forward path that transports `ζ` at the first to `ζ` at the second. -/
theorem exists_forward_continuation_in_chart {τ₀ z₀ : ℂ} (hτ₀ : 0 < τ₀.re)
    (h0 : complexHeat τ₀ z₀ = 0) (h1 : deriv (complexHeat τ₀) z₀ ≠ 0) :
    ∃ r > 0, ∃ ρ > 0, ∃ ζ : ℂ → ℂ, ContinuousOn ζ (ball τ₀ r) ∧
      (∀ τ ∈ ball τ₀ r, ∀ z ∈ ball z₀ ρ, complexHeat τ z = 0 → z = ζ τ) ∧
      ∀ τ₁ ∈ ball τ₀ r, τ₁ ∉ branchTimes → ∀ τ' ∈ ball τ₀ r, τ' ∉ branchTimes →
        ∃ g, IsForwardPath g ∧ g 0 = τ₁ ∧ g 1 = τ' ∧ Transports g (ζ τ₁) (ζ τ') := by
  obtain ⟨W, hWo, hτW, ρ, hρ, ζ, hζc, -, hchart⟩ := exists_simple_zero_chart h0 h1
  obtain ⟨r₀, hr₀, hsub⟩ := Metric.isOpen_iff.mp hWo τ₀ hτW
  have hsub' : ball τ₀ (min r₀ (τ₀.re / 2)) ⊆ W :=
    (ball_subset_ball (min_le_left _ _)).trans hsub
  refine ⟨min r₀ (τ₀.re / 2), lt_min hr₀ (half_pos hτ₀), ρ, hρ, ζ, hζc.mono hsub',
    fun τ hτ z hz hzero => (hchart τ (hsub' hτ)).2.2.2 z hz hzero,
    fun τ₁ hτ₁ hb₁ τ' hτ' hb' => ?_⟩
  obtain ⟨g, hg, hg0, hg1, hgball⟩ :=
    exists_isForwardPath_mem_ball (min_le_right _ _) hτ₁ hτ' hb₁ hb'
  have hgW : MapsTo g (Icc (0 : ℝ) 1) W := fun s hs => hsub' (hgball s hs)
  refine ⟨g, hg, hg0, hg1, fun s => ζ (g s),
    ⟨hζc.comp hg.continuousOn hgW, fun s hs => (hchart _ (hgW hs)).2.1⟩, ?_, ?_⟩
  · show ζ (g 0) = ζ τ₁
    rw [hg0]
  · show ζ (g 1) = ζ τ'
    rw [hg1]

/-! ## Following a zero through simple zeros -/

/-- The property carried along a path `γ` with a lift `w`: the times near `γ(s)` off the branch
times are reached from `γ(0)` by forward paths that transport `w(0)` to zeros near `w(s)`. -/
def ReachedNear (γ w : ℝ → ℂ) (s : ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ τ' in 𝓝 (γ s), τ' ∉ branchTimes →
    ∃ g, IsForwardPath g ∧ g 0 = γ 0 ∧ g 1 = τ' ∧ ∃ z₁, Transports g (w 0) z₁ ∧ dist z₁ (w s) < ε

/-- The property holds at the start. -/
theorem reachedNear_zero {γ w : ℝ → ℂ} (hpos : 0 < (γ 0).re) (h0 : complexHeat (γ 0) (w 0) = 0)
    (h1 : deriv (complexHeat (γ 0)) (w 0) ≠ 0) (hb : γ 0 ∉ branchTimes) : ReachedNear γ w 0 := by
  intro ε hε
  obtain ⟨r, hr, ρ, hρ, ζ, hζc, huniq, hcont⟩ := exists_forward_continuation_in_chart hpos h0 h1
  have hc : γ 0 ∈ ball (γ 0) r := mem_ball_self hr
  have hwζ : w 0 = ζ (γ 0) := huniq _ hc _ (mem_ball_self hρ) h0
  have hζat : ContinuousAt ζ (γ 0) := hζc.continuousAt (isOpen_ball.mem_nhds hc)
  filter_upwards [isOpen_ball.eventually_mem hc, hζat.eventually (ball_mem_nhds _ hε)]
    with τ' hτ'ball hτ'close hτ'b
  obtain ⟨g, hg, hg0, hg1, hT⟩ := hcont (γ 0) hc hb τ' hτ'ball hτ'b
  refine ⟨g, hg, hg0, hg1, ζ τ', ?_, ?_⟩
  · rw [hwζ]
    exact hT
  · rw [hwζ]
    exact mem_ball.mp hτ'close

/-- The property spreads over a neighbourhood of every parameter. -/
theorem exists_reachedNear_local {γ w : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re) (hw : IsZeroLift γ 1 w)
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, deriv (complexHeat (γ s)) (w s) ≠ 0) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Icc (0 : ℝ) 1) :
    ∃ δ > 0, ∀ s₁ ∈ Icc (0 : ℝ) 1, dist s₁ s₀ < δ → ∀ s ∈ Icc (0 : ℝ) 1, dist s s₀ < δ →
      ReachedNear γ w s₁ → ReachedNear γ w s := by
  have hdense : Dense (branchTimesᶜ : Set ℂ) := countable_branchTimes.dense_compl ℝ
  obtain ⟨r, hr, ρ, hρ, ζ, hζc, huniq, hcont⟩ :=
    exists_forward_continuation_in_chart (hpos s₀ hs₀) (hw.zero s₀ hs₀) (hsimple s₀ hs₀)
  obtain ⟨δ₁, hδ₁, hγδ⟩ := Metric.continuousWithinAt_iff.mp (hγ s₀ hs₀) r hr
  obtain ⟨δ₂, hδ₂, hwδ⟩ :=
    Metric.continuousWithinAt_iff.mp (hw.continuousOn s₀ hs₀) (ρ / 2) (half_pos hρ)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s₁ hs₁ hd₁ s hs hd hG₁ ε hε => ?_⟩
  have hγs₁ : γ s₁ ∈ ball (γ s₀) r := hγδ hs₁ (hd₁.trans_le (min_le_left _ _))
  have hγs : γ s ∈ ball (γ s₀) r := hγδ hs (hd.trans_le (min_le_left _ _))
  have hws₁ : dist (w s₁) (w s₀) < ρ / 2 := hwδ hs₁ (hd₁.trans_le (min_le_right _ _))
  have hws : dist (w s) (w s₀) < ρ / 2 := hwδ hs (hd.trans_le (min_le_right _ _))
  have hwζ : w s = ζ (γ s) :=
    huniq _ hγs _ (mem_ball.mpr (hws.trans (half_lt_self hρ))) (hw.zero s hs)
  -- a time of the chart near `γ s₁`, off the branch times, reached from the base
  have hev : ∀ᶠ τ₁ in 𝓝 (γ s₁), τ₁ ∈ ball (γ s₀) r ∧ (τ₁ ∉ branchTimes →
      ∃ g, IsForwardPath g ∧ g 0 = γ 0 ∧ g 1 = τ₁ ∧
        ∃ z₁, Transports g (w 0) z₁ ∧ dist z₁ (w s₁) < ρ / 2) :=
    (isOpen_ball.eventually_mem hγs₁).and (hG₁ (ρ / 2) (half_pos hρ))
  obtain ⟨U, hU, hUo, hUmem⟩ := _root_.eventually_nhds_iff.mp hev
  obtain ⟨τ₁, hτ₁b, hτ₁U⟩ := hdense.exists_mem_open hUo ⟨γ s₁, hUmem⟩
  obtain ⟨hτ₁ball, hτ₁G⟩ := hU τ₁ hτ₁U
  obtain ⟨g₁, hg₁, hg₁0, hg₁1, z₁, hT₁, hz₁⟩ := hτ₁G hτ₁b
  have hz₁ζ : z₁ = ζ τ₁ := by
    refine huniq τ₁ hτ₁ball z₁ ?_ ?_
    · rw [mem_ball]
      calc dist z₁ (w s₀) ≤ dist z₁ (w s₁) + dist (w s₁) (w s₀) := dist_triangle _ _ _
        _ < ρ / 2 + ρ / 2 := add_lt_add hz₁ hws₁
        _ = ρ := add_halves ρ
    · have := hT₁.zero_right
      rwa [hg₁1] at this
  -- the continuation inside the chart
  have hζat : ContinuousAt ζ (γ s) := hζc.continuousAt (isOpen_ball.mem_nhds hγs)
  filter_upwards [isOpen_ball.eventually_mem hγs, hζat.eventually (ball_mem_nhds _ hε)]
    with τ' hτ'ball hτ'close hτ'b
  obtain ⟨g₂, hg₂, hg₂0, hg₂1, hT₂⟩ := hcont τ₁ hτ₁ball hτ₁b τ' hτ'ball hτ'b
  refine ⟨pathJoin g₁ g₂, hg₁.join hg₂ (hg₁1.trans hg₂0.symm), by rw [pathJoin_zero, hg₁0],
    by rw [pathJoin_one, hg₂1], ζ τ', ?_, ?_⟩
  · rw [hz₁ζ] at hT₁
    exact hT₁.trans hT₂
  · rw [hwζ]
    exact mem_ball.mp hτ'close

/-- **A zero followed through simple zeros is transported along a forward path.** Let `γ` be a
continuous path of forward times whose ends are not branch times, and `w` a continuous lift of
zeros through simple zeros. Then a forward path off the branch times with the same ends transports
`w(0)` to `w(1)`. -/
theorem exists_forward_transports_of_simple_lift {γ w : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1))
    (hpos : ∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re) (hw : IsZeroLift γ 1 w)
    (hsimple : ∀ s ∈ Icc (0 : ℝ) 1, deriv (complexHeat (γ s)) (w s) ≠ 0)
    (hb : γ 0 ∉ branchTimes) (hb' : γ 1 ∉ branchTimes) :
    ∃ g, IsForwardPath g ∧ g 0 = γ 0 ∧ g 1 = γ 1 ∧ Transports g (w 0) (w 1) := by
  have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hG0 : ReachedNear γ w 0 :=
    reachedNear_zero (hpos 0 h01) (hw.zero 0 h01) (hsimple 0 h01) hb
  -- the property holds on the whole interval
  have hsub : Icc (0 : ℝ) 1 ⊆ {s | ReachedNear γ w s} := by
    refine IsClosed.Icc_subset_of_forall_mem_nhdsWithin ?_ hG0 ?_
    · refine isClosed_of_closure_subset fun x hx => ?_
      have hxI : x ∈ Icc (0 : ℝ) 1 := closure_minimal inter_subset_right isClosed_Icc hx
      obtain ⟨δ, hδ, hloc⟩ := exists_reachedNear_local hγ hpos hw hsimple hxI
      obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx δ hδ
      exact ⟨hloc y hy.2 (by rwa [dist_comm]) x hxI (by rw [dist_self]; exact hδ) hy.1, hxI⟩
    · rintro x ⟨hxG, hx⟩
      have hxI : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
      obtain ⟨δ, hδ, hloc⟩ := exists_reachedNear_local hγ hpos hw hsimple hxI
      have hlt : x < min (x + δ) 1 := lt_min (by linarith) hx.2
      refine Filter.mem_of_superset (Ioo_mem_nhdsGT hlt) fun y hy => ?_
      have hy1 : y ∈ Icc (0 : ℝ) 1 :=
        ⟨by linarith [hx.1, hy.1], (hy.2.trans_le (min_le_right _ _)).le⟩
      refine hloc x hxI (by rw [dist_self]; exact hδ) y hy1 ?_ hxG
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2.trans_le (min_le_left (x + δ) 1)]
  -- at the end the zero near `w 1` is `w 1`
  obtain ⟨W, -, hτW, ρ, hρ, ζ, -, hζ1, hchart⟩ :=
    exists_simple_zero_chart (hw.zero 1 h11) (hsimple 1 h11)
  obtain ⟨g, hg, hg0, hg1, z₁, hT, hz₁⟩ := (hsub h11 ρ hρ).self_of_nhds hb'
  have hz : z₁ = w 1 := by
    have hzero := hT.zero_right
    rw [hg1] at hzero
    rw [← hζ1]
    exact (hchart (γ 1) hτW).2.2.2 z₁ (mem_ball.mpr hz₁) hzero
  rw [hz] at hT
  exact ⟨g, hg, hg0, hg1, hT⟩

/-! ## Simple joins and the orbits of the forward monodromy group -/

/-- `(τ, z)` and `(τ', z')` are joined through simple zeros: a continuous path of forward times
from `τ` to `τ'` has a continuous lift of zeros from `z` to `z'` all of whose points are simple
zeros. The path may pass through branch times. -/
def SimplyJoined (τ z τ' z' : ℂ) : Prop :=
  ∃ γ w : ℝ → ℂ, ContinuousOn γ (Icc 0 1) ∧ (∀ s ∈ Icc (0 : ℝ) 1, 0 < (γ s).re) ∧
    IsZeroLift γ 1 w ∧ (∀ s ∈ Icc (0 : ℝ) 1, deriv (complexHeat (γ s)) (w s) ≠ 0) ∧
    γ 0 = τ ∧ γ 1 = τ' ∧ w 0 = z ∧ w 1 = z'

theorem SimplyJoined.symm {τ z τ' z' : ℂ} (h : SimplyJoined τ z τ' z') :
    SimplyJoined τ' z' τ z := by
  obtain ⟨γ, w, hγ, hpos, hw, hs, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨pathRev γ, pathRev w, continuousOn_pathRev hγ, fun s hs' => hpos _ (mapsTo_one_sub hs'),
    ⟨continuousOn_pathRev hw.continuousOn, fun s hs' => hw.zero _ (mapsTo_one_sub hs')⟩,
    fun s hs' => hs _ (mapsTo_one_sub hs'), pathRev_zero γ, pathRev_one γ, pathRev_zero w,
    pathRev_one w⟩

theorem SimplyJoined.trans {τ z τ' z' τ'' z'' : ℂ} (h₁ : SimplyJoined τ z τ' z')
    (h₂ : SimplyJoined τ' z' τ'' z'') : SimplyJoined τ z τ'' z'' := by
  obtain ⟨γ₁, w₁, hγ₁, hpos₁, hw₁, hs₁, rfl, rfl, rfl, rfl⟩ := h₁
  obtain ⟨γ₂, w₂, hγ₂, hpos₂, hw₂, hs₂, hγ20, rfl, hw20, rfl⟩ := h₂
  refine ⟨pathJoin γ₁ γ₂, pathJoin w₁ w₂, continuousOn_pathJoin hγ₁ hγ₂ hγ20.symm,
    fun s hs => ?_, ⟨continuousOn_pathJoin hw₁.continuousOn hw₂.continuousOn hw20.symm,
      fun s hs => ?_⟩, fun s hs => ?_, pathJoin_zero γ₁ γ₂, pathJoin_one γ₁ γ₂,
    pathJoin_zero w₁ w₂, pathJoin_one w₁ w₂⟩
  · rcases le_or_gt s (1 / 2) with hle | hlt
    · rw [pathJoin_of_le hle]
      exact hpos₁ _ (mapsTo_double ⟨hs.1, hle⟩)
    · rw [pathJoin_of_lt hlt]
      exact hpos₂ _ (mapsTo_double_sub_one ⟨hlt.le, hs.2⟩)
  · rcases le_or_gt s (1 / 2) with hle | hlt
    · rw [pathJoin_of_le hle, pathJoin_of_le hle]
      exact hw₁.zero _ (mapsTo_double ⟨hs.1, hle⟩)
    · rw [pathJoin_of_lt hlt, pathJoin_of_lt hlt]
      exact hw₂.zero _ (mapsTo_double_sub_one ⟨hlt.le, hs.2⟩)
  · rcases le_or_gt s (1 / 2) with hle | hlt
    · rw [pathJoin_of_le hle, pathJoin_of_le hle]
      exact hs₁ _ (mapsTo_double ⟨hs.1, hle⟩)
    · rw [pathJoin_of_lt hlt, pathJoin_of_lt hlt]
      exact hs₂ _ (mapsTo_double_sub_one ⟨hlt.le, hs.2⟩)

/-- A transport along a forward path is a simple join. -/
theorem IsForwardPath.simplyJoined {γ : ℝ → ℂ} (hγ : IsForwardPath γ) {z z' : ℂ}
    (h : Transports γ z z') : SimplyJoined (γ 0) z (γ 1) z' := by
  obtain ⟨w, hw, rfl, rfl⟩ := h
  exact ⟨γ, w, hγ.continuousOn, hγ.re_pos, hw, fun s hs =>
    deriv_complexHeat_ne_zero_of_not_mem_branchTimes (hγ.simple s hs) (hw.zero s hs), rfl, rfl,
    rfl, rfl⟩

/-- A simple join between two times off the branch times is a transport along a forward path. -/
theorem SimplyJoined.exists_transports {b z b' z' : ℂ} (h : SimplyJoined b z b' z')
    (hb : b ∉ branchTimes) (hb' : b' ∉ branchTimes) :
    ∃ g, IsForwardPath g ∧ g 0 = b ∧ g 1 = b' ∧ Transports g z z' := by
  obtain ⟨γ, w, hγ, hpos, hw, hs, rfl, rfl, rfl, rfl⟩ := h
  exact exists_forward_transports_of_simple_lift hγ hpos hw hs hb hb'

/-- **The orbits of the forward monodromy group are the classes of simple joins.** Two zeros of
`H_b` are in one orbit of `G₊(b)` iff they are joined through simple zeros along a loop of forward
times. -/
theorem simplyJoined_iff_exists_mem_forwardMonodromy {b : ℂ} {hb₀ : 0 < b.re}
    {hb : b ∉ branchTimes} {p q : {z : ℂ // complexHeat b z = 0}} :
    SimplyJoined b p.1 b q.1 ↔ ∃ σ ∈ forwardMonodromy b hb₀ hb, σ p = q := by
  constructor
  · intro h
    obtain ⟨g, hg, hg0, hg1, hT⟩ := h.exists_transports hb hb
    obtain ⟨σ, hσ, hσT⟩ := hg.exists_mem_forwardMonodromy (hτ := hb₀) (hb := hb) hg0 hg1
    exact ⟨σ, hσ, Subtype.ext (hg.transports_unique (hσT p) hT)⟩
  · rintro ⟨σ, ⟨γ, hγ, h0, h1, hT⟩, rfl⟩
    have h := hγ.simplyJoined (hT p)
    rwa [h0, h1] at h

end

end GaloisForLFunctions.GaloisTheoryOfZeros
