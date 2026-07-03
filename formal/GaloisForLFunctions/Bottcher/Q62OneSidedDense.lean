/-
# Decomposing the ray-landing epic `OneSidedDense` (#133)

`OneSidedDense c` (`OneSidedCertificate.lean`) — one-sided frontier points (single local access to the
exterior) are dense in `J_c` — is the classical ray-landing input of the both-connected q62 chain.  It is
genuinely deep and *case-sensitive*: at an arc point of a dendrite Julia set, `ball x ρ \ K` splits into
two sides, so one-sidedness holds only at single-access points (dendrite *tips*), whose density is
Douady–Hubbard/Yoccoz-level and mathlib-absent.  This file does **not** fabricate that; it decomposes the
epic into a proven elementary part and a crisply-isolated deep part.

* `exists_supportBall_frontier_dense` — **proven.**  The elementary "part A": *supporting-ball* access
  points are dense in the frontier of any nonempty compact set.  Nearest-point construction — for a
  `Kᶜ`-point `y` near `x`, its nearest point `z ∈ K` carries a tangent ball `ball y r ⊆ Kᶜ`
  (`r = dist y z`) with `z ∈ frontier K` near `x`.  No external rays, no conformal boundary theory.
* `oneSidedAt_of_supportBall_singleAccess` — **proven.**  The reduction: a supporting-ball point whose
  local exterior is *exactly* that one ball (`ball z ρ ⊆ ball y r ∪ K` for small `ρ`, the single-access
  clause) is one-sided, because then `ball z ρ \ K = ball z ρ ∩ ball y r` is convex, hence connected.
* `SingleAccessDense` / `oneSidedDense_of_singleAccessDense` — **proven reduction.**  `OneSidedDense c`
  follows from the density of supporting-ball points that additionally have single access.

So #133's remaining content is exactly `SingleAccessDense c` — supporting-ball points with a *single*
round exterior access are dense — the sharp elementary-geometric form of ray-landing/local-connectivity
(the deep, still-open core).  The round-access density (part A) is discharged outright.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.OneSidedCertificate
import Mathlib.Tactic.ComputeDegree
import Mathlib.Analysis.Complex.Polynomial.Basic

open Set Metric Filter Topology Bornology

namespace Bottcher

/-- **Supporting-ball access points are dense in the frontier (part A of #133).**  For a nonempty
compact `K` and a frontier point `x`, arbitrarily close there is a frontier point `z` carrying a tangent
exterior ball `ball y r ⊆ Kᶜ` with `dist y z = r` — a *round* local access to the exterior.  Nearest-point
construction: take a `Kᶜ`-point `y` within `ε/3` of `x`; its nearest point `z ∈ K` has `r = dist y z =
dist y K > 0`, the open ball `ball y r` misses `K`, and `z` (on that ball's sphere, approached from inside
`ball y r ⊆ Kᶜ`) lies on `frontier K` within `ε` of `x`.  Elementary — no external rays. -/
theorem exists_supportBall_frontier_dense {K : Set ℂ} (hK : IsCompact K) (hKne : K.Nonempty)
    {x : ℂ} (hx : x ∈ frontier K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (z y : ℂ) (r : ℝ), z ∈ frontier K ∧ dist z x < ε ∧ 0 < r ∧ dist y z = r ∧
      Metric.ball y r ⊆ Kᶜ := by
  rw [frontier_eq_closure_inter_closure] at hx
  obtain ⟨hxK, hxKc⟩ := hx
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨y, hyKc, hyx⟩ := Metric.mem_closure_iff.mp hxKc (ε / 3) hε3
  obtain ⟨x', hx'K, hx'x⟩ := Metric.mem_closure_iff.mp hxK (ε / 3) hε3
  obtain ⟨z, hzK, hzmin⟩ :=
    hK.exists_isMinOn hKne (by fun_prop : ContinuousOn (fun w => dist y w) K)
  set r : ℝ := dist y z with hrdef
  have hr : 0 < r := by
    rw [hrdef, dist_pos]; rintro rfl; exact hyKc hzK
  -- the tangent ball misses `K`
  have hball : Metric.ball y r ⊆ Kᶜ := by
    intro w hw hwK
    rw [Metric.mem_ball, dist_comm] at hw
    exact absurd (lt_of_lt_of_le hw (hzmin hwK)) (lt_irrefl _)
  -- `z ∈ closure Kᶜ`: points on the segment `[z,y]` near `z` lie in `ball y r ⊆ Kᶜ`
  have hnorm_yz : ‖y - z‖ = r := by rw [← dist_eq_norm]
  have hzKc : z ∈ closure Kᶜ := by
    rw [Metric.mem_closure_iff]
    intro δ hδ
    set t : ℝ := min (δ / (2 * r)) (1 / 2) with htdef
    have ht0 : 0 < t := lt_min (by positivity) (by norm_num)
    have ht1 : t ≤ 1 / 2 := min_le_right _ _
    set w : ℂ := z + (t : ℂ) * (y - z) with hwdef
    have hwz : w - z = (t : ℂ) * (y - z) := by rw [hwdef]; ring
    have hwy : w - y = ((t : ℂ) - 1) * (y - z) := by rw [hwdef]; ring
    -- `w ∈ ball y r`
    have hwmem : w ∈ Metric.ball y r := by
      rw [Metric.mem_ball, dist_eq_norm, hwy, norm_mul, hnorm_yz]
      have h1 : ‖(t : ℂ) - 1‖ = 1 - t := by
        have e : (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
      rw [h1]; nlinarith [mul_pos ht0 hr]
    -- `dist z w < δ`
    have hdzw : dist z w < δ := by
      rw [dist_comm, dist_eq_norm, hwz, norm_mul, hnorm_yz]
      have h2 : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0.le]
      rw [h2]
      have htle : t ≤ δ / (2 * r) := min_le_left _ _
      calc t * r ≤ (δ / (2 * r)) * r := mul_le_mul_of_nonneg_right htle hr.le
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
    exact ⟨w, hball hwmem, hdzw⟩
  have hzfront : z ∈ frontier K := by
    rw [frontier_eq_closure_inter_closure]; exact ⟨subset_closure hzK, hzKc⟩
  -- `z` is within `ε` of `x`
  have hzx : dist z x < ε := by
    have hzy : dist z y = r := by rw [hrdef, dist_comm]
    have hr_le : r ≤ dist y x' := hzmin hx'K
    have hyx' : dist y x' < 2 * (ε / 3) := by
      calc dist y x' ≤ dist y x + dist x x' := dist_triangle y x x'
        _ < ε / 3 + ε / 3 := by rw [dist_comm y x]; exact add_lt_add hyx hx'x
        _ = 2 * (ε / 3) := by ring
    calc dist z x ≤ dist z y + dist y x := dist_triangle z y x
      _ = r + dist y x := by rw [hzy]
      _ < 2 * (ε / 3) + ε / 3 := by
          rw [dist_comm y x]; exact add_lt_add (lt_of_le_of_lt hr_le hyx') hyx
      _ = ε := by ring
  exact ⟨z, y, r, hzfront, hzx, hr, hrdef.symm, hball⟩

/-- **Single-access supporting ball ⟹ one-sided (the reduction).**  A frontier point `z` with a tangent
exterior ball `ball y r ⊆ Kᶜ` (`dist y z = r`) whose *only* local exterior is that ball — i.e.
`ball z ρ ⊆ ball y r ∪ filledJulia c` for all small `ρ` (the single-access clause) — is one-sided:
`ball z ρ \ K = ball z ρ ∩ ball y r`, an intersection of two balls, hence convex and connected. -/
theorem oneSidedAt_of_supportBall_singleAccess {c : ℂ} {z y : ℂ} {r : ℝ}
    (hzfront : z ∈ frontier (filledJulia c)) (hr : 0 < r) (hyz : dist y z = r)
    (hball : Metric.ball y r ⊆ (filledJulia c)ᶜ)
    (hsingle : ∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
        Metric.ball z ρ ⊆ Metric.ball y r ∪ filledJulia c) :
    OneSidedAt c z := by
  refine ⟨hzfront, ?_⟩
  obtain ⟨ρ₀, hρ₀, hcov⟩ := hsingle
  refine ⟨min ρ₀ r, lt_min hρ₀ hr, ?_⟩
  intro ρ hρ hρle
  have hρρ₀ : ρ ≤ ρ₀ := le_trans hρle (min_le_left _ _)
  have hρr : ρ ≤ r := le_trans hρle (min_le_right _ _)
  have hnorm_yz : ‖y - z‖ = r := by rw [← dist_eq_norm]; exact hyz
  -- identify the punctured ball with an intersection of two balls
  have hEq : Metric.ball z ρ \ filledJulia c = Metric.ball z ρ ∩ Metric.ball y r := by
    apply Set.eq_of_subset_of_subset
    · rintro w ⟨hwz, hwK⟩
      refine ⟨hwz, ?_⟩
      rcases hcov ρ hρ hρρ₀ hwz with hwy | hwK'
      · exact hwy
      · exact absurd hwK' hwK
    · rintro w ⟨hwz, hwy⟩
      exact ⟨hwz, fun hwK => hball hwy hwK⟩
  rw [hEq]
  refine ⟨?_, ((convex_ball z ρ).inter (convex_ball y r)).isPreconnected⟩
  -- nonempty: the point `w₀` a small step from `z` toward `y` lies in both balls
  set s : ℝ := ρ / 2 with hsdef
  have hs0 : 0 < s := by positivity
  have hsr : s < r := by rw [hsdef]; linarith
  set w₀ : ℂ := z + (↑(s / r) : ℂ) * (y - z) with hw₀def
  have hw₀z : w₀ - z = (↑(s / r) : ℂ) * (y - z) := by rw [hw₀def]; ring
  have hw₀y : w₀ - y = ((↑(s / r) : ℂ) - 1) * (y - z) := by rw [hw₀def]; ring
  refine ⟨w₀, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, hw₀z, norm_mul, hnorm_yz]
    have h1 : ‖(↑(s / r) : ℂ)‖ = s / r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h1, div_mul_cancel₀ s (ne_of_gt hr), hsdef]; linarith
  · rw [Metric.mem_ball, dist_eq_norm, hw₀y, norm_mul, hnorm_yz]
    have h2 : ‖(↑(s / r) : ℂ) - 1‖ = 1 - s / r := by
      have hsrle1 : s / r ≤ 1 := (div_le_one hr).mpr hsr.le
      have e : (↑(s / r) : ℂ) - 1 = ((s / r - 1 : ℝ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
    rw [h2, sub_mul, one_mul, div_mul_cancel₀ s (ne_of_gt hr)]; linarith

/-- **The single-access density Prop — the crisp remaining core of #133.**  Supporting-ball points with
a *single* round exterior access are dense in the frontier: near every frontier point there is a frontier
point `z` with a tangent exterior ball `ball y r ⊆ Kᶜ` that is its only local exterior.  This is the sharp
elementary-geometric form of the ray-landing/local-connectivity content; part A (round-access density,
`exists_supportBall_frontier_dense`) is proven, so this Prop is exactly the deep residual. -/
def SingleAccessDense (c : ℂ) : Prop :=
  ∀ p ∈ frontier (filledJulia c), ∀ ε > 0, ∃ (z y : ℂ) (r : ℝ),
    z ∈ frontier (filledJulia c) ∧ dist z p < ε ∧ 0 < r ∧ dist y z = r ∧
      Metric.ball y r ⊆ (filledJulia c)ᶜ ∧
      (∃ ρ₀ > 0, ∀ ρ, 0 < ρ → ρ ≤ ρ₀ →
        Metric.ball z ρ ⊆ Metric.ball y r ∪ filledJulia c)

/-- **`OneSidedDense` ⟸ `SingleAccessDense`.**  The single-access density Prop discharges the ray-landing
epic: each single-access supporting-ball point is one-sided (`oneSidedAt_of_supportBall_singleAccess`), so
one-sided points inherit its density.  This reduces #133 to `SingleAccessDense c` — with part A already
proven, that is precisely the deep single-access content. -/
theorem oneSidedDense_of_singleAccessDense {c : ℂ} (h : SingleAccessDense c) : OneSidedDense c := by
  intro p hp ε hε
  obtain ⟨z, y, r, hzf, hzp, hr, hyz, hball, hsingle⟩ := h p hp ε hε
  exact ⟨z, oneSidedAt_of_supportBall_singleAccess hzf hr hyz hball hsingle, by
    rw [dist_comm]; exact hzp⟩

/-! ## Visibility from infinity — the provable half of `ExposedOneSided` (OP6)

`ExposedOneSided c₁ c₂` needs a one-sided point of `J_{c₁}`, off `K_{c₂}`, **visible from infinity**
(`VisibleFromInfinity`).  The one-sidedness is the deep prime-end residual above; the visibility half is
elementary and proven here from the unbounded component of the joint complement `(K₁ ∪ K₂)ᶜ`: a boundary
point reached by an exterior ball whose component is unbounded lies in the closure of that unbounded
preconnected set. -/

/-- **Unbounded component from an unbounded preconnected subset.**  If a preconnected `T ⊆ S` through `y`
is unbounded, so is the connected component of `y` in `S` (it contains `T`).  The usual way to certify
that a component reaches infinity: exhibit one unbounded preconnected set inside it. -/
theorem unbounded_connectedComponentIn_of_subset {S T : Set ℂ} {y : ℂ}
    (hT : IsPreconnected T) (hyT : y ∈ T) (hTS : T ⊆ S) (hTunb : ¬ IsBounded T) :
    ¬ IsBounded (connectedComponentIn S y) := fun hbd =>
  hTunb (hbd.subset (hT.subset_connectedComponentIn hyT hTS))

/-- **Visibility from an exterior ball in the unbounded component.**  If `x` lies on the sphere of a
ball `ball y r ⊆ (K₁ ∪ K₂)ᶜ` (`dist x y = r`) whose connected component in the joint complement is
unbounded, then `x` is visible from infinity: that component is an unbounded preconnected subset of
`(K₁ ∪ K₂)ᶜ` containing `ball y r`, hence containing `x` in its closure.  This is the visibility clause of
`ExposedOneSided` discharged for any boundary point exposed to the unbounded joint exterior. -/
theorem visibleFromInfinity_of_supportBall_unbounded {c₁ c₂ x y : ℂ} {r : ℝ} (hr : r ≠ 0)
    (hxy : dist x y = r)
    (hball : Metric.ball y r ⊆ (filledJulia c₁ ∪ filledJulia c₂)ᶜ)
    (hunb : ¬ IsBounded (connectedComponentIn ((filledJulia c₁ ∪ filledJulia c₂)ᶜ) y)) :
    VisibleFromInfinity c₁ c₂ x := by
  have hrpos : 0 < r := lt_of_le_of_ne (hxy ▸ dist_nonneg) (Ne.symm hr)
  set S : Set ℂ := (filledJulia c₁ ∪ filledJulia c₂)ᶜ with hSdef
  set W : Set ℂ := connectedComponentIn S y with hWdef
  have hballW : Metric.ball y r ⊆ W :=
    (convex_ball y r).isPreconnected.subset_connectedComponentIn (Metric.mem_ball_self hrpos) hball
  refine ⟨W, isPreconnected_connectedComponentIn, hunb, connectedComponentIn_subset S y, ?_⟩
  have hxcl : x ∈ closure (Metric.ball y r) := by
    rw [closure_ball y hr, Metric.mem_closedBall]; exact le_of_eq hxy
  exact closure_mono hballW hxcl

/-- **The filled Julia set is always nonempty.**  A fixed point of `z ↦ z² + c` (a root of `z² − z + c`,
which exists over `ℂ`) has a constant, hence bounded, orbit, so lies in `filledJulia c`. -/
theorem nonempty_filledJulia (c : ℂ) : (filledJulia c).Nonempty := by
  have hdeg : (Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c).degree = 2 := by compute_degree!
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (p := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C c) (by rw [hdeg]; decide)
  have hfix : quadratic c z = z := by
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C] at hz
    rw [quadratic_apply]; linear_combination hz
  refine ⟨z, ?_⟩
  rw [mem_filledJulia_iff]
  have horbit : ∀ n : ℕ, (quadratic c)^[n] z = z := by
    intro n; induction n with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ', Function.comp_apply, ih, hfix]
  have hset : (Set.range fun n : ℕ => (quadratic c)^[n] z) = {z} := by
    ext w; simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨n, hn⟩ => hn ▸ horbit n, fun h => ⟨0, h ▸ rfl⟩⟩
  rw [hset]; exact (Set.finite_singleton z).isBounded

/-- **A visible frontier point of the joint set always exists.**  For the joint set `K₁ ∪ K₂` (compact),
a far real point `y₀` (beyond a bounding radius) has a nearest joint-set point `x₀`, giving an exterior
ball tangent at `x₀`; the outward ray from `y₀` certifies its component is unbounded, so `x₀ ∈
frontier (K₁ ∪ K₂)` is visible from infinity.  The visibility half of `ExposedOneSided`, unconditionally. -/
theorem exists_visible_frontier_point (c₁ c₂ : ℂ) :
    ∃ x ∈ frontier (filledJulia c₁ ∪ filledJulia c₂), VisibleFromInfinity c₁ c₂ x := by
  set K : Set ℂ := filledJulia c₁ ∪ filledJulia c₂ with hKdef
  have hKcomp : IsCompact K := (isCompact_filledJulia c₁).union (isCompact_filledJulia c₂)
  have hKne : K.Nonempty := (nonempty_filledJulia c₁).mono subset_union_left
  -- a bounding radius `R` for `K`
  obtain ⟨R, hR0, hRK⟩ := hKcomp.isBounded.subset_closedBall_lt 0 0
  -- a far real anchor `y₀`
  set y₀ : ℂ := ((R + 1 : ℝ) : ℂ) with hy₀def
  have hy₀norm : ‖y₀‖ = R + 1 := by rw [hy₀def, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith)]
  have hy₀K : y₀ ∉ K := by
    intro h; have := hRK h; rw [Metric.mem_closedBall, dist_zero_right, hy₀norm] at this; linarith
  -- nearest joint-set point to `y₀`
  obtain ⟨x₀, hx₀K, hx₀min⟩ :=
    hKcomp.exists_isMinOn hKne (by fun_prop : ContinuousOn (fun w => dist y₀ w) K)
  set r : ℝ := dist y₀ x₀ with hrdef
  have hr : 0 < r := by rw [hrdef, dist_pos]; rintro rfl; exact hy₀K hx₀K
  -- the tangent ball misses `K`
  have hball : Metric.ball y₀ r ⊆ Kᶜ := by
    intro w hw hwK
    rw [Metric.mem_ball, dist_comm] at hw
    exact absurd (lt_of_lt_of_le hw (hx₀min hwK)) (lt_irrefl _)
  -- outward ray from `y₀` (real direction), unbounded, in `Kᶜ`
  set T : Set ℂ := (fun t : ℝ => y₀ + ((t : ℝ) : ℂ)) '' Set.Ici 0 with hTdef
  have hTconn : IsPreconnected T :=
    (isPreconnected_Ici).image _ (by fun_prop : Continuous fun t : ℝ => y₀ + ((t : ℝ) : ℂ)).continuousOn
  have hTnorm : ∀ p ∈ T, R + 1 ≤ ‖p‖ := by
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_Ici] at ht
    show R + 1 ≤ ‖y₀ + (t : ℂ)‖
    rw [show y₀ + (t : ℂ) = (((R + 1 + t : ℝ)) : ℂ) by rw [hy₀def]; push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hTK : T ⊆ Kᶜ := by
    intro p hp hpK; have := hRK hpK
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith [hTnorm p hp]
  have hy₀T : y₀ ∈ T := ⟨0, Set.mem_Ici.mpr le_rfl, by simp⟩
  have hTunb : ¬ IsBounded T := by
    intro hbd
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbd
    have hp : (y₀ + ((max C 0 + 1 : ℝ) : ℂ)) ∈ T :=
      ⟨max C 0 + 1, Set.mem_Ici.mpr (by positivity), rfl⟩
    have h1 := hC _ hp
    have h2 := hTnorm _ hp
    have h3 : R + 1 ≤ C := le_trans h2 h1
    -- but the point has norm ≥ R + 1 + (max C 0 + 1) > C
    rw [show y₀ + ((max C 0 + 1 : ℝ) : ℂ) = (((R + 1 + (max C 0 + 1) : ℝ)) : ℂ) by
        rw [hy₀def]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at h1
    have : C ≤ max C 0 := le_max_left _ _
    linarith
  have hunb : ¬ IsBounded (connectedComponentIn Kᶜ y₀) :=
    unbounded_connectedComponentIn_of_subset hTconn hy₀T hTK hTunb
  -- `x₀ ∈ frontier K`
  have hx₀front : x₀ ∈ frontier K := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure hx₀K, ?_⟩
    rw [Metric.mem_closure_iff]
    intro δ hδ
    set t : ℝ := min (δ / 2) (r / 2) with htdef
    have ht0 : 0 < t := lt_min (by linarith) (by linarith)
    set w : ℂ := x₀ + ((t / r : ℝ) : ℂ) * (y₀ - x₀) with hwdef
    have hnorm : ‖y₀ - x₀‖ = r := by rw [← dist_eq_norm]
    have hwx : w - x₀ = ((t / r : ℝ) : ℂ) * (y₀ - x₀) := by rw [hwdef]; ring
    have hwmem : w ∈ Metric.ball y₀ r := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : w - y₀ = ((t / r - 1 : ℝ) : ℂ) * (y₀ - x₀) := by rw [hwdef]; push_cast; ring
      rw [this, norm_mul, hnorm]
      have hnn : ‖((t / r - 1 : ℝ) : ℂ)‖ = 1 - t / r := by
        have htr1 : t / r ≤ 1 := by
          rw [div_le_one hr]; calc t ≤ r / 2 := min_le_right _ _
            _ ≤ r := by linarith
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
      rw [hnn, sub_mul, one_mul, div_mul_cancel₀ t (ne_of_gt hr)]; linarith
    refine ⟨w, hball hwmem, ?_⟩
    rw [dist_comm, dist_eq_norm, hwx, norm_mul, hnorm]
    have hnn : ‖((t / r : ℝ) : ℂ)‖ = t / r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hnn, div_mul_cancel₀ t (ne_of_gt hr)]
    calc t ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  exact ⟨x₀, hx₀front, visibleFromInfinity_of_supportBall_unbounded (ne_of_gt hr)
    (by rw [hrdef, dist_comm]) hball hunb⟩

end Bottcher
