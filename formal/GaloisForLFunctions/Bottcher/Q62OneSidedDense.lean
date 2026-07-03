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

open Set Metric Filter Topology

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

end Bottcher
