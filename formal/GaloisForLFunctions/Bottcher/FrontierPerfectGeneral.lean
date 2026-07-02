/-
# The frontier of a perfect closed plane set is perfect (no empty-interior hypothesis)

The witness-supply brick of the pigeonhole route for the OP4 class, whose filled Julia sets have
nonempty interior — the in-tree perfect-frontier results all assume empty interior.  The proof is
elementary plane geometry, no Jordan curve theorem: if `w` were isolated in `∂K`, pick an interior
point `k` of `K` near `w` (perfectness of `K`) and TWO exterior points `e, e′` near `w` with
non-parallel directions `w−e, w−e′` (rotate by `i` inside an exterior ball).  Each segment from
`k` to an exterior point crosses `∂K` inside the isolation ball, hence through `w`; so `k − w` is
a nonnegative multiple of both `w−e` and `w−e′`, forcing `k = w` — contradiction.  Feeds the
countable-avoidance witness selection at the hole-free tip.  Axiom-clean.
-/
import Mathlib.Topology.MetricSpace.Perfect
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Topology
import GaloisForLFunctions.Bottcher.JuliaFrontierPerfect

open Set Metric Filter Topology

namespace Bottcher

/-- **Segment crossing**: a segment from an interior point of a closed set to an exterior point
meets the frontier. -/
theorem segment_meets_frontier {K : Set ℂ} (hKcl : IsClosed K) {x y : ℂ}
    (hx : x ∈ interior K) (hy : y ∉ K) :
    ∃ z ∈ segment ℝ x y, z ∈ frontier K := by
  by_contra hcon
  push Not at hcon
  have hcover : segment ℝ x y ⊆ interior K ∪ Kᶜ := by
    intro z hz
    by_cases hzK : z ∈ K
    · left
      by_contra hzint
      exact hcon z hz (by rw [hKcl.frontier_eq]; exact ⟨hzK, hzint⟩)
    · exact Or.inr hzK
  have hsegc : IsPreconnected (segment ℝ x y) := (convex_segment x y).isPreconnected
  obtain ⟨z, hz⟩ := hsegc (interior K) Kᶜ isOpen_interior hKcl.isOpen_compl hcover
    ⟨x, left_mem_segment ℝ x y, hx⟩ ⟨y, right_mem_segment ℝ x y, hy⟩
  exact hz.2.2 (interior_subset hz.2.1)

/-- A segment point `w ≠ e` on `[k, e]` puts `k` on the ray from `w` away from `e`. -/
theorem sub_eq_smul_of_mem_segment {k e w : ℂ} (hw : w ∈ segment ℝ k e) (hne : w ≠ e) :
    ∃ s : ℝ, 0 ≤ s ∧ k - w = s • (w - e) := by
  rw [segment_eq_image] at hw
  obtain ⟨t, hmem, hteq⟩ := hw
  obtain ⟨ht0, ht1⟩ := hmem
  have htne : t ≠ 1 := fun h => hne (by rw [← hteq, h]; simp)
  have htlt : t < 1 := lt_of_le_of_ne ht1 htne
  have h1t : (0 : ℝ) < 1 - t := by linarith
  refine ⟨t / (1 - t), div_nonneg ht0 h1t.le, ?_⟩
  have hteq' : ((1 - t : ℝ) : ℂ) * k + ((t : ℝ) : ℂ) * e = w := by
    rw [← hteq]
    simp only
    rw [Complex.real_smul, Complex.real_smul]
  have h1tC : (1 : ℂ) - (t : ℂ) ≠ 0 := by
    exact_mod_cast h1t.ne'
  rw [Complex.real_smul]
  push_cast at hteq' ⊢
  field_simp
  linear_combination hteq'

/-- **The frontier of a perfect closed plane set is perfect.**  The two-ray isolation argument;
no empty-interior or Jordan-curve input. -/
theorem perfect_frontier_of_perfect {K : Set ℂ} (hK : Perfect K) :
    Perfect (frontier K) := by
  refine ⟨isClosed_frontier, ?_⟩
  intro w hw
  rw [accPt_iff_nhds]
  intro V hV
  by_contra hcon
  push Not at hcon
  -- the isolation ball
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hiso : ∀ y ∈ Metric.ball w ε ∩ frontier K, y = w := fun y hy =>
    hcon y ⟨hball hy.1, hy.2⟩
  have hwK : w ∈ K := hK.closed.frontier_subset hw
  -- an interior point of `K` in the ball, distinct from `w`
  obtain ⟨k, ⟨hkball, hkK⟩, hkne⟩ :=
    accPt_iff_nhds.mp (hK.acc w hwK) (Metric.ball w ε) (Metric.ball_mem_nhds w hε)
  have hkint : k ∈ interior K := by
    by_contra hint
    exact hkne (hiso k ⟨hkball, by rw [hK.closed.frontier_eq]; exact ⟨hkK, hint⟩⟩)
  -- an exterior point in the ball, and a small exterior ball around it
  have hwcl : w ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hw
    exact hw.2
  obtain ⟨e, heball, heK⟩ := mem_closure_iff.mp hwcl _ Metric.isOpen_ball
    (Metric.mem_ball_self hε)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp
    (Metric.isOpen_ball.inter hK.closed.isOpen_compl) e ⟨heball, heK⟩
  -- the two exterior directions
  set u : ℂ := w - e with hudef
  have hwe : w ≠ e := fun h => heK (h ▸ hwK)
  have hu : u ≠ 0 := sub_ne_zero.mpr hwe
  have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set d : ℝ := δ / (2 * ‖u‖) with hddef
  have hd : 0 < d := by positivity
  set e' : ℂ := e + d • (Complex.I * u) with he'def
  have he'mem : e' ∈ Metric.ball w ε ∩ Kᶜ := by
    apply hδsub
    rw [Metric.mem_ball, dist_eq_norm, he'def, add_sub_cancel_left, norm_smul,
      norm_mul, Complex.norm_I, one_mul, Real.norm_eq_abs, abs_of_pos hd]
    have hlt : d * ‖u‖ = δ / 2 := by
      rw [hddef]
      field_simp
    rw [hlt]
    linarith
  have hwe' : w ≠ e' := fun h => he'mem.2 (h ▸ hwK)
  -- both segments cross the frontier inside the ball, hence through `w`
  have hcross : ∀ y : ℂ, y ∈ Metric.ball w ε → y ∉ K → w ∈ segment ℝ k y := by
    intro y hyball hyK
    obtain ⟨z, hzseg, hzfr⟩ := segment_meets_frontier hK.closed hkint hyK
    have hzball : z ∈ Metric.ball w ε :=
      (convex_ball w ε).segment_subset hkball hyball hzseg
    have hzw : z = w := hiso z ⟨hzball, hzfr⟩
    rwa [hzw] at hzseg
  obtain ⟨s, _hs0, hs⟩ :=
    sub_eq_smul_of_mem_segment (hcross e heball heK) hwe
  obtain ⟨s', _hs'0, hs'⟩ :=
    sub_eq_smul_of_mem_segment (hcross e' he'mem.1 he'mem.2) hwe'
  -- the two ray equations force `k = w`
  have hfac : w - e' = u * (1 - (d : ℝ) * Complex.I) := by
    rw [he'def, hudef, Complex.real_smul]
    ring
  have hcancel : ((s : ℝ) : ℂ) = ((s' : ℝ) : ℂ) * (1 - (d : ℝ) * Complex.I) := by
    have h1 : u * ((s : ℝ) : ℂ) = u * (((s' : ℝ) : ℂ) * (1 - (d : ℝ) * Complex.I)) := by
      have h2 : (s : ℝ) • (w - e) = (s' : ℝ) • (w - e') := by rw [← hs, ← hs']
      rw [Complex.real_smul, Complex.real_smul, hfac, ← hudef] at h2
      calc u * ((s : ℝ) : ℂ) = ((s : ℝ) : ℂ) * u := by ring
        _ = ((s' : ℝ) : ℂ) * (u * (1 - (d : ℝ) * Complex.I)) := h2
        _ = u * (((s' : ℝ) : ℂ) * (1 - (d : ℝ) * Complex.I)) := by ring
    exact mul_left_cancel₀ hu h1
  have hs'0 : s' = 0 := by
    have him := congrArg Complex.im hcancel
    simp [Complex.mul_im, Complex.sub_im, Complex.sub_re, Complex.mul_re,
      Complex.I_im, Complex.I_re, Complex.ofReal_im, Complex.ofReal_re,
      Complex.one_im, Complex.one_re] at him
    rcases him with h | h
    · exact h
    · exact absurd h hd.ne'
  have hkw : k - w = 0 := by
    rw [hs', hs'0]
    simp
  exact hkne (sub_eq_zero.mp hkw)

/-- **Perfect frontier for every connected filled Julia set** — no empty-interior hypothesis; in
particular for the OP4 main-cardioid class where `K_c` has interior. -/
theorem perfect_frontier_filledJulia_of_preconnected {c : ℂ}
    (hconn : IsPreconnected (filledJulia c)) :
    Perfect (frontier (filledJulia c)) :=
  perfect_frontier_of_perfect
    (perfect_filledJulia_of_preconnected_nontrivial hconn (filledJulia_nontrivial c))

/-- Uncountability of every Julia ball piece, connected case, no empty-interior hypothesis —
the countable-avoidance supply for the separable-witness selection at the hole-free tip. -/
theorem not_countable_ball_inter_frontier_filledJulia_of_preconnected {c p : ℂ}
    (hconn : IsPreconnected (filledJulia c))
    (hp : p ∈ frontier (filledJulia c)) {r : ℝ} (hr : 0 < r) :
    ¬ (Metric.ball p r ∩ frontier (filledJulia c)).Countable :=
  not_countable_ball_inter_perfect (perfect_frontier_filledJulia_of_preconnected hconn) hp hr

end Bottcher
