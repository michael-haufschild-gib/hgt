import GaloisForLFunctions.InfiniteRankPurityTheory.EliminationNeedsOnlyAnAttainedTop
import GaloisForLFunctions.BlackHoleRingdown.TheInverseXiContour
import GaloisForLFunctions.HTGeometry.CircleQuadraturePositiveWolffMeasure

/-!
# A mode accessible from infinity is eliminated

Elimination with an attained top reads the weight on the top circle by window means. This module
eliminates modes below the top by a second mechanism, the analytic continuation of the resolvent,
and so weakens the hypothesis that the top is attained.

For a summable tower with bounded modes the resolvent `Φ(w) = Σ_i c_i / (w − z_i)` is analytic off
the closure of the modes, and outside the modes it is the Laurent series `Σ_ν S(ν) w^{−ν−1}` of the
level sums (`towerResolvent_eq_levelSeries`). If `‖S(ν)‖ ≤ C r^ν` at every level, the Laurent series
is analytic on `‖w‖ > r` (`analyticAt_levelSeries`).

**Theorem** (`merged_eq_zero_of_accessible`). Let `‖S(ν)‖ ≤ C r^ν` at every level. Let `z_j` be an
isolated mode joined to a point beyond all modes by a path that, apart from `z_j`, stays in
`‖w‖ > r` and off the closure of the modes. Then the tower carries no weight at `z_j`.

**Proof.** Along the path the resolvent and the Laurent series are analytic and agree at its far
end, hence on the whole path. Near `z_j` the Laurent series is bounded, while `(w − z_j) Φ(w)` tends
to the weight at `z_j`.

Modes above `z_j` may be infinite in number and may accumulate on the top circle; the top need not
be attained. Elimination on all levels fails only behind a wall: when the closure of the modes
separates `z_j` from infinity. Such walls exist: no isolated node of the positive Wolff measure is
accessible (`wolff_node_not_accessible`). The outward segment is the simplest path
(`merged_eq_zero_of_radially_visible`).

For the tower of `ζ` at a base `ℓ` (`lag_not_small_of_accessible`,
`lag_not_small_of_radially_visible`): a zero `ρ₀` with `Re ρ₀ > ½ + a` whose mode is isolated and
accessible is incompatible with the count `Φ(νℓ) = O(e^{aνℓ})` along all levels, and RH follows
from a bounded lag along one tower as soon as a failure of RH comes with one such zero
(`riemannHypothesis_of_lag_bounded_of_accessible`).
-/

open Filter Topology Complex Set Metric

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.InfiniteRankWeilTheory renaming lagWeight → lagW,
  summable_norm_lagWeight → summable_norm_lagW, re_lagWeight_pos → re_lagW_pos

variable {ι : Type*}

/-- The resolvent of a tower: `Φ(w) = Σ_i c_i / (w − z_i)`. -/
noncomputable def towerResolvent (c z : ι → ℂ) (w : ℂ) : ℂ := ∑' i, c i / (w - z i)

/-- The Laurent series of the level sums: `Σ_ν S(ν) / w^{ν+1}`. -/
noncomputable def levelSeries (c z : ι → ℂ) (w : ℂ) : ℂ :=
  ∑' ν : ℕ, towerSum c z ν / w ^ (ν + 1)

/-- **Outside the modes the resolvent is the Laurent series of the level sums.** -/
theorem towerResolvent_eq_levelSeries {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ i, ‖z i‖ ≤ R) {w : ℂ} (hw : R < ‖w‖) :
    towerResolvent c z w = levelSeries c z w := by
  have hw0 : 0 < ‖w‖ := hR0.trans_lt hw
  have hwne : w ≠ 0 := norm_pos_iff.mp hw0
  have hq0 : 0 ≤ R / ‖w‖ := div_nonneg hR0 hw0.le
  have hq : R / ‖w‖ < 1 := (div_lt_one hw0).mpr hw
  -- the geometric expansion of one term
  have hgeo : ∀ i, HasSum (fun ν : ℕ => c i * z i ^ ν / w ^ (ν + 1)) (c i / (w - z i)) := by
    intro i
    have hξ : ‖z i / w‖ < 1 := by
      rw [norm_div, div_lt_one hw0]
      exact (hR i).trans_lt hw
    have hne : w - z i ≠ 0 := sub_ne_zero.mpr fun h => by
      rw [h] at hw
      exact absurd (hR i) (not_le.mpr hw)
    have h := (hasSum_geometric_of_norm_lt_one hξ).mul_left (c i / w)
    have hval : c i / w * (1 - z i / w)⁻¹ = c i / (w - z i) := by
      have h1 : 1 - z i / w = (w - z i) / w := by
        rw [sub_div, div_self hwne]
      rw [h1, inv_div, div_mul_div_comm, mul_comm (c i) w, mul_div_mul_left _ _ hwne]
    have hfun : (fun ν : ℕ => c i * z i ^ ν / w ^ (ν + 1)) =
        fun ν => c i / w * (z i / w) ^ ν := by
      funext ν
      rw [div_pow, pow_succ, div_mul_div_comm, mul_comm (w ^ ν) w]
    rw [hfun, ← hval]
    exact h
  -- the double series converges absolutely
  have hsum : Summable (Function.uncurry fun (i : ι) (ν : ℕ) =>
      c i * z i ^ ν / w ^ (ν + 1)) := by
    have hmaj : Summable fun p : ι × ℕ => ‖c p.1‖ * ((R / ‖w‖) ^ p.2 / ‖w‖) :=
      Summable.mul_of_nonneg hc ((summable_geometric_of_lt_one hq0 hq).div_const _)
        (fun _ => norm_nonneg _) fun ν => div_nonneg (pow_nonneg hq0 ν) hw0.le
    refine Summable.of_norm_bounded hmaj fun p => ?_
    simp only [Function.uncurry]
    rw [norm_div, norm_mul, norm_pow, norm_pow, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [div_pow, pow_succ, div_div]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hR p.1) p.2)
      (mul_nonneg (pow_nonneg hw0.le _) hw0.le)
  rw [towerResolvent, levelSeries]
  calc ∑' i, c i / (w - z i) = ∑' i, ∑' ν : ℕ, c i * z i ^ ν / w ^ (ν + 1) :=
        tsum_congr fun i => (hgeo i).tsum_eq.symm
    _ = ∑' ν : ℕ, ∑' i, c i * z i ^ ν / w ^ (ν + 1) := hsum.tsum_comm.symm
    _ = ∑' ν : ℕ, towerSum c z ν / w ^ (ν + 1) :=
        tsum_congr fun ν => by rw [towerSum, tsum_div_const]

/-- **A bound `O(r^ν)` on the level sums continues the Laurent series to `‖w‖ > r`.** -/
theorem analyticAt_levelSeries {c z : ι → ℂ} {C r : ℝ} (hr : 0 ≤ r)
    (hS : ∀ ν : ℕ, ‖towerSum c z ν‖ ≤ C * r ^ ν) {w : ℂ} (hw : r < ‖w‖) :
    AnalyticAt ℂ (levelSeries c z) w := by
  obtain ⟨r', hr1, hr2⟩ := exists_between hw
  have hr'0 : 0 < r' := hr.trans_lt hr1
  have hopen : IsOpen {u : ℂ | r' < ‖u‖} := isOpen_lt continuous_const continuous_norm
  have hq : r / r' < 1 := (div_lt_one hr'0).mpr hr1
  have hd : DifferentiableOn ℂ (fun u : ℂ => ∑' ν : ℕ, towerSum c z ν / u ^ (ν + 1))
      {u : ℂ | r' < ‖u‖} := by
    refine differentiableOn_tsum_of_summable_norm (u := fun ν : ℕ => |C| * (r / r') ^ ν / r')
      (((summable_geometric_of_lt_one (div_nonneg hr hr'0.le) hq).mul_left |C|).div_const r')
      (fun ν u hu => ?_) hopen fun ν u hu => ?_
    · have hu0 : u ≠ 0 := norm_pos_iff.mp (hr'0.trans hu)
      have hd1 : DifferentiableAt ℂ (fun u : ℂ => u ^ (ν + 1)) u := differentiableAt_pow (ν + 1)
      exact ((differentiableAt_const (towerSum c z ν)).div hd1
        (pow_ne_zero _ hu0)).differentiableWithinAt
    · have hu' : r' < ‖u‖ := hu
      have h1 : ‖towerSum c z ν‖ ≤ |C| * r ^ ν :=
        (hS ν).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hr ν))
      have h2 : r' ^ (ν + 1) ≤ ‖u‖ ^ (ν + 1) := pow_le_pow_left₀ hr'0.le hu'.le _
      rw [norm_div, norm_pow]
      calc ‖towerSum c z ν‖ / ‖u‖ ^ (ν + 1) ≤ |C| * r ^ ν / r' ^ (ν + 1) :=
            div_le_div₀ (mul_nonneg (abs_nonneg C) (pow_nonneg hr ν)) h1 (pow_pos hr'0 _) h2
        _ = |C| * (r / r') ^ ν / r' := by
            rw [div_pow, pow_succ]
            field_simp
  exact hd.analyticAt (hopen.mem_nhds hr2)

/-- **The resolvent is analytic off the closure of the modes.** -/
theorem analyticAt_towerResolvent {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) {w : ℂ}
    (hw : w ∉ closure (Set.range z)) : AnalyticAt ℂ (towerResolvent c z) w := by
  obtain ⟨d, hd0, hd⟩ : ∃ d > 0, ∀ i, d ≤ ‖w - z i‖ := by
    rw [Metric.mem_closure_iff] at hw
    push Not at hw
    obtain ⟨ε, hε, h⟩ := hw
    exact ⟨ε, hε, fun i => by
      have := h (z i) ⟨i, rfl⟩
      rwa [dist_eq_norm] at this⟩
  have hlow : ∀ i, ∀ u ∈ ball w (d / 2), d / 2 ≤ ‖u - z i‖ := by
    intro i u hu
    have h1 : ‖w - z i‖ ≤ ‖w - u‖ + ‖u - z i‖ := by
      have := norm_add_le (w - u) (u - z i)
      rwa [sub_add_sub_cancel] at this
    have h2 : ‖w - u‖ < d / 2 := by
      rw [← dist_eq_norm, dist_comm]
      exact mem_ball.mp hu
    linarith [hd i]
  have hdiff : DifferentiableOn ℂ (fun u : ℂ => ∑' i, c i / (u - z i)) (ball w (d / 2)) := by
    refine differentiableOn_tsum_of_summable_norm (u := fun i => ‖c i‖ * (2 / d))
      (hc.mul_right _) (fun i u hu => ?_) isOpen_ball fun i u hu => ?_
    · have hne : u - z i ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) (hlow i u hu))
      have hd1 : DifferentiableAt ℂ (fun u : ℂ => u - z i) u := differentiableAt_id.sub_const (z i)
      exact ((differentiableAt_const (c i)).div hd1 hne).differentiableWithinAt
    · rw [norm_div]
      calc ‖c i‖ / ‖u - z i‖ ≤ ‖c i‖ / (d / 2) :=
            div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (hlow i u hu)
        _ = ‖c i‖ * (2 / d) := by rw [div_div_eq_mul_div, mul_div_assoc]
  exact hdiff.analyticAt (ball_mem_nhds w (by positivity))

/-- Near an isolated mode `z_j`: `(w − z_j) Φ(w)` is the weight at `z_j` up to
`(2/δ) (Σ‖c_i‖) ‖w − z_j‖`. -/
theorem norm_merged_le_of_isolated {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) {j : ι}
    {δ : ℝ} (hδ : 0 < δ) (hiso : ∀ i, z i ≠ z j → δ ≤ ‖z i - z j‖) {w : ℂ} (hwj : w ≠ z j)
    (hwδ : ‖w - z j‖ ≤ δ / 2) :
    ‖∑' i, if z i = z j then c i else 0‖ ≤
      ‖w - z j‖ * ‖towerResolvent c z w‖ + 2 / δ * (∑' i, ‖c i‖) * ‖w - z j‖ := by
  classical
  have hwne : w - z j ≠ 0 := sub_ne_zero.mpr hwj
  have hfar : ∀ i, z i ≠ z j → δ / 2 ≤ ‖w - z i‖ := by
    intro i hi
    have h1 : ‖z i - z j‖ ≤ ‖w - z j‖ + ‖w - z i‖ := by
      have := norm_sub_le (w - z j) (w - z i)
      rwa [sub_sub_sub_cancel_left] at this
    linarith [hiso i hi]
  have hterm : ∀ i, (w - z j) * (c i / (w - z i)) = (if z i = z j then c i else 0) +
      (if z i = z j then 0 else c i * (w - z j) / (w - z i)) := by
    intro i
    by_cases h : z i = z j
    · rw [if_pos h, if_pos h, h, add_zero, mul_div_assoc', mul_comm, mul_div_assoc,
        div_self hwne, mul_one]
    · rw [if_neg h, if_neg h, zero_add, mul_div_assoc', mul_comm]
  have hs1 : Summable fun i => (if z i = z j then c i else 0 : ℂ) :=
    Summable.of_norm_bounded hc fun i => by split_ifs <;> simp
  have hb2 : ∀ i, ‖(if z i = z j then 0 else c i * (w - z j) / (w - z i) : ℂ)‖ ≤
      ‖c i‖ * (2 / δ * ‖w - z j‖) := by
    intro i
    by_cases h : z i = z j
    · rw [if_pos h, norm_zero]
      positivity
    · rw [if_neg h, norm_div, norm_mul]
      have hpos : 0 < ‖w - z i‖ := lt_of_lt_of_le (by positivity) (hfar i h)
      calc ‖c i‖ * ‖w - z j‖ / ‖w - z i‖ ≤ ‖c i‖ * ‖w - z j‖ / (δ / 2) :=
            div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              (by positivity) (hfar i h)
        _ = ‖c i‖ * (2 / δ * ‖w - z j‖) := by
            rw [div_div_eq_mul_div]
            ring
  have hs2 : Summable fun i => (if z i = z j then 0 else c i * (w - z j) / (w - z i) : ℂ) :=
    Summable.of_norm_bounded (hc.mul_right _) hb2
  have hsplit : (w - z j) * towerResolvent c z w =
      (∑' i, if z i = z j then c i else 0) +
        ∑' i, (if z i = z j then 0 else c i * (w - z j) / (w - z i) : ℂ) := by
    rw [towerResolvent, ← tsum_mul_left, ← hs1.tsum_add hs2]
    exact tsum_congr hterm
  have hE : ‖∑' i, (if z i = z j then 0 else c i * (w - z j) / (w - z i) : ℂ)‖ ≤
      2 / δ * (∑' i, ‖c i‖) * ‖w - z j‖ := by
    have h := tsum_of_norm_bounded (hc.mul_right (2 / δ * ‖w - z j‖)).hasSum hb2
    rw [tsum_mul_right] at h
    calc _ ≤ (∑' i, ‖c i‖) * (2 / δ * ‖w - z j‖) := h
      _ = 2 / δ * (∑' i, ‖c i‖) * ‖w - z j‖ := by ring
  have hm : (∑' i, if z i = z j then c i else 0) = (w - z j) * towerResolvent c z w -
      ∑' i, (if z i = z j then 0 else c i * (w - z j) / (w - z i) : ℂ) := by
    rw [hsplit, add_sub_cancel_right]
  rw [hm]
  calc _ ≤ ‖(w - z j) * towerResolvent c z w‖ +
        ‖∑' i, (if z i = z j then 0 else c i * (w - z j) / (w - z i) : ℂ)‖ := norm_sub_le _ _
    _ ≤ ‖w - z j‖ * ‖towerResolvent c z w‖ + 2 / δ * (∑' i, ‖c i‖) * ‖w - z j‖ := by
        rw [norm_mul]
        exact add_le_add_right hE _

/-- **The weight at an isolated mode vanishes if the resolvent continues past it.** Let `Ψ` be
continuous at the isolated mode `z_j` and analytic along a path from `z_j` that, apart from `z_j`,
avoids the closure of the modes, and let `Ψ` agree with the resolvent near the end of the path.
Then the tower carries no weight at `z_j`. -/
theorem merged_eq_zero_of_continuation {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    {Ψ : ℂ → ℂ} {j : ι} (hΨj : ContinuousAt Ψ (z j)) {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ i, z i ≠ z j → δ ≤ ‖z i - z j‖) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Set.Icc 0 1)) (hγ0 : γ 0 = z j)
    (hγfree : ∀ t ∈ Set.Ioc (0 : ℝ) 1, γ t ∉ closure (Set.range z))
    (hΨ : ∀ t ∈ Set.Ioc (0 : ℝ) 1, AnalyticAt ℂ Ψ (γ t))
    (hend : towerResolvent c z =ᶠ[𝓝 (γ 1)] Ψ) :
    (∑' i, if z i = z j then c i else 0) = 0 := by
  -- the resolvent and `Ψ` agree along the path
  have heq : ∀ t ∈ Set.Ioc (0 : ℝ) 1, towerResolvent c z (γ t) = Ψ (γ t) := by
    have hpre : IsPreconnected (γ '' Set.Ioc 0 1) :=
      isPreconnected_Ioc.image γ (hγ.mono Set.Ioc_subset_Icc_self)
    have hf : AnalyticOnNhd ℂ (towerResolvent c z) (γ '' Set.Ioc 0 1) := by
      rintro _ ⟨t, ht, rfl⟩
      exact analyticAt_towerResolvent hc (hγfree t ht)
    have hg : AnalyticOnNhd ℂ Ψ (γ '' Set.Ioc 0 1) := by
      rintro _ ⟨t, ht, rfl⟩
      exact hΨ t ht
    have h1mem : γ 1 ∈ γ '' Set.Ioc 0 1 := ⟨1, ⟨one_pos, le_rfl⟩, rfl⟩
    have h := hf.eqOn_of_preconnected_of_eventuallyEq hg hpre h1mem hend
    intro t ht
    exact h ⟨t, ht, rfl⟩
  -- `Ψ` is bounded near `z_j`
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.mp hΨj 1 one_pos
  have hbound : ∀ w : ℂ, dist w (z j) < η → ‖Ψ w‖ ≤ ‖Ψ (z j)‖ + 1 := by
    intro w hw
    have h1 := hηb hw
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (Ψ w) (Ψ (z j))
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ‖Ψ (z j)‖ + 1 + 2 / δ * ∑' i, ‖c i‖ := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    have : 0 ≤ ∑' i, ‖c i‖ := tsum_nonneg fun _ => norm_nonneg _
    positivity
  -- the path comes arbitrarily close to `z_j`
  have hnear : ∀ ε : ℝ, 0 < ε → ∃ t ∈ Set.Ioc (0 : ℝ) 1, dist (γ t) (z j) < ε := by
    intro ε hε
    have hcw : ContinuousWithinAt γ (Set.Icc 0 1) 0 := hγ 0 (Set.left_mem_Icc.mpr zero_le_one)
    have ht := hcw.tendsto
    rw [hγ0] at ht
    have hev : ∀ᶠ t in 𝓝[Set.Icc (0 : ℝ) 1] 0, dist (γ t) (z j) < ε :=
      ht.eventually (Metric.ball_mem_nhds _ hε)
    have hle : 𝓝[Set.Ioc (0 : ℝ) 1] 0 ≤ 𝓝[Set.Icc (0 : ℝ) 1] 0 :=
      nhdsWithin_mono _ Set.Ioc_subset_Icc_self
    have hne : (𝓝[Set.Ioc (0 : ℝ) 1] 0).NeBot := by
      rw [nhdsWithin_Ioc_eq_nhdsGT one_pos]
      infer_instance
    have hev' : ∀ᶠ t in 𝓝[Set.Ioc (0 : ℝ) 1] 0, dist (γ t) (z j) < ε := hev.filter_mono hle
    haveI := hne
    obtain ⟨t, ht1, ht2⟩ := (hev'.and eventually_mem_nhdsWithin).exists
    exact ⟨t, ht2, ht1⟩
  have hsmall : ∀ ε : ℝ, 0 < ε → ε ≤ δ / 2 → ε ≤ η →
      ‖∑' i, if z i = z j then c i else 0‖ ≤ ε * K := by
    intro ε hε hεδ hεη
    obtain ⟨t, ht, hdist⟩ := hnear ε hε
    have hzmem : z j ∈ closure (Set.range z) := subset_closure ⟨j, rfl⟩
    have hwj : γ t ≠ z j := fun h => hγfree t ht (h ▸ hzmem)
    have hnorm : ‖γ t - z j‖ < ε := by rwa [dist_eq_norm] at hdist
    have hmain := norm_merged_le_of_isolated hc hδ hiso hwj (hnorm.le.trans hεδ)
    rw [heq t ht] at hmain
    have hL := hbound (γ t) (hdist.trans_le hεη)
    have hA : 0 ≤ 2 / δ * ∑' i, ‖c i‖ := by
      have : 0 ≤ ∑' i, ‖c i‖ := tsum_nonneg fun _ => norm_nonneg _
      positivity
    calc ‖∑' i, if z i = z j then c i else 0‖
        ≤ ‖γ t - z j‖ * ‖Ψ (γ t)‖ + 2 / δ * (∑' i, ‖c i‖) * ‖γ t - z j‖ := hmain
      _ = ‖γ t - z j‖ * (‖Ψ (γ t)‖ + 2 / δ * ∑' i, ‖c i‖) := by ring
      _ ≤ ε * (‖Ψ (z j)‖ + 1 + 2 / δ * ∑' i, ‖c i‖) :=
          mul_le_mul hnorm.le (by linarith) (add_nonneg (norm_nonneg _) hA) hε.le
      _ = ε * K := by rw [hK]
  -- hence it vanishes
  by_contra hne
  have hpos : 0 < ‖∑' i, if z i = z j then c i else 0‖ := norm_pos_iff.mpr hne
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (min (δ / 2) η)
      (‖∑' i, if z i = z j then c i else 0‖ / (2 * (K + 1))) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min (by positivity) hη) (by positivity)
  have h1 := hsmall ε hεpos
    (by rw [hεdef]; exact (min_le_left _ _).trans (min_le_left _ _))
    (by rw [hεdef]; exact (min_le_left _ _).trans (min_le_right _ _))
  have h2 : ε * K ≤ ‖∑' i, if z i = z j then c i else 0‖ / (2 * (K + 1)) * K :=
    mul_le_mul_of_nonneg_right (by rw [hεdef]; exact min_le_right _ _) hK0
  have h3 : ‖∑' i, if z i = z j then c i else 0‖ / (2 * (K + 1)) * K <
      ‖∑' i, if z i = z j then c i else 0‖ := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **A mode accessible from infinity is eliminated.** Let the level sums of a summable tower with
modes bounded by `R` satisfy `‖S(ν)‖ ≤ C r^ν` at every level. Let `z_j` be an isolated mode joined
to a point beyond `R` by a path that, apart from its starting point `z_j`, stays in `‖w‖ > r` and
does not meet the closure of the modes. Then the tower carries no weight at `z_j`. -/
theorem merged_eq_zero_of_accessible {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ i, ‖z i‖ ≤ R) {C r : ℝ} (hr : 0 ≤ r)
    (hS : ∀ ν : ℕ, ‖towerSum c z ν‖ ≤ C * r ^ ν) {j : ι} (hj : r < ‖z j‖) {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ i, z i ≠ z j → δ ≤ ‖z i - z j‖) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Set.Icc 0 1)) (hγ0 : γ 0 = z j)
    (hγfree : ∀ t ∈ Set.Ioc (0 : ℝ) 1, γ t ∉ closure (Set.range z))
    (hγr : ∀ t ∈ Set.Ioc (0 : ℝ) 1, r < ‖γ t‖) (hγ1 : R < ‖γ 1‖) :
    (∑' i, if z i = z j then c i else 0) = 0 := by
  refine merged_eq_zero_of_continuation hc (analyticAt_levelSeries hr hS hj).continuousAt hδ hiso
    hγ hγ0 hγfree (fun t ht => analyticAt_levelSeries hr hS (hγr t ht)) ?_
  have hopen : IsOpen {w : ℂ | R < ‖w‖} := isOpen_lt continuous_const continuous_norm
  filter_upwards [hopen.mem_nhds (show γ 1 ∈ {w : ℂ | R < ‖w‖} from hγ1)] with w hw
  exact towerResolvent_eq_levelSeries hc hR0 hR hw

/-- **A radially visible mode is eliminated**: the path is the outward segment `z_j (1 + t)`,
`0 < t ≤ T`. -/
theorem merged_eq_zero_of_radially_visible {c z : ι → ℂ} (hc : Summable fun i => ‖c i‖) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ i, ‖z i‖ ≤ R) {C r : ℝ} (hr : 0 ≤ r)
    (hS : ∀ ν : ℕ, ‖towerSum c z ν‖ ≤ C * r ^ ν) {j : ι} (hj : r < ‖z j‖) {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ i, z i ≠ z j → δ ≤ ‖z i - z j‖) {T : ℝ} (hT : 0 < T)
    (hTR : R < ‖z j‖ * (1 + T))
    (hray : ∀ t ∈ Set.Ioc (0 : ℝ) T, z j * (1 + (t : ℂ)) ∉ closure (Set.range z)) :
    (∑' i, if z i = z j then c i else 0) = 0 := by
  have hzj0 : 0 < ‖z j‖ := hr.trans_lt hj
  have hnormray : ∀ t : ℝ, 0 ≤ t → ‖z j * (1 + ((t * T : ℝ) : ℂ))‖ = ‖z j‖ * (1 + t * T) := by
    intro t ht
    have h1 : (1 + ((t * T : ℝ) : ℂ)) = ((1 + t * T : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [norm_mul, h1, Complex.norm_real,
      Real.norm_of_nonneg (by nlinarith [mul_nonneg ht hT.le])]
  refine merged_eq_zero_of_accessible hc hR0 hR hr hS hj hδ hiso
    (γ := fun t : ℝ => z j * (1 + ((t * T : ℝ) : ℂ))) (by fun_prop) (by simp) (fun t ht => ?_)
    (fun t ht => ?_) ?_
  · exact hray (t * T) ⟨mul_pos ht.1 hT, by nlinarith [ht.2]⟩
  · show r < ‖z j * (1 + ((t * T : ℝ) : ℂ))‖
    rw [hnormray t ht.1.le]
    nlinarith [mul_pos ht.1 hT]
  · show R < ‖z j * (1 + ((1 * T : ℝ) : ℂ))‖
    rw [hnormray 1 zero_le_one, one_mul]
    exact hTR

/-! ### Behind a wall -/

open GaloisForLFunctions.HTGeometry.CircleQuadraturePositive in
/-- **Walls exist.** The nodes of the positive Wolff measure carry positive masses and their level
sums vanish at every level `ν ≥ 1`. So no isolated node is accessible from infinity: every path
from it to a point beyond all nodes meets the closure of the nodes. Accessibility cannot be dropped
from the elimination theorem. -/
theorem wolff_node_not_accessible {j : PIdx} {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ i, ppoint i ≠ ppoint j → δ ≤ ‖ppoint i - ppoint j‖) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Set.Icc 0 1)) (hγ0 : γ 0 = ppoint j)
    (hγr : ∀ t ∈ Set.Ioc (0 : ℝ) 1, 0 < ‖γ t‖) (hγ1 : 10 < ‖γ 1‖) :
    ∃ t ∈ Set.Ioc (0 : ℝ) 1, γ t ∈ closure (Set.range ppoint) := by
  by_contra hcon
  have hfree : ∀ t ∈ Set.Ioc (0 : ℝ) 1, γ t ∉ closure (Set.range ppoint) := fun t ht hmem =>
    hcon ⟨t, ht, hmem⟩
  have hc : Summable fun i : PIdx => ‖(pcoef i : ℂ)‖ := by
    have h : (fun i : PIdx => ‖(pcoef i : ℂ)‖) = pcoef := by
      funext i
      rw [Complex.norm_real, Real.norm_of_nonneg (pcoef_pos i).le]
    rw [h]
    exact summable_pcoef
  -- the level sums vanish from level one on
  have hS : ∀ ν : ℕ, ‖towerSum (fun i : PIdx => (pcoef i : ℂ)) ppoint ν‖ ≤
      ‖towerSum (fun i : PIdx => (pcoef i : ℂ)) ppoint 0‖ * (0 : ℝ) ^ ν := by
    intro ν
    rcases Nat.eq_zero_or_pos ν with rfl | hν
    · rw [pow_zero, mul_one]
    · rw [towerSum, (hasSum_pcoef_mul_ppoint_pow hν).tsum_eq, norm_zero, zero_pow hν.ne', mul_zero]
  have hj : (0 : ℝ) < ‖ppoint j‖ := lt_of_lt_of_le (by norm_num) (norm_ppoint_ge j)
  have hzero := merged_eq_zero_of_accessible hc (by norm_num : (0 : ℝ) ≤ 10) norm_ppoint_le le_rfl
    hS hj hδ hiso hγ hγ0 hfree hγr hγ1
  rw [tsum_eq_single j (fun i hi => by rw [if_neg fun h => hi (ppoint_injective h)]),
    if_pos rfl] at hzero
  exact (pcoef_pos j).ne' (by exact_mod_cast hzero)

/-- **For `ζ`: an off-line zero whose mode is accessible from infinity contradicts a crude count
along all levels of its tower.** In the tower of base `ℓ` with modes `e^{ℓ(ρ − 1)}`, let `ρ₀` have
`Re ρ₀ > ½ + a` and an isolated mode joined to a point outside the unit disc by a path that, apart
from its starting point, stays outside the disc of radius `e^{ℓ(a − ½)}` and off the closure of the
modes. Then `Φ(νℓ) = O(e^{aνℓ})` fails along the levels `ν`. -/
theorem lag_not_small_of_accessible {ℓ : ℝ} (hℓ : 0 < ℓ) {a : ℝ} {q₀ : XiZeroCopy}
    (hq₀ : 1 / 2 + a < (q₀.1 : ℂ).re) {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ q, abscissaMode ℓ 1 q ≠ abscissaMode ℓ 1 q₀ →
      δ ≤ ‖abscissaMode ℓ 1 q - abscissaMode ℓ 1 q₀‖) {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Set.Icc 0 1)) (hγ0 : γ 0 = abscissaMode ℓ 1 q₀)
    (hγfree : ∀ t ∈ Set.Ioc (0 : ℝ) 1, γ t ∉ closure (Set.range (abscissaMode ℓ 1)))
    (hγr : ∀ t ∈ Set.Ioc (0 : ℝ) 1, Real.exp (ℓ * (a - 1 / 2)) < ‖γ t‖) (hγ1 : 1 < ‖γ 1‖)
    (C : ℝ) : ¬ ∀ ν : ℕ, ‖weilLagFunction (ν * ℓ)‖ ≤ C * Real.exp (a * (ν * ℓ)) := by
  intro hbound
  have hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 := fun q =>
    (re_lt_one_of_xi_eq_zero (xi_xiZeroCopy_eq_zero q)).le
  have hS : ∀ ν : ℕ, ‖towerSum lagW (abscissaMode ℓ 1) ν‖ ≤
      C * Real.exp (ℓ * (a - 1 / 2)) ^ ν := by
    intro ν
    rw [norm_abscissa_towerSum ℓ 1 ν, ← Real.exp_nat_mul]
    calc Real.exp (-(ν * (ℓ * (1 - 1 / 2)))) * ‖weilLagFunction (ν * ℓ)‖
        ≤ Real.exp (-(ν * (ℓ * (1 - 1 / 2)))) * (C * Real.exp (a * (ν * ℓ))) :=
          mul_le_mul_of_nonneg_left (hbound ν) (Real.exp_pos _).le
      _ = C * Real.exp (ν * (ℓ * (a - 1 / 2))) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hj : Real.exp (ℓ * (a - 1 / 2)) < ‖abscissaMode ℓ 1 q₀‖ := by
    rw [norm_abscissaMode, Real.exp_lt_exp]
    nlinarith
  have hzero := merged_eq_zero_of_accessible summable_norm_lagW zero_le_one
    (norm_abscissaMode_le_one hℓ hmax) (Real.exp_pos _).le hS hj hδ hiso hγ hγ0 hγfree hγr hγ1
  exact merged_ne_zero_of_re_pos summable_norm_lagW (fun q => (re_lagW_pos q).le)
    (re_lagW_pos q₀) hzero

/-- **For `ζ`: an off-line zero whose mode is isolated and radially visible contradicts a crude
count along all levels of its tower.** In the tower of base `ℓ` with modes `e^{ℓ(ρ − 1)}`, let `ρ₀`
have `Re ρ₀ > ½ + a` and an isolated mode whose outward segment to the unit circle does not meet
the closure of the modes. Then `Φ(νℓ) = O(e^{aνℓ})` fails along the levels `ν`. -/
theorem lag_not_small_of_radially_visible {ℓ : ℝ} (hℓ : 0 < ℓ) {a : ℝ} {q₀ : XiZeroCopy}
    (hq₀ : 1 / 2 + a < (q₀.1 : ℂ).re) {δ : ℝ} (hδ : 0 < δ)
    (hiso : ∀ q, abscissaMode ℓ 1 q ≠ abscissaMode ℓ 1 q₀ →
      δ ≤ ‖abscissaMode ℓ 1 q - abscissaMode ℓ 1 q₀‖) {T : ℝ} (hT : 0 < T)
    (hTR : 1 < ‖abscissaMode ℓ 1 q₀‖ * (1 + T))
    (hray : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      abscissaMode ℓ 1 q₀ * (1 + (t : ℂ)) ∉ closure (Set.range (abscissaMode ℓ 1))) (C : ℝ) :
    ¬ ∀ ν : ℕ, ‖weilLagFunction (ν * ℓ)‖ ≤ C * Real.exp (a * (ν * ℓ)) := by
  intro hbound
  have hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ 1 := fun q =>
    (re_lt_one_of_xi_eq_zero (xi_xiZeroCopy_eq_zero q)).le
  -- the level sums of the tower are `O(r^ν)` with `r = e^{ℓ(a − ½)}`
  have hS : ∀ ν : ℕ, ‖towerSum lagW (abscissaMode ℓ 1) ν‖ ≤
      C * Real.exp (ℓ * (a - 1 / 2)) ^ ν := by
    intro ν
    rw [norm_abscissa_towerSum ℓ 1 ν, ← Real.exp_nat_mul]
    calc Real.exp (-(ν * (ℓ * (1 - 1 / 2)))) * ‖weilLagFunction (ν * ℓ)‖
        ≤ Real.exp (-(ν * (ℓ * (1 - 1 / 2)))) * (C * Real.exp (a * (ν * ℓ))) :=
          mul_le_mul_of_nonneg_left (hbound ν) (Real.exp_pos _).le
      _ = C * Real.exp (ν * (ℓ * (a - 1 / 2))) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hj : Real.exp (ℓ * (a - 1 / 2)) < ‖abscissaMode ℓ 1 q₀‖ := by
    rw [norm_abscissaMode, Real.exp_lt_exp]
    nlinarith
  have hzero := merged_eq_zero_of_radially_visible summable_norm_lagW zero_le_one
    (norm_abscissaMode_le_one hℓ hmax) (Real.exp_pos _).le hS hj hδ hiso hT hTR hray
  exact merged_ne_zero_of_re_pos summable_norm_lagW (fun q => (re_lagW_pos q).le)
    (re_lagW_pos q₀) hzero

/-- **RH from a crude count and one accessible zero.** If the lag is bounded along all levels of
the tower of base `ℓ`, and a failure of RH comes with an off-line zero whose mode in that tower is
isolated and joined to a point outside the unit disc by a path that, apart from its starting point,
stays outside the disc of radius `e^{−ℓ/2}` and off the closure of the modes, then RH holds. The
abscissa need not be attained. -/
theorem riemannHypothesis_of_lag_bounded_of_accessible {ℓ : ℝ} (hℓ : 0 < ℓ) {C : ℝ}
    (hbound : ∀ ν : ℕ, ‖weilLagFunction (ν * ℓ)‖ ≤ C)
    (hvis : (∃ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re) →
      ∃ q₀ : XiZeroCopy, 1 / 2 < (q₀.1 : ℂ).re ∧ ∃ δ > 0,
        (∀ q, abscissaMode ℓ 1 q ≠ abscissaMode ℓ 1 q₀ →
          δ ≤ ‖abscissaMode ℓ 1 q - abscissaMode ℓ 1 q₀‖) ∧
        ∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) ∧ γ 0 = abscissaMode ℓ 1 q₀ ∧
          (∀ t ∈ Set.Ioc (0 : ℝ) 1, γ t ∉ closure (Set.range (abscissaMode ℓ 1))) ∧
          (∀ t ∈ Set.Ioc (0 : ℝ) 1, Real.exp (ℓ * (0 - 1 / 2)) < ‖γ t‖) ∧ 1 < ‖γ 1‖) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  intro ρ hρ
  by_contra hgt
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have hoff : ∃ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re :=
    ⟨q, by rw [hq]; linarith [not_le.mp hgt]⟩
  obtain ⟨q₀, hq₀, δ, hδ, hiso, γ, hγ, hγ0, hγfree, hγr, hγ1⟩ := hvis hoff
  exact lag_not_small_of_accessible hℓ (a := 0) (by linarith) hδ hiso hγ hγ0 hγfree hγr hγ1 C
    fun ν => by simpa using hbound ν

/-- The same with the outward segment as the path. -/
theorem riemannHypothesis_of_lag_bounded_of_visible {ℓ : ℝ} (hℓ : 0 < ℓ) {C : ℝ}
    (hbound : ∀ ν : ℕ, ‖weilLagFunction (ν * ℓ)‖ ≤ C)
    (hvis : (∃ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re) →
      ∃ q₀ : XiZeroCopy, 1 / 2 < (q₀.1 : ℂ).re ∧ ∃ δ > 0,
        (∀ q, abscissaMode ℓ 1 q ≠ abscissaMode ℓ 1 q₀ →
          δ ≤ ‖abscissaMode ℓ 1 q - abscissaMode ℓ 1 q₀‖) ∧
        ∃ T > 0, 1 < ‖abscissaMode ℓ 1 q₀‖ * (1 + T) ∧
          ∀ t ∈ Set.Ioc (0 : ℝ) T, abscissaMode ℓ 1 q₀ * (1 + (t : ℂ)) ∉
            closure (Set.range (abscissaMode ℓ 1))) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  intro ρ hρ
  by_contra hgt
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  have hoff : ∃ q : XiZeroCopy, 1 / 2 < (q.1 : ℂ).re :=
    ⟨q, by rw [hq]; linarith [not_le.mp hgt]⟩
  obtain ⟨q₀, hq₀, δ, hδ, hiso, T, hT, hTR, hray⟩ := hvis hoff
  exact lag_not_small_of_radially_visible hℓ (a := 0) (by linarith) hδ hiso hT hTR hray C
    fun ν => by simpa using hbound ν

end GaloisForLFunctions.InfiniteRankPurityTheory
