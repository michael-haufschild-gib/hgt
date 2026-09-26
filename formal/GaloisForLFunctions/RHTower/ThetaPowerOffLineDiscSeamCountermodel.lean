import GaloisForLFunctions.RHTower.ThetaPowerOffLineParameterSet
import GaloisForLFunctions.RHTower.XiRightDiscPhaseIndexRiemannHypothesis

/-!
# The disc seam criterion fails in the theta-power family at every transcendental parameter

For `0 < a < 1/2` let `Λ_a = thetaPowerXiC a` be the transform of `F_a = θ₃^{1−2a}(θ₂θ₄)^a`.  Its
critical line is the real axis `Im w = 0` (it corresponds to `Re s = 1/2`), and it shares with `Ξ`
the functional equation, reality on the line, weight-½ modularity on `Γ_θ` with a unitary
character, holomorphy and vanishing at both cusps, and a zero-free source on the upper half-plane.

For `ξ`, the Riemann hypothesis is equivalent to the adjoint Hankel seam `(1 − P) U† P` of the
boundary phase being a strict contraction on every disc on one side of the critical line
(`riemannHypothesis_iff_forall_xiRightDisc_adjointSeam_lt_one`).  For `Λ_a` with `a`
transcendental the same statement is false: `exists_upperDisc_relativeIndex_pos_seam_ge_one` gives
a closed disc inside `0 < Im w`, with `Λ_a ≠ 0` on its boundary circle, whose Hardy pair has
positive relative index and whose adjoint seam has norm `≥ 1`.  The disc is a small disc around
the off-line zero of `thetaPowerXiC_offline_zero_of_transcendental`.

Consequence: a producer of the seam contraction that uses only the properties shared by the
family (functional equation, modularity, cusp behaviour, positivity of the source) would also
produce it for `Λ_a`, which is false.  A producer must use the Euler product.
-/

noncomputable section

open Complex Metric Filter Topology

namespace RHTower

namespace ThetaPowerSeam

variable {a : ℝ}

/-- The argument datum of `Λ_a` on a circle `|w − c| = t` on which `Λ_a` does not vanish. -/
def discDatum (ha : 0 < a) (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, thetaPowerXiC a ζ ≠ 0) : DiscArgumentDatum where
  c := c
  t := t
  R := t + 1
  U := Set.univ
  F := thetaPowerXiC a
  t_pos := ht
  t_lt_R := by linarith
  isOpen := isOpen_univ
  closedBall_subset := Set.subset_univ _
  differentiableOn := (differentiable_thetaPowerXiC ha).differentiableOn
  ne_zero := hne

/-- A zero of `Λ_a` has multiplicity at least one. -/
theorem one_le_zeroMult (ha : 0 < a) {w : ℂ} (hw : thetaPowerXiC a w = 0) :
    1 ≤ GaloisForLFunctions.HTGeometry.zeroMult (thetaPowerXiC a) w := by
  have hdiff := differentiable_thetaPowerXiC ha
  have han : AnalyticAt ℂ (thetaPowerXiC a) w := hdiff.analyticAt w
  have hne0 : analyticOrderAt (thetaPowerXiC a) w ≠ 0 := by
    rw [ne_eq, han.analyticOrderAt_eq_zero]
    exact fun h => h hw
  have hnetop : analyticOrderAt (thetaPowerXiC a) w ≠ ⊤ := by
    intro htop
    have hev : thetaPowerXiC a =ᶠ[𝓝 w] 0 := analyticOrderAt_eq_top.mp htop
    have hall : Set.EqOn (thetaPowerXiC a) 0 Set.univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun z _ => hdiff.analyticAt z) isPreconnected_univ (Set.mem_univ w) hev
    exact thetaPowerXiC_zero_ne_zero ha (hall (Set.mem_univ 0))
  unfold GaloisForLFunctions.HTGeometry.zeroMult
  rw [Nat.one_le_iff_ne_zero, ne_eq, ENat.toNat_eq_zero]
  push Not
  exact ⟨hne0, hnetop⟩

/-- **The seam criterion fails for `Λ_a` at transcendental `a`.**  There is a closed disc inside
the upper half-plane, with `Λ_a` zero-free on its boundary circle, whose Hardy pair has positive
relative index and whose adjoint Hankel seam has norm at least one. -/
theorem exists_upperDisc_relativeIndex_pos_seam_ge_one (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (htr : Transcendental ℚ a) :
    ∃ (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, thetaPowerXiC a ζ ≠ 0),
      (∀ z ∈ closedBall c t, 0 < z.im) ∧
      0 < restrictedProjectionRelativeIndex
        (discDatum ha0 c t ht hne).circlePhase.datum.conjugateProjection
        (discDatum ha0 c t ht hne).circlePhase.datum.projection ∧
      1 ≤ ‖(discDatum ha0 c t ht hne).circlePhase.datum.adjointHankelSeam‖ := by
  obtain ⟨w, hw0, -, hw⟩ := thetaPowerXiC_offline_zero_of_transcendental ha0 ha1 htr
  have hdiff := differentiable_thetaPowerXiC ha0
  have han : AnalyticAt ℂ (thetaPowerXiC a) w := hdiff.analyticAt w
  have hiso : ∀ᶠ z in 𝓝[≠] w, thetaPowerXiC a z ≠ 0 := by
    rcases han.eventually_eq_zero_or_eventually_ne_zero with hev | hev
    · exfalso
      have hall : Set.EqOn (thetaPowerXiC a) 0 Set.univ :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (fun z _ => hdiff.analyticAt z) isPreconnected_univ (Set.mem_univ w) hev
      exact thetaPowerXiC_zero_ne_zero ha0 (hall (Set.mem_univ 0))
    · exact hev
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hiso
  obtain ⟨ε, hε, hεne⟩ := hiso
  set t : ℝ := min (ε / 2) (w.im / 2) with htdef
  have ht : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hne : ∀ ζ ∈ sphere w t, thetaPowerXiC a ζ ≠ 0 := by
    intro ζ hζ
    rw [mem_sphere] at hζ
    refine hεne (by rw [hζ]; exact htε) ?_
    intro hζw
    rw [Set.mem_singleton_iff] at hζw
    rw [hζw, dist_self] at hζ
    exact (ne_of_gt ht) hζ.symm
  have hup : ∀ z ∈ closedBall w t, 0 < z.im := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im] at h1
    have h2 : t ≤ w.im / 2 := min_le_right _ _
    have h3 := neg_abs_le (z.im - w.im)
    linarith
  set D := discDatum ha0 w t ht hne with hD
  have hpos : 0 < restrictedProjectionRelativeIndex D.circlePhase.datum.conjugateProjection
      D.circlePhase.datum.projection := by
    obtain ⟨Z, -, hZzero, hidx⟩ := D.relativeIndex_eq_zeroCount
    have hwZ : w ∈ Z := (hZzero w (mem_ball_self ht)).mp hw
    rw [hidx]
    have hle := Finset.single_le_sum
      (f := fun ρ' => (GaloisForLFunctions.HTGeometry.zeroMult D.F ρ' : ℤ))
      (fun ρ' _ => Int.natCast_nonneg _) hwZ
    have h1 : (1 : ℤ) ≤ (GaloisForLFunctions.HTGeometry.zeroMult D.F w : ℤ) := by
      exact_mod_cast one_le_zeroMult ha0 hw
    exact lt_of_lt_of_le one_pos (h1.trans hle)
  refine ⟨w, t, ht, hne, hup, hpos, ?_⟩
  by_contra hlt
  push Not at hlt
  have hnonpos := D.circlePhase.datum.re_opTrace_cubicDefect_nonpos_of_adjointSeam hlt
  rw [D.circlePhase.datum.opTrace_cubicDefect_eq_relativeIndex, Complex.intCast_re] at hnonpos
  have hle : restrictedProjectionRelativeIndex D.circlePhase.datum.conjugateProjection
      D.circlePhase.datum.projection ≤ 0 := by exact_mod_cast hnonpos
  omega

end ThetaPowerSeam

end RHTower
