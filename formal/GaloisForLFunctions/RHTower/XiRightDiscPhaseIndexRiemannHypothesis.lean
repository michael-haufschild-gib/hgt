import GaloisForLFunctions.RHTower.CircleArgumentPhaseRelativeIndex
import GaloisForLFunctions.RHTower.GaussianPassageBoundedUnderRiemannHypothesis
import GaloisForLFunctions.RHTower.RestrictedProjectionIndexOperatorNormCriterion

/-!
# The Riemann hypothesis as vanishing of the Hardy relative index on right discs

For a closed disc `closedBall c t` strictly right of the critical line, with `xi ≠ 0` on its
boundary circle, let `u = xi/|xi|` be the boundary phase, `P` the Hardy projection and `U = M_u`.
The relative index of the Hardy pair `(U† P U, P)` is the number of zeros of `xi` in the disc
(`DiscArgumentDatum.relativeIndex_eq_zeroCount`). Hence:

* `riemannHypothesis_iff_forall_xiRightDisc_relativeIndex_eq_zero`: RH holds iff this relative
  index vanishes on every such disc.
* `riemannHypothesis_of_forall_xiRightDisc_adjointSeam_lt_one`: RH follows from the operator-norm
  bound `‖(1 − P) U† P‖ < 1` on the adjoint Hankel seam of every such disc. A contraction of that
  seam makes the relative index nonpositive, while a zero count is nonnegative.

These theorems are consumers: they turn any producer of the disc-wise index or seam bound into RH
and produce nothing towards it.
-/

noncomputable section

open Complex Metric Filter Topology

namespace RHTower

/-- The argument datum of `xi` on a circle `|z − c| = t` on which `xi` does not vanish. -/
def xiDiscDatum (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) :
    DiscArgumentDatum where
  c := c
  t := t
  R := t + 1
  U := Set.univ
  F := xi
  t_pos := ht
  t_lt_R := by linarith
  isOpen := isOpen_univ
  closedBall_subset := Set.subset_univ _
  differentiableOn := xi_differentiable.differentiableOn
  ne_zero := hne

/-- The relative index of the Hardy pair of the `xi` boundary phase on the circle `|z − c| = t`. -/
def xiDiscRelativeIndex (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) : ℤ :=
  restrictedProjectionRelativeIndex (xiDiscDatum c t ht hne).circlePhase.datum.conjugateProjection
    (xiDiscDatum c t ht hne).circlePhase.datum.projection

/-- A zero of `xi` has multiplicity at least one. -/
theorem one_le_zeroMult_xi {ρ : ℂ} (hρ : xi ρ = 0) :
    1 ≤ GaloisForLFunctions.HTGeometry.zeroMult xi ρ := by
  have han : AnalyticAt ℂ xi ρ := xi_differentiable.analyticAt ρ
  have hne0 : analyticOrderAt xi ρ ≠ 0 := by
    rw [ne_eq, han.analyticOrderAt_eq_zero]
    exact fun h => h hρ
  have hnetop : analyticOrderAt xi ρ ≠ ⊤ := by
    intro htop
    have hev : xi =ᶠ[𝓝 ρ] 0 := analyticOrderAt_eq_top.mp htop
    have hall : Set.EqOn xi 0 Set.univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (fun z _ => xi_differentiable.analyticAt z)
        isPreconnected_univ (Set.mem_univ ρ) hev
    have h2 : xi 2 ≠ 0 := xi_ne_zero_of_one_le_re (by norm_num)
    exact h2 (hall (Set.mem_univ 2))
  unfold GaloisForLFunctions.HTGeometry.zeroMult
  rw [Nat.one_le_iff_ne_zero, ne_eq, ENat.toNat_eq_zero]
  push Not
  exact ⟨hne0, hnetop⟩

/-- The relative index on a disc is the zero count, hence nonnegative. -/
theorem xiDiscRelativeIndex_nonneg (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) : 0 ≤ xiDiscRelativeIndex c t ht hne := by
  obtain ⟨Z, -, -, hidx⟩ := (xiDiscDatum c t ht hne).relativeIndex_eq_zeroCount
  unfold xiDiscRelativeIndex
  rw [hidx]
  exact Finset.sum_nonneg fun ρ _ => Int.natCast_nonneg _

/-- A zero of `xi` inside the disc makes the relative index positive. -/
theorem xiDiscRelativeIndex_pos_of_zero (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) {ρ : ℂ} (hρball : ρ ∈ ball c t) (hρ : xi ρ = 0) :
    0 < xiDiscRelativeIndex c t ht hne := by
  obtain ⟨Z, -, hZzero, hidx⟩ := (xiDiscDatum c t ht hne).relativeIndex_eq_zeroCount
  have hρZ : ρ ∈ Z := (hZzero ρ hρball).mp hρ
  unfold xiDiscRelativeIndex
  rw [hidx]
  have hle := Finset.single_le_sum
    (f := fun ρ' => (GaloisForLFunctions.HTGeometry.zeroMult (xiDiscDatum c t ht hne).F ρ' : ℤ))
    (fun ρ' _ => Int.natCast_nonneg _) hρZ
  have h1 : (1 : ℤ) ≤ (GaloisForLFunctions.HTGeometry.zeroMult (xiDiscDatum c t ht hne).F ρ : ℤ) := by
    exact_mod_cast one_le_zeroMult_xi hρ
  exact lt_of_lt_of_le one_pos (h1.trans hle)

/-- Under RH the relative index vanishes on every disc strictly right of the critical line. -/
theorem xiDiscRelativeIndex_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis)
    (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0)
    (hright : ∀ z ∈ closedBall c t, 1 / 2 < z.re) :
    xiDiscRelativeIndex c t ht hne = 0 := by
  obtain ⟨Z, hZball, hZzero, hidx⟩ := (xiDiscDatum c t ht hne).relativeIndex_eq_zeroCount
  have hbound := xiZeroHalfPlaneBound_zero_iff_rh.mpr hRH
  have hZ : Z = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ρ hρ
    have hball := hZball ρ hρ
    have hxi : xi ρ = 0 := (hZzero ρ hball).mpr hρ
    have hre := hbound ρ hxi
    have hgt := hright ρ (ball_subset_closedBall hball)
    linarith
  unfold xiDiscRelativeIndex
  rw [hidx, hZ, Finset.sum_empty]

/-- Every zero of `xi` right of the critical line lies inside an admissible right disc. -/
theorem exists_xiRightDisc_of_zero {ρ : ℂ} (hρ : xi ρ = 0) (hre : 1 / 2 < ρ.re) :
    ∃ t : ℝ, ∃ ht : 0 < t, ∃ hne : ∀ ζ ∈ sphere ρ t, xi ζ ≠ 0,
      (∀ z ∈ closedBall ρ t, 1 / 2 < z.re) ∧ 0 < xiDiscRelativeIndex ρ t ht hne := by
  have han : AnalyticAt ℂ xi ρ := xi_differentiable.analyticAt ρ
  have hiso : ∀ᶠ z in 𝓝[≠] ρ, xi z ≠ 0 := by
    rcases han.eventually_eq_zero_or_eventually_ne_zero with hev | hev
    · exfalso
      have hall : Set.EqOn xi 0 Set.univ :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (fun z _ => xi_differentiable.analyticAt z)
          isPreconnected_univ (Set.mem_univ ρ) hev
      exact xi_ne_zero_of_one_le_re (ρ := 2) (by norm_num) (hall (Set.mem_univ 2))
    · exact hev
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hiso
  obtain ⟨ε, hε, hεne⟩ := hiso
  set t : ℝ := min (ε / 2) ((ρ.re - 1 / 2) / 2) with htdef
  have ht : 0 < t := lt_min (by linarith) (by linarith)
  have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hne : ∀ ζ ∈ sphere ρ t, xi ζ ≠ 0 := by
    intro ζ hζ
    rw [mem_sphere] at hζ
    refine hεne (by rw [hζ]; exact htε) ?_
    intro hζρ
    rw [Set.mem_singleton_iff] at hζρ
    rw [hζρ, dist_self] at hζ
    exact (ne_of_gt ht) hζ.symm
  refine ⟨t, ht, hne, ?_, ?_⟩
  · intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    have h1 : |(z - ρ).re| ≤ ‖z - ρ‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re] at h1
    have h2 : t ≤ (ρ.re - 1 / 2) / 2 := min_le_right _ _
    have h3 := neg_abs_le (z.re - ρ.re)
    linarith
  · exact xiDiscRelativeIndex_pos_of_zero ρ t ht hne (mem_ball_self ht) hρ

/-- **RH as vanishing of the Hardy relative index.**  The Riemann hypothesis holds if and only if,
on every circle bounding a closed disc strictly right of the critical line and avoiding the zeros
of `xi`, the Hardy pair of the `xi` boundary phase has relative index zero. -/
theorem riemannHypothesis_iff_forall_xiRightDisc_relativeIndex_eq_zero :
    RiemannHypothesis ↔
      ∀ (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0),
        (∀ z ∈ closedBall c t, 1 / 2 < z.re) → xiDiscRelativeIndex c t ht hne = 0 := by
  constructor
  · intro hRH c t ht hne hright
    exact xiDiscRelativeIndex_eq_zero_of_riemannHypothesis hRH c t ht hne hright
  · intro h
    rw [← xiZeroHalfPlaneBound_zero_iff_rh]
    intro ρ hρ
    by_contra hgt
    push Not at hgt
    obtain ⟨t, ht, hne, hright, hpos⟩ := exists_xiRightDisc_of_zero hρ (by linarith)
    have h0 := h ρ t ht hne hright
    omega

/-- **Adjoint-seam consumer.**  If on every admissible right disc the adjoint Hankel seam
`(1 − P) U† P` of the `xi` boundary phase is a strict contraction, the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_forall_xiRightDisc_adjointSeam_lt_one
    (h : ∀ (c : ℂ) (t : ℝ) (ht : 0 < t) (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0),
      (∀ z ∈ closedBall c t, 1 / 2 < z.re) →
        ‖(xiDiscDatum c t ht hne).circlePhase.datum.adjointHankelSeam‖ < 1) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_xiRightDisc_relativeIndex_eq_zero]
  intro c t ht hne hright
  set D := (xiDiscDatum c t ht hne).circlePhase.datum with hD
  have hnonpos := D.re_opTrace_cubicDefect_nonpos_of_adjointSeam (h c t ht hne hright)
  rw [D.opTrace_cubicDefect_eq_relativeIndex, Complex.intCast_re] at hnonpos
  have hle : xiDiscRelativeIndex c t ht hne ≤ 0 := by exact_mod_cast hnonpos
  exact le_antisymm hle (xiDiscRelativeIndex_nonneg c t ht hne)

end RHTower
