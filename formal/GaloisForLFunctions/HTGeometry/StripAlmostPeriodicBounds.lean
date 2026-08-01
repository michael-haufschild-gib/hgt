import GaloisForLFunctions.HTGeometry.VerticalAlmostPeriodicDerivative
import Mathlib.Analysis.Complex.Convex

/-!
# Bounds for strip almost periodic holomorphic functions

Almost periodicity on a closed substrip makes a continuous function bounded there: an almost period
carries any point into a compact window of the substrip, where continuity supplies the bound.  For a
holomorphic function this propagates to the derivative through Cauchy's estimate on discs contained
in a slightly wider substrip, and the mean value inequality then makes the function Lipschitz on the
substrip — the substrip being convex.  In particular vertical translation moves the function
Lipschitz-continuously in the translation parameter, uniformly on the substrip.

These are the estimates that make the family of vertical translates a continuous, bounded,
almost periodic curve in the sup-norm space of the substrip — the analytic input for transferring
the phase carrier from the line to the strip.
-/

open Filter Topology Metric Set

namespace GaloisForLFunctions

/-- The closed vertical substrip of half-width `r`. -/
def closedStrip (σ r : ℝ) : Set ℂ := {z : ℂ | |z.re - σ| ≤ r}

theorem isClosed_closedStrip (σ r : ℝ) : IsClosed (closedStrip σ r) := by
  have : closedStrip σ r = (fun z : ℂ => |z.re - σ|) ⁻¹' (Set.Iic r) := rfl
  rw [this]
  exact (isClosed_Iic).preimage ((Complex.continuous_re.sub continuous_const).abs)

theorem closedStrip_subset_verticalStrip {σ r R : ℝ} (h : r < R) :
    closedStrip σ r ⊆ verticalStrip σ R := fun _ hz => lt_of_le_of_lt hz h

/-- **A strip almost periodic function is bounded on the substrip.**  Every point is moved into a
compact window by an almost period, where continuity supplies a bound. -/
theorem exists_bound_of_isStripAlmostPeriodicOn {F : ℂ → ℂ} {σ r : ℝ}
    (hFcont : ContinuousOn F (closedStrip σ r)) (hap : IsStripAlmostPeriodicOn F σ r) :
    ∃ M : ℝ, ∀ z ∈ closedStrip σ r, ‖F z‖ ≤ M := by
  obtain ⟨L, hL, hdense⟩ := hap 1 one_pos
  set K : Set ℂ := {z : ℂ | |z.re - σ| ≤ r ∧ z.im ∈ Set.Icc (0 : ℝ) L} with hKdef
  have hKclosed : IsClosed K := by
    have h1 : IsClosed {z : ℂ | |z.re - σ| ≤ r} := isClosed_closedStrip σ r
    have h2 : IsClosed {z : ℂ | z.im ∈ Set.Icc (0 : ℝ) L} :=
      isClosed_Icc.preimage Complex.continuous_im
    exact h1.inter h2
  have hKbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨|σ| + r + L, fun z hz => ?_⟩
    have h1 : |z.re| ≤ |σ| + r := by
      have := hz.1
      calc |z.re| = |(z.re - σ) + σ| := by ring_nf
        _ ≤ |z.re - σ| + |σ| := abs_add_le _ _
        _ ≤ r + |σ| := by linarith
        _ = |σ| + r := by ring
    have h2 : |z.im| ≤ L := by
      have h3 := hz.2
      rw [abs_le]
      exact ⟨by linarith [h3.1], h3.2⟩
    rw [mem_closedBall_zero_iff]
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ (|σ| + r) + L := add_le_add h1 h2
      _ = |σ| + r + L := by ring
  have hKcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  have hKsub : K ⊆ closedStrip σ r := fun z hz => hz.1
  obtain ⟨M₀, hM₀⟩ := hKcompact.exists_bound_of_continuousOn (hFcont.mono hKsub)
  refine ⟨M₀ + 1, fun z hz => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense (-z.im)
  have hzK : z + (τ : ℂ) * Complex.I ∈ K := by
    refine ⟨?_, ?_, ?_⟩
    · have hre : (z + (τ : ℂ) * Complex.I).re = z.re := by simp
      rw [hre]
      exact hz
    · have him : (z + (τ : ℂ) * Complex.I).im = z.im + τ := by simp
      rw [him]
      linarith [hτmem.1]
    · have him : (z + (τ : ℂ) * Complex.I).im = z.im + τ := by simp
      rw [him]
      linarith [hτmem.2]
  have hb := hτ z hz
  have hbound := hM₀ _ hzK
  calc ‖F z‖ = ‖F (z + (τ : ℂ) * Complex.I) - (F (z + (τ : ℂ) * Complex.I) - F z)‖ := by ring_nf
    _ ≤ ‖F (z + (τ : ℂ) * Complex.I)‖ + ‖F (z + (τ : ℂ) * Complex.I) - F z‖ := norm_sub_le _ _
    _ ≤ M₀ + 1 := add_le_add hbound hb

theorem convex_closedStrip (σ r : ℝ) : Convex ℝ (closedStrip σ r) := by
  have hset : closedStrip σ r = {z : ℂ | z.re ≤ σ + r} ∩ {z : ℂ | σ - r ≤ z.re} := by
    ext z
    simp only [closedStrip, Set.mem_setOf_eq, Set.mem_inter_iff, abs_le]
    constructor
    · intro h; exact ⟨by linarith [h.2], by linarith [h.1]⟩
    · intro h; exact ⟨by linarith [h.2], by linarith [h.1]⟩
  rw [hset]
  exact (convex_halfSpace_re_le _).inter (convex_halfSpace_re_ge _)

/-- **A strip almost periodic holomorphic function has bounded derivative on every substrip.** -/
theorem exists_deriv_bound {F : ℂ → ℂ} {σ R r : ℝ} (hr : r < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedStrip σ r, ‖deriv F z‖ ≤ M := by
  set r' : ℝ := (r + R) / 2 with hr'def
  have hrr' : r < r' := by rw [hr'def]; linarith
  have hr'R : r' < R := by rw [hr'def]; linarith
  set ρ : ℝ := r' - r with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  have hsub : closedStrip σ r' ⊆ verticalStrip σ R := closedStrip_subset_verticalStrip hr'R
  have hcont : ContinuousOn F (closedStrip σ r') := (hF.mono hsub).continuousOn
  obtain ⟨M₀, hM₀⟩ := exists_bound_of_isStripAlmostPeriodicOn hcont (hap r' hr'R)
  refine ⟨max (M₀ / ρ) 0, le_max_right _ _, fun z hz => ?_⟩
  have hball : closedBall z ρ ⊆ closedStrip σ r' := by
    intro w hw
    have h1 : |w.re - z.re| ≤ ρ := le_trans (abs_re_sub_le_dist w z) (mem_closedBall.mp hw)
    calc |w.re - σ| = |(w.re - z.re) + (z.re - σ)| := by ring_nf
      _ ≤ |w.re - z.re| + |z.re - σ| := abs_add_le _ _
      _ ≤ ρ + r := add_le_add h1 hz
      _ = r' := by rw [hρdef]; ring
  have hdiff : ∀ w ∈ closedBall z ρ, DifferentiableAt ℂ F w := by
    intro w hw
    exact hF.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds (hsub (hball hw)))
  have hcauchy : ‖deriv F z‖ ≤ M₀ / ρ := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρpos ?_ ?_
    · refine DiffContOnCl.mk ?_ ?_
      · intro w hw
        exact (hdiff w (ball_subset_closedBall hw)).differentiableWithinAt
      · rw [closure_ball z hρpos.ne']
        intro w hw
        exact (hdiff w hw).continuousAt.continuousWithinAt
    · intro w hw
      exact hM₀ w (hball (sphere_subset_closedBall hw))
  exact le_trans hcauchy (le_max_left _ _)

/-- **A strip almost periodic holomorphic function is Lipschitz on every substrip.** -/
theorem exists_lipschitzOnWith_closedStrip {F : ℂ → ℂ} {σ R r : ℝ} (hr : r < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ closedStrip σ r, ∀ w ∈ closedStrip σ r,
      ‖F z - F w‖ ≤ M * ‖z - w‖ := by
  obtain ⟨M, hM0, hMb⟩ := exists_deriv_bound hr hF hap
  refine ⟨M, hM0, ?_⟩
  have hdiff : ∀ z ∈ closedStrip σ r, HasFDerivWithinAt F
      (((fderiv ℂ F z).restrictScalars ℝ)) (closedStrip σ r) z := by
    intro z hz
    have hzs : z ∈ verticalStrip σ R := closedStrip_subset_verticalStrip hr hz
    have hd : HasFDerivAt F (fderiv ℂ F z) z :=
      (hF.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds hzs)).hasFDerivAt
    exact ((hd.restrictScalars ℝ).hasFDerivWithinAt)
  have hnorm : ∀ z ∈ closedStrip σ r, ‖((fderiv ℂ F z).restrictScalars ℝ)‖ ≤ M := by
    intro z hz
    rw [ContinuousLinearMap.norm_restrictScalars]
    have hzs : z ∈ verticalStrip σ R := closedStrip_subset_verticalStrip hr hz
    have hd : HasFDerivAt F (fderiv ℂ F z) z :=
      (hF.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds hzs)).hasFDerivAt
    have heq : fderiv ℂ F z = ContinuousLinearMap.toSpanSingleton ℂ (deriv F z) := by
      rw [← toSpanSingleton_deriv]
    rw [heq, ContinuousLinearMap.norm_toSpanSingleton]
    exact hMb z hz
  intro z hz w hw
  exact (convex_closedStrip σ r).norm_image_sub_le_of_norm_hasFDerivWithin_le hdiff hnorm hw hz

/-- Vertical translates of a strip almost periodic holomorphic function move Lipschitz-continuously
in the parameter, uniformly on the substrip. -/
theorem norm_translate_sub_le {F : ℂ → ℂ} {σ R r : ℝ} (hr : r < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (τ τ' : ℝ), ∀ z ∈ closedStrip σ r,
      ‖F (z + (τ : ℂ) * Complex.I) - F (z + (τ' : ℂ) * Complex.I)‖ ≤ M * |τ - τ'| := by
  obtain ⟨M, hM0, hMb⟩ := exists_lipschitzOnWith_closedStrip hr hF hap
  refine ⟨M, hM0, fun τ τ' z hz => ?_⟩
  have hmem : ∀ s : ℝ, z + (s : ℂ) * Complex.I ∈ closedStrip σ r := by
    intro s
    have hre : (z + (s : ℂ) * Complex.I).re = z.re := by simp
    show |(z + (s : ℂ) * Complex.I).re - σ| ≤ r
    rw [hre]
    exact hz
  have hdist : ‖(z + (τ : ℂ) * Complex.I) - (z + (τ' : ℂ) * Complex.I)‖ = |τ - τ'| := by
    have : (z + (τ : ℂ) * Complex.I) - (z + (τ' : ℂ) * Complex.I)
        = ((τ - τ' : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have h := hMb _ (hmem τ) _ (hmem τ')
  rwa [hdist] at h

end GaloisForLFunctions
