import GaloisForLFunctions.HTGeometry.BohrReturnSequence
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Almost periodicity on a vertical strip passes to every derivative

Almost periodicity of a holomorphic function on a vertical strip is uniform convergence of vertical
translates on each closed substrip.  Cauchy's estimate turns it into almost periodicity of the
derivative on any slightly narrower substrip: the translated difference is holomorphic and bounded by
`ε` on discs of radius `ρ` around the narrower strip, so its derivative is bounded by `ε / ρ` there,
and rescaling the tolerance absorbs the loss.  Iterating, every derivative is almost periodic on
every closed substrip, and restricting to the central line makes each jet coordinate a Bohr almost
periodic function of the imaginary part.

The strip — rather than the plane — is the right domain: a holomorphic function whose vertical
translates converge uniformly on all of `ℂ` has, by Liouville applied to the translated difference,
a genuinely periodic behaviour, so plane-uniform almost periodicity would be an empty setting for the
finite-phase law.  On a strip the class is the intended one.

The consequence used by the recurrence collapse is a *single* sequence of vertical return times
along which the function and all its derivatives up to any fixed order return to themselves.
-/

open Filter Topology Metric

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The open vertical strip of half-width `R` around the abscissa `σ`. -/
def verticalStrip (σ R : ℝ) : Set ℂ := {z : ℂ | |z.re - σ| < R}

theorem isOpen_verticalStrip (σ R : ℝ) : IsOpen (verticalStrip σ R) := by
  have : verticalStrip σ R = (fun z : ℂ => |z.re - σ|) ⁻¹' (Set.Iio R) := rfl
  rw [this]
  exact (isOpen_Iio).preimage ((Complex.continuous_re.sub continuous_const).abs)

/-- Almost periodicity of `F` uniformly on the closed vertical substrip of half-width `r`. -/
def IsStripAlmostPeriodicOn (F : ℂ → ℂ) (σ r : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, 0 < L ∧ ∀ a : ℝ, ∃ τ ∈ Set.Icc a (a + L),
    ∀ z : ℂ, |z.re - σ| ≤ r → ‖F (z + (τ : ℂ) * Complex.I) - F z‖ ≤ ε

/-- Almost periodicity on every closed substrip strictly inside the open strip of half-width `R`. -/
def IsStripAlmostPeriodic (F : ℂ → ℂ) (σ R : ℝ) : Prop :=
  ∀ r : ℝ, r < R → IsStripAlmostPeriodicOn F σ r

/-- **Cauchy's estimate for an almost period.**  If the translated difference is bounded by `ε` on a
closed disc of radius `ρ`, the derivative of the difference at the centre is at most `ε / ρ`. -/
theorem norm_deriv_sub_deriv_le_of_ball {F : ℂ → ℂ} {S : Set ℂ} (hS : IsOpen S)
    (hF : DifferentiableOn ℂ F S) {τ ε ρ : ℝ} (hρ : 0 < ρ) {z : ℂ}
    (hball : Metric.closedBall z ρ ⊆ S)
    (hballτ : ∀ w ∈ Metric.closedBall z ρ, w + (τ : ℂ) * Complex.I ∈ S)
    (hb : ∀ w ∈ Metric.closedBall z ρ, ‖F (w + (τ : ℂ) * Complex.I) - F w‖ ≤ ε) :
    ‖deriv F (z + (τ : ℂ) * Complex.I) - deriv F z‖ ≤ ε / ρ := by
  set G : ℂ → ℂ := fun w => F (w + (τ : ℂ) * Complex.I) - F w with hG
  have hshift : ∀ w ∈ Metric.closedBall z ρ,
      DifferentiableAt ℂ (fun u : ℂ => F (u + (τ : ℂ) * Complex.I)) w := by
    intro w hw
    exact (hF.differentiableAt (hS.mem_nhds (hballτ w hw))).comp w
      ((differentiable_id.add_const _) w)
  have hGdiff : ∀ w ∈ Metric.closedBall z ρ, DifferentiableAt ℂ G w := by
    intro w hw
    exact (hshift w hw).sub (hF.differentiableAt (hS.mem_nhds (hball hw)))
  have hderiv : deriv G z = deriv F (z + (τ : ℂ) * Complex.I) - deriv F z := by
    have hsub : deriv (fun w : ℂ => F (w + (τ : ℂ) * Complex.I) - F w) z
        = deriv (fun w : ℂ => F (w + (τ : ℂ) * Complex.I)) z - deriv F z :=
      deriv_sub (hshift z (Metric.mem_closedBall_self hρ.le))
        (hF.differentiableAt (hS.mem_nhds (hball (Metric.mem_closedBall_self hρ.le))))
    rw [hG, hsub, deriv_comp_add_const]
  rw [← hderiv]
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ ?_ ?_
  · refine DiffContOnCl.mk ?_ ?_
    · intro w hw
      exact ((hGdiff w (ball_subset_closedBall hw)).differentiableWithinAt)
    · rw [closure_ball z hρ.ne']
      intro w hw
      exact (hGdiff w hw).continuousAt.continuousWithinAt
  · intro w hw
    exact hb w (sphere_subset_closedBall hw)

theorem re_add_mul_I (w : ℂ) (τ : ℝ) : (w + (τ : ℂ) * Complex.I).re = w.re := by
  simp

theorem abs_re_sub_le_dist (w z : ℂ) : |w.re - z.re| ≤ dist w z := by
  have h := Complex.abs_re_le_norm (w - z)
  rw [Complex.sub_re] at h
  rwa [dist_eq_norm]

/-- **The derivative of a strip-almost-periodic holomorphic function is strip almost periodic**, on
any slightly narrower substrip. -/
theorem isStripAlmostPeriodicOn_deriv {F : ℂ → ℂ} {σ R r ρ : ℝ} (hρ : 0 < ρ)
    (hrρ : r + ρ < R) (_hr : 0 ≤ r)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hap : IsStripAlmostPeriodicOn F σ (r + ρ)) :
    IsStripAlmostPeriodicOn (deriv F) σ r := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hap (ε * ρ) (by positivity)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτ, hb⟩ := hdense a
  refine ⟨τ, hτ, fun z hz => ?_⟩
  have hre : ∀ w ∈ closedBall z ρ, |w.re - σ| ≤ r + ρ := by
    intro w hw
    have h1 : |w.re - z.re| ≤ ρ := le_trans (abs_re_sub_le_dist w z) (mem_closedBall.mp hw)
    calc |w.re - σ| = |(w.re - z.re) + (z.re - σ)| := by ring_nf
      _ ≤ |w.re - z.re| + |z.re - σ| := abs_add_le _ _
      _ ≤ ρ + r := add_le_add h1 hz
      _ = r + ρ := by ring
  have hball : closedBall z ρ ⊆ verticalStrip σ R := by
    intro w hw
    have := hre w hw
    exact lt_of_le_of_lt this hrρ
  have hballτ : ∀ w ∈ closedBall z ρ, w + (τ : ℂ) * Complex.I ∈ verticalStrip σ R := by
    intro w hw
    have hval : (w + (τ : ℂ) * Complex.I).re = w.re := re_add_mul_I w τ
    have : |(w + (τ : ℂ) * Complex.I).re - σ| ≤ r + ρ := by
      rw [hval]
      exact hre w hw
    exact lt_of_le_of_lt this hrρ
  have hbb : ∀ w ∈ closedBall z ρ, ‖F (w + (τ : ℂ) * Complex.I) - F w‖ ≤ ε * ρ :=
    fun w hw => hb w (hre w hw)
  have hmain := norm_deriv_sub_deriv_le_of_ball (isOpen_verticalStrip σ R) hF hρ hball hballτ hbb
  calc ‖deriv F (z + (τ : ℂ) * Complex.I) - deriv F z‖ ≤ (ε * ρ) / ρ := hmain
    _ = ε := by field_simp

/-- Holomorphy on the strip passes to the derivative. -/
theorem differentiableOn_deriv_verticalStrip {F : ℂ → ℂ} {σ R : ℝ}
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) :
    DifferentiableOn ℂ (deriv F) (verticalStrip σ R) :=
  ((hF.analyticOnNhd (isOpen_verticalStrip σ R)).deriv).differentiableOn

/-- **Strip almost periodicity passes to the derivative.** -/
theorem isStripAlmostPeriodic_deriv {F : ℂ → ℂ} {σ R : ℝ}
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R) :
    IsStripAlmostPeriodic (deriv F) σ R := by
  intro r hr
  rcases lt_or_ge r 0 with hneg | hpos
  · intro ε hε
    refine ⟨1, one_pos, fun a => ⟨a, ⟨le_refl a, by linarith⟩, fun z hz => ?_⟩⟩
    exact absurd (le_trans (abs_nonneg _) hz) (not_le.mpr hneg)
  · have hρ : 0 < (R - r) / 2 := by linarith
    have hsum : r + (R - r) / 2 < R := by linarith
    exact isStripAlmostPeriodicOn_deriv hρ hsum hpos hF (hap _ hsum)

/-- Every iterated derivative is holomorphic and strip almost periodic. -/
theorem isStripAlmostPeriodic_iteratedDeriv {F : ℂ → ℂ} {σ R : ℝ}
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R) :
    ∀ n : ℕ, DifferentiableOn ℂ (iteratedDeriv n F) (verticalStrip σ R) ∧
      IsStripAlmostPeriodic (iteratedDeriv n F) σ R := by
  intro n
  induction n with
  | zero =>
      rw [iteratedDeriv_zero]
      exact ⟨hF, hap⟩
  | succ m ih =>
      obtain ⟨hd, ha⟩ := ih
      rw [iteratedDeriv_succ]
      exact ⟨differentiableOn_deriv_verticalStrip hd, isStripAlmostPeriodic_deriv hd ha⟩

/-- The restriction to the central line of a strip almost periodic function is Bohr almost
periodic. -/
theorem isBohrAlmostPeriodic_line {F : ℂ → ℂ} {σ R : ℝ} (hR : 0 < R)
    (hap : IsStripAlmostPeriodic F σ R) :
    IsBohrAlmostPeriodic (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hap 0 hR ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτ, hb⟩ := hdense a
  refine ⟨τ, hτ, fun x => ?_⟩
  have hz : |((σ : ℂ) + (x : ℂ) * Complex.I).re - σ| ≤ 0 := by
    simp
  have h := hb ((σ : ℂ) + (x : ℂ) * Complex.I) hz
  have hrw : (σ : ℂ) + (x : ℂ) * Complex.I + (τ : ℂ) * Complex.I
      = (σ : ℂ) + ((x + τ : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rwa [hrw] at h

/-- The restriction of a holomorphic function on the strip to the central line is continuous. -/
theorem continuous_line_restriction {F : ℂ → ℂ} {σ R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) :
    Continuous fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  have hline : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ verticalStrip σ R := by
    intro t
    have : |((σ : ℂ) + (t : ℂ) * Complex.I).re - σ| = 0 := by simp
    rw [verticalStrip, Set.mem_setOf_eq, this]
    exact hR
  have hcont : Continuous fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hd : DifferentiableAt ℂ F ((σ : ℂ) + (t : ℂ) * Complex.I) :=
    hF.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds (hline t))
  exact ContinuousAt.comp (x := t) hd.continuousAt hcont.continuousAt

/-- **One return sequence for the function and all its derivatives on the central line.** -/
theorem exists_return_sequence_jets {F : ℂ → ℂ} {σ R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R) (n : ℕ) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      ∀ (k : Fin n) (x : ℝ),
        Tendsto (fun l => iteratedDeriv (k : ℕ) F ((σ : ℂ) + ((x + T l : ℝ) : ℂ) * Complex.I))
          atTop (nhds (iteratedDeriv (k : ℕ) F ((σ : ℂ) + (x : ℂ) * Complex.I))) := by
  obtain ⟨T, hT, hret⟩ := exists_bohr_return_sequence_tendsto
    (g := fun k : Fin n => fun t : ℝ =>
      iteratedDeriv (k : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I))
    (fun k => continuous_line_restriction hR (isStripAlmostPeriodic_iteratedDeriv hF hap k).1)
    (fun k => isBohrAlmostPeriodic_line hR (isStripAlmostPeriodic_iteratedDeriv hF hap k).2)
  exact ⟨T, hT, fun k x => hret k x⟩

end GaloisForLFunctions
