import GaloisForLFunctions.HTGeometry.BallLogarithm
import Mathlib.Analysis.Complex.Liouville

/-!
# The logarithmic derivative of a zero-free function

On a disc where a holomorphic function does not vanish, the logarithmic derivative is the derivative
of a branch of the logarithm.  Borel--Carathéodory bounds that branch by the logarithm of the
maximum-to-anchor ratio, and Cauchy's estimate turns the bound on the branch into a bound on its
derivative.

The result is the zero-free case of Nevanlinna's estimate for the logarithmic derivative: the bound
is logarithmic in the maximum modulus, hence small compared with the characteristic.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-- **The logarithmic derivative is the derivative of the branch.** -/
theorem logDeriv_eq_deriv_branch {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hg : DifferentiableOn ℂ g (ball c R))
    (hfg : ∀ z ∈ ball c R, f z = f c * Complex.exp (g z))
    (hne : ∀ z ∈ ball c R, f z ≠ 0)
    {z : ℂ} (hz : z ∈ ball c R) :
    deriv f z / f z = deriv g z := by
  have hnhds : ball c R ∈ nhds z := isOpen_ball.mem_nhds hz
  have hgz : HasDerivAt g (deriv g z) z :=
    (hg.differentiableAt hnhds).hasDerivAt
  have hexp : HasDerivAt (fun w => f c * Complex.exp (g w))
      (f c * (Complex.exp (g z) * deriv g z)) z := (hgz.cexp).const_mul (f c)
  have heq : f =ᶠ[nhds z] fun w => f c * Complex.exp (g w) := by
    filter_upwards [hnhds] with w hw
    exact hfg w hw
  have hderiv : deriv f z = f c * (Complex.exp (g z) * deriv g z) := by
    rw [heq.deriv_eq]
    exact hexp.deriv
  have hfz : f z = f c * Complex.exp (g z) := hfg z hz
  have hR0 : 0 < R := by
    have hlt := mem_ball_iff_norm.mp hz
    have h0 : (0 : ℝ) ≤ ‖z - c‖ := norm_nonneg _
    linarith
  have hfc0 : f c ≠ 0 := hne c (mem_ball_self hR0)
  have hexp0 : Complex.exp (g z) ≠ 0 := Complex.exp_ne_zero _
  rw [hderiv, hfz]
  field_simp

/-- **The logarithmic derivative of a zero-free function.**  On the disc of radius `ρ` about `c`,

  `‖f' / f‖ ≤ 2 (log (M/m) + 1) r / (R - r) / (r - ρ)`,

where `M` bounds `f` on the disc of radius `R` and `m` is an anchor at the centre.  The bound is
logarithmic in `M`, which is what makes the corresponding proximity term small. -/
theorem norm_logDeriv_le {f : ℂ → ℂ} {c : ℂ} {R r ρ M m : ℝ}
    (hρ0 : 0 ≤ ρ) (hρr : ρ < r) (hrR : r < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hne : ∀ z ∈ ball c R, f z ≠ 0)
    (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (hm0 : 0 < m) (hm : m ≤ ‖f c‖)
    {z : ℂ} (hz : ‖z - c‖ ≤ ρ) :
    ‖deriv f z / f z‖
      ≤ 2 * (Real.log (M / m) + 1) * r / (R - r) / (r - ρ) := by
  have hr0 : (0 : ℝ) ≤ r := le_trans hρ0 (le_of_lt hρr)
  have hR0 : (0 : ℝ) < R := lt_of_le_of_lt hr0 hrR
  obtain ⟨g, hgon, hg0, hgeq, hgbd⟩ :=
    exists_bound_log_on_ball hr0 hrR hf hne hM hm0 hm
  set B : ℝ := 2 * (Real.log (M / m) + 1) * r / (R - r) with hB
  have hzmem : z ∈ ball c R := by
    rw [mem_ball_iff_norm]
    linarith
  have hstep : deriv f z / f z = deriv g z := logDeriv_eq_deriv_branch hgon hgeq hne hzmem
  have hgap : (0 : ℝ) < r - ρ := by linarith
  -- the small disc around `z` stays inside the big one
  have hsub : closedBall z (r - ρ) ⊆ ball c R := by
    intro w hw
    have hwz : ‖w - z‖ ≤ r - ρ := mem_closedBall_iff_norm.mp hw
    have : ‖w - c‖ ≤ r := by
      calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
        _ ≤ r := by linarith
    rw [mem_ball_iff_norm]
    linarith
  have hdc : DiffContOnCl ℂ g (ball z (r - ρ)) := by
    refine ⟨hgon.mono (subset_trans ball_subset_closedBall hsub), ?_⟩
    rw [closure_ball z (ne_of_gt hgap)]
    exact (hgon.mono hsub).continuousOn
  have hC : ∀ w ∈ sphere z (r - ρ), ‖g w‖ ≤ B := by
    intro w hw
    have hwz : ‖w - z‖ = r - ρ := by simpa [mem_sphere_iff_norm] using hw
    refine hgbd w ?_
    calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by ring_nf
      _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
      _ ≤ r := by rw [hwz]; linarith
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hgap hdc hC
  rw [hstep]
  exact hcauchy

end GaloisForLFunctions.HTGeometry
