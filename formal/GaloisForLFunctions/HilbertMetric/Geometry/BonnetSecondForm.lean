import GaloisForLFunctions.HilbertMetric.Geometry.BonnetSurface
import GaloisForLFunctions.RHTower.Suzuki.SuzukiInteriorExcursionSpectralTurningPoint
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The normal component of the actual second derivative

Differentiating orthogonality of the unit normal and surface tangent
recovers the second fundamental form. The explicit positive radius scale
then excludes a height maximum whose direction opposes the Gauss normal.
-/

open scoped ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.BonnetSecondForm
open BonnetSupport BonnetSurface StereographicFrame SchwartzRadius
noncomputable section

/-- The sphere normal and its two tangent vectors resolve every ambient vector. -/
theorem frame_resolution (p : ℝ × ℝ) (v : Space) :
    v = inner ℝ v (normal p) • normal p +
      (denominator p ^ 2 / 4 * inner ℝ v (tangentX p)) • tangentX p +
      (denominator p ^ 2 / 4 * inner ℝ v (tangentY p)) • tangentY p := by
  ext i
  fin_cases i <;>
    simp [normal_formula, tangentX, tangentY, PiLp.inner_apply, Fin.sum_univ_three,
      PiLp.add_apply, PiLp.smul_apply] <;>
    field_simp [(denominator_pos p).ne'] <;> unfold denominator <;> ring

private theorem slice_smooth {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (y : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => surface ρ (t, y)) :=
  (surface_smooth hρ).comp (contDiff_id.prodMk contDiff_const)

/-- The second height derivative is the normal component of the actual second surface derivative. -/
theorem height_second {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (p : ℝ × ℝ) (n : Space) :
    deriv (deriv (fun t => inner ℝ (surface ρ (t, p.2)) n)) p.1 =
      inner ℝ (deriv (deriv (fun t => surface ρ (t, p.2))) p.1) n := by
  have hs := slice_smooth hρ p.2
  have hd : ContDiff ℝ ∞ (deriv (fun t => surface ρ (t, p.2))) :=
    (contDiff_infty_iff_deriv.mp hs).2
  have he : deriv (fun t => inner ℝ (surface ρ (t, p.2)) n) =
      (fun t => inner ℝ (deriv (fun s => surface ρ (s, p.2)) t) n) := by
    funext t
    have h := ((hs.differentiable (by simp) t).hasDerivAt).inner ℝ (hasDerivAt_const t n)
    simpa only [inner_zero_right, zero_add] using h.deriv
  rw [he]
  have h := ((hd.differentiable (by simp) p.1).hasDerivAt).inner ℝ (hasDerivAt_const p.1 n)
  simpa only [inner_zero_right, zero_add] using h.deriv

/-- The round conformal factor times the radius entry is the negative normal second derivative. -/
theorem normal_second {ρ : ℝ × ℝ → ℝ} (hρ : ContDiff ℝ ∞ ρ) (p : ℝ × ℝ) :
    inner ℝ (deriv (deriv (fun t => surface ρ (t, p.2))) p.1) (normal p) =
      -(2 / denominator p) ^ 2 * radiusXX ρ p := by
  have hs := slice_smooth hρ p.2
  have hd : ContDiff ℝ ∞ (deriv (fun t => surface ρ (t, p.2))) :=
    (contDiff_infty_iff_deriv.mp hs).2
  have hn : HasDerivAt (fun t => normal (t, p.2)) (tangentX p) p.1 := by
    simpa only [one_smul, zero_smul, add_zero, id_eq, Prod.mk.eta] using
      normal_path (hasDerivAt_id p.1) (hasDerivAt_const p.1 p.2)
  have hi := ((hd.differentiable (by simp) p.1).hasDerivAt).inner ℝ hn
  have he : (fun t => inner ℝ (deriv (fun s => surface ρ (s, p.2)) t) (normal (t, p.2))) =
      (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    rw [real_inner_comm]
    exact (surface_normal hρ (t, p.2)).1
  have hzero := hi.deriv
  rw [he] at hzero
  simp only [deriv_const] at hzero
  obtain ⟨hx, _⟩ := surface_partials hρ p
  obtain ⟨hxx, _, hxy⟩ := tangent_metric p
  have hyx : inner ℝ (tangentY p) (tangentX p) = 0 := by rw [real_inner_comm, hxy]
  have hp : inner ℝ (deriv (fun t => surface ρ (t, p.2)) p.1) (tangentX p) =
      (2 / denominator p) ^ 2 * radiusXX ρ p := by
    rw [hx]
    simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial,
      hxx, hyx, mul_zero, add_zero]
    ring
  rw [hp] at hzero
  linarith only [hzero]

/-- A height in the opposite normal direction has strictly positive second derivative. -/
theorem opposite_height_second_pos (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    0 < deriv (deriv (fun t => inner ℝ
      (surface (support f (positiveScale f)) (t, p.2)) (-normal p))) p.1 := by
  have hs : ContDiff ℝ ∞ (support f (positiveScale f)) := support_smooth (f.smooth ⊤) _
  rw [height_second hs, inner_neg_right, normal_second hs]
  have hp := radius_uniform_positive f p 1 0
  norm_num at hp
  have hc : 0 < (2 / denominator p) ^ 2 := sq_pos_of_pos (div_pos (by norm_num) (denominator_pos p))
  have hr : 0 < radiusXX (support f (positiveScale f)) p := by linarith only [hp]
  nlinarith only [mul_pos hc hr]

/-- An actual local height maximum cannot have direction opposite to the surface normal. -/
theorem no_opposite_height_max (f : SchwartzMap (ℝ × ℝ) ℝ) (p : ℝ × ℝ) :
    ¬ IsLocalMax (fun t => inner ℝ
      (surface (support f (positiveScale f)) (t, p.2)) (-normal p)) p.1 := by
  intro hmax
  have hs := slice_smooth (support_smooth (f.smooth ⊤) (positiveScale f)) p.2
  have hc : ContinuousAt (fun t => inner ℝ
      (surface (support f (positiveScale f)) (t, p.2)) (-normal p)) p.1 :=
    hs.continuous.continuousAt.inner continuousAt_const
  exact (not_le_of_gt (opposite_height_second_pos f p))
    (_root_.RHTower.suzukiSecondDeriv_nonpos_of_isLocalMax hmax hc)

#print axioms frame_resolution
#print axioms height_second
#print axioms normal_second
#print axioms opposite_height_second_pos
#print axioms no_opposite_height_max
end
end GaloisForLFunctions.HilbertMetric.Geometry.BonnetSecondForm
