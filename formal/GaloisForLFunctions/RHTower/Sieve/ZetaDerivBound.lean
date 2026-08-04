import GaloisForLFunctions.RHTower.Sieve.ZetaStripGrowth
import GaloisForLFunctions.RHTower.Sieve.ZetaTruncated
import Mathlib.Analysis.Complex.Liouville

/-!
# A Cauchy estimate for the derivative of zeta

The classical zero-free region needs more than a lower bound for `‖ζ‖` off the real axis: it needs
to know that a hypothetical zero would force `ζ` to be *small nearby*, which is a statement about
`ζ'`.  Cauchy's estimate supplies it from the growth bound already proved: on a disc avoiding the
pole,

`‖ζ'(c)‖ ≤ C / R`  whenever `‖ζ‖ ≤ C` on the bounding circle.

Combined with the mean value inequality this gives `‖ζ(σ+iγ)‖ ≤ (σ − β)·C/R` at a zero `β+iγ`,
which is the last ingredient of the classical argument.
-/

namespace RHTower.Sieve

open Complex Metric

/-- Zeta is differentiable on any set avoiding the pole. -/
theorem differentiableOn_riemannZeta_of_ne_one {S : Set ℂ} (hS : ∀ w ∈ S, w ≠ 1) :
    DifferentiableOn ℂ riemannZeta S :=
  fun w hw => (differentiableAt_riemannZeta (hS w hw)).differentiableWithinAt

/-- **Cauchy's estimate for zeta.** -/
theorem norm_deriv_riemannZeta_le {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hne : ∀ w ∈ closedBall c R, w ≠ 1)
    (hC : ∀ w ∈ sphere c R, ‖riemannZeta w‖ ≤ C) :
    ‖deriv riemannZeta c‖ ≤ C / R := by
  have hdiffOn : DifferentiableOn ℂ riemannZeta (closedBall c R) :=
    differentiableOn_riemannZeta_of_ne_one hne
  have hdcc : DiffContOnCl ℂ riemannZeta (ball c R) := by
    refine ⟨hdiffOn.mono ball_subset_closedBall, ?_⟩
    exact hdiffOn.continuousOn.mono closure_ball_subset_closedBall
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdcc hC

/-- **Zeta is small near a zero.**  Parametrising the segment by a real variable turns the mean
value inequality into the one-dimensional statement, avoiding any scalar restriction. -/
theorem norm_riemannZeta_le_of_zero {z c : ℂ} {M : ℝ}
    (hzero : riemannZeta z = 0)
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, z + (t : ℂ) * (c - z) ≠ 1)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv riemannZeta (z + (t : ℂ) * (c - z))‖ ≤ M) :
    ‖riemannZeta c‖ ≤ M * ‖c - z‖ * 1 := by
  set g : ℝ → ℂ := fun t => riemannZeta (z + (t : ℂ) * (c - z)) with hg
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g ((c - z) * deriv riemannZeta (z + (t : ℂ) * (c - z)))
        (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hinner : HasDerivAt (fun u : ℝ => z + (u : ℂ) * (c - z)) (c - z) t := by
      have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h2 := (h1.mul_const (c - z)).const_add z
      simpa using h2
    have houter : HasDerivAt riemannZeta
        (deriv riemannZeta (z + (t : ℂ) * (c - z))) (z + (t : ℂ) * (c - z)) :=
      (differentiableAt_riemannZeta (hne t ht)).hasDerivAt
    have hcomp := HasDerivAt.scomp t houter hinner
    rw [smul_eq_mul] at hcomp
    exact hcomp.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(c - z) * deriv riemannZeta (z + (t : ℂ) * (c - z))‖ ≤ M * ‖c - z‖ := by
    intro t ht
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _)
  have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have hg0 : g 0 = 0 := by
    simp only [hg, Complex.ofReal_zero, zero_mul, add_zero]
    exact hzero
  have hg1 : g 1 = riemannZeta c := by
    simp only [hg, Complex.ofReal_one, one_mul]
    congr 1
    ring
  rw [hg0, hg1, sub_zero] at hmvt
  simpa using hmvt

/-- **The derivative bound made explicit.**  On a disc that stays in the right half-plane and away
from the real axis, the strip growth bound supplies the constant of Cauchy's estimate. -/
theorem norm_deriv_riemannZeta_le_explicit {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hre : R < c.re) (him : R < |c.im|) :
    ‖deriv riemannZeta c‖
      ≤ ((‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R)) / R := by
  have hne : ∀ w ∈ Metric.closedBall c R, w ≠ 1 := by
    intro w hw hcon
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hbase := Complex.abs_im_le_norm (w - c)
    have him' : |w.im - c.im| ≤ R := by
      simp only [Complex.sub_im] at hbase
      linarith
    rw [hcon] at him'
    simp only [Complex.one_im, zero_sub, abs_neg] at him'
    linarith
  have hC : ∀ w ∈ Metric.sphere c R,
      ‖riemannZeta w‖ ≤ (‖c‖ + R) / (|c.im| - R) + (‖c‖ + R) / (c.re - R) := by
    intro w hw
    rw [Metric.mem_sphere, Complex.dist_eq] at hw
    have hwc : ‖w - c‖ = R := hw
    have hnorm : ‖w‖ ≤ ‖c‖ + R := by
      have h := norm_add_le (w - c) c
      rw [hwc] at h
      simp only [sub_add_cancel] at h
      linarith
    have hrew : c.re - R ≤ w.re := by
      have h := Complex.abs_re_le_norm (w - c)
      rw [hwc] at h
      simp only [Complex.sub_re] at h
      have hb := abs_le.1 h
      linarith [hb.1]
    have himw : |c.im| - R ≤ ‖w - 1‖ := by
      have h := Complex.abs_im_le_norm (w - c)
      rw [hwc] at h
      simp only [Complex.sub_im] at h
      have hb := abs_le.1 h
      have hw1 := Complex.abs_im_le_norm (w - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at hw1
      rcases abs_cases c.im with ⟨hc, _⟩ | ⟨hc, _⟩ <;>
        rcases abs_cases w.im with ⟨hwi, _⟩ | ⟨hwi, _⟩ <;> linarith [hw1, hb.1, hb.2]
    have hstrip := norm_riemannZeta_strip_le (s := w) (by linarith) (hne w (by
      rw [Metric.mem_closedBall, Complex.dist_eq, hwc]))
    refine le_trans hstrip ?_
    have hden1 : (0 : ℝ) < |c.im| - R := by linarith
    have hden2 : (0 : ℝ) < c.re - R := by linarith
    have h1 : ‖w‖ / ‖w - 1‖ ≤ (‖c‖ + R) / (|c.im| - R) := by gcongr
    have h2 : ‖w‖ / w.re ≤ (‖c‖ + R) / (c.re - R) := by gcongr
    linarith
  exact norm_deriv_riemannZeta_le hR hne hC

/-- **The derivative bound with the logarithmic estimate.**  On a disc straddling the abscissa but
avoiding the pole, `ζ'` is `O(log N / R)`. -/
theorem norm_deriv_riemannZeta_le_log {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hre : 1 / 2 ≤ c.re - R) (him : R < |c.im|)
    {N : ℕ} (hN : 2 ≤ N) (hlow : 1 - 1 / Real.log N ≤ c.re - R)
    (hNw : ‖c‖ + R ≤ (N : ℝ)) :
    ‖deriv riemannZeta c‖
      ≤ (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|c.im| - R) + 2 * Real.exp 1) / R := by
  have hne : ∀ w ∈ Metric.closedBall c R, w ≠ 1 := by
    intro w hw hcon
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hbase := Complex.abs_im_le_norm (w - c)
    have him' : |w.im - c.im| ≤ R := by
      simp only [Complex.sub_im] at hbase
      linarith
    rw [hcon] at him'
    simp only [Complex.one_im, zero_sub, abs_neg] at him'
    linarith
  have hC : ∀ w ∈ Metric.sphere c R,
      ‖riemannZeta w‖
        ≤ 2 + Real.exp 1 * Real.log N + Real.exp 1 / (|c.im| - R) + 2 * Real.exp 1 := by
    intro w hw
    rw [Metric.mem_sphere, Complex.dist_eq] at hw
    have hwc : ‖w - c‖ = R := hw
    have hnorm : ‖w‖ ≤ ‖c‖ + R := by
      have h := norm_add_le (w - c) c
      rw [hwc] at h
      simp only [sub_add_cancel] at h
      linarith
    have hrew : c.re - R ≤ w.re := by
      have h := Complex.abs_re_le_norm (w - c)
      rw [hwc] at h
      simp only [Complex.sub_re] at h
      have hb := abs_le.1 h
      linarith [hb.1]
    have himw : |c.im| - R ≤ ‖w - 1‖ := by
      have h := Complex.abs_im_le_norm (w - c)
      rw [hwc] at h
      simp only [Complex.sub_im] at h
      have hb := abs_le.1 h
      have hw1 := Complex.abs_im_le_norm (w - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at hw1
      rcases abs_cases c.im with ⟨hc, _⟩ | ⟨hc, _⟩ <;>
        rcases abs_cases w.im with ⟨hwi, _⟩ | ⟨hwi, _⟩ <;> linarith [hw1, hb.1, hb.2]
    have hwne : w ≠ 1 := hne w (by rw [Metric.mem_closedBall, Complex.dist_eq, hwc])
    have hlog := norm_riemannZeta_le_log_uniform (w := w) (by linarith) hwne hN
      (by linarith) (by linarith)
    refine le_trans hlog ?_
    have hden : (0 : ℝ) < |c.im| - R := by linarith
    have hw1pos : (0 : ℝ) < ‖w - 1‖ := by linarith
    have hdiv : Real.exp 1 / ‖w - 1‖ ≤ Real.exp 1 / (|c.im| - R) := by gcongr
    linarith
  exact norm_deriv_riemannZeta_le hR hne hC

/-- **The derivative bound in the form the segment argument uses.**  Any point whose real part is at
least `β` and whose imaginary part is `γ` inherits the bound with the same constants. -/
theorem norm_deriv_riemannZeta_le_log_of_re_ge {p : ℂ} {β γ R : ℝ} {N : ℕ} (hR : 0 < R)
    (hre : β ≤ p.re) (him : p.im = γ)
    (hβ : 1 / 2 + R ≤ β) (hlow : 1 - 1 / Real.log N ≤ β - R)
    (hγ : R < |γ|) (hN : 2 ≤ N) (hNp : ‖p‖ + R ≤ (N : ℝ)) :
    ‖deriv riemannZeta p‖
      ≤ (2 + Real.exp 1 * Real.log N + Real.exp 1 / (|γ| - R) + 2 * Real.exp 1) / R := by
  have hpim : |p.im| = |γ| := by rw [him]
  have hbase := norm_deriv_riemannZeta_le_log (c := p) (R := R) hR
    (by linarith) (by rw [hpim]; exact hγ) hN (by linarith) hNp
  rw [hpim] at hbase
  exact hbase

/-- **The mean value inequality for zeta along a segment.**  The version without a zero: the
difference of values is bounded by the derivative bound times the distance. -/
theorem norm_riemannZeta_sub_le {z c : ℂ} {M : ℝ}
    (hne : ∀ t ∈ Set.Icc (0 : ℝ) 1, z + (t : ℂ) * (c - z) ≠ 1)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv riemannZeta (z + (t : ℂ) * (c - z))‖ ≤ M) :
    ‖riemannZeta c - riemannZeta z‖ ≤ M * ‖c - z‖ * 1 := by
  set g : ℝ → ℂ := fun t => riemannZeta (z + (t : ℂ) * (c - z)) with hg
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt g ((c - z) * deriv riemannZeta (z + (t : ℂ) * (c - z)))
        (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    have hinner : HasDerivAt (fun u : ℝ => z + (u : ℂ) * (c - z)) (c - z) t := by
      have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h2 := (h1.mul_const (c - z)).const_add z
      simpa using h2
    have houter : HasDerivAt riemannZeta
        (deriv riemannZeta (z + (t : ℂ) * (c - z))) (z + (t : ℂ) * (c - z)) :=
      (differentiableAt_riemannZeta (hne t ht)).hasDerivAt
    have hcomp := HasDerivAt.scomp t houter hinner
    rw [smul_eq_mul] at hcomp
    exact hcomp.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖(c - z) * deriv riemannZeta (z + (t : ℂ) * (c - z))‖ ≤ M * ‖c - z‖ := by
    intro t ht
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _)
  have hmvt := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  have hg0 : g 0 = riemannZeta z := by
    simp only [hg, Complex.ofReal_zero, zero_mul, add_zero]
  have hg1 : g 1 = riemannZeta c := by
    simp only [hg, Complex.ofReal_one, one_mul]
    congr 1
    ring
  rw [hg0, hg1] at hmvt
  simpa using hmvt

end RHTower.Sieve
