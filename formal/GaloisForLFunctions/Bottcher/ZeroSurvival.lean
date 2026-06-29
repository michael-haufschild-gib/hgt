/-
# Newton zero-survival lemmas

This file isolates the analytic zero-production step needed by the Poincare/Hurwitz route:
if a Newton correction maps a closed ball into itself and contracts there, then the original
function has a zero in the ball.  The final theorem packages this in the derivative-variation
form used when a locally uniform limit has a simple zero.
-/
import GaloisForLFunctions.Bottcher.InverseBranchPeriodic

open Set Filter Topology Metric

namespace Bottcher

noncomputable section

/-- A derivative-bounded Newton correction on a closed ball has a zero of the original function. -/
theorem exists_zero_of_newton_contraction_closedBall
    {a A : ℂ} {r : ℝ} {F : ℂ → ℂ} {K : NNReal}
    (hA : A ≠ 0)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hcenter : dist (a - A * F a) a + (K : ℝ) * r ≤ r)
    (hderivWithin : ∀ z ∈ Metric.closedBall a r,
      HasDerivWithinAt (fun w => w - A * F w)
        (deriv (fun w => w - A * F w) z) (Metric.closedBall a r) z)
    (hderiv_bound : ∀ z ∈ Metric.closedBall a r,
      ‖deriv (fun w => w - A * F w) z‖ ≤ (K : ℝ)) :
    ∃ y ∈ Metric.closedBall a r, F y = 0 := by
  let T : ℂ → ℂ := fun w => w - A * F w
  have hlip : LipschitzOnWith K T (Metric.closedBall a r) := by
    apply (convex_closedBall a r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (by simpa [T] using hderivWithin)
    intro z hz
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact by simpa [T] using hderiv_bound z hz
  have ha : a ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall, dist_self]
    exact hr
  have hmaps : Set.MapsTo T (Metric.closedBall a r) (Metric.closedBall a r) := by
    intro y hy
    rw [Metric.mem_closedBall] at hy ⊢
    have hdist := hlip.dist_le_mul y hy a ha
    have hstep : dist (T y) a ≤ (K : ℝ) * r + dist (T a) a := by
      have hdist' : dist (T y) (T a) ≤ (K : ℝ) * dist y a := hdist
      have hmul : (K : ℝ) * dist y a ≤ (K : ℝ) * r :=
        mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg K)
      calc
        dist (T y) a ≤ dist (T y) (T a) + dist (T a) a := dist_triangle _ _ _
        _ ≤ (K : ℝ) * dist y a + dist (T a) a := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hdist' (dist (T a) a)
        _ ≤ (K : ℝ) * r + dist (T a) a := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_right hmul (dist (T a) a)
    linarith [hstep, hcenter]
  have hcontr : ContractingWith K (Set.MapsTo.restrict T (Metric.closedBall a r)
      (Metric.closedBall a r) hmaps) := by
    refine ⟨hK, ?_⟩
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    have hdist := hlip.dist_le_mul x.1 x.2 y.1 y.2
    simpa [Set.MapsTo.restrict, Subtype.dist_eq] using hdist
  have hcomplete : IsComplete (Metric.closedBall a r) := Metric.isClosed_closedBall.isComplete
  obtain ⟨y, hy, hfix, _htend, _hest⟩ :=
    hcontr.exists_fixedPoint' hcomplete hmaps ha (edist_ne_top a (T a))
  have hmul : A * F y = 0 := by
    have hsub : y - A * F y - y = 0 := sub_eq_zero.mpr hfix
    linear_combination -hsub
  exact ⟨y, hy, (mul_eq_zero.mp hmul).resolve_left hA⟩

/-- Target-ball version of `exists_zero_of_newton_contraction_closedBall`. -/
theorem exists_zero_mem_ball_of_newton_contraction
    {ζ a A : ℂ} {R r : ℝ} {F : ℂ → ℂ} {K : NNReal}
    (hA : A ≠ 0)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hclosed : Metric.closedBall a r ⊆ Metric.ball ζ R)
    (hcenter : dist (a - A * F a) a + (K : ℝ) * r ≤ r)
    (hderivWithin : ∀ z ∈ Metric.closedBall a r,
      HasDerivWithinAt (fun w => w - A * F w)
        (deriv (fun w => w - A * F w) z) (Metric.closedBall a r) z)
    (hderiv_bound : ∀ z ∈ Metric.closedBall a r,
      ‖deriv (fun w => w - A * F w) z‖ ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, F y = 0 := by
  obtain ⟨y, hy, hzero⟩ :=
    exists_zero_of_newton_contraction_closedBall
      (a := a) (A := A) (r := r) (F := F) (K := K)
      hA hr hK hcenter hderivWithin hderiv_bound
  exact ⟨y, hclosed hy, hzero⟩

/-- Derivative of the Newton correction with an exact inverse derivative coefficient. -/
theorem deriv_newton_correction_eq_inv_mul_deriv_sub
    {F : ℂ → ℂ} {a A y : ℂ}
    (hAinv : A * deriv F a = 1)
    (hF : HasDerivAt F (deriv F y) y) :
    deriv (fun w => w - A * F w) y = A * (deriv F a - deriv F y) := by
  have hT : HasDerivAt (fun w => w - A * F w) (1 - A * deriv F y) y :=
    (hasDerivAt_id y).sub (hF.const_mul A)
  rw [hT.deriv]
  calc
    1 - A * deriv F y = A * deriv F a - A * deriv F y := by rw [hAinv]
    _ = A * (deriv F a - deriv F y) := by ring

/-- A derivative-variation bound gives the Newton contraction bound for a true inverse-derivative
coefficient. -/
theorem newton_correction_deriv_bound_of_deriv_variation
    {F : ℂ → ℂ} {a A : ℂ} {r μ : ℝ} {K : NNReal}
    (hAinv : A * deriv F a = 1)
    (hderivAt : ∀ y ∈ Metric.closedBall a r, HasDerivAt F (deriv F y) y)
    (hvar : ∀ y ∈ Metric.closedBall a r, ‖deriv F y - deriv F a‖ ≤ μ)
    (hsmall : ‖A‖ * μ ≤ (K : ℝ)) :
    ∀ y ∈ Metric.closedBall a r,
      ‖deriv (fun w => w - A * F w) y‖ ≤ (K : ℝ) := by
  intro y hy
  rw [deriv_newton_correction_eq_inv_mul_deriv_sub hAinv (hderivAt y hy)]
  calc
    ‖A * (deriv F a - deriv F y)‖
        = ‖A‖ * ‖deriv F y - deriv F a‖ := by
          rw [norm_mul]
          congr 1
          rw [← norm_neg (deriv F a - deriv F y)]
          ring_nf
    _ ≤ ‖A‖ * μ := by
          exact mul_le_mul_of_nonneg_left (hvar y hy) (norm_nonneg A)
    _ ≤ (K : ℝ) := hsmall

/-- A true Newton step with small center error and small derivative variation has a zero in the
target ball.  This is the form used by a future locally-uniform/simple-zero survival argument. -/
theorem exists_zero_mem_ball_of_newton_deriv_variation
    {ζ a A : ℂ} {R r μ : ℝ} {F : ℂ → ℂ} {K : NNReal}
    (hA : A ≠ 0)
    (hAinv : A * deriv F a = 1)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hclosed : Metric.closedBall a r ⊆ Metric.ball ζ R)
    (hcenter : ‖A‖ * ‖F a‖ ≤ (1 - (K : ℝ)) * r)
    (hderivAt : ∀ y ∈ Metric.closedBall a r, HasDerivAt F (deriv F y) y)
    (hvar : ∀ y ∈ Metric.closedBall a r, ‖deriv F y - deriv F a‖ ≤ μ)
    (hsmall : ‖A‖ * μ ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, F y = 0 := by
  refine exists_zero_mem_ball_of_newton_contraction
    (ζ := ζ) (a := a) (A := A) (R := R) (r := r) (F := F) (K := K)
    hA hr hK hclosed ?_ ?_
    (newton_correction_deriv_bound_of_deriv_variation hAinv hderivAt hvar hsmall)
  · have hdist : dist (a - A * F a) a ≤ (1 - (K : ℝ)) * r := by
      rw [dist_eq_norm]
      rw [show a - A * F a - a = -(A * F a) by ring, norm_neg, norm_mul]
      exact hcenter
    have hKle : (K : ℝ) ≤ 1 := le_of_lt hK
    nlinarith [hdist, hr, NNReal.coe_nonneg K]
  · intro y hy
    have hT : HasDerivAt (fun w => w - A * F w) (1 - A * deriv F y) y :=
      (hasDerivAt_id y).sub ((hderivAt y hy).const_mul A)
    have hderiv_eq :
        deriv (fun w => w - A * F w) y = 1 - A * deriv F y := hT.deriv
    simpa [hderiv_eq] using hT.hasDerivWithinAt (s := Metric.closedBall a r)

/-- Closed-ball version of `exists_zero_mem_ball_of_newton_deriv_variation`. -/
theorem exists_zero_mem_closedBall_of_newton_deriv_variation
    {a A : ℂ} {r μ : ℝ} {F : ℂ → ℂ} {K : NNReal}
    (hA : A ≠ 0)
    (hAinv : A * deriv F a = 1)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hcenter : ‖A‖ * ‖F a‖ ≤ (1 - (K : ℝ)) * r)
    (hderivAt : ∀ y ∈ Metric.closedBall a r, HasDerivAt F (deriv F y) y)
    (hvar : ∀ y ∈ Metric.closedBall a r, ‖deriv F y - deriv F a‖ ≤ μ)
    (hsmall : ‖A‖ * μ ≤ (K : ℝ)) :
    ∃ y ∈ Metric.closedBall a r, F y = 0 := by
  refine exists_zero_of_newton_contraction_closedBall
    (a := a) (A := A) (r := r) (F := F) (K := K)
    hA hr hK ?_ ?_
    (newton_correction_deriv_bound_of_deriv_variation hAinv hderivAt hvar hsmall)
  · have hdist : dist (a - A * F a) a ≤ (1 - (K : ℝ)) * r := by
      rw [dist_eq_norm]
      rw [show a - A * F a - a = -(A * F a) by ring, norm_neg, norm_mul]
      exact hcenter
    have hKle : (K : ℝ) ≤ 1 := le_of_lt hK
    nlinarith [hdist, hr, NNReal.coe_nonneg K]
  · intro y hy
    have hT : HasDerivAt (fun w => w - A * F w) (1 - A * deriv F y) y :=
      (hasDerivAt_id y).sub ((hderivAt y hy).const_mul A)
    have hderiv_eq :
        deriv (fun w => w - A * F w) y = 1 - A * deriv F y := hT.deriv
    simpa [hderiv_eq] using hT.hasDerivWithinAt (s := Metric.closedBall a r)

/-- Periodic-point specialization of `exists_zero_mem_ball_of_newton_deriv_variation`, using the
true displacement function `f_c^[q] - id`.  This is the Newton/Hurwitz producer needed after a
Poincare-type construction supplies center and derivative-variation estimates for the displacement. -/
theorem exists_positive_periodic_mem_ball_of_displacement_newton_deriv_variation
    {c ζ a A : ℂ} {q : ℕ} {R r μ : ℝ} {K : NNReal}
    (hq : 1 ≤ q)
    (hA : A ≠ 0)
    (hAinv : A * deriv (fun w => (quadratic c)^[q] w - w) a = 1)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hclosed : Metric.closedBall a r ⊆ Metric.ball ζ R)
    (hcenter : ‖A‖ * ‖(quadratic c)^[q] a - a‖ ≤ (1 - (K : ℝ)) * r)
    (hvar : ∀ y ∈ Metric.closedBall a r,
      ‖deriv (fun w => (quadratic c)^[q] w - w) y -
        deriv (fun w => (quadratic c)^[q] w - w) a‖ ≤ μ)
    (hsmall : ‖A‖ * μ ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q' : ℕ, 1 ≤ q' ∧ (quadratic c)^[q'] y = y := by
  let F : ℂ → ℂ := fun w => (quadratic c)^[q] w - w
  have hderivAt : ∀ y ∈ Metric.closedBall a r, HasDerivAt F (deriv F y) y := by
    intro y _hy
    have hdiff : DifferentiableAt ℂ F y := by
      dsimp [F]
      exact ((differentiable_quadratic_iterate c q).differentiableAt).sub differentiableAt_id
    exact hdiff.hasDerivAt
  obtain ⟨y, hy, hzero⟩ :=
    exists_zero_mem_ball_of_newton_deriv_variation
      (ζ := ζ) (a := a) (A := A) (R := R) (r := r) (μ := μ)
      (F := F) (K := K)
      hA (by simpa [F] using hAinv) hr hK hclosed
      (by simpa [F] using hcenter) hderivAt
      (by simpa [F] using hvar) hsmall
  refine ⟨y, hy, q, hq, ?_⟩
  exact sub_eq_zero.mp hzero

/-- Scaled-coordinate periodic-point producer for the Poincare/Hurwitz route.

Instead of contracting the unscaled displacement near a forward-hit preimage, this theorem applies
Newton zero-survival to the rescaled displacement
`t ↦ f_c^[q] (z + scale * t) - (z + scale * t)`, then maps the surviving zero back to the original
plane.  This is the right interface when the natural root lives at scale `|scale|` around `z`. -/
theorem exists_positive_periodic_mem_ball_of_scaled_displacement_newton_deriv_variation
    {c ζ z τ scale A : ℂ} {q : ℕ} {R r μ : ℝ} {K : NNReal}
    (hq : 1 ≤ q)
    (hA : A ≠ 0)
    (hAinv : A *
      deriv (fun t => (quadratic c)^[q] (z + scale * t) - (z + scale * t)) τ = 1)
    (hr : 0 ≤ r)
    (hK : K < 1)
    (hscale : ∀ t ∈ Metric.closedBall τ r, z + scale * t ∈ Metric.ball ζ R)
    (hcenter :
      ‖A‖ * ‖(quadratic c)^[q] (z + scale * τ) - (z + scale * τ)‖ ≤
        (1 - (K : ℝ)) * r)
    (hvar : ∀ t ∈ Metric.closedBall τ r,
      ‖deriv (fun u => (quadratic c)^[q] (z + scale * u) - (z + scale * u)) t -
        deriv (fun u => (quadratic c)^[q] (z + scale * u) - (z + scale * u)) τ‖ ≤ μ)
    (hsmall : ‖A‖ * μ ≤ (K : ℝ)) :
    ∃ y ∈ Metric.ball ζ R, ∃ q' : ℕ, 1 ≤ q' ∧ (quadratic c)^[q'] y = y := by
  let F : ℂ → ℂ := fun t => (quadratic c)^[q] (z + scale * t) - (z + scale * t)
  have hderivAt : ∀ t ∈ Metric.closedBall τ r, HasDerivAt F (deriv F t) t := by
    intro t _ht
    have haff : DifferentiableAt ℂ (fun u : ℂ => z + scale * u) t :=
      (differentiableAt_const z).add (differentiableAt_id.const_mul scale)
    have hdiff : DifferentiableAt ℂ F t := by
      dsimp [F]
      exact (((differentiable_quadratic_iterate c q).differentiableAt.comp t haff).sub haff)
    exact hdiff.hasDerivAt
  obtain ⟨t, ht, hzero⟩ :=
    exists_zero_mem_closedBall_of_newton_deriv_variation
      (a := τ) (A := A) (r := r) (μ := μ) (F := F) (K := K)
      hA (by simpa [F] using hAinv) hr hK
      (by simpa [F] using hcenter) hderivAt
      (by simpa [F] using hvar) hsmall
  refine ⟨z + scale * t, hscale t ht, q, hq, ?_⟩
  exact sub_eq_zero.mp hzero

end

end Bottcher
