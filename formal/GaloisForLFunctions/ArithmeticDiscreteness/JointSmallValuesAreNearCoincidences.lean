import GaloisForLFunctions.ArithmeticDiscreteness.ANearCoincidenceFlattensZeta
import GaloisForLFunctions.RHTower.RiemannGaussian.FiniteToEntireRouche
import GaloisForLFunctions.HTGeometry.ZeroDivisorCount

/-!
# Joint small values are near-coincidences

The converse of `NearCoincidencesAreJointSmallValues`. If an entire `F` is jointly small with its
derivative at `c` while its second derivative is not, `F` has exactly two zeros (with multiplicity)
near `c`.

* **Third-order Taylor bound** (`norm_taylor_two_remainder_le`). If `|F| ≤ M` on `‖z − c‖ ≤ R`,
  then `|F(z) − F(c) − F'(c)(z − c) − ½F''(c)(z − c)²| ≤ (64M/R³)|z − c|³` for `‖z − c‖ ≤ R/8`:
  `|F'''| ≤ 64M/R³` there (`norm_deriv_deriv_le` for `F'`), and three mean value steps.
* **Joint small values force two zeros** (`two_zeros_of_joint_small_values`). If
  `|F(c)| + |F'(c)| r + (64M/R³) r³ < ½|F''(c)| r²` for some `0 < r ≤ R/8`, then `F` has zeros in
  `‖z − c‖ < r` of total multiplicity exactly two: on the circle `F` is dominated by
  `½F''(c)(z − c)²`, and Rouché (`RiemannGaussian.circleIntegral_logDeriv_eq_of_norm_sub_lt`,
  `HTGeometry.exists_zeroSet_circleIntegral_logDeriv`) transfers its double zero.

With `NearCoincidencesAreJointSmallValues`: two zeros at distance `2h` make `(F, F')` jointly small
at scale `(h², h)`, and joint smallness at scale `(r², r)` with `F''(c)` bounded below gives two
zeros within `r`. Collide-or-repel is the emptiness of the joint small-value set of `(F, F')`.
-/

open Complex Metric

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The second-order Taylor remainder at `c`. -/
def taylorTwoRemainder (F : ℂ → ℂ) (c z : ℂ) : ℂ :=
  F z - F c - deriv F c * (z - c) - deriv (deriv F) c / 2 * (z - c) ^ 2

/-- **Third-order Taylor bound.** -/
theorem norm_taylor_two_remainder_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c : ℂ} {R M : ℝ}
    (hR : 0 < R) (hM : ∀ z ∈ closedBall c R, ‖F z‖ ≤ M) {z : ℂ} (hz : ‖z - c‖ ≤ R / 8) :
    ‖taylorTwoRemainder F c z‖ ≤ 64 * M / R ^ 3 * ‖z - c‖ ^ 3 := by
  have hF1 : Differentiable ℂ (deriv F) := fun w =>
    (hF.differentiableOn.deriv isOpen_univ).differentiableAt (isOpen_univ.mem_nhds trivial)
  have hF2 : Differentiable ℂ (deriv (deriv F)) := fun w =>
    (hF1.differentiableOn.deriv isOpen_univ).differentiableAt (isOpen_univ.mem_nhds trivial)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_closedBall_self hR.le))
  -- `|F'| ≤ 2M/R` on `closedBall c (R/2)`
  have hd1 : ∀ w ∈ closedBall c (R / 2), ‖deriv F w‖ ≤ 2 * M / R := by
    intro w hw
    have hwsub : closedBall w (R / 2) ⊆ closedBall c R := by
      intro u hu
      rw [mem_closedBall] at hu hw ⊢
      linarith [dist_triangle u w c]
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hF.differentiableOn.diffContOnCl) fun u hu => hM u (hwsub (sphere_subset_closedBall hu))
    calc ‖deriv F w‖ ≤ M / (R / 2) := this
      _ = 2 * M / R := by field_simp
  -- `|F'''| ≤ 64M/R³` on `closedBall c (R/8)`
  have hd3 : ∀ w ∈ closedBall c (R / 8), ‖deriv (deriv (deriv F)) w‖ ≤ 64 * M / R ^ 3 := by
    intro w hw
    have := norm_deriv_deriv_le isOpen_univ hF1.differentiableOn (by positivity : 0 < R / 2)
      (Set.subset_univ _) hd1 w (by rw [mem_closedBall] at hw ⊢; linarith)
    calc ‖deriv (deriv (deriv F)) w‖ ≤ 8 * (2 * M / R) / (R / 2) ^ 2 := this
      _ = 64 * M / R ^ 3 := by field_simp; ring
  set K : ℝ := 64 * M / R ^ 3 with hK
  have hK0 : 0 ≤ K := by positivity
  set ρ : ℝ := ‖z - c‖ with hρ
  have hseg : segment ℝ c z ⊆ closedBall c (R / 8) :=
    (convex_closedBall c _).segment_subset (mem_closedBall_self (by positivity))
      (by rw [mem_closedBall, dist_eq_norm]; exact hz)
  have hnear : ∀ w ∈ segment ℝ c z, ‖w - c‖ ≤ ρ := by
    intro w hw
    obtain ⟨t, u, ht, hu, htu, rfl⟩ := hw
    have : t • c + u • z - c = u • (z - c) := by
      rw [show t = 1 - u by linarith]; simp only [sub_smul, one_smul, smul_sub]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  -- step 1: `|F''(w) − F''(c)| ≤ K ρ` on the segment
  have hs1 : ∀ w ∈ segment ℝ c z, ‖deriv (deriv F) w - deriv (deriv F) c‖ ≤ K * ρ := by
    intro w hw
    have := (convex_segment c z).norm_image_sub_le_of_norm_deriv_le
      (fun v _ => hF2 v) (fun v hv => hd3 v (hseg hv)) (left_mem_segment ℝ c z) hw
    exact this.trans (mul_le_mul_of_nonneg_left (hnear w hw) hK0)
  -- step 2: `g₁(w) = F'(w) − F'(c) − F''(c)(w − c)` is at most `K ρ²`
  set g₁ : ℂ → ℂ := fun w => deriv F w - deriv F c - deriv (deriv F) c * (w - c) with hg₁
  have hg₁d : ∀ w, HasDerivAt g₁ (deriv (deriv F) w - deriv (deriv F) c) w := by
    intro w
    have := (((hF1 w).hasDerivAt.sub_const (deriv F c)).sub
      (((hasDerivAt_id w).sub_const c).const_mul (deriv (deriv F) c)))
    rw [mul_one] at this
    exact this
  have hs2 : ∀ w ∈ segment ℝ c z, ‖g₁ w‖ ≤ K * ρ * ρ := by
    intro w hw
    have := (convex_segment c z).norm_image_sub_le_of_norm_deriv_le
      (fun v _ => (hg₁d v).differentiableAt) (fun v hv => by rw [(hg₁d v).deriv]; exact hs1 v hv)
      (left_mem_segment ℝ c z) hw
    have hg0 : g₁ c = 0 := by simp [hg₁]
    rw [hg0, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hnear w hw) (by positivity))
  -- step 3: the remainder
  have hgd : ∀ w, HasDerivAt (fun v => taylorTwoRemainder F c v) (g₁ w) w := by
    intro w
    have h1 := (((hF w).hasDerivAt.sub_const (F c)).sub
      (((hasDerivAt_id w).sub_const c).const_mul (deriv F c))).sub
      ((((hasDerivAt_id w).sub_const c).pow 2).const_mul (deriv (deriv F) c / 2))
    unfold taylorTwoRemainder
    refine h1.congr_deriv ?_
    simp only [hg₁, id]
    push_cast
    ring
  have := (convex_segment c z).norm_image_sub_le_of_norm_deriv_le
    (fun v _ => (hgd v).differentiableAt) (fun v hv => by rw [(hgd v).deriv]; exact hs2 v hv)
    (left_mem_segment ℝ c z) (right_mem_segment ℝ c z)
  have hr0 : taylorTwoRemainder F c c = 0 := by simp [taylorTwoRemainder]
  rw [hr0, sub_zero] at this
  calc ‖taylorTwoRemainder F c z‖ ≤ K * ρ * ρ * ‖z - c‖ := this
    _ = K * ρ ^ 3 := by rw [← hρ]; ring

/-- **Joint small values force two zeros.** -/
theorem two_zeros_of_joint_small_values {F : ℂ → ℂ} (hF : Differentiable ℂ F) {c : ℂ}
    {R M r : ℝ} (hR : 0 < R) (hM : ∀ z ∈ closedBall c R, ‖F z‖ ≤ M) (hr : 0 < r)
    (hrR : r ≤ R / 8) (h2 : deriv (deriv F) c ≠ 0)
    (hsmall : ‖F c‖ + ‖deriv F c‖ * r + 64 * M / R ^ 3 * r ^ 3 <
      ‖deriv (deriv F) c‖ / 2 * r ^ 2) :
    ∃ Z : Finset ℂ, (∀ z ∈ Z, z ∈ ball c r) ∧ (∀ z ∈ ball c r, F z = 0 ↔ z ∈ Z) ∧
      ∑ z ∈ Z, HTGeometry.zeroMult F z = 2 := by
  classical
  set a : ℂ := deriv (deriv F) c / 2 with ha
  have ha0 : a ≠ 0 := div_ne_zero h2 two_ne_zero
  set Q : ℂ → ℂ := fun z => a * (z - c) ^ 2 with hQ
  have hQd : Differentiable ℂ Q := (differentiable_const _).mul ((differentiable_id.sub_const c).pow 2)
  -- domination on the circle
  have hdom : ∀ z ∈ sphere c r, ‖F z - Q z‖ < ‖Q z‖ := by
    intro z hz
    have hzr : ‖z - c‖ = r := by rw [← dist_eq_norm]; exact mem_sphere.mp hz
    have hrem := norm_taylor_two_remainder_le hF hR hM (by rw [hzr]; exact hrR)
    have hdecomp : F z - Q z = F c + deriv F c * (z - c) + taylorTwoRemainder F c z := by
      simp only [hQ, ha, taylorTwoRemainder]; ring
    have hQn : ‖Q z‖ = ‖deriv (deriv F) c‖ / 2 * r ^ 2 := by
      rw [hQ, norm_mul, norm_pow, hzr, ha, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    rw [hdecomp, hQn]
    calc ‖F c + deriv F c * (z - c) + taylorTwoRemainder F c z‖
        ≤ ‖F c‖ + ‖deriv F c‖ * r + 64 * M / R ^ 3 * r ^ 3 := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans ?_) ?_)
          · rw [norm_mul, hzr]
          · rw [hzr] at hrem; exact hrem
      _ < _ := hsmall
  -- equal logarithmic-derivative integrals
  have hint := RiemannGaussian.circleIntegral_logDeriv_eq_of_norm_sub_lt hQd hF hr.le hdom
  have hneF : ∀ ζ ∈ sphere c r, F ζ ≠ 0 :=
    (RiemannGaussian.ne_zero_on_sphere_of_norm_sub_lt hdom).2
  have hneQ : ∀ ζ ∈ sphere c r, Q ζ ≠ 0 :=
    (RiemannGaussian.ne_zero_on_sphere_of_norm_sub_lt hdom).1
  obtain ⟨Z, hZb, hZiff, hZint⟩ := HTGeometry.exists_zeroSet_circleIntegral_logDeriv hr
    (lt_add_one r) isOpen_univ (Set.subset_univ _) hF.differentiableOn hneF
  obtain ⟨W, hWb, hWiff, hWint⟩ := HTGeometry.exists_zeroSet_circleIntegral_logDeriv hr
    (lt_add_one r) isOpen_univ (Set.subset_univ _) hQd.differentiableOn hneQ
  -- the zero set of `Q` in the disc is `{c}`, of multiplicity two
  have hW : W = {c} := by
    ext z
    rw [Finset.mem_singleton]
    constructor
    · intro hz
      have h0 := (hWiff z (hWb z hz)).mpr hz
      simp only [hQ, mul_eq_zero, ha0, false_or, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at h0
      exact h0
    · intro hz
      rw [hz]
      exact (hWiff c (mem_ball_self hr)).mp (by simp [hQ])
  have hmultQ : HTGeometry.zeroMult Q c = 2 := by
    have han : AnalyticAt ℂ Q c := hQd.analyticAt c
    have hord : analyticOrderAt Q c = (2 : ℕ) :=
      (han.analyticOrderAt_eq_natCast).mpr ⟨fun _ => a, analyticAt_const, ha0,
        Filter.Eventually.of_forall fun z => by simp [hQ, smul_eq_mul, mul_comm]⟩
    rw [HTGeometry.zeroMult, hord]; rfl
  refine ⟨Z, hZb, hZiff, ?_⟩
  rw [hW, Finset.sum_singleton, hmultQ] at hWint
  have heq := hZint.symm.trans (hint.trans hWint)
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have := mul_left_cancel₀ h2pi heq
  exact_mod_cast this

end GaloisForLFunctions.ArithmeticDiscreteness
