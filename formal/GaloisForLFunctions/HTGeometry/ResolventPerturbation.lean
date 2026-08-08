/-
# Perturbation of the resolvent and of the Riesz projection

If `l` is in the resolvent set of `a` and `b` is close enough to `a`, then `l` is in the resolvent
set of `b` as well, and the two resolvents are close:

  `R_b(l) − R_a(l) = R_b(l) (b − a) R_a(l)`.

On a circle contained in the resolvent set of `a` the resolvent is bounded, so the estimate is
uniform there, and integrating it shows that the Riesz projection depends continuously on the
element in the operator norm.

Main results:
* `mem_resolventSet_of_norm_sub_mul_lt` — the resolvent set is stable under small perturbations.
* `resolvent_sub_resolvent_perturb` — the second resolvent identity.
* `norm_resolvent_sub_le_of_norm_sub_le` — the quantitative form.
* `exists_norm_resolvent_le_on_sphere` — a uniform resolvent bound on a contour.
* `norm_rieszProjection_sub_le` — **the Riesz projection is norm continuous in the element**.
-/
import GaloisForLFunctions.HTGeometry.RieszProjection

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] {a b : A} {l : ℂ}

/-- **The resolvent set is stable under perturbations smaller than the reciprocal resolvent
norm.** -/
theorem mem_resolventSet_of_norm_sub_mul_lt (ha : l ∈ resolventSet ℂ a)
    (h : ‖b - a‖ * ‖resolvent a l‖ < 1) : l ∈ resolventSet ℂ b := by
  have hfac : algebraMap ℂ A l - b
      = (algebraMap ℂ A l - a) * (1 - resolvent a l * (b - a)) := by
    rw [mul_sub, mul_one, ← mul_assoc, sub_mul_resolvent ha, one_mul]
    abel
  have hlt : ‖resolvent a l * (b - a)‖ < 1 := by
    have := norm_mul_le (resolvent a l) (b - a)
    nlinarith [norm_nonneg (resolvent a l * (b - a)), norm_nonneg (b - a),
      norm_nonneg (resolvent a l)]
  have : IsUnit (algebraMap ℂ A l - b) := by
    rw [hfac]
    exact (isUnit_of_mem_resolventSet ha).mul (isUnit_one_sub_of_norm_lt_one hlt)
  exact this

omit [CompleteSpace A] in
/-- **The second resolvent identity** `R_b − R_a = R_b (b − a) R_a`. -/
theorem resolvent_sub_resolvent_perturb (ha : l ∈ resolventSet ℂ a) (hb : l ∈ resolventSet ℂ b) :
    resolvent b l - resolvent a l = resolvent b l * (b - a) * resolvent a l := by
  have hd : b - a = (algebraMap ℂ A l - a) - (algebraMap ℂ A l - b) := by abel
  rw [hd, mul_sub, sub_mul, mul_assoc (resolvent b l) (algebraMap ℂ A l - a),
    sub_mul_resolvent ha, mul_one, resolvent_mul_sub hb, one_mul]

omit [CompleteSpace A] in
/-- The norm of the perturbed resolvent, in product form. -/
theorem norm_resolvent_mul_le (ha : l ∈ resolventSet ℂ a) (hb : l ∈ resolventSet ℂ b) :
    ‖resolvent b l‖ * (1 - ‖b - a‖ * ‖resolvent a l‖) ≤ ‖resolvent a l‖ := by
  have hid := resolvent_sub_resolvent_perturb ha hb
  have hle : ‖resolvent b l - resolvent a l‖
      ≤ ‖resolvent b l‖ * ‖b - a‖ * ‖resolvent a l‖ := by
    rw [hid]
    exact le_trans (norm_mul_le _ _) (by
      have := norm_mul_le (resolvent b l) (b - a)
      nlinarith [norm_nonneg (resolvent a l), norm_nonneg (resolvent b l * (b - a))])
  have htri : ‖resolvent b l‖ - ‖resolvent a l‖ ≤ ‖resolvent b l - resolvent a l‖ :=
    norm_sub_norm_le _ _
  nlinarith

/-- **The quantitative resolvent perturbation estimate** on a set where the resolvent of `a` is
bounded by `M`. -/
theorem norm_resolvent_sub_le_of_norm_sub_le {M : ℝ} (ha : l ∈ resolventSet ℂ a)
    (hM : ‖resolvent a l‖ ≤ M) (hab : 2 * ‖b - a‖ * M ≤ 1) :
    l ∈ resolventSet ℂ b ∧
      ‖resolvent b l - resolvent a l‖ ≤ 2 * M ^ 2 * ‖b - a‖ := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) hM
  have hd0 : 0 ≤ ‖b - a‖ := norm_nonneg _
  have hhalf : ‖b - a‖ * ‖resolvent a l‖ ≤ 1 / 2 := by nlinarith
  have hlt : ‖b - a‖ * ‖resolvent a l‖ < 1 := by linarith
  have hb : l ∈ resolventSet ℂ b := mem_resolventSet_of_norm_sub_mul_lt ha hlt
  refine ⟨hb, ?_⟩
  have hnb : ‖resolvent b l‖ ≤ 2 * M := by
    have := norm_resolvent_mul_le ha hb
    nlinarith [norm_nonneg (resolvent b l)]
  have hid := resolvent_sub_resolvent_perturb ha hb
  have hle : ‖resolvent b l - resolvent a l‖
      ≤ ‖resolvent b l‖ * ‖b - a‖ * ‖resolvent a l‖ := by
    rw [hid]
    exact le_trans (norm_mul_le _ _) (by
      have := norm_mul_le (resolvent b l) (b - a)
      nlinarith [norm_nonneg (resolvent a l), norm_nonneg (resolvent b l * (b - a))])
  calc ‖resolvent b l - resolvent a l‖
      ≤ ‖resolvent b l‖ * ‖b - a‖ * ‖resolvent a l‖ := hle
    _ ≤ 2 * M * ‖b - a‖ * M := by
        have h1 : ‖resolvent b l‖ * ‖b - a‖ ≤ 2 * M * ‖b - a‖ :=
          mul_le_mul_of_nonneg_right hnb hd0
        have h2 : (0 : ℝ) ≤ 2 * M * ‖b - a‖ := by nlinarith
        exact mul_le_mul h1 hM (norm_nonneg _) h2
    _ = 2 * M ^ 2 * ‖b - a‖ := by ring

/-- **A uniform resolvent bound on a contour in the resolvent set.** -/
theorem exists_norm_resolvent_le_on_sphere (a : A) {c : ℂ} {r : ℝ}
    (h : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ a) :
    ∃ M : ℝ, 0 < M ∧ ∀ lam ∈ sphere c r, ‖resolvent a lam‖ ≤ M := by
  have hcont : ContinuousOn (resolvent a) (sphere c r) := fun lam hlam =>
    ((spectrum.hasDerivAt_resolvent_const_left (h lam hlam)).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere c r).exists_bound_of_continuousOn hcont
  exact ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun lam hlam => le_trans (hC lam hlam) (le_max_left _ _)⟩

/-- **The Riesz projection is norm continuous in the element.** -/
theorem norm_rieszProjection_sub_le (a b : A) {c : ℂ} {r M : ℝ} (hr : 0 ≤ r)
    (ha : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ a)
    (hbound : ∀ lam ∈ sphere c r, ‖resolvent a lam‖ ≤ M)
    (hab : 2 * ‖b - a‖ * M ≤ 1) :
    ‖rieszProjection b c r - rieszProjection a c r‖ ≤ r * (2 * M ^ 2 * ‖b - a‖) := by
  have hbres : ∀ lam ∈ sphere c r, lam ∈ resolventSet ℂ b := fun lam hlam =>
    (norm_resolvent_sub_le_of_norm_sub_le (ha lam hlam) (hbound lam hlam) hab).1
  have hcib : CircleIntegrable (resolvent b) c r := circleIntegrable_resolvent hr hbres
  have hcia : CircleIntegrable (resolvent a) c r := circleIntegrable_resolvent hr ha
  have hsplit : rieszProjection b c r - rieszProjection a c r
      = (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ lam in C(c, r), (resolvent b lam - resolvent a lam) := by
    rw [rieszProjection, rieszProjection, ← smul_sub, circleIntegral.integral_sub hcib hcia]
  have hptw : ∀ lam ∈ sphere c r, ‖resolvent b lam - resolvent a lam‖ ≤ 2 * M ^ 2 * ‖b - a‖ :=
    fun lam hlam => (norm_resolvent_sub_le_of_norm_sub_le (ha lam hlam) (hbound lam hlam) hab).2
  have hint : ‖∮ lam in C(c, r), (resolvent b lam - resolvent a lam)‖
      ≤ 2 * Real.pi * r * (2 * M ^ 2 * ‖b - a‖) :=
    circleIntegral.norm_integral_le_of_norm_le_const hr hptw
  have hnorm : ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv]
    congr 1
    simp [Complex.norm_I, abs_of_pos Real.pi_pos]
  rw [hsplit, norm_smul, hnorm]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [inv_mul_eq_div, div_le_iff₀ hpi]
  calc ‖∮ lam in C(c, r), (resolvent b lam - resolvent a lam)‖
      ≤ 2 * Real.pi * r * (2 * M ^ 2 * ‖b - a‖) := hint
    _ = r * (2 * M ^ 2 * ‖b - a‖) * (2 * Real.pi) := by ring

end GaloisForLFunctions.HTGeometry
