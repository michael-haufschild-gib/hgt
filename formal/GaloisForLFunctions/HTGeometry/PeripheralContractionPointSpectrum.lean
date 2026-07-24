import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Bases

/-!
# Peripheral point-spectrum rigidity for contractions

If a contraction has an eigenvector with a unimodular eigenvalue, equality in the norm bound
forces the adjoint eigenrelation as well.  Consequently eigenvectors belonging to distinct
peripheral eigenvalues are orthogonal.

In a separable Hilbert space, an injectively parameterized family of nonzero peripheral
eigenvectors is therefore countable.  This is useful when auditing proposed analytic
reproducing-kernel models: a continuum of nonzero point evaluations cannot all become distinct
unimodular eigenfunctionals of one contraction.
-/

open scoped InnerProductSpace

noncomputable section

namespace HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/--
Equality case for a contraction eigenvector: a unimodular eigenvector is also an adjoint
eigenvector with conjugate eigenvalue.
-/
theorem adjoint_eigenvector_of_contraction
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    {x : H} {lam : ℂ} (hx : T x = lam • x) (hlam : ‖lam‖ = 1) :
    T.adjoint x = star lam • x := by
  by_cases hx0 : x = 0
  · subst x
    simp
  have hAdjNorm : ‖T.adjoint‖ ≤ 1 := by simpa using hT
  have hu : ‖T.adjoint x‖ ≤ ‖x‖ := by
    calc
      ‖T.adjoint x‖ ≤ ‖T.adjoint‖ * ‖x‖ := T.adjoint.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hAdjNorm (norm_nonneg x)
      _ = ‖x‖ := one_mul _
  have hv : ‖star lam • x‖ = ‖x‖ := by
    rw [norm_smul, norm_star, hlam, one_mul]
  have hinner : ⟪T.adjoint x, star lam • x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_smul_right, T.adjoint_inner_left, hx, inner_smul_right,
      ← mul_assoc, ← starRingEnd_apply, RCLike.conj_mul]
    simp [hlam, inner_self_eq_norm_sq_to_K]
  have hlow : ‖x‖ ^ 2 ≤ ‖T.adjoint x‖ * ‖star lam • x‖ := by
    calc
      ‖x‖ ^ 2 = ‖((‖x‖ ^ 2 : ℝ) : ℂ)‖ := by
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x‖)]
      _ = ‖⟪T.adjoint x, star lam • x⟫_ℂ‖ := by rw [hinner]
      _ ≤ ‖T.adjoint x‖ * ‖star lam • x‖ := norm_inner_le_norm _ _
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have huEq : ‖T.adjoint x‖ = ‖x‖ := by
    rw [hv, pow_two] at hlow
    nlinarith [norm_nonneg (T.adjoint x)]
  have hu0 : T.adjoint x ≠ 0 := by
    rw [← norm_ne_zero_iff, huEq]
    exact ne_of_gt hxnorm
  have hphase :
      ⟪T.adjoint x, star lam • x⟫_ℂ =
        (‖T.adjoint x‖ : ℂ) * ‖star lam • x‖ := by
    rw [hinner, huEq, hv, pow_two]
    norm_cast
  have hcol := (inner_eq_norm_mul_iff_div hu0).mp hphase
  rw [huEq, hv] at hcol
  simpa [Complex.ofReal_ne_zero.mpr (ne_of_gt hxnorm)] using hcol

/--
One peripheral eigenvector of a contraction is orthogonal to every eigenvector belonging to a
different eigenvalue.
-/
theorem inner_eq_zero_of_distinct_peripheral_eigenvectors
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    {x y : H} {lam mu : ℂ}
    (hx : T x = lam • x) (hy : T y = mu • y)
    (hlam : ‖lam‖ = 1) (hne : lam ≠ mu) :
    ⟪x, y⟫_ℂ = 0 := by
  have hadj := adjoint_eigenvector_of_contraction T hT hx hlam
  have hpair := T.adjoint_inner_left y x
  rw [hadj, hy, inner_smul_left, inner_smul_right] at hpair
  simp only [starRingEnd_apply, star_star] at hpair
  have hprod : (lam - mu) * ⟪x, y⟫_ℂ = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact hpair
  exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne)

/--
An injectively parameterized family of nonzero peripheral eigenvectors of a contraction on a
separable Hilbert space is countable.
-/
theorem countable_of_injective_peripheral_eigenvector_family
    [TopologicalSpace.SeparableSpace H] {ι : Type*}
    (T : H →L[ℂ] H) (hT : ‖T‖ ≤ 1)
    (v : ι → H) (lam : ι → ℂ)
    (hv : ∀ i, v i ≠ 0)
    (heigen : ∀ i, T (v i) = lam i • v i)
    (hperipheral : ∀ i, ‖lam i‖ = 1)
    (hinj : Function.Injective lam) :
    Countable ι := by
  let u : ι → H := fun i => ((‖v i‖ : ℂ)⁻¹) • v i
  have huNorm : ∀ i, ‖u i‖ = 1 := by
    intro i
    simp only [u, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (v i))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hv i))
  have huOrth : Pairwise fun i j => ⟪u i, u j⟫_ℂ = 0 := by
    intro i j hij
    have hlam : lam i ≠ lam j := fun h => hij (hinj h)
    have hinner := inner_eq_zero_of_distinct_peripheral_eigenvectors
      T hT (heigen i) (heigen j) (hperipheral i) hlam
    simp only [u, inner_smul_left, inner_smul_right, hinner, mul_zero]
  have huSeparated : Pairwise fun i j => 1 ≤ dist (u i) (u j) := by
    intro i j hij
    rw [dist_eq_norm]
    have horthNeg : ⟪u i, -u j⟫_ℂ = 0 := by
      rw [inner_neg_right, huOrth hij, neg_zero]
    have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (u i) (-u j) horthNeg
    rw [huNorm i, norm_neg, huNorm j] at hsq
    norm_num at hsq
    have hsq' : ‖u i - u j‖ * ‖u i - u j‖ = 2 := by
      simpa only [sub_eq_add_neg] using hsq
    nlinarith [norm_nonneg (u i - u j)]
  have hballs :
      Pairwise (Function.onFun Disjoint fun i => Metric.ball (u i) (1 / 2)) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    norm_num
    exact huSeparated hij
  apply hballs.countable_of_isOpen_disjoint
  · intro i
    exact Metric.isOpen_ball
  · intro i
    exact ⟨u i, Metric.mem_ball_self (by norm_num)⟩

end HTGeometry
