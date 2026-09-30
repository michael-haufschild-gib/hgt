import GaloisForLFunctions.RHTower.KiKimLeeLargeHeightReality
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# Ki–Kim–Lee: the de Bruijn–Newman deformation has only finitely many non-real zeros

For every `t > 0`, `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx` has only finitely many non-real zeros
(`riemannHeat_nonreal_zeros_finite`). Every zero satisfies `(Im z)² ≤ max(¼ − 2t, 0)`, zeros of large
real part are real (`exists_riemannHeat_zeros_real`), so the non-real zeros lie in a compact set;
`H_t` is entire and `H_t(0) ≠ 0`, so its zeros there are finitely many.

At `t = 0` the same statement is the Riemann hypothesis up to finitely many exceptions; the
threshold beyond which the argument applies grows like `2π e^{c/t}` as `t → 0`.
-/

open Complex Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

theorem differentiable_riemannHeat {t : ℝ} (ht : 0 ≤ t) : Differentiable ℂ (riemannHeat t) :=
  (riemannKernel_superExp.mul_exp_sq ht).differentiable

theorem riemannHeat_zero_ne {t : ℝ} (ht : 0 ≤ t) : riemannHeat t 0 ≠ 0 :=
  (riemannKernel_superExp.mul_exp_sq ht).cosTransform_zero_ne

/-- **Ki–Kim–Lee finiteness.** For every `t > 0`, `H_t` has only finitely many non-real zeros. -/
theorem riemannHeat_nonreal_zeros_finite {t : ℝ} (ht : 0 < t) :
    {z : ℂ | riemannHeat t z = 0 ∧ z.im ≠ 0}.Finite := by
  obtain ⟨X₀, hX₀⟩ := exists_riemannHeat_zeros_real ht
  have hdiff := differentiable_riemannHeat ht.le
  have hiso : ∀ z ∈ (univ : Set ℂ), ¬ (∀ᶠ w in 𝓝 z, riemannHeat t w = 0) := by
    intro z _ h
    have := (hdiff.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ z) h (mem_univ 0)
    exact riemannHeat_zero_ne ht.le this
  have hfin := GaloisForLFunctions.HTGeometry.finite_zeros_of_isCompact isOpen_univ
    hdiff.differentiableOn hiso (isCompact_closedBall (0 : ℂ) (|X₀| + 1)) (subset_univ _)
  refine hfin.subset fun z ⟨hz, him⟩ => ⟨?_, hz⟩
  have hre : |z.re| < X₀ := by
    by_contra h
    exact him (hX₀ z hz (not_lt.mp h))
  have him2 : z.im ^ 2 ≤ 1 / 4 :=
    (riemannHeat_zeros_im_sq_le ht hz).trans (max_le (by linarith) (by norm_num))
  have him' : |z.im| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  rw [mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ |X₀| + 1 := by linarith [le_abs_self X₀]

end

end RHTower.DeBruijn
